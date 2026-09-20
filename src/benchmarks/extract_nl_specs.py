"""Convert upstream GNU Texinfo sections into benchmark natural-language descriptions."""

from __future__ import annotations

import argparse
import re
from collections.abc import Callable
from pathlib import Path

from benchmarks.definition import BenchmarkKind
from benchmarks.profiles import ResolvedBenchmark
from benchmarks.repository import BenchmarkRepository

MACRO_RE = re.compile(r"@([A-Za-z]+)\{([^{}]*)\}")
CODE_LIKE_MACROS = {"command", "option", "file", "code", "samp", "env", "url", "w"}
TEXT_LIKE_MACROS = {"var", "dfn", "xref", "pxref", "ref"}
HEADING_PREFIXES = (("@section ", "##"), ("@subsection ", "###"))
CODE_BLOCK_STARTS = {"@example", "@smallexample", "@display"}
CODE_BLOCK_ENDS = {"@end example", "@end smallexample", "@end display"}
TABLE_CONTROL_LINES = {"@end table", "@enumerate", "@end enumerate"}
SPECIAL_PREFIX_MACROS = {
    "@optZero{": "- `-z`, `--zero`: end each output item with NUL instead of newline.",
    "@optNull{": "- `-0`, `--null`: end each output item with NUL instead of newline.",
    "@choptH{": "- `-H`: when recursive, follow command-line symlinks to directories.",
    "@choptL{": "- `-L`: when recursive, follow all symlinks to directories.",
    "@choptP{": "- `-P`: when recursive, do not follow symlinks encountered during traversal.",
}
SPECIAL_EXACT_MACROS = {
    "@choptDefault": "- Default recursive traversal follows command-line symlinks only.",
    "@warnOptDerefWithRec": (
        "- Note: interaction between `--dereference` and recursive traversal is "
        "special and should be handled explicitly."
    ),
}


def extract_node_slice(lines: list[str], node_name: str) -> tuple[int, int, list[str]]:
    start = -1
    for idx, line in enumerate(lines):
        if line.strip() == f"@node {node_name}":
            start = idx
            break
    if start < 0:
        raise ValueError(f"could not find Texinfo node '@node {node_name}'")

    end = len(lines)
    for idx in range(start + 1, len(lines)):
        if lines[idx].strip().startswith("@node "):
            end = idx
            break

    return start + 1, end, lines[start:end]


def replace_texi_macro(match: re.Match[str]) -> str:
    name = match.group(1)
    body = match.group(2)

    if name in CODE_LIKE_MACROS:
        return f"`{body}`"
    if name in TEXT_LIKE_MACROS:
        return body.split(",", 1)[0]
    return "..." if name == "dots" else body


def strip_texi_markup(line: str) -> str:
    current = line.replace("@dots{}", "...")
    previous = None
    while previous != current:
        previous = current
        current = MACRO_RE.sub(replace_texi_macro, current)
    return current


def _render_option_item(line: str) -> str | None:
    if not line.startswith(("@optItem{", "@optItemx{")):
        return None
    inside = line.split("{", 1)[1].rsplit("}", 1)[0]
    parts = [part.strip() for part in inside.split(",") if part.strip()]
    options = [part for part in parts if part.startswith("-")]
    return f"- {', '.join(f'`{opt}`' for opt in options)}" if options else f"- {inside}"


def _macro_invocation(line: str) -> tuple[str, list[str]] | None:
    match = re.fullmatch(r"@([A-Za-z]+)(?:\{(.*)\})?", line)
    if match is None:
        return None
    body = match.group(2)
    args = [] if body is None else [arg.strip() for arg in body.split(",")]
    return match.group(1), args


def _arg(args: list[str], index: int, default: str = "") -> str:
    return args[index] if index < len(args) and args[index] else default


def _option_lines(*options: str) -> list[str]:
    return [f"- `{option}`" for option in options]


def _render_legacy_digest() -> list[str]:
    return [
        "This is a legacy interface to the more modern `cksum` utility.",
        "cksum invocation.",
    ]


def _render_weak_hash(args: list[str]) -> list[str]:
    hash_name = _arg(args, 0, "hash")
    return [
        f"The {hash_name} digest is more reliable than a simple CRC (provided by",
        "the `cksum` command) for detecting accidental file corruption,",
        f"as the chances of accidentally having two files with identical {hash_name}",
        "are vanishingly small. However, it should not be considered secure",
        f"against malicious tampering: although finding a file with a given {hash_name}",
        "fingerprint is considered infeasible at the moment, it is known how",
        "to modify certain files, including digital certificates, so that they",
        f"appear valid when signed with an {hash_name} digest. For more secure hashes,",
        "consider using `sha2`, `sha3`, or `blake2b`,",
        "available through the `cksum` `--algorithm` option.",
    ]


def _render_checksum_usage(args: list[str]) -> list[str]:
    command = _arg(args, 0, "COMMAND")
    return [
        "If a file is specified as `-` or if no files are given",
        f"`{command}` computes the checksum for the standard input.",
        f"`{command}` can also determine whether a file and checksum are",
        "consistent. Synopsis:",
        "",
        "```text",
        f"{command} [option]... [file]...",
        "```",
        "",
        f"`{command}` uses the `Untagged output format`",
        "for each specified file, as described at cksum output modes.",
        "",
        "The program accepts cksum common options. Also see Common options.",
    ]


def _render_may_conflict_with_shell_builtin(args: list[str]) -> list[str]:
    command = _arg(args, 0, "COMMAND")
    return [
        f"Due to shell aliases and built-in `{command}` functions, using an",
        f"unadorned `{command}` interactively or in a script may get you",
        "different functionality than that described here. Invoke it via",
        f"`env` (i.e., `env {command} ...`) to avoid interference from the shell.",
    ]


def _render_print_dash(args: list[str]) -> list[str]:
    command = _arg(args, 0, "COMMAND")
    return [
        "To output an argument that begins with `-`, precede it with",
        f"`--`, e.g., `{command} -- --help`.",
    ]


def _render_opt_backup() -> list[str]:
    return [
        *_option_lines("-b", "--backup[=method]"),
        "Make a backup of each file that would otherwise be overwritten or removed.",
    ]


def _render_opt_backup_suffix() -> list[str]:
    return [
        *_option_lines("-S suffix", "--suffix=suffix"),
        "Append suffix to each backup file made with `-b`.",
        "Backup options.",
    ]


def _render_opt_target_directory() -> list[str]:
    return [
        *_option_lines("-t directory", "--target-directory=directory"),
        "Specify the destination directory.",
        "Target directory.",
    ]


def _render_opt_no_target_directory() -> list[str]:
    return [
        *_option_lines("-T", "--no-target-directory"),
        "Do not treat the last operand specially when it is a directory or a",
        "symbolic link to a directory. Target directory.",
    ]


def _render_opt_strip_trailing_slashes() -> list[str]:
    return [
        *_option_lines("--strip-trailing-slashes"),
        "Remove any trailing slashes from each source argument.",
        "Trailing slashes.",
    ]


def _render_opt_debug_copy() -> list[str]:
    return [
        *_option_lines("--debug"),
        "Print extra information to standard output, explaining how files are copied.",
        "This option implies the `--verbose` option.",
    ]


def _render_mv_opts_ifn() -> list[str]:
    return [
        "If you specify more than one of the `-i`, `-f`, `-n`",
        "options, only the final one takes effect.",
    ]


def _render_which_update() -> list[str]:
    return [
        "which gives more control over which existing files in the",
        "destination are replaced, and its value can be one of the following:",
        "",
        "- `all`: the default when `--update` is not specified; replace all existing "
        "destination files.",
        "- `none`: like deprecated `--no-clobber`; replace no destination files, and "
        "skipping a file does not induce failure.",
        "- `none-fail`: replace no destination files, but diagnose skipped files and "
        "induce failure.",
        "- `older`: the default when `--update` is specified; replace files if they "
        "are older than the corresponding source file.",
    ]


def _render_files_zero_from_option(args: list[str]) -> list[str]:
    command = _arg(args, 0, "COMMAND")
    sub_list_output = _arg(args, 2, "output")
    return [
        "- `--files0-from=file`",
        "Disallow processing files named on the command line, and instead process",
        "those named in file file; each name being terminated by a zero byte",
        "(ASCII NUL).",
        "This is useful when the list of file names is so long that it may exceed a",
        "command line length limitation.",
        f"In such cases, running `{command}` via `xargs` is undesirable",
        f"because it splits the list into pieces and makes `{command}` print",
        f"{sub_list_output} for each sublist rather than for the entire list.",
        "One way to produce a list of ASCII NUL terminated file names is with GNU",
        "`find`, using its `-print0` predicate.",
        "If file is `-` then the ASCII NUL terminated file names are read from",
        "standard input.",
    ]


MACRO_RENDERERS: dict[str, Callable[[list[str]], list[str]]] = {
    "checksumUsage": _render_checksum_usage,
    "filesZeroFromOption": _render_files_zero_from_option,
    "mayConflictWithShellBuiltIn": _render_may_conflict_with_shell_builtin,
    "printDash": _render_print_dash,
    "weakHash": _render_weak_hash,
}
NO_ARG_MACRO_RENDERERS: dict[str, Callable[[], list[str]]] = {
    "legacyDigest": _render_legacy_digest,
    "mvOptsIfn": _render_mv_opts_ifn,
    "optBackup": _render_opt_backup,
    "optBackupSuffix": _render_opt_backup_suffix,
    "optDebugCopy": _render_opt_debug_copy,
    "optNoTargetDirectory": _render_opt_no_target_directory,
    "optStripTrailingSlashes": _render_opt_strip_trailing_slashes,
    "optTargetDirectory": _render_opt_target_directory,
    "whichUpdate": _render_which_update,
}


def _render_macro_invocation(line: str) -> list[str] | None:
    parsed = _macro_invocation(line)
    if parsed is None:
        return None
    name, args = parsed
    renderer = MACRO_RENDERERS.get(name)
    if renderer is not None:
        return renderer(args)
    no_arg_renderer = NO_ARG_MACRO_RENDERERS.get(name)
    return no_arg_renderer() if no_arg_renderer is not None else None


def convert_special_macro(line: str) -> list[str] | None:
    option_item = _render_option_item(line)
    if option_item is not None:
        return [option_item]
    for prefix in ("@itemx ", "@item "):
        if line.startswith(prefix):
            return [f"- {strip_texi_markup(line[len(prefix) :].strip())}"]
    for prefix, rendered in SPECIAL_PREFIX_MACROS.items():
        if line.startswith(prefix):
            return [rendered]
    if line in SPECIAL_EXACT_MACROS:
        return [SPECIAL_EXACT_MACROS[line]]
    return _render_macro_invocation(line)


def _should_skip_line(line: str) -> bool:
    return line == "@c" or line.startswith("@c ") or line.startswith("@node ")


def _heading_lines(line: str) -> list[str] | None:
    for prefix, marker in HEADING_PREFIXES:
        if line.startswith(prefix):
            heading = strip_texi_markup(line[len(prefix) :].strip())
            return [f"{marker} {heading}", ""]
    if line == "@exitstatus":
        return ["### Exit Status", ""]
    return None


def _code_block_lines(line: str, *, in_code: bool) -> tuple[list[str] | None, bool]:
    if line in CODE_BLOCK_STARTS:
        return ([] if in_code else ["```text"]), True
    if line in CODE_BLOCK_ENDS:
        return ((["```", ""] if in_code else []), False)
    return None, in_code


def _table_lines(line: str) -> list[str] | None:
    if line.startswith("@table "):
        return []
    if line in TABLE_CONTROL_LINES:
        return [""] if line == "@end table" else []
    return None


def _plain_text_lines(line: str) -> list[str]:
    text = strip_texi_markup(line)
    text = re.sub(r"@([A-Za-z]+)\{", "", text)
    text = text.replace("@{", "{").replace("@}", "}")
    text = text.replace("@c", "")
    text = text.replace("{", "").replace("}", "")
    text = text.replace("@@", "@")
    text = re.sub(r"\s+", " ", text).strip()
    if not text:
        return [""]
    if text.startswith("index ") or text.startswith("@"):
        return []
    return [text]


def _compact_blank_lines(lines: list[str]) -> list[str]:
    compact: list[str] = []
    previous_blank = False
    for line in lines:
        blank = line.strip() == ""
        if blank and previous_blank:
            continue
        compact.append(line)
        previous_blank = blank
    while compact and compact[-1].strip() == "":
        compact.pop()
    return compact


def _skipped_by_state(
    line: str,
    *,
    in_menu: bool,
    in_macro_definition: bool,
) -> tuple[bool, bool, bool]:
    if in_macro_definition:
        return True, line != "@end macro", in_menu
    if line.startswith("@macro "):
        return True, True, in_menu
    if in_menu:
        return True, in_macro_definition, line != "@end menu"
    if line == "@menu":
        return True, in_macro_definition, True
    return False, in_macro_definition, in_menu


def _converted_line(line: str, *, in_code: bool) -> tuple[list[str], bool]:
    if _should_skip_line(line):
        return [], in_code

    heading = _heading_lines(line)
    if heading is not None:
        return heading, in_code

    block_lines, next_in_code = _code_block_lines(line, in_code=in_code)
    if block_lines is not None:
        return block_lines, next_in_code

    table_lines = _table_lines(line)
    if table_lines is not None:
        return table_lines, in_code

    special = convert_special_macro(line)
    if special is not None:
        return special, in_code

    return _plain_text_lines(line), in_code


def convert_texinfo_to_markdown(section_lines: list[str]) -> list[str]:
    out: list[str] = []
    in_menu = False
    in_code = False
    in_macro_definition = False

    for raw in section_lines:
        stripped = raw.rstrip("\n").strip()
        skipped, in_macro_definition, in_menu = _skipped_by_state(
            stripped,
            in_menu=in_menu,
            in_macro_definition=in_macro_definition,
        )
        if skipped:
            continue

        converted, in_code = _converted_line(stripped, in_code=in_code)
        out.extend(converted)

    if in_code:
        out.append("```")

    return _compact_blank_lines(out)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Extract natural-language utility specifications from GNU coreutils "
            "Texinfo documentation into each utility bench directory"
        )
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path.cwd(),
        help="Benchmark repository root",
    )
    parser.add_argument(
        "--docs-path",
        type=Path,
        default=Path("coreutils/doc/coreutils.texi"),
        help="GNU coreutils Texinfo source, relative to --root by default",
    )
    parser.add_argument(
        "--utilities",
        default=None,
        help="Comma-separated utility names (default: all configured utilities)",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    root = args.root.resolve()
    repository = BenchmarkRepository.open(root)
    doc_utilities = [
        ResolvedBenchmark.for_task(definition.task_id)
        for definition in repository.definitions(BenchmarkKind.COREUTILS)
    ]
    all_utility_names = [utility.name for utility in doc_utilities]
    selected_names = _selected_names(args.utilities, all_utility_names)
    unknown = sorted(set(selected_names) - set(all_utility_names))
    if unknown:
        raise ValueError("unknown coreutils benchmarks: " + ", ".join(unknown))

    docs_path = args.docs_path if args.docs_path.is_absolute() else root / args.docs_path
    lines = docs_path.read_text(encoding="utf-8").splitlines()

    selected_set = set(selected_names)
    for utility in doc_utilities:
        utility_name = utility.name
        if utility_name not in selected_set:
            continue

        node_name = utility.official_doc_node
        if node_name is None:
            continue
        start_line, end_line, section_lines = extract_node_slice(lines, node_name)
        markdown_lines = convert_texinfo_to_markdown(section_lines)

        definition = repository.load_definition(utility_name)
        out_path = root / definition.description_path
        out_path.parent.mkdir(parents=True, exist_ok=True)
        header = [
            f"# {utility_name} NL Specification",
            "",
            "Source:",
            "- `coreutils/doc/coreutils.texi`",
            f"- `@node {node_name}`",
            f"- Source line range: {start_line}-{end_line}",
            "",
            "This file is generated by ",
            "`python3 -m benchmarks.extract_nl_specs`.",
            "",
        ]
        out_path.write_text("\n".join(header + markdown_lines) + "\n", encoding="utf-8")
        print(f"[ok] wrote {out_path}")

    return 0


def _selected_names(raw: str | None, all_names: list[str]) -> list[str]:
    if raw is None or not raw.strip():
        return list(all_names)
    return [name.strip() for name in raw.split(",") if name.strip()]


if __name__ == "__main__":
    raise SystemExit(main())
