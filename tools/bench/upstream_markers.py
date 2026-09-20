"""Extract root-relative upstream test references from benchmark pytest modules."""

from __future__ import annotations

import ast
import io
import re
import tokenize
from dataclasses import dataclass
from pathlib import Path

_UPSTREAM_MARKER = re.compile(r"^\s*#\s*upstream:\s*(?P<value>.*?)\s*$")
_UPSTREAM_REASON = re.compile(r"^\s*#\s*upstream-reason:\s*(?P<value>.*?)\s*$")
_UPSTREAM_PATH = re.compile(r"^coreutils/(?:tests|gnulib-tests)/[^\s]+$")
_REPO_ONLY_PREFIX = "none - "


@dataclass(frozen=True)
class UpstreamReferences:
    paths: tuple[str, ...] = ()
    repo_only_reason: str | None = None


@dataclass(frozen=True)
class _FunctionSpan:
    name: str
    body_region_start_line: int
    ast_end_line: int
    trailing_end_line: int
    body_column: int


@dataclass
class _ReferenceBuilder:
    paths: list[str]
    repo_only_reason: str | None = None

    def build(self) -> UpstreamReferences:
        return UpstreamReferences(tuple(dict.fromkeys(self.paths)), self.repo_only_reason)


def test_names(module_path: Path) -> list[str]:
    return [span.name for span in _test_function_spans(module_path)]


def upstream_references_by_test(module_path: Path) -> dict[str, UpstreamReferences]:
    spans = _test_function_spans(module_path)
    builders = {span.name: _ReferenceBuilder(paths=[]) for span in spans}

    for line_number, column, comment in _comment_tokens(module_path):
        match = _UPSTREAM_MARKER.match(comment)
        if match is not None:
            test_name = _function_name_for_line(spans, line_number, column)
            if test_name is None:
                raise ValueError(
                    f"{module_path}:{line_number}: upstream marker must be inside a test"
                )
            _add_marker_value(
                module_path,
                line_number,
                builders[test_name],
                match.group("value").strip(),
            )
            continue

        match = _UPSTREAM_REASON.match(comment)
        if match is not None:
            test_name = _function_name_for_line(spans, line_number, column)
            if test_name is None:
                message = "upstream reason continuation must be inside a test"
                raise ValueError(f"{module_path}:{line_number}: {message}")
            _add_repo_only_reason_continuation(
                module_path,
                line_number,
                builders[test_name],
                match.group("value").strip(),
            )

    return {name: builder.build() for name, builder in builders.items()}


def _test_function_spans(module_path: Path) -> list[_FunctionSpan]:
    module_text = module_path.read_text(encoding="utf-8")
    tree = ast.parse(module_text)
    eof_line = len(module_text.splitlines())
    spans: list[_FunctionSpan] = []
    for index, node in enumerate(tree.body):
        if isinstance(node, ast.FunctionDef | ast.AsyncFunctionDef) and node.name.startswith(
            "test_"
        ):
            ast_end_line = node.end_lineno or node.lineno
            spans.append(
                _FunctionSpan(
                    name=node.name,
                    body_region_start_line=_function_body_region_start_line(
                        module_text,
                        node.lineno,
                    ),
                    ast_end_line=ast_end_line,
                    trailing_end_line=(eof_line if index + 1 == len(tree.body) else ast_end_line),
                    body_column=node.body[0].col_offset,
                )
            )
    return spans


def _function_body_region_start_line(module_text: str, start_line: int) -> int:
    source_after_def = "".join(module_text.splitlines(keepends=True)[start_line - 1 :])
    paren_depth = 0
    for token in tokenize.generate_tokens(io.StringIO(source_after_def).readline):
        if token.type != tokenize.OP:
            continue
        if token.string in "([{":
            paren_depth += 1
            continue
        if token.string in ")]}":
            paren_depth -= 1
            continue
        if token.string == ":" and paren_depth == 0:
            return start_line + token.start[0]

    raise ValueError(f"unable to locate function header end after line {start_line}")


def _comment_tokens(module_path: Path) -> list[tuple[int, int, str]]:
    comments: list[tuple[int, int, str]] = []
    with tokenize.open(module_path) as source:
        for token in tokenize.generate_tokens(source.readline):
            if token.type == tokenize.COMMENT:
                comments.append((token.start[0], token.start[1], token.string))
    return comments


def _function_name_for_line(
    spans: list[_FunctionSpan],
    line_number: int,
    column: int,
) -> str | None:
    for span in spans:
        if column < span.body_column or line_number < span.body_region_start_line:
            continue
        if line_number <= span.ast_end_line:
            return span.name
        if span.ast_end_line < line_number <= span.trailing_end_line:
            return span.name
    return None


def _add_marker_value(
    module_path: Path,
    line_number: int,
    builder: _ReferenceBuilder,
    value: str,
) -> None:
    if value.startswith(_REPO_ONLY_PREFIX):
        reason = value[len(_REPO_ONLY_PREFIX) :].strip()
        if not reason:
            raise ValueError(f"{module_path}:{line_number}: repo-only marker needs a reason")
        if builder.paths:
            raise ValueError(f"{module_path}:{line_number}: repo-only marker cannot mix with paths")
        if builder.repo_only_reason is not None:
            raise ValueError(f"{module_path}:{line_number}: duplicate repo-only marker")
        builder.repo_only_reason = reason
        return

    if _UPSTREAM_PATH.fullmatch(value) is None:
        raise ValueError(f"{module_path}:{line_number}: invalid upstream marker: {value}")
    if builder.repo_only_reason is not None:
        raise ValueError(f"{module_path}:{line_number}: path marker cannot mix with repo-only")
    builder.paths.append(value)


def _add_repo_only_reason_continuation(
    module_path: Path,
    line_number: int,
    builder: _ReferenceBuilder,
    value: str,
) -> None:
    if not value:
        raise ValueError(
            f"{module_path}:{line_number}: repo-only reason continuation needs a value"
        )
    if builder.paths:
        raise ValueError(
            f"{module_path}:{line_number}: repo-only reason continuation cannot follow path marker"
        )
    if builder.repo_only_reason is None:
        raise ValueError(
            f"{module_path}:{line_number}: repo-only reason continuation needs a repo-only marker"
        )
    builder.repo_only_reason = f"{builder.repo_only_reason} {value}"
