"""Exercise the evaluator package through the installed interpreter."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path


# A regular package install loads the forced pytest plugin outside the source tree.
def test_installed_evaluator_loads_pytest_plugin_without_source_path(tmp_path: Path) -> None:
    repository = Path(__file__).resolve().parents[2]
    source = tmp_path / "package"
    source.mkdir()
    shutil.copy2(repository / "pyproject.toml", source / "pyproject.toml")
    shutil.copytree(
        repository / "src",
        source / "src",
        ignore=shutil.ignore_patterns("__pycache__", "*.pyc", "*.egg-info"),
    )
    installation = tmp_path / "userbase"
    env = dict(os.environ)
    env.pop("PYTHONPATH", None)
    env.pop("PYTHONNOUSERSITE", None)
    env["PYTHONUSERBASE"] = str(installation)
    subprocess.run(
        [
            sys.executable,
            "-m",
            "pip",
            "install",
            "--no-deps",
            "--no-build-isolation",
            "--user",
            "--break-system-packages",
            str(source),
        ],
        check=True,
        capture_output=True,
        text=True,
        timeout=60,
        env=env,
    )
    tests = tmp_path / "outside-source"
    tests.mkdir()
    (tests / "test_plugin.py").write_text(
        f"""import subprocess
from pathlib import Path

import evaluation.submission.pytest_infrastructure as plugin
from evaluation.task.workspace import _shell_template

def test_installed_plugin():
    assert plugin.__file__.startswith({str(installation)!r})
    installed_package = Path(plugin.__file__).parent
    assert (installed_package / "oracle_isolation_entrypoint.sh").is_file()
    assert (installed_package / "compose_check.sh").is_file()
    values = {{"DOTNET_HEAP_LIMIT": "0x280000000"}}
    environment = _shell_template("build_environment.sh", values)
    values = {{
        "BUILD_ENVIRONMENT": environment,
        "SCRIPT_PARENT": "..",
        "UTILITY_ROOT": "bench/algorithm/1",
        "MANIFEST_PATH": "eval_support/entry_contract.json",
        "RUNTIME_BUILD_ARGS": "build --output _build/bench/algorithm-1_bench.dll config.toml",
        "FULL_BUILD_ARGS": "--build-arg=build",
    }}
    for name in ("build.sh", "check_proof_layout.sh", "verify.sh"):
        rendered = _shell_template(name, values)
        script = Path(name)
        script.write_text(rendered)
        subprocess.run(["bash", "-n", str(script)], check=True)
""",
        encoding="utf-8",
    )
    env["DAFNYUTILS_REPO_ROOT"] = str(repository)
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "pytest",
            "-q",
            "-n0",
            "-p",
            "evaluation.submission.pytest_infrastructure",
            str(tests),
        ],
        cwd=tests,
        env=env,
        capture_output=True,
        text=True,
        timeout=60,
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert "1 passed" in completed.stdout
