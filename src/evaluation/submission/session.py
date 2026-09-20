"""Own sequential command logs and execution records for one task run."""

from dataclasses import dataclass, field
from pathlib import Path

from benchmarks.checks import EvaluationName
from evaluation.models import CommandResultModel
from evaluation.submission.command_execution import run_logged_command


@dataclass
class EvaluationSession:
    run_directory: Path
    executions: list[CommandResultModel] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)

    def note(self, text: str) -> None:
        self.notes.append(text)

    def run_logged(
        self,
        *,
        evaluation: EvaluationName,
        name: str,
        command: str,
        env: dict[str, str],
        timeout_sec: int | None,
        cwd: Path,
        infrastructure_report_containerized: bool = False,
    ) -> CommandResultModel:
        log_directory = self.run_directory / "evaluation"
        log_directory.mkdir(parents=True, exist_ok=True)
        result = run_logged_command(
            sequence_id=len(self.executions) + 1,
            evaluation=evaluation,
            name=name,
            command=command,
            env=env,
            timeout_sec=timeout_sec,
            cwd=cwd,
            run_dir=log_directory,
            events_path=log_directory / "events.jsonl",
            infrastructure_report_containerized=infrastructure_report_containerized,
        )
        self.executions.append(result)
        return result
