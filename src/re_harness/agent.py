"""Applicant-facing agent protocol."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Mapping, Protocol, runtime_checkable

if False:  # pragma: no cover - imports for type checkers without cycles
    from .lean import LeanClient
    from .llm import LLMClient

JSONValue = None | bool | int | float | str | list["JSONValue"] | dict[str, "JSONValue"]


@dataclass(frozen=True)
class Problem:
    id: str
    description: str
    challenge: str
    metadata: Mapping[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class AgentResult:
    solution: str
    metadata: Mapping[str, JSONValue] = field(default_factory=dict)


class Services:
    """Capabilities provided to an applicant agent for one problem."""

    def __init__(self, *, llm: "LLMClient", lean: "LeanClient", checkpoint,
                 state_dir=None, compare=None):
        self.llm = llm
        self.lean = lean
        self._checkpoint = checkpoint
        # Durable per-problem scratch directory (the problem's output dir).
        # Lets an agent persist search state so an interrupted worker can be
        # resumed without redoing work; None-safe for older callers.
        self.state_dir = state_dir
        # Optional real-comparator precheck: (source, timeout_s=…) -> dict
        # with passed/timed_out/duration_ms. The warm REPL cannot observe
        # cold-build kernel cost, so an agent may verify a candidate against
        # the actual scoring gate when time permits; None-safe.
        self.compare = compare

    def checkpoint(
        self, source: str, metadata: Mapping[str, JSONValue] | None = None
    ) -> None:
        """Atomically preserve a candidate for timeout/crash recovery."""

        self._checkpoint(source, dict(metadata or {}))


@runtime_checkable
class Agent(Protocol):
    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        """Return the best complete Lean source for ``problem``."""

