"""Parallel raw pair: two independent single-model repair loops, one verifier.

This is the least coordination that still uses both models. The kit's raw
baseline loop (``baselines.simple_agent``) runs once per model, concurrently,
on the same problem, under one budget ledger and one time window; the first
loop whose candidate the warm REPL accepts wins and the other loop is asked
to stop. Nothing is shared between the loops: no handoff, no critique, no
staged search. It exists as a control arm for the coordination layer in
``submission/``: any gain the staged controller shows over this arm is a
gain of search organization, not of merely having two models.

Knobs (all optional):
  BASELINE_MAX_TURNS / BASELINE_MAX_TOKENS / BASELINE_TEMPERATURE
      apply to each loop exactly as they do to the raw baseline.
  PAIR_RESTARTS=1
      a loop that exhausts its turns without acceptance starts over with a
      fresh conversation while the window allows (long-horizon control:
      "independent restarts", the simplest possible use of a long window).
  PAIR_TURN_GUARD_S (default 480)
      a loop starts a new turn only if at least this many seconds remain
      before the agent deadline, so a call is never cut off by the harness
      (a cancelled call closes the shared ledger for both loops).
  VM_TIME_LIMIT_S / VM_VERIFY_RESERVE_S
      the window, read the same way the harness worker derives the agent
      deadline (limit minus min(reserve, limit / 4)).
  PAIR_GUARD=1
      reject (with feedback, as a failed turn) any candidate that drops or
      rewrites a challenge declaration header or adds an import the
      challenge lacks. The raw loop as shipped stops on the first REPL
      acceptance, and the warm REPL accepts theorem-less fragments and
      files whose imports the scoring build cannot see; both were observed
      to end 4-hour restart runs with a Comparator rejection.
"""

from __future__ import annotations

import asyncio
import os
import time
from dataclasses import asdict
from typing import Any, Callable

from re_harness import AgentResult, Problem, Services
from re_harness.budget import BudgetAccountingError, BudgetExceeded
from re_harness.lean import LeanRuntimeError
from re_harness.llm import LLMCallError, LLMPolicyError
from re_harness.models import MODEL_A, MODEL_B

from baselines.simple_agent import (
    Attempt,
    SimpleBaselineAgent,
    _env_float,
    _extract_lean,
    _format_messages,
)

DEFAULT_TURN_GUARD_S = 480.0  # observed raw-call tail (~470 s) + one REPL check


def guard_violation(challenge: str, candidate: str) -> str | None:
    """Why `candidate` cannot score against `challenge`, or None.

    Every declaration header line of the challenge (theorem/lemma/abbrev/def
    up to and including ':=') must appear verbatim, and the candidate may
    not import anything the challenge does not.
    """

    def headers(text: str) -> list[str]:
        out = []
        for line in text.splitlines():
            if line.startswith(("theorem ", "lemma ", "abbrev ", "def ")):
                out.append(line.split(":=")[0].rstrip())
        return out

    missing = [h for h in headers(challenge) if h not in candidate]
    if missing:
        return f"declaration header changed or missing: {missing[0][:80]}"
    allowed = {l.strip() for l in challenge.splitlines() if l.strip().startswith("import ")}
    extra = [l.strip() for l in candidate.splitlines()
             if l.strip().startswith("import ") and l.strip() not in allowed]
    if extra:
        return f"import not available to the scoring build: {extra[0][:80]}"
    return None


class _Loop:
    """State of one raw loop inside the pair."""

    def __init__(self, model: str):
        self.model = model
        self.candidate: str | None = None
        self.error_count: int | None = None
        self.turns = 0
        self.restarts = 0
        self.accepted = False
        self.stopped = "running"
        self.repl_failures = 0
        self.call_failures = 0
        self.attempts: list[Attempt] = []

    def summary(self) -> dict[str, Any]:
        return {
            "model": self.model,
            "turns": self.turns,
            "restarts": self.restarts,
            "accepted": self.accepted,
            "stopped": self.stopped,
            "attempts": [asdict(attempt) for attempt in self.attempts],
        }


class PairAgent:
    def __init__(
        self,
        *,
        models: tuple[str, str] = (MODEL_A, MODEL_B),
        max_turns: int | None = None,
        max_tokens: int | None = None,
        temperature: float | None = None,
        restarts: bool | None = None,
        guard: bool | None = None,
        turn_guard_s: float | None = None,
        time_limit_s: float | None = None,
        verify_reserve_s: float | None = None,
        clock: Callable[[], float] = time.monotonic,
        retry_pause_s: float = 30.0,
    ):
        self.retry_pause_s = retry_pause_s
        self.models = models
        # One raw-baseline prompt builder per model keeps the loop's prompts
        # byte-identical to the kit baseline's.
        self.loops_cfg = {
            model: SimpleBaselineAgent(
                model=model, max_turns=max_turns, max_tokens=max_tokens,
                temperature=temperature,
            )
            for model in models
        }
        self.restarts = (
            restarts if restarts is not None
            else os.environ.get("PAIR_RESTARTS", "").strip() == "1"
        )
        self.guard = (
            guard if guard is not None
            else os.environ.get("PAIR_GUARD", "").strip() == "1"
        )
        self.turn_guard_s = (
            turn_guard_s if turn_guard_s is not None
            else _env_float("PAIR_TURN_GUARD_S", DEFAULT_TURN_GUARD_S, minimum=0.0, maximum=3600.0)
        )
        limit = (
            time_limit_s if time_limit_s is not None
            else float(os.environ.get("VM_TIME_LIMIT_S", "28800") or 28800)
        )
        reserve = (
            verify_reserve_s if verify_reserve_s is not None
            else float(os.environ.get("VM_VERIFY_RESERVE_S", "120") or 120)
        )
        self.agent_time_s = max(1.0, limit - min(reserve, limit * 0.25))
        self.clock = clock

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        started = self.clock()
        deadline = started + self.agent_time_s
        stop = asyncio.Event()
        loops = {model: _Loop(model) for model in self.models}

        def remaining() -> float:
            return deadline - self.clock()

        async def run_loop(state: _Loop) -> None:
            cfg = self.loops_cfg[state.model]
            while True:
                feedback = ""
                turn = 0
                while turn < cfg.max_turns:
                    turn += 1
                    if stop.is_set():
                        state.stopped = "stop"
                        return
                    if remaining() < self.turn_guard_s:
                        state.stopped = "deadline"
                        return
                    is_last = turn == cfg.max_turns and not self.restarts
                    try:
                        response = await services.llm.complete(
                            model=state.model,
                            messages=cfg._messages(
                                problem, feedback=feedback, turn=turn, is_last=is_last
                            ),
                            max_tokens=cfg.max_tokens,
                            temperature=cfg.temperature,
                        )
                    except LLMCallError as exc:
                        # A transport or provider fault. Under the kit as
                        # shipped the ledger is already closed and the next
                        # reservation raises BudgetAccountingError below;
                        # under the dev release policy the loop may go on.
                        # Retry the same turn after a pause, at most three
                        # faults in a row.
                        state.call_failures += 1
                        if state.call_failures >= 3:
                            state.stopped = f"error:LLMCallError:{str(exc)[:80]}"
                            return
                        await asyncio.sleep(self.retry_pause_s)
                        turn -= 1  # retry the same turn
                        continue
                    except (BudgetExceeded, BudgetAccountingError, LLMPolicyError) as exc:
                        state.stopped = f"error:{type(exc).__name__}"
                        return
                    state.call_failures = 0
                    state.turns += 1
                    if stop.is_set():
                        # The other loop was accepted while this call was in
                        # flight; do not checkpoint over its solution.
                        state.stopped = "stop"
                        return
                    candidate = _extract_lean(
                        response.content, fallback=state.candidate or problem.challenge
                    )
                    state.candidate = candidate
                    if self.guard:
                        violation = guard_violation(problem.challenge, candidate)
                        if violation:
                            state.attempts.append(Attempt(
                                turn=state.turns, accepted=False, timed_out=False,
                                message_count=1))
                            state.error_count = 1 << 20
                            feedback = ("error: " + violation + ". Keep every theorem "
                                        "statement and the import lines exactly as in "
                                        "the challenge; only replace `sorry`.")
                            continue
                    services.checkpoint(
                        candidate,
                        {"baseline": "pair", "model": state.model,
                         "pair_turn": state.turns, "restarts": state.restarts},
                    )
                    try:
                        check = await services.lean.check_file(candidate)
                    except LeanRuntimeError as exc:
                        # The warm REPL failed (typically a Mathlib import
                        # timeout under machine load); the client restarts
                        # it on the next call. Two failures in a row end
                        # this loop, as in the coordination layer's rail.
                        state.repl_failures += 1
                        state.attempts.append(Attempt(
                            turn=state.turns, accepted=False, timed_out=True,
                            message_count=0,
                        ))
                        if state.repl_failures >= 2:
                            state.stopped = f"error:LeanRuntimeError:{str(exc)[:80]}"
                            return
                        feedback = "Lean was unavailable while checking the previous candidate."
                        continue
                    state.repl_failures = 0
                    state.attempts.append(Attempt(
                        turn=state.turns, accepted=check.accepted,
                        timed_out=check.timed_out, message_count=len(check.messages),
                    ))
                    state.error_count = sum(
                        1 for m in check.messages if m.get("severity") == "error"
                    )
                    if check.accepted:
                        state.accepted = True
                        state.stopped = "accepted"
                        stop.set()
                        return
                    feedback = _format_messages(check.messages)
                    if check.timed_out and not feedback:
                        feedback = "Lean timed out while checking the previous candidate."
                if not self.restarts:
                    state.stopped = "turns"
                    return
                state.restarts += 1

        tasks = [asyncio.create_task(run_loop(state)) for state in loops.values()]
        results = await asyncio.gather(*tasks, return_exceptions=True)
        for state, outcome in zip(loops.values(), results):
            if isinstance(outcome, BaseException):
                if isinstance(outcome, asyncio.CancelledError):
                    raise outcome
                state.stopped = f"crash:{type(outcome).__name__}:{str(outcome)[:80]}"

        winner = next((s for s in loops.values() if s.accepted), None)
        if winner is None:
            # Fall back to the loop whose last check had the fewest errors;
            # ties go to the first-listed model.
            ranked = sorted(
                (s for s in loops.values() if s.candidate is not None),
                key=lambda s: (s.error_count if s.error_count is not None else 1 << 30),
            )
            winner = ranked[0] if ranked else None
        solution = winner.candidate if winner and winner.candidate else problem.challenge
        return AgentResult(
            solution,
            {
                "baseline": "pair",
                "arm": "pair" + ("+restarts" if self.restarts else "") + ("+guard" if self.guard else ""),
                "origin": f"pair:{winner.model}" if winner else "challenge",
                "winner": winner.model if winner and winner.accepted else None,
                "accepted_by_repl": bool(winner and winner.accepted),
                "elapsed_s": round(self.clock() - started, 1),
                "loops": {s.model: s.summary() for s in loops.values()},
            },
        )


def create_agent() -> PairAgent:
    return PairAgent()
