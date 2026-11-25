"""Run the whole certificate (or a part of it) and collect the results.

Order: the constant check li(e^5) < e^5/3, Benchmark 0, the slab schedule
check, the 30 slabs of Regime 2, the tail (Regime 3).  Regime 1 is the cited
Goldbach verification and involves no computation here.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Union

from .benchmark import BenchmarkResult, run_benchmark
from .checks import Check, CheckList
from .constants import E5_OVER_3, LI_E5
from .regime2 import SLABS, SlabResult, certify_slab, require_schedule_covers
from .regime3 import TAIL, TailResult, certify_tail


@dataclass(frozen=True)
class SlabsDone:
    """Progress event: every selected slab has been certified."""

    slabs: tuple[SlabResult, ...]


Progress = Callable[[Union[BenchmarkResult, SlabResult, SlabsDone, TailResult]], None]

STATUS_LINE = (
    "This certificate checks arithmetic given the cited theorems; it does not prove the cited "
    "theorems. The tail regime (N >= 1e170) depends on the hypothesis scope of the explicit linear "
    "sieve theorem ([BJS] Theorem 6), which is under repair (see the repository README)."
)


@dataclass(frozen=True)
class CertificateRun:
    """What was checked.  ``complete`` is True only if every part was run."""

    global_checks: tuple[Check, ...]
    benchmark: BenchmarkResult | None
    slabs: tuple[SlabResult, ...]
    tail: TailResult | None
    complete: bool

    def all_checks(self) -> list[tuple[str, Check]]:
        """Every recorded check with its scope, in run order."""
        out = [("global", c) for c in self.global_checks]
        if self.benchmark is not None:
            out += [("benchmark", c) for c in self.benchmark.checks]
        for s in self.slabs:
            out += [(f"slab {s.params.index}", c) for c in s.checks]
        if self.tail is not None:
            out += [("tail", c) for c in self.tail.checks]
        return out

    def min_slab(self) -> SlabResult | None:
        """The slab with the smallest certified net lower bound."""
        return min_net_slab(self.slabs)


def min_net_slab(slabs: tuple[SlabResult, ...]) -> SlabResult | None:
    """The slab with the smallest certified net lower bound (None if there are none)."""
    if not slabs:
        return None
    return min(slabs, key=lambda s: s.net.lo)


def run_certificate(slab_indices: tuple[int, ...] | None = None, with_benchmark: bool = True,
                    with_tail: bool = True, on_progress: Progress | None = None) -> CertificateRun:
    """Run the selected parts; any failed check raises CertificationError."""
    global_checks = CheckList("global")
    global_checks.require("li(e^5) < e^5/3", "note s0.4", LI_E5, "<", E5_OVER_3)
    require_schedule_covers(global_checks)

    benchmark = None
    if with_benchmark:
        benchmark = run_benchmark()
        if on_progress:
            on_progress(benchmark)

    selected = SLABS if slab_indices is None else tuple(s for s in SLABS if s.index in slab_indices)
    if slab_indices is not None and len(selected) != len(set(slab_indices)):
        raise ValueError(f"unknown slab index in {slab_indices}; valid: 1..{len(SLABS)}")
    slabs = []
    for params in selected:
        result = certify_slab(params)
        slabs.append(result)
        if on_progress:
            on_progress(result)
    if on_progress:
        on_progress(SlabsDone(tuple(slabs)))

    tail = None
    if with_tail:
        tail = certify_tail(TAIL)
        if on_progress:
            on_progress(tail)

    complete = with_benchmark and with_tail and len(selected) == len(SLABS)
    return CertificateRun(global_checks.frozen(), benchmark, tuple(slabs), tail, complete)
