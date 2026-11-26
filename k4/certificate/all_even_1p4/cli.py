"""Command line: ``python -m all_even_1p4 [--json OUT] [--table OUT] [--slab K] [--quick]``.

Default: the full certificate (constants, Benchmark 0, 30 slabs, tail).
--slab K   only slab K (repeatable); no benchmark, no tail.
--quick    everything except the tail (the tail takes most of the run time).
Exit status 0 if every check of the parts run holds; a failed check raises.
"""

from __future__ import annotations

import argparse
import sys
import time
from pathlib import Path

from . import START_NS, report
from .benchmark import BenchmarkResult
from .certificate import SlabsDone, run_certificate
from .regime2 import SlabResult
from .regime3 import TailResult


def _print(lines: list[str] | str) -> None:
    for line in [lines] if isinstance(lines, str) else lines:
        print(line, flush=True)


def _on_progress(result: BenchmarkResult | SlabResult | SlabsDone | TailResult) -> None:
    if isinstance(result, BenchmarkResult):
        _print(report.benchmark_lines(result))
        _print([""] + report.regime1_lines() + ["", report.REGIME2_HEADER])
    elif isinstance(result, SlabResult):
        _print(report.slab_line(result))
    elif isinstance(result, SlabsDone):
        _print(report.regime2_summary_line(result.slabs))
    else:
        _print([""] + report.tail_lines(result))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="python -m all_even_1p4", description=__doc__.splitlines()[0])
    parser.add_argument("--json", type=Path, help="write the machine-readable summary here")
    parser.add_argument("--table", type=Path, help="write the Markdown parameter table here")
    parser.add_argument("--slab", type=int, action="append", help="certify only this slab (1..30); repeatable")
    parser.add_argument("--quick", action="store_true", help="skip the tail (Regime 3)")
    args = parser.parse_args(argv)

    _print(report.constants_lines())
    slabs = tuple(args.slab) if args.slab else None
    if slabs is not None:
        _print(report.REGIME2_HEADER)
    run = run_certificate(
        slab_indices=slabs,
        with_benchmark=slabs is None,
        with_tail=slabs is None and not args.quick,
        on_progress=_on_progress,
    )
    _print([""] + report.result_lines(run))
    if args.json:
        args.json.write_text(report.summary_json(run))
        _print(f"  wrote {args.json}")
    if args.table:
        args.table.write_text(report.parameter_table(run))
        _print(f"  wrote {args.table}")
    elapsed = (time.perf_counter_ns() - START_NS) // 10**9
    _print(f"  run time {elapsed} s including import (Python {sys.version.split()[0]})")
    return 0
