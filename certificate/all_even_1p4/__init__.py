"""Certificate for the note: under GRH every even N >= 4 is p + eta with Omega(eta) <= 4.

Arithmetic check in exact integers and outward-rounded Decimal intervals (see
``interval``).  Run with ``python -m all_even_1p4`` from certificate.
See README.md for the architecture, the cited results and the status.
"""

import time as _time

START_NS = _time.perf_counter_ns()
"""Clock reading when the package was first imported (for the run time in the log)."""
