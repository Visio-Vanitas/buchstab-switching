"""Negative and edge-case tests for all_even_1p4_ext/replay.py."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

CERT_ROOT = Path(__file__).resolve().parents[2]
DATA_ROOT = CERT_ROOT.parent / "data" / "certificate"
REPLAY_SCRIPT = CERT_ROOT / "all_even_1p4_ext" / "replay.py"
LADDER_JSON = DATA_ROOT / "ladder_4e18_500_all.json"
TAIL_JSON = DATA_ROOT / "tail" / "tail_at_500.json"


class ReplayNegativeTest(unittest.TestCase):
    def _run_replay(self, lad_path: Path, tail_path: Path) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, "-I", str(REPLAY_SCRIPT), str(lad_path), str(tail_path)],
            cwd=str(CERT_ROOT),
            capture_output=True,
            text=True,
            check=False,
        )

    def test_empty_tail_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            empty_tail = Path(tmp) / "empty_tail.json"
            empty_tail.write_text("[]")
            res = self._run_replay(LADDER_JSON, empty_tail)
            self.assertNotEqual(res.returncode, 0)

    def test_empty_ladder_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            empty_lad = Path(tmp) / "empty_lad.json"
            empty_lad.write_text("[]")
            res = self._run_replay(empty_lad, TAIL_JSON)
            self.assertNotEqual(res.returncode, 0)

    def test_tampered_slab_and_tail_net_lo_exit_nonzero(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            lad_data = json.loads(LADDER_JSON.read_text())
            lad_data[0]["net_lo"] = "0.0"
            bad_lad = Path(tmp) / "bad_lad.json"
            bad_lad.write_text(json.dumps(lad_data))

            tail_data = json.loads(TAIL_JSON.read_text())
            tail_data[0]["net_lo"] = "0.0"
            bad_tail = Path(tmp) / "bad_tail.json"
            bad_tail.write_text(json.dumps(tail_data))

            res = self._run_replay(bad_lad, bad_tail)
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("FAILURES", res.stdout)


if __name__ == "__main__":
    unittest.main()
