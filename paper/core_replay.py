"""Recheck the finite chain and ray arithmetic with Lean core, without mathlib.

Usage: python3 core_replay.py /path/to/buchstab-switching /path/to/lean
The Lean executable should be the repository's pinned v4.37.0-rc1.
"""
from hashlib import sha256
from pathlib import Path
import argparse
import re
import subprocess
import tempfile


def read_pinned(path, digest):
    contents = path.read_bytes()
    if sha256(contents).hexdigest() != digest:
        raise ValueError(f'Unexpected contents of {path}')
    return contents.decode('utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repository', type=Path)
    parser.add_argument('lean')
    args = parser.parse_args()
    source = args.repository / 'k3' / 'BuchstabSwitching' / 'Certificates'
    types = read_pinned(source / 'Types.lean', '28bff944619291d17aef45b078a8be7c6e928c8fa66928fb0b4a5eb990c2d71b')
    data = read_pinned(source / 'Data.lean', '19a5a75259c348335e2f667662d5399745cf4719a6c3293390336e0f1f6e7ab4')
    namespace = 'namespace BuchstabSwitching'
    types = types[types.index(namespace):].replace('ℕ', 'Nat')
    # The six rational projections, printers and structural equality instances
    # are not used by the Boolean natural-number checker.
    types, removed = re.subn(r'/-- Rational.*?\n\n', '', types, flags=re.DOTALL)
    if removed != 6:
        raise ValueError('Unexpected number of rational projections')
    types = types.replace('  deriving Repr, DecidableEq\n', '')
    data = data[data.index(namespace):].replace('ℕ', 'Nat')
    checks = '''namespace BuchstabSwitching
theorem replaySlabs : checkSlabChain (4 * 10 ^ 18) asymptoticCert.X_LS allSlabs = true := by decide
theorem replayRay : asymptoticCert.valid = true := by decide
theorem replayNonunitRows : allSlabs.all (fun c =>
    decide (3 ≤ c.z ∧ c.z ^ 2 ≤ c.X_lo ∧ c.den < 1000 * c.net_num)) = true := by decide
#print axioms replayNonunitRows
#print axioms replaySlabs
#print axioms replayRay
end BuchstabSwitching
'''
    with tempfile.TemporaryDirectory() as temp:
        out = Path(temp) / 'CertificateArithmetic.lean'
        out.write_text('set_option maxRecDepth 10000\n' + types + '\n' + data + '\n' + checks)
        subprocess.run([args.lean, '--version'], check=True)
        subprocess.run([args.lean, str(out)], check=True)


if __name__ == '__main__':
    main()
