"""Replay the committed finite-slab witness bodies against the committed headers.

Usage: python3 witness_replay.py /path/to/buchstab-switching
Witness fields are read from the Lean source. The checks themselves are the
upstream certifier's pure-integer Python mirror of the Lean predicates.
"""
import argparse
import json
from pathlib import Path
import re
import sys


def load_rows(path, scientific):
    text = path.read_text(encoding='utf-8')
    payload = text.split('Witness := ', 1)[1].rsplit('end BuchstabSwitching.SieveInst', 1)[0]
    # The generated declarations use only arrays, records, booleans, Nat numerals,
    # and the two-field decimal constructor. Convert these literals to JSON.
    payload = re.sub(r'([A-Za-z][A-Za-z0-9_]*)\s*:=', r'"\1":', payload)
    payload = re.sub(r'⟨(\d+),\s*(\d+)⟩', r'{"_decimal":[\1,\2]}', payload)
    return json.loads(payload, object_hook=lambda d: scientific(*d['_decimal']) if '_decimal' in d else d)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repository', type=Path)
    args = parser.parse_args()
    root = args.repository.resolve() / 'k3'
    sys.path.insert(0, str(root / 'scripts'))
    from sieve_cert.slab_witness_export import (
        SciNat, _parse_data_lean, verify_slab_2ab_bool, verify_slab_2c_bool,
    )
    where = root / 'BuchstabSwitching' / 'Sieve' / 'Regime2SlabBridge'
    paths = sorted(where.glob('SlabCertInstData2*.lean'))
    headers = _parse_data_lean(root)
    witnesses = [row for path in paths for row in load_rows(path, SciNat)]
    if len(headers) != 127 or len(witnesses) != 127:
        raise ValueError('Expected 127 headers and witness records')
    for i, (header, witness) in enumerate(zip(headers, witnesses, strict=True)):
        check = verify_slab_2ab_bool if i < 61 else verify_slab_2c_bool
        if not check(header, witness):
            raise ValueError(f'Slab witness {i+1} failed')
    print('PASS: 127 committed finite-slab witness bodies and their headers')


if __name__ == '__main__':
    main()
