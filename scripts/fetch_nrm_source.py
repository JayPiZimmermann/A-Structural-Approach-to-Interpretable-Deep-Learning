#!/usr/bin/env python3
"""Fetch the exact third-party NRM source/PDF used by the thesis comparison."""
import argparse
import hashlib
import json
from pathlib import Path
import tarfile
import tempfile
import urllib.request

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--destination', type=Path,
                        default=ROOT / 'literature/references/normalized_relevance_measure')
    args = parser.parse_args()
    provenance = json.loads((ROOT / 'reports/nrm-source-provenance.json').read_text())
    args.destination.mkdir(parents=True, exist_ok=True)
    for item in provenance['files']:
        target = args.destination / item['filename']
        if target.exists():
            data = target.read_bytes()
        else:
            with urllib.request.urlopen(item['url'], timeout=120) as response:
                data = response.read()
        if hashlib.sha256(data).hexdigest() != item['sha256']:
            raise SystemExit('Checksum mismatch; file not replaced: ' + str(target))
        if not target.exists():
            with tempfile.NamedTemporaryFile(dir=args.destination, delete=False) as temporary:
                temporary.write(data)
                temporary_path = Path(temporary.name)
            temporary_path.replace(target)
        print('Verified ' + str(target))
    source = args.destination / 'source'
    if not source.exists():
        with tarfile.open(args.destination / '2606.00557v1-source.tar.gz') as archive:
            archive.extractall(source, filter='data')
    (args.destination / 'provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
    print('Source directory: ' + str(source))


if __name__ == '__main__':
    main()
