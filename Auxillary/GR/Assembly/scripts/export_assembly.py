#!/usr/bin/env python3
"""Export native GR assembly sources and evidence; no Lean execution."""
import argparse
import hashlib
import json
from pathlib import Path
import zipfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
repo = Path(__file__).resolve().parents[4]
paths = []
for root in ['ASSEMBLY', 'GR_adapter', 'TEMP', 'Auxillary/GR/Assembly']:
    paths.extend(p for p in (repo / root).rglob('*') if p.is_file()
                 and not set(p.relative_to(repo).parts) &
                 {'.lake', '__pycache__', 'exports', 'evidence-current'})
paths.extend(repo / p for p in ['Auxillary/GR/audit-targets.json',
                              'Auxillary/TEMP/audit-targets.json',
                              '.github/workflows/lean-gr-assembly.yml'])
entries = {}
for path in sorted(set(paths)):
    name = path.relative_to(repo).as_posix()
    if any(c in name for c in '<>:"|?*'):
        raise ValueError('Non-Windows archive path: ' + name)
    entries[name] = path.read_bytes()
manifest = {'scope': 'native GR assembly; GR/TEMP source dependencies; exact locks; external runners; retained evidence',
            'cache_policy': 'preserve existing compatible caches; acquire official Mathlib cached objects',
            'local_lean_executions': 0,
            'files': [{'path': n, 'sha256': hashlib.sha256(b).hexdigest()} for n, b in entries.items()]}
entries['ASSEMBLY_EXPORT_MANIFEST.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
args.output.parent.mkdir(parents=True, exist_ok=True)
with zipfile.ZipFile(args.output, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
    for name, data in entries.items():
        info = zipfile.ZipInfo(name, date_time=(2026, 11, 13, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        info.external_attr = 0o100644 << 16
        archive.writestr(info, data)
with zipfile.ZipFile(args.output) as archive:
    assert archive.testzip() is None
    for item in manifest['files']:
        assert hashlib.sha256(archive.read(item['path'])).hexdigest() == item['sha256']
print(json.dumps({'path': str(args.output.resolve()), 'files': len(entries),
                  'bytes': args.output.stat().st_size,
                  'sha256': hashlib.sha256(args.output.read_bytes()).hexdigest()}))
