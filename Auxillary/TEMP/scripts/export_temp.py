#!/usr/bin/env python3
"""Create a Windows-safe standalone TEMP source/evidence archive. No Lean execution."""
import argparse
import hashlib
import json
from pathlib import Path
import zipfile

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    repo = Path(__file__).resolve().parents[3]
    paths = []
    for root in (repo/'TEMP', repo/'Auxillary/TEMP'):
        paths.extend(p for p in root.rglob('*') if p.is_file()
                     and not set(p.relative_to(repo).parts) & {'.lake', '__pycache__', 'exports', 'evidence-current'})
    paths.append(repo/'.github/workflows/lean-temp.yml')
    entries = {}
    for p in sorted(set(paths)):
        name = p.relative_to(repo).as_posix()
        assert not any(c in name for c in '<>:"|?*'), name
        entries[name] = p.read_bytes()
    manifest = {'archive_scope': 'TEMP source package, pinned dependency lock, external runners and retained evidence',
                'local_lean_execution': False,
                'files': [{'path': name, 'sha256': hashlib.sha256(data).hexdigest()} for name, data in entries.items()]}
    entries['TEMP_EXPORT_MANIFEST.json'] = (json.dumps(manifest,indent=2)+'\n').encode()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(args.output,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for name,data in entries.items():
            info=zipfile.ZipInfo(name,(2026,11,13,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED
            z.writestr(info,data)
    with zipfile.ZipFile(args.output) as z:
        assert z.testzip() is None
        for row in manifest['files']:
            assert hashlib.sha256(z.read(row['path'])).hexdigest()==row['sha256']
    print(json.dumps({'path':str(args.output),'files':len(entries),
                      'sha256':hashlib.sha256(args.output.read_bytes()).hexdigest(),'zip_validation':'PASS'}))

if __name__=='__main__':main()
