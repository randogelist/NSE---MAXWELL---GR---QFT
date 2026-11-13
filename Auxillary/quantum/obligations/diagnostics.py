#!/usr/bin/env python3
"""NON-PROMOTING external elaboration; the concatenation emits no object files."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import platform
import subprocess
import time


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo-root', type=Path, default=Path(__file__).resolve().parents[3])
    p.add_argument('--timeout-seconds', type=int, default=240)
    p.add_argument('--source-commit', default=os.environ.get('GITHUB_SHA', ''))
    args = p.parse_args()
    if os.environ.get('GITHUB_ACTIONS') != 'true' and os.environ.get('NSE_QUANTUM_DIAGNOSTICS_EXTERNAL') != '1':
        raise RuntimeError('External diagnostic opt-in required')
    if platform.system() != 'Linux':
        raise RuntimeError('External native Linux diagnostic runner required')
    root = args.repo_root.resolve()
    report = root / 'artifacts/external-diagnostics'
    report.mkdir(parents=True, exist_ok=True)
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
    if args.source_commit and args.source_commit != commit:
        raise RuntimeError('Source commit mismatch')
    modules = json.loads((root/'Auxillary/quantum/obligations/module-targets.json').read_text())
    selected = {m['module'] for m in modules}
    imports, bodies = set(), []
    for m in modules:
        raw = (root/m['path']).read_bytes()
        git_blob = subprocess.check_output(['git','rev-parse',commit+':'+m['path']],cwd=root,text=True).strip()
        if hashlib.sha1(f'blob {len(raw)}\0'.encode()+raw).hexdigest() != git_blob:
            raise RuntimeError('Source bytes differ: '+m['path'])
        lines = raw.decode().splitlines()
        for i,line in enumerate(lines):
            match = re.match(r'^(?:public\s+)?import\s+(.+)',line)
            if match:
                imports.update(x for x in match[1].split('--',1)[0].split() if x not in selected)
                lines[i] = ''
            elif line in {'module','prelude'}:
                raise RuntimeError('Unsupported diagnostic source header')
        bodies.append((m,lines,hashlib.sha256(raw).hexdigest(),git_blob))
    lines = ['/- NON-PROMOTING DIAGNOSTIC. Error recovery is not proof evidence. -/']
    lines += ['import '+n for n in sorted(imports)]
    mapping=[]
    for m,body,sha,blob in bodies:
        lines += ['', 'section', '/- Original source: '+m['path']+' -/']
        start=len(lines)+1
        lines += body
        mapping.append({'module':m['module'],'path':m['path'],'source_sha256':sha,'git_blob_sha':blob,
                        'generated_start_line':start,'generated_end_line':len(lines)})
        lines += ['end', '']
    source=report/'ConcatenatedDiagnostic.lean'
    source.write_text('\n'.join(lines)+'\n',encoding='utf-8')
    (report/'source-line-map.json').write_text(json.dumps(mapping,indent=2)+'\n')
    env=dict(os.environ,ELAN_TOOLCHAIN='leanprover/lean4:v4.34.0-rc1',MATHLIB_NO_CACHE_ON_UPDATE='1')
    env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
    log=report/'diagnostic.log'
    # Only existing non-obligation imports are built; their caches are shared.
    base=subprocess.run(['lake','build',*sorted(imports)],cwd=root,env=env,capture_output=True,text=True)
    (report/'external-imports.log').write_text(base.stdout+base.stderr,encoding='utf-8')
    if base.returncode:
        status='EXTERNAL_IMPORTS_FAILED';code=base.returncode;elapsed=0
    else:
        start=time.monotonic()
        with log.open('w',encoding='utf-8') as out:
            proc=subprocess.Popen(['lake','env','lean',str(source)],cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
            try:
                code=proc.wait(timeout=args.timeout_seconds);status='DIAGNOSTIC_COMPLETE'
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGTERM)
                try:proc.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(proc.pid, signal.SIGKILL);proc.wait()
                code=None;status='DIAGNOSTIC_TIMEOUT_PARTIAL_OUTPUT'
        elapsed=round(time.monotonic()-start,3)
    errors=[]
    if log.exists():
        for line in log.read_text(encoding='utf-8',errors='replace').splitlines():
            match=re.search(r'ConcatenatedDiagnostic\.lean:(\d+):(\d+):\s*(.*)',line)
            if not match:continue
            number,column,message=int(match[1]),int(match[2]),match[3]
            owner=next((m for m in mapping if m['generated_start_line']<=number<=m['generated_end_line']),None)
            errors.append({'generated_line':number,'column':column,'message':message,
                           'source_path':owner['path'] if owner else None,
                           'source_line':number-owner['generated_start_line']+1 if owner else None})
    summary={'source_commit':commit,'status':status,'lean_exit_code':code,'elapsed_seconds':elapsed,
             'A_TIER_PROMOTION_ALLOWED':False,'axiom_audit_performed':False,'source_insertions_of_axiom_sorry_or_admit':False,
             'scope':'DIAGNOSTICS_ONLY; section/import interaction and ordinary error recovery may create cascades',
             'generated_source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'errors':errors}
    (report/'diagnostic-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({'status':status,'diagnostic_messages':len(errors),'promotion_allowed':False}))
    return 0

if __name__=='__main__':raise SystemExit(main())
