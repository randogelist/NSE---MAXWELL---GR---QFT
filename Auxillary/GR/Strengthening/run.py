#!/usr/bin/env python3
"""External cached GR strengthening build; exact audits, no implicit premise discharge."""
from __future__ import annotations
import argparse
import datetime as dt
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time

sys.dont_write_bytecode = True
TOOLCHAIN = 'leanprover/lean4:v4.34.0-rc1'
COMPILER = '3447a668783dbce1a8fdb97101dd067687b2b418'
MATHLIB = 'de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11'

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def dump(p, value):
    p.write_text(json.dumps(value, indent=2, ensure_ascii=False)+'\n', encoding='utf-8')

def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    args = parser.parse_args()
    if os.environ.get('GITHUB_ACTIONS') != 'true':
        raise SystemExit('EXTERNAL_GITHUB_CI_REQUIRED; local Lean execution disabled')
    repo = Path(__file__).resolve().parents[3]
    package = repo/'ASSEMBLY'
    support = repo/'Auxillary/GR/Strengthening'
    report = support/'evidence-current'
    report.mkdir(parents=True, exist_ok=True)
    registry_path = support/'audit-targets.json'
    registry = json.loads(registry_path.read_text())
    modules = registry['modules']
    assert modules and len({m['module'] for m in modules}) == len(modules)
    assert all(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*',m['module']) for m in modules)
    names = [n for m in modules for n in m['audit_targets']]
    assert len(names) == len(set(names))
    kinds = {n:m.get('kind','declaration') for m in modules for n in m['audit_targets']}
    env = os.environ.copy()
    env.update(ELAN_TOOLCHAIN=TOOLCHAIN, MATHLIB_NO_CACHE_ON_UPDATE='1')
    env.setdefault('LEAN_NUM_THREADS','4')
    env.pop('LEAN_PATH',None)
    env.pop('LEAN_SRC_PATH',None)
    provenance = dict(schema_version=1, source_commit=args.source_commit,
        github_run_id=os.environ.get('GITHUB_RUN_ID'), github_run_attempt=os.environ.get('GITHUB_RUN_ATTEMPT'),
        external_platform=platform.system().lower(), requested_toolchain=TOOLCHAIN,
        requested_compiler_commit=COMPILER, requested_mathlib_commit=MATHLIB,
        cache_policy='PRESERVE_AND_REUSE_COMPATIBLE_OBJECTS',
        elaboration='LAKE_PARALLEL_DAG_AND_NATIVE_ASYNC', audit='FRESH_BATCH_EXACT_THEOREM_AXIOMS',
        started_at_utc=dt.datetime.now(dt.timezone.utc).isoformat(), commands=[], status='RUNNING',
        semantic_discharge='NOT_INFERRED_FROM_AXIOM_AUDIT')

    def persist():
        dump(report/'provenance.json',provenance)

    def run(command, log_name, cwd=package):
        print('COMMAND='+' '.join(command),flush=True)
        start=time.monotonic()
        chunks=[]
        with (report/log_name).open('w',encoding='utf-8') as log:
            process=subprocess.Popen(command,cwd=cwd,env=env,stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
            for line in process.stdout:
                log.write(line); log.flush(); chunks.append(line)
                print(line,end='',flush=True)
            code=process.wait()
        provenance['commands'].append(dict(command=command,log=log_name,exit_code=code,
            seconds=round(time.monotonic()-start,3),sha256=digest(report/log_name)))
        persist()
        return code,''.join(chunks)

    def checked(command,log_name,cwd=package):
        code,text=run(command,log_name,cwd)
        if code: raise RuntimeError('Command failed: '+log_name)
        return text

    persist()
    try:
        assert platform.system().lower()=='linux'
        assert re.fullmatch(r'[a-f0-9]{40}',args.source_commit)
        assert checked(['git','rev-parse','HEAD'],'source-commit.log',repo).strip()==args.source_commit
        assert (package/'lean-toolchain').read_text().strip()==TOOLCHAIN
        version=checked(['lean','--version'],'lean-version.log')
        assert re.search(r'version 4\.34\.0-rc1,\s*[^,\s]*-linux-[^,\s]*,',version)
        assert COMPILER[:7] in version
        provenance['actual_lean_version']=version.strip()
        lock_path=package/'lake-manifest.json'
        lock_hash=digest(lock_path)
        lock=json.loads(lock_path.read_text())
        assert next(p for p in lock['packages'] if p['name']=='mathlib')['rev']==MATHLIB
        deps=[]
        for p in lock['packages']:
            assert p['type']=='git' and re.fullmatch(r'[a-f0-9]{40}',p['rev'])
            path=package/'.lake/packages'/p['name']
            rev=checked(['git','-C',str(path),'rev-parse','HEAD'],'dependency-'+p['name']+'.log').strip()
            assert rev==p['rev']
            assert not checked(['git','-C',str(path),'status','--porcelain','--untracked-files=no'],
                'dependency-clean-'+p['name']+'.log').strip()
            deps.append(dict(name=p['name'],revision=rev))
        provenance['dependency_revisions']=deps
        provenance['actual_mathlib_commit']=MATHLIB
        sources=set()
        for base in ['ASSEMBLY','GR_adapter','TEMP']:
            for ext in ['*.lean','*.json']:
                sources.update(p for p in (repo/base).rglob(ext) if '.lake' not in p.parts)
            sources.add(repo/base/'lean-toolchain')
        sources.update([registry_path,Path(__file__).resolve(),
            repo/'Auxillary/quantum/obligations/batch.py',repo/'Auxillary/scripts/verify_audit.py',
            repo/'.github/workflows/gr-strengthening.yml'])
        manifest=dict(source_commit=args.source_commit,files=[dict(path=p.relative_to(repo).as_posix(),
            sha256=digest(p)) for p in sorted(sources)])
        dump(report/'source-manifest.json',manifest)
        provenance['source_manifest_sha256']=digest(report/'source-manifest.json')
        batch=load_module('strengthening_shared_batch',repo/'Auxillary/quantum/obligations/batch.py')
        verifier=load_module('strengthening_shared_verifier',repo/'Auxillary/scripts/verify_audit.py')
        results,declarations,errors=batch.execute(package,report,modules,kinds,verifier,run)
        assert digest(lock_path)==lock_hash
        assert all(digest(repo/p['path'])==p['sha256'] for p in manifest['files'])
        summary=dict(schema_version=1,source_commit=args.source_commit,
            github_run_id=provenance['github_run_id'],github_run_attempt=provenance['github_run_attempt'],
            actual_lean_version=version.strip(),actual_mathlib_commit=MATHLIB,
            source_manifest_sha256=provenance['source_manifest_sha256'],source_input_verification='PASS',
            allowed_axioms=sorted(verifier.ALLOWED_AXIOMS),modules=results,declarations=declarations,
            errors=errors,status='PARTIAL_STANDARD_ONLY' if errors else 'PASS_STANDARD_ONLY',
            global_root_status='OPEN_UNTIL_EXACT_ROOT_AND_ALL_OBLIGATIONS_AUDITED',
            semantic_discharge='NAMED_THEOREM_TYPES_AND_PREMISES_REQUIRE_SEPARATE_REVIEW')
        dump(report/'audit-summary.json',summary)
        provenance['status']=summary['status']
        persist()
        for row in declarations:
            if row['status']=='PASS_STANDARD_ONLY':
                print('AUDITED_DECLARATION='+row['name']+'; STATUS=PASS_STANDARD_ONLY',flush=True)
        print('STRENGTHENING_AUDIT_STATUS='+summary['status'],flush=True)
        return bool(errors)
    except Exception as error:
        provenance.update(status='FAIL',error=str(error))
        persist()
        print('STRENGTHENING_CI_ERROR='+str(error),file=sys.stderr,flush=True)
        return 1

if __name__=='__main__':
    raise SystemExit(main())
