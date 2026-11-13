#!/usr/bin/env python3
"""Verify retained external TEMP evidence against exact local source bytes. No Lean."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--artifact-dir',type=Path,required=True)
    ap.add_argument('--expected-sha',required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    repo=Path(__file__).resolve().parents[3]; artifact=args.artifact_dir.resolve()
    spec=importlib.util.spec_from_file_location('temp_audit_parser',Path(__file__).with_name('run_temp.py'))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    require=module.require
    summary=read(artifact/'audit-summary.json');provenance=read(artifact/'provenance-build.json')
    manifest=read(artifact/'source-manifest.json')
    targets=read(repo/'Auxillary/TEMP/audit-targets.json')
    expected=[x['name'] for x in targets]
    require(len(expected)==85 and len(set(expected))==85,'Exact target inventory')
    for data in [summary,provenance,manifest]:require(data['source_commit']==args.expected_sha,'Source commit mismatch')
    require(summary['status']=='PASS_STANDARD_ONLY' and provenance['status']=='PASS_STANDARD_ONLY','External pass absent')
    require(summary['target_count']==85,'Wrong target count')
    require(summary['actual_mathlib_commit']==module.MATHLIB,'Mathlib mismatch')
    version=summary['actual_lean_version']
    require('4.34.0-rc1' in version and module.COMPILER_COMMIT[:7] in version,'Compiler mismatch')
    require((artifact/'lean-version-build.log').read_text().strip()==version,'Compiler log mismatch')
    require(summary['source_manifest_sha256']==digest(artifact/'source-manifest.json'),'Source manifest hash')
    require(summary['audit_source_sha256']==digest(artifact/'EndpointAudit.lean'),'Audit program hash')
    require(summary['audit_log_sha256']==digest(artifact/'endpoints-audit.log'),'Audit log hash')
    require(summary['source_input_verification']=='PASS','Source input validation absent')
    verified=[]
    for item in manifest['files']:
        p=repo/item['path'];require(p.resolve().is_relative_to(repo.resolve()),'Source path escaped repository')
        require(p.is_file() and digest(p)==item['sha256'],'Source hash mismatch: '+item['path'])
        verified.append(item['path'])
    log=(artifact/'endpoints-audit.log').read_text()
    actual=module.audit_records(log,expected)
    require(actual==summary['targets'],'Summary/raw named audits differ')
    matches=re.findall(r'TYPE_MATCH (GRTemp\.[A-Za-z0-9_.]+)',module.ANSI.sub('',log))
    require(sorted(matches)==sorted(expected),'Exact source-type ledger differs')
    require(summary['source_type_match']=='PASS' and summary['source_type_match_count']==85,'Type equality absent')
    pairs={x['export']:x['source'] for x in summary['source_type_pairs']}
    index=read(repo/'TEMP/INDEX.json')
    require(pairs=={x['export']:x['source_name'] for x in index['records']},'Type comparator source mismatch')
    for record in index['records']:require(record['path'] in verified,'Endpoint not in audited source manifest')
    commands=provenance['commands'];require(all(c['exit_code']==0 for c in commands),'Nonzero external command')
    result={'status':'PASS_STANDARD_ONLY','source_commit':args.expected_sha,
        'workflow_run_id':provenance['github_run_id'],'compiler':version,'mathlib':module.MATHLIB,
        'endpoint_count':85,'source_type_match_count':85,'source_files_verified':len(verified),
        'source_manifest_sha256':digest(artifact/'source-manifest.json'),
        'audit_log_sha256':digest(artifact/'endpoints-audit.log'),
        'local_lean_execution':False,'gr_root_promotion':'NONE'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))

if __name__=='__main__':main()
