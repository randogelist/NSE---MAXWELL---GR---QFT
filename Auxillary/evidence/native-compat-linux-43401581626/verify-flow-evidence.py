#!/usr/bin/env python3
"""Verify external flow evidence against Git source bytes; never execute Lean."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(test, message):
    if not test:
        raise ValueError(message)

def load(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--repo',type=Path,required=True)
    p.add_argument('--evidence',type=Path,required=True)
    p.add_argument('--commit',required=True)
    p.add_argument('--run',type=int,required=True)
    p.add_argument('--artifact',type=int,required=True)
    p.add_argument('--archive',type=Path,required=True)
    p.add_argument('--archive-sha256',required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args(); root=a.repo.resolve(); ev=a.evidence.resolve()
    require(sha(a.archive)==a.archive_sha256, 'Artifact archive digest mismatch')
    require(re.fullmatch(r'[0-9a-f]{40}',a.commit) is not None, 'Invalid source commit')
    # Repository attributes explicitly check out *.cmd as CRLF, including Linux.
    # Verify attributes against the source commit before reconstructing checkout bytes.
    attribute_paths=subprocess.check_output(['git','ls-tree','-r','--name-only',a.commit],cwd=root,text=True).splitlines()
    for relative in attribute_paths:
        if Path(relative).name=='.gitattributes':
            require((root/relative).read_bytes()==subprocess.check_output(['git','show',a.commit+':'+relative],cwd=root),'Checkout attributes changed')
    blob_cache={}
    def blob(relative):
        if relative not in blob_cache:
            result=subprocess.run(['git','cat-file','--filters',a.commit+':'+relative],cwd=root,check=True,capture_output=True)
            blob_cache[relative]=result.stdout
        return blob_cache[relative]
    spec=importlib.util.spec_from_file_location('flow_evidence_parser',root/'Auxillary/scripts/verify_audit.py')
    parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
    require(parser.ALLOWED_AXIOMS==frozenset({'propext','Classical.choice','Quot.sound'}),'Foundational allowlist changed')
    require(blob('lean-toolchain').decode().strip()=='leanprover/lean4:v4.34.0-rc1','Toolchain source mismatch')
    policy=json.loads(blob('Auxillary/assembly/flow-targets.json'))
    targets={x['module']:x['targets'] for x in policy['modules']}
    aggregate=load(ev/'flow/aggregate-summary.json')
    require(aggregate['source_commit']==a.commit,'Aggregate source mismatch')
    require(set(aggregate['module_schedule'])==set(targets),'Module schedule mismatch')
    require(len(aggregate['modules'])==len(targets),'Module result count mismatch')
    require(sha(ev/'source-manifest.json')==aggregate['standard_43_source_manifest_sha256'],'Parent manifest linkage mismatch')
    require(sha(ev/'audit-summary.json')==aggregate['standard_43_audit_summary_sha256'],'Parent audit linkage mismatch')
    require(sha(ev/'run-provenance.json')==aggregate['standard_43_provenance_sha256'],'Parent provenance linkage mismatch')
    parent=load(ev/'audit-summary.json')
    require(parent['status']=='PASS_STANDARD_ONLY' and len(parent['theorems'])==43,'Preserved43 did not pass')
    checked_manifests={}
    def check_manifest(path):
        data=load(path);require(data['source_commit']==a.commit,'Manifest source mismatch')
        names=set()
        for entry in data['files']:
            rel=entry['path'];require(rel not in names,'Duplicate source input');names.add(rel)
            require(not Path(rel).is_absolute() and '..' not in Path(rel).parts,'Escaping source input')
            if rel.startswith('artifacts/assembly/'):
                actual=(ev/rel.removeprefix('artifacts/assembly/')).resolve()
                require(actual.is_relative_to(ev) and actual.is_file(),'Missing generated input '+rel)
                got=sha(actual)
            else:
                got=hashlib.sha256(blob(rel)).hexdigest()
            require(got==entry['sha256'],'Source SHA mismatch '+rel)
        checked_manifests[str(path.relative_to(ev))]=len(names)
        return data
    check_manifest(ev/'source-manifest.json')
    passes=[]; failed=[]
    for record in aggregate['modules']:
        module=record['module'];require(record['targets']==targets[module],'Per-module target mismatch')
        if record['status']!='PASS_STANDARD_ONLY':
            failed.append({'module':module,'status':record['status'],'blocked_by':record['blocked_by']})
            continue
        directory=ev/'flow'/module.rsplit('.',1)[1]
        provenance=load(directory/'run-provenance.json'); summary=load(directory/'audit-summary.json')
        require(provenance['source_commit']==summary['source_commit']==a.commit,'Passed module source mismatch')
        require(provenance['build_status']==provenance['audit_command_status']=='PASS','Compiler/audit command not passed')
        require(provenance['theorem_axiom_audit_status']==summary['status']=='PASS_STANDARD_ONLY','Axiom audit not passed')
        require(provenance['external_native_linux'] is True and '-linux-' in provenance['actual_lean_version'] and '4.34.0-rc1' in provenance['actual_lean_version'],'Wrong compiler')
        require(provenance['actual_mathlib_commit']=='de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11','Wrong Mathlib revision')
        require(provenance['lockfile_sha256']==hashlib.sha256(blob('lake-manifest.json')).hexdigest(),'Wrong dependency lock')
        require(provenance['source_manifest_sha256']==summary['source_manifest_sha256']==record['source_manifest_sha256']==sha(directory/'source-manifest.json'),'Manifest hash disagreement')
        require(record['audit_summary_sha256']==sha(directory/'audit-summary.json'),'Audit summary hash disagreement')
        check_manifest(directory/'source-manifest.json')
        for linked in [provenance['native_source_hydration'],*provenance['native_source_closure']]:
            require(Path(linked['report']).name==linked['report'],'Invalid native report path')
            require(sha(directory/linked['report'])==linked['sha256'] and load(directory/linked['report'])['status']=='PASS','Native dependency report mismatch')
        names=targets[module];audit=(directory/'Audit.lean').read_text()
        require(re.findall(r'^#check @(.+)$',audit,re.M)==names,'Exact signature checks mismatch')
        require(re.findall(r'^#print axioms (.+)$',audit,re.M)==names,'Exact axiom commands mismatch')
        parsed=parser.parse_axioms((directory/'audit.log').read_text())
        require(set(parsed)==set(names) and all(len(x)==1 for x in parsed.values()),'Missing/duplicate/unexpected axiom records')
        theorem_records=[]
        for name in names:
            axioms={parser.normalize_axiom_name(x) for x in parsed[name][0]}
            require(axioms<=parser.ALLOWED_AXIOMS,'Unapproved axiom '+name)
            theorem_records.append({'name':name,'axioms':sorted(axioms)})
        require([x['name'] for x in summary['theorems']]==names,'Audit summary target order mismatch')
        for item in summary['theorems']:
            require(item['status']=='PASS_STANDARD_ONLY' and not item['unapproved_axioms'] and not item['malformed_axioms'],'Failed summary record')
            require(set(item['axioms'])==set(next(x['axioms'] for x in theorem_records if x['name']==item['name'])),'Raw/summary axiom disagreement')
        closure=load(directory/'import-closure.json')['local_modules']; current=[]
        for item in closure:
            require(hashlib.sha256(blob(item['path'])).hexdigest()==item['sha256'],'Import closure source mismatch')
            path=root/item['path'];current.append({'module':item['module'],'path':item['path'],'sha256':item['sha256'],'current_worktree_match':path.is_file() and sha(path)==item['sha256']})
        passes.append({'module':module,'declaration_count':len(names),'axiom_records':theorem_records,'source_manifest_sha256':sha(directory/'source-manifest.json'),'import_closure':current,'current_import_closure_match':all(x['current_worktree_match'] for x in current)})
    require(len(passes)==aggregate['passed_modules'],'Passed count disagreement')
    require(sum(x['declaration_count'] for x in passes)==aggregate['audited_passed_theorems'],'Audited declaration count disagreement')
    certificate={'schema_version':1,'status':'PASS_SOURCE_MATCH','source_commit':a.commit,'external_run_id':a.run,'external_artifact_id':a.artifact,'external_artifact_sha256':a.archive_sha256,'external_run_url':f'https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/{a.run}','artifact_url':f'https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/{a.run}/artifacts/{a.artifact}','aggregate_status':aggregate['status'],'matched_unique_tracked_inputs':len(blob_cache),'verified_manifests':checked_manifests,'passed_modules':passes,'failed_or_blocked_modules':failed,'passed_declaration_count':sum(x['declaration_count'] for x in passes),'local_lean_executions':0,'scope':'Exact passed declarations only; every explicit premise is retained. Exact root contract identity and compatibility migration require the separate type-preservation certificate.'}
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(certificate,indent=2)+'\n')
    print(json.dumps({'status':certificate['status'],'passed_modules':len(passes),'declarations':certificate['passed_declaration_count'],'current_closures_match':all(x['current_import_closure_match'] for x in passes),'unique_source_inputs':len(blob_cache)}))

if __name__=='__main__':
    main()
