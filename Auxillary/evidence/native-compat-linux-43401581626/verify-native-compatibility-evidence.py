#!/usr/bin/env python3
"""Verify retained external compatibility evidence; never execute Lean."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

def require(ok, reason):
    if not ok:
        raise ValueError(reason)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def norm_type(log, name):
    found = re.findall(r'@' + re.escape(name) + r'\s*:\s*([\s\S]*?)\n[\x27\u2018]' + re.escape(name) + r'[\x27\u2019]', log)
    require(len(found) == 1, 'Missing or duplicate signature: ' + name)
    return re.sub(r'\s+', ' ', found[0]).strip()

def main():
    p = argparse.ArgumentParser()
    for name in ['repo','evidence','baseline','output']:
        p.add_argument('--'+name, type=Path, required=True)
    p.add_argument('--commit', required=True)
    a=p.parse_args(); root=a.repo.resolve(); ev=a.evidence.resolve(); old=a.baseline.resolve()
    spec=importlib.util.spec_from_file_location('compat_runner',root/'Auxillary/assembly/run_literature.py')
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    parser=m.import_helper(root/'Auxillary/scripts/verify_audit.py','compat_parser')
    blobs={}
    def blob(relative):
        if relative not in blobs:
            blobs[relative]=subprocess.check_output(['git','cat-file','--filters',a.commit+':'+relative],cwd=root)
        return blobs[relative]
    foundations={'propext','Classical.choice','Quot.sound'}
    policy=json.loads(blob('Auxillary/assembly/literature-targets.json'))
    names=m.validate_policy(policy)
    directory=ev/'literature'
    summary=load(directory/'audit-summary.json');prov=load(directory/'run-provenance.json')
    flow=load(ev/'source-match-certificate.json')
    require(flow['source_commit']==a.commit and flow['status']=='PASS_SOURCE_MATCH','Flow source identity mismatch')
    require(flow['passed_declaration_count']==169 and len(flow['passed_modules'])==18 and not flow['failed_or_blocked_modules'],'Native169 gate incomplete')
    require(all(x['current_import_closure_match'] for x in flow['passed_modules']),'Native source closure changed')
    require(summary['source_commit']==prov['source_commit']==a.commit,'Compatibility source identity mismatch')
    require(summary['status']==prov['theorem_axiom_audit_status']=='PASS_STANDARD_ONLY','Compatibility not standard only')
    require(prov['build_status']==prov['audit_command_status']=='PASS','Compatibility compiler did not pass')
    require(prov['external_native_linux'] and '4.34.0-rc1' in prov['actual_lean_version'] and '-linux-' in prov['actual_lean_version'],'Wrong compiler')
    require(prov['actual_mathlib_commit']=='de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11','Wrong Mathlib')
    require(prov['lockfile_sha256']==hashlib.sha256(blob('lake-manifest.json')).hexdigest(),'Wrong lockfile')
    require(summary['authorized_axiom_declarations']==[] and prov['authorized_axiom_declaration_count']==0 and prov['literature_theorem_count']==5,'Custom axiom counter')
    require(prov['source_manifest_sha256']==summary['source_manifest_sha256']==sha(directory/'source-manifest.json'),'Manifest linkage')
    require(prov['literature_policy_sha256']==summary['axiom_policy_sha256']==hashlib.sha256(blob('Auxillary/assembly/literature-targets.json')).hexdigest(),'Policy linkage')
    for stem,key in [('source-manifest','standard_43_source_manifest_sha256'),('audit-summary','standard_43_audit_summary_sha256'),('run-provenance','standard_43_provenance_sha256')]:
        require(prov[key]==sha(ev/(stem+'.json')),'Parent43 linkage '+key)
    manifest=load(directory/'source-manifest.json');require(manifest['source_commit']==a.commit,'Manifest commit')
    manifest_paths=set()
    for item in manifest['files']:
        relative=item['path']; require(relative not in manifest_paths,'Duplicate manifest input');manifest_paths.add(relative)
        require(not Path(relative).is_absolute() and '..' not in Path(relative).parts,'Unsafe manifest path')
        if relative.startswith('artifacts/assembly/'):
            path=ev/relative.removeprefix('artifacts/assembly/');actual=sha(path)
        else:
            actual=hashlib.sha256(blob(relative)).hexdigest()
        require(actual==item['sha256'],'Compatibility source hash: '+relative)
    for linked in [prov['native_source_hydration'],*prov['native_source_closure']]:
        path=directory/linked['report'];require(path.parent==directory and sha(path)==linked['sha256'] and load(path)['status']=='PASS','Native hydration provenance')
    require(prov['generated_audit_sha256']==sha(directory/'LiteratureAudit.lean') and prov['import_closure_sha256']==sha(directory/'import-closure.json'),'Generated input linkage')
    log=(directory/'audit.log').read_text();audit=(directory/'LiteratureAudit.lean').read_text()
    records=m.verify_target_axioms(log,audit,policy,parser)
    require(records==summary['targets'],'Raw five records differ from summary')
    require(all(set(x['axioms'])==foundations for x in records),'Expected exact standard3 for each compatibility theorem')
    closure=load(directory/'import-closure.json')['local_modules']
    for item in closure:
        require(hashlib.sha256(blob(item['path'])).hexdigest()==item['sha256']==sha(root/item['path']),'Compatibility closure mismatch '+item['path'])
    parent=load(ev/'audit-summary.json');raw=parser.parse_axioms((ev/'audit.log').read_text())
    require(len(parent['theorems'])==len(raw)==43 and parent['status']=='PASS_STANDARD_ONLY','Strict43 mismatch')
    for item in parent['theorems']:
        name=item['name'];require(name in raw and len(raw[name])==1,'Strict43 raw record missing')
        actual={parser.normalize_axiom_name(x) for x in raw[name][0]}
        require(actual<=foundations and actual==set(item['axioms']),'Strict43 unexpected axiom')
    baseline_commit=load(old/'native-root-type-certificate.json')['source_commit']
    old_log=(old/'literature/audit.log').read_text();signatures=[]
    for name in names:
        before=norm_type(old_log,name);after=norm_type(log,name)
        require(before==after,'Legacy signature changed: '+name)
        signatures.append({'name':name,'status':'EXACT_ELABORATED_TYPE_UNCHANGED','normalized_type_sha256':hashlib.sha256(after.encode()).hexdigest(),'normalized_type':after})
    native_log=(ev/'flow/FlowRealization/audit.log').read_text()
    require(norm_type(native_log,'ClassicalMechanicsAssembly.L1_native')==signatures[0]['normalized_type'],'Exact native L1 type mismatch')
    native_closure=load(ev/'flow/FlowRealization/import-closure.json')['local_modules']
    require(not any('.Literature' in x['module'] for x in native_closure),'Native L1 imports historical compatibility')
    relative='ASSEMBLY/ClassicalMechanicsAssembly/LiteratureClosure.lean'
    old_source=subprocess.check_output(['git','show',baseline_commit+':'+relative],cwd=root,text=True)
    new_source=blob(relative).decode()
    def uncomment(text):
        text=re.sub(r'/\*[\s\S]*?\*/','',text)
        text=re.sub(r'/\-[\s\S]*?\-/','',text)
        return '\n'.join(x for x in text.splitlines() if x.strip())
    require(uncomment(old_source)==uncomment(new_source),'Legacy root declaration bodies or signatures changed')
    output={'schema_version':1,'status':'PASS_NATIVE_COMPATIBILITY_AND_EXACT_LEGACY_TYPES','source_commit':a.commit,'baseline_source_commit':baseline_commit,'external_run_id':flow['external_run_id'],'external_artifact_id':flow['external_artifact_id'],'external_artifact_sha256':flow['external_artifact_sha256'],'source_match_certificate_sha256':sha(ev/'source-match-certificate.json'),'baseline_native_root_certificate_sha256':sha(old/'native-root-type-certificate.json'),'strict_assembly_declarations':43,'native_flow_declarations':169,'compatibility_theorems':5,'total_fresh_standard_only_records':217,'authorized_custom_axioms':[],'compatibility_source_input_count':len(manifest_paths),'compatibility_import_closure_count':len(closure),'compatibility_source_inputs_match':True,'compatibility_current_import_closure_match':True,'exact_L1_native_matches_original_L1':True,'legacy_root_types_and_bodies_unchanged':True,'native_root_imports_literature_module':False,'compatibility_axiom_records':records,'preserved_elaborated_types':signatures,'local_lean_executions':0,'scope':'Finite positive slab; supplied smooth spatially periodic divergence-free velocity; constructed normalized material path and equation equivalence with literal pressure pullback. Original explicit premises retained. Arbitrary-data NSE existence and full solution-set bijection are not asserted.'}
    a.output.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:output[k] for k in ['status','total_fresh_standard_only_records','compatibility_import_closure_count','exact_L1_native_matches_original_L1','legacy_root_types_and_bodies_unchanged']}))

if __name__=='__main__':
    main()
