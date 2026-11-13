#!/usr/bin/env python3
"""Pure Python policy mutation checks. No Lean invocation."""
import argparse, ast, copy, hashlib, importlib.util, json, subprocess
from pathlib import Path
import yaml

def main():
    p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();root=a.repo.resolve()
    paths=['Auxillary/assembly/run_literature.py','Auxillary/assembly/run_flow.py','Auxillary/assembly/literature-targets.json','.github/workflows/classical-assembly.yml','Auxillary/scripts/verify_audit.py']
    for x in [paths[0],paths[1],paths[4]]:ast.parse((root/x).read_text())
    policy=json.loads((root/paths[2]).read_text())
    workflow=yaml.safe_load((root/paths[3]).read_text());steps=next(iter(workflow['jobs'].values()))['steps'];runs=[s.get('run','') for s in steps]
    indices=[runs.index('bash Auxillary/'+x+'.sh') for x in ['run_assembly','run_flow','run_literature']];assert indices==sorted(indices)
    spec=importlib.util.spec_from_file_location('compat_policy_runner',root/paths[0]);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    parser=m.import_helper(root/paths[4],'compat_policy_parser');names=m.validate_policy(policy)
    source='\n'.join(f'#check @{n}\n#print axioms {n}' for n in names)
    log='\n'.join(f"@{n} : True\n'{n}' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in names)
    assert len(m.verify_target_axioms(log,source,policy,parser))==5
    rejected=[]
    for n in names:
        for ax in [names[0],names[1],'sorryAx','Unknown.admission']:
            bad=log.replace(f"'{n}' depends on axioms: [propext, Classical.choice, Quot.sound]",f"'{n}' depends on axioms: [propext, Classical.choice, Quot.sound, {ax}]")
            try:m.verify_target_axioms(bad,source,policy,parser)
            except ValueError as e:rejected.append({'kind':'injected_axiom','target':n,'axiom':ax,'result':'REJECTED','reason':str(e)})
            else:raise AssertionError((n,ax))
    for mutation in ['authorize','expected','kind','omit','duplicate']:
        q=copy.deepcopy(policy)
        if mutation=='authorize':q['authorized_axiom_declarations']=[names[0]]
        elif mutation=='expected':q['targets'][0]['expected_nonfoundational_axioms']=[names[0]]
        elif mutation=='kind':q['targets'][0]['kind']='axiom'
        elif mutation=='omit':q['targets'].pop()
        else:q['targets'][0]=q['targets'][1]
        try:m.validate_policy(q)
        except ValueError as e:rejected.append({'kind':'mutated_policy','mutation':mutation,'result':'REJECTED','reason':str(e)})
        else:raise AssertionError(mutation)
    for mutation,bad in [('duplicate_axiom_record',log+'\n'+log.splitlines()[-1]),('missing_axiom_record','\n'.join(log.splitlines()[:-2]))]:
        try:m.verify_target_axioms(bad,source,policy,parser)
        except ValueError as e:rejected.append({'kind':'mutated_output','mutation':mutation,'result':'REJECTED','reason':str(e)})
        else:raise AssertionError(mutation)
    for x in ['Auxillary/run_assembly.sh','Auxillary/run_flow.sh','Auxillary/run_literature.sh']:subprocess.run(['bash','-n',str(root/x)],check=True)
    result={'schema_version':1,'status':'PASS_STATIC_POLICY_AND_FAILURE_INJECTION','source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'inputs':[{'path':x,'sha256':hashlib.sha256((root/x).read_bytes()).hexdigest()} for x in paths],'workflow_order':['strict43','native169','compatibility5'],'workflow_zero_based_step_indices':indices,'authorized_custom_axioms':[],'target_count':5,'positive_case':'PASS_STANDARD_ONLY','negative_cases_rejected':len(rejected),'negative_cases':rejected,'python_json_yaml_bash_syntax':'PASS','local_lean_executions':0,'scope':'Verifier and policy behavior only; this static certificate does not establish any Lean theorem.'}
    assert len(rejected)==27
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'negative_cases_rejected':len(rejected)}))

if __name__=='__main__':main()
