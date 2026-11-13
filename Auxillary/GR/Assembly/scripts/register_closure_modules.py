#!/usr/bin/env python3
"""Register prepared module signatures; this does not compile or promote proofs."""
import argparse
import hashlib
import json
from pathlib import Path
import re

parser = argparse.ArgumentParser()
parser.add_argument('modules', nargs='+')
args = parser.parse_args()
repo = Path(__file__).resolve().parents[4]
support = repo / 'Auxillary/GR/Assembly'
inventory_path = support / 'audit-targets.json'
inventory = json.loads(inventory_path.read_text())
root_path = repo / 'ASSEMBLY/GRAssembly.lean'
root_lines = root_path.read_text().splitlines()
registered = []
for short in args.modules:
    assert re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', short), short
    module = 'GRAssembly.' + short
    source = repo / ('ASSEMBLY/GRAssembly/' + short + '.lean')
    text = source.read_text()
    namespaces = re.findall(r'^namespace\s+(\S+)', text, re.M)
    assert namespaces == ['NSEGR.Assembly'], (module, namespaces)
    declarations = re.findall(r'^(?:noncomputable\s+)?(theorem|def|abbrev|structure)\s+([\w.\']+)', text, re.M)
    assert declarations, module
    inventory = [row for row in inventory if row['module'] != module]
    for kind, name in declarations:
        inventory.append({'name': 'NSEGR.Assembly.' + name,
                          'module': module, 'kind': kind,
                          'gc': [], 'status': 'A_TIER_CANDIDATE'})
    line = 'import ' + module
    if line not in root_lines:
        root_lines.append(line)
    registered.append({'module': module, 'path': source.relative_to(repo).as_posix(),
                       'sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                       'declarations': len(declarations), 'status': 'A_TIER_CANDIDATE'})
assert len({row['name'] for row in inventory}) == len(inventory), 'duplicate declaration'
inventory_path.write_text(json.dumps(inventory, indent=2, ensure_ascii=False) + '\n')
root_path.write_text('\n'.join(root_lines) + '\n')
print(json.dumps({'registered': registered, 'total_named_assembly_targets': len(inventory)}, indent=2))
