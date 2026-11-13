#!/usr/bin/env python3
"""Index actual assembly source declarations; no Lean execution."""
import hashlib
import json
import re
from pathlib import Path

repo = Path(__file__).resolve().parents[4]
package = repo / 'ASSEMBLY'
support = repo / 'Auxillary/GR/Assembly'
gc = {
    'AnalyticFourier': ['GC03'],
    'GaugePrimitive': ['GC21'],
    'GaussianConstraints': ['GC16'],
    'HodgeLocal': ['GC02', 'GC17'],
    'HodgeTime': ['GC02', 'GC17'],
    'HodgeTransport': ['GC01', 'GC02', 'GC04'],
    'LorentzFactor': ['GC15'],
    'LorentzNeighborhood': ['GC15'],
    'PeriodicGluing': ['GC07', 'GC08', 'GC09'],
    'PeriodicWitness': ['GC08', 'GC09', 'GC14'],
    'PressureGauge': ['GC21'],
    'ScalarCompletion': ['GC11', 'GC19'],
    'ScalarCore': ['GC05', 'GC06', 'GC10', 'GC20'],
    'ScalarJet': ['GC05', 'GC06', 'GC10', 'GC20'],
}
pattern = re.compile(r'^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(theorem|def)\s+([^\s:(]+)', re.M)
files = sorted((package / 'GRAssembly').glob('*.lean'))
targets, declarations, modules = [], [], []
for file in files:
    text = file.read_text(encoding='utf-8')
    module = 'GRAssembly.' + file.stem
    assert file.stem in gc, module
    imports = re.findall(r'^import (\S+)', text, re.M)
    modules.append({'module': module, 'source': file.relative_to(repo).as_posix(),
                    'sha256': hashlib.sha256(file.read_bytes()).hexdigest(),
                    'gc': gc[file.stem], 'imports': imports})
    for match in pattern.finditer(text):
        target = {'name': 'NSEGR.Assembly.' + match[2], 'module': module,
                  'kind': match[1], 'gc': gc[file.stem]}
        targets.append(target)
        declarations.append(dict(target, source=file.relative_to(repo).as_posix(),
                                 line=text[:match.start()].count('\n') + 1))
assert len({t['name'] for t in targets}) == len(targets)
(package / 'GRAssembly.lean').write_text('import TempEndpoints\n' +
    ''.join('import ' + m['module'] + '\n' for m in modules), encoding='utf-8')
(support / 'audit-targets.json').write_text(json.dumps(targets, indent=2) + '\n', encoding='utf-8')
index = {'schema_version': 1, 'scope': 'native GR assembly declarations; premises remain in exact Lean types',
         'baseline_gr_declarations': 401, 'cutout_declarations': 85,
         'new_theorems': sum(t['kind'] == 'theorem' for t in targets),
         'new_definitions': sum(t['kind'] == 'def' for t in targets),
         'modules': modules, 'declarations': declarations}
(support / 'endpoint-index.json').write_text(json.dumps(index, indent=2) + '\n', encoding='utf-8')
print(json.dumps({k: index[k] for k in ['new_theorems', 'new_definitions']}, sort_keys=True))
