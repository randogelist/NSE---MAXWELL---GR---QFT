#!/usr/bin/env python3
"""Static endpoint catalog; never invokes Lean, Lake or elan."""
from pathlib import Path
import hashlib
import json
import re
import shutil

REPO = Path(__file__).resolve().parents[3]
PACKAGE = REPO / 'TEMP'
SOURCE_INDEX = REPO / 'GR_adapter/Derivation/NSE_GR_AXIOM_GLUING_INDEX.json'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def first(record, *keys):
    for key in keys:
        if key in record:
            return record[key]
    raise ValueError(f'Missing keys {keys}')

def main():
    source = json.loads(SOURCE_INDEX.read_text())
    records = []
    expected = {(e['id'], e['name']) for e in source['mathlib']}
    expected |= {(e['id'], d['full_name']) for e in source['methlib'] for d in e['declarations']}
    for p in sorted(PACKAGE.glob('M*/**/source.json')):
        data = json.loads(p.read_text())
        endpoint = p.with_name('Endpoint.lean')
        entry = first(data, 'entry_id', 'id')
        name = first(data, 'source_name', 'upstream_name')
        export = first(data, 'export_name', 'endpoint', 'export', 'candidate_export')
        stated_hash = first(data, 'candidate_sha256', 'endpoint_sha256', 'endpoint_file_sha256', 'extracted_file_sha256')
        assert stated_hash == sha(endpoint), (p, 'candidate hash mismatch')
        body = endpoint.read_text()
        assert re.search(r'\b(?:theorem|lemma|def)\s+_root_\.' + re.escape(export) + r'\b', body), p
        assert (entry, name) in expected, (p, name)
        imports = first(data, 'upstream_imports', 'upstream_import', 'imports')
        if isinstance(imports, str): imports = [imports]
        records.append({
            'entry_id': entry, 'member_id': data.get('member_id'),
            'module': data['module'], 'export': export, 'source_name': name,
            'path': str(endpoint.relative_to(REPO)), 'metadata': str(p.relative_to(REPO)),
            'sha256': sha(endpoint), 'source_sha256': data['source_sha256'],
            'source_url': data['source_url'],
            'source_revision': first(data, 'source_revision', 'source_commit'),
            'imports': imports, 'uses': data['uses'],
            'extraction_kind': first(data, 'extraction_kind', 'extraction_method'),
            'status': 'A_TIER_CANDIDATE',
        })
    assert len(records) == 85, len(records)
    assert {(r['entry_id'], r['source_name']) for r in records} == expected
    assert len({r['export'] for r in records}) == 85
    assert len({r['module'] for r in records}) == 85
    closure = json.loads((PACKAGE/'dependency-sources.json').read_text())
    groups = {}
    for r in records: groups.setdefault(r['entry_id'], []).append(r)
    assert len(groups) == 82
    index = {
        'schema_version': 1, 'mode': 'A_TIER_DERIVATION',
        'status': 'A_TIER_CANDIDATE', 'local_lean_executions': 0,
        'entry_folders': 82, 'endpoint_modules': 85, 'mathlib_entries': 65,
        'methlib_entries': 17, 'methlib_named_endpoints': 20,
        'copied_non_mathlib_dependency_modules': closure['module_count'],
        'mathlib_pin': source['mathlib_pin'], 'lean_toolchain': 'leanprover/lean4:v4.34.0-rc1',
        'source_index': str(SOURCE_INDEX.relative_to(REPO)), 'source_index_sha256': sha(SOURCE_INDEX),
        'endpoint_contract': 'Exactly one selected exported declaration per Endpoint.lean; copied body, explicit imported upstream definitions/helpers.',
        'not_claimed': ['dependency-free Lean', 'GR namespace/sign/time-domain adapters', 'LI01-LI03 discharge', 'GR root closure'],
        'external_evidence_status': 'See TEMP_ENDPOINT_EXTRACTION_A_TIER.txt; this catalog records candidate source provenance.',
        'records': records,
        'chain_nodes': {n['id']: [r['export'] for r in records if n['id'] in r['uses']] for n in source['nodes']},
    }
    (PACKAGE/'INDEX.json').write_text(json.dumps(index, ensure_ascii=False, indent=2)+'\n')
    lines = ['# TEMP — isolated endpoint bodies', '', '```text',
        'ENTRY_FOLDERS = 82', 'SINGLE_ENDPOINT_MODULES = 85',
        'MATHLIB_ENTRIES = 65', 'METHLIB_ENTRIES = 17 / 20 declarations',
        'COPIED_NON_MATHLIB_DEPENDENCIES = 72',
        'SOURCE_STATUS = A_TIER_CANDIDATE; promotion requires matching external evidence',
        'LOCAL_LEAN_EXECUTIONS = 0', '```', '',
        'Each leaf contains `Endpoint.lean` and exact source metadata in `source.json`.',
        'ML047 and ML049 explicitly adapt generated `to_additive` proofs. ML006/ML008',
        'retain their definition-valued outputs; ML064/ML065 export structure-valued',
        'definitions without registering new global instances.', '',
        'The target proof bodies are isolated. Owning upstream modules remain explicit',
        'imports for definitions, notation, instances and helper results. Mathlib stays',
        'pinned; the 72-module non-Mathlib source closure is copied byte-for-byte.',
        'This does not supply the unimplemented GR adapters or the GR root.', '',
        '[Endpoint/chain index](INDEX.json) · [Dependency provenance](dependency-sources.json) ·',
        '[Compiler status](TEMP_ENDPOINT_EXTRACTION_A_TIER.txt)', '',
        'External cached execution: `run.cmd` on native Windows, or `bash run.sh` on Linux.',
        'Each export is compared with its original type and receives a named axiom audit.', '',
        '| Entry | Endpoint modules | Original declarations | GC nodes |',
        '|---|---|---|---|']
    for entry, rs in sorted(groups.items()):
        modules = '<br>'.join(f'[`{r["module"]}`]({Path(r["path"]).relative_to("TEMP").as_posix()})' for r in rs)
        names = '<br>'.join('`'+r['source_name']+'`' for r in rs)
        uses = ', '.join(sorted(set(x for r in rs for x in r['uses'])))
        lines.append(f'| {entry} | {modules} | {names} | {uses} |')
    (PACKAGE/'README.md').write_text('\n'.join(lines)+'\n')
    shutil.copyfile(REPO/'Fefferman_adapter/NativeSources/mathlib/LICENSE', PACKAGE/'LICENSE')
    print(json.dumps({k:index[k] for k in ['entry_folders','endpoint_modules','copied_non_mathlib_dependency_modules','status']}))

if __name__ == '__main__': main()
