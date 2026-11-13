#!/usr/bin/env python3
"""Register committed proof bodies for external named audits; no Lean execution.

This source inventory is not compiler evidence. The external runner compiles
each selected module and checks every listed declaration's actual axioms.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re


def strip_comments(source):
    out = []
    i = 0
    depth = 0
    string = False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                depth += 1; out.extend('  '); i += 2
            elif source.startswith('-/', i):
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if source[i] == '\n' else ' '); i += 1
        elif string:
            if source[i] == '\\':
                out.extend('  '); i += 2
            elif source[i] == '"':
                string = False; out.append(' '); i += 1
            else:
                out.append('\n' if source[i] == '\n' else ' '); i += 1
        elif source.startswith('/-', i):
            depth = 1; out.extend('  '); i += 2
        elif source.startswith('--', i):
            j = source.find('\n', i)
            j = len(source) if j < 0 else j
            out.extend(' ' * (j-i)); i = j
        elif source[i] == '"':
            string = True; out.append(' '); i += 1
        else:
            out.append(source[i]); i += 1
    assert depth == 0 and not string, 'unterminated source comment/string'
    return ''.join(out)


def declarations(source):
    text = strip_comments(source)
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', text), 'forbidden proof construction'
    frames = []
    namespace = ''
    result = []
    for number, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        ns = re.match(r'^namespace\s+([\w.\']+)\s*$', line)
        if ns:
            frames.append(('namespace', namespace))
            name = ns[1]
            namespace = (namespace+'.'+name).strip('.')
            continue
        if re.match(r'^(?:noncomputable\s+)?section(?:\s+[\w\']+)?\s*$', line):
            frames.append(('section', namespace)); continue
        if re.match(r'^end(?:\s+[\w.\']+)?\s*$', line):
            assert frames, ('unmatched end', number)
            _, namespace = frames.pop(); continue
        while line.startswith('@['):
            end = line.find(']')
            assert end >= 0, ('multiline attribute unsupported', number)
            line = line[end+1:].lstrip()
        if line.startswith('private '):
            continue
        m = re.match(r'^(?:(?:noncomputable|protected)\s+)*(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([\w.\']+)\b', line)
        if not m:
            continue
        name = m[2]
        if name.startswith('_root_.'):
            full = name[len('_root_.'):]
        else:
            full = (namespace+'.'+name).strip('.')
        assert full.startswith('NSEGR.NativeLiterature.'), (number, full)
        result.append({'name':full,'kind':m[1],'line':number})
    assert not frames, ('unclosed namespaces/sections', frames)
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('modules', nargs='+')
    args = ap.parse_args()
    repo = Path(__file__).resolve().parents[4]
    support = repo/'Auxillary/GR/Assembly'
    target_file = support/'audit-targets.json'
    inventory = json.loads(target_file.read_text())
    root = repo/'ASSEMBLY/GRAssembly.lean'
    root_lines = root.read_text().splitlines()
    records = []
    for short in args.modules:
        assert re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',short)
        module = 'GRAssembly.'+short
        source = repo/('ASSEMBLY/GRAssembly/'+short+'.lean')
        decls = declarations(source.read_text())
        assert decls, ('no named declarations', module)
        inventory = [r for r in inventory if r['module'] != module]
        for d in decls:
            inventory.append({**{k:d[k] for k in ['name','kind']},'module':module,
                              'gc':[],'status':'A_TIER_CANDIDATE'})
        line='import '+module
        if line not in root_lines:
            root_lines.append(line)
        records.append({'module':module,'path':source.relative_to(repo).as_posix(),
                        'sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
                        'declarations':decls,'status':'A_TIER_CANDIDATE'})
    assert len({r['name'] for r in inventory})==len(inventory),'duplicate audit name'
    target_file.write_text(json.dumps(inventory,indent=2,ensure_ascii=False)+'\n')
    root.write_text('\n'.join(root_lines)+'\n')
    print(json.dumps({'registered':records,'total_named_assembly_targets':len(inventory)},indent=2))


if __name__=='__main__':
    main()
