"""Reproduce the exact delivered sources without installing dependencies."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def tool(name):
    found = shutil.which(name)
    if found:
        return found
    found = Path.home()/'.elan'/'bin'/(name+'.exe' if os.name == 'nt' else name)
    if found.is_file():
        return str(found)
    raise RuntimeError(name+' must already be installed; no download attempted')


def public_text(value):
    value = value.replace(str(ROOT), '<VERIFICATION_ROOT>')
    value = value.replace(str(Path.home()), '<USER_HOME>')
    return value


def run(command, log, env):
    completed = subprocess.run(command, cwd=ROOT, env=env, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, encoding='utf-8', errors='replace')
    log.write(public_text('$ '+' '.join(map(str, command))+'\n'+completed.stdout+'\n'))
    log.flush()
    if completed.returncode:
        raise RuntimeError('Command failed: '+public_text(str(command))+'\n'+public_text(completed.stdout[-5000:]))
    return completed.stdout


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--toolchain', default='leanprover/lean4:v4.35.0')
    args = parser.parse_args()
    start = time.time()
    cache_before = (ROOT/'.lake/build').exists()
    manifest = json.loads((ROOT/'source-manifest.json').read_text(encoding='utf-8'))
    modules = re.findall(r'^name\s*=\s*"([^"]+)"', (ROOT/'lakefile.toml').read_text(encoding='utf-8'), re.M)[1:]
    if len(modules) != len(set(modules)):
        raise RuntimeError('Duplicate module registration')
    source_theorems = 0
    for name, digest in manifest['sha256'].items():
        data = (ROOT/name).read_bytes()
        if hashlib.sha256(data).hexdigest() != digest:
            raise RuntimeError('Source hash mismatch: '+name)
        if name.endswith('.lean'):
            source = re.sub(r'/\-.*?\-/', '', data.decode('utf-8-sig'), flags=re.S)
            source = re.sub(r'--[^\n]*', '', source)
            if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b|#eval!', source):
                raise RuntimeError('Proof placeholder or bypass: '+name)
            if name[:-5] in modules:
                source_theorems += len(re.findall(r'^theorem\s+', source, re.M))
    audit_source = (ROOT/'AuditComplete.lean').read_text(encoding='utf-8')
    expected = re.findall(r'^#print axioms (\S+)', audit_source, re.M)
    if len(expected) != len(set(expected)) or len(expected) != source_theorems:
        raise RuntimeError('Theorem audit coverage mismatch')
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    reports = ROOT/'reports'
    reports.mkdir(exist_ok=True)
    with (reports/'reproduction.log').open('w', encoding='utf-8') as log:
        installed = run([tool('elan'), 'toolchain', 'list'], log, env)
        if args.toolchain not in {v.split()[0] for v in installed.splitlines() if v.strip()}:
            raise RuntimeError('Choose an already installed Lean 4.35.0 toolchain; no download attempted')
        prefix = [tool('lake'), '+'+args.toolchain]
        version = run(prefix+['env', 'lean', '--version'], log, env).strip()
        if 'version 4.35.0' not in version:
            raise RuntimeError('Unexpected Lean version: '+version)
        run(prefix+['build'], log, env)
        audit = run(prefix+['env', 'lean', 'AuditComplete.lean'], log, env)
        parsed = {n: [v.strip() for v in a.split(',') if v.strip()]
                  for n, a in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", audit, re.M)}
        parsed.update({n: [] for n in re.findall(r"^'([^']+)' does not depend on any axioms$", audit, re.M)})
        if set(parsed) != set(expected) or any(set(v)-ALLOWED for v in parsed.values()):
            raise RuntimeError('Incomplete axiom audit or unexpected axiom')
        replayed = []
        for offset in range(0, len(modules), 8):
            batch = modules[offset:offset+8]
            replay = run(prefix+['env', 'leanchecker', '--verbose']+batch, log, env)
            checked = re.findall(r'^replaying (\S+)\s*$', replay, re.M)
            if len(checked) != len(batch) or set(checked) != set(batch):
                raise RuntimeError('Incomplete kernel replay batch')
            replayed.extend(checked)
            (reports/'kernel-progress.json').write_text(json.dumps({
                'completed':len(replayed), 'total':len(modules),
                'completed_modules':replayed}, indent=2), encoding='utf-8')
            print('Kernel replay: '+str(len(replayed))+'/'+str(len(modules)), flush=True)
        if len(replayed) != len(modules) or set(replayed) != set(modules):
            raise RuntimeError('Incomplete local-module kernel replay')
        run(prefix+['env', 'lean', 'RuntimeCheck.lean'], log, env)
        run([sys.executable, '-X', 'utf8', 'check_runtime.py'], log, env)
    finite = json.loads((reports/'runtime-crosscheck.json').read_text(encoding='utf-8'))
    if not finite['success'] or finite['class_comparisons'] != 70 or finite['source_rows_compared'] != 499:
        raise RuntimeError('Unexpected finite cross-check results')
    result = {
        'success': True,
        'verified_utc': datetime.now(timezone.utc).isoformat(),
        'lean_version': version,
        'source_files_verified': len(manifest['sha256']),
        'project_build_cache_existed_before': cache_before,
        'audited_declarations': len(parsed),
        'axiom_closures': parsed,
        'kernel_replayed_local_modules': len(replayed),
        'kernel_replayed_module_names': replayed,
        'kernel_replay_implementation': 'bundled Lean 4.35.0 kernel; imported Std artifacts trusted',
        'second_independent_kernel_implementation': False,
        'external_human_mathematical_review': False,
        'nonempty_count_all_natural_x_ge_3': '(23*x*x+81*x+16)/2',
        'including_empty_count_all_natural_x_ge_3': '(23*x*x+81*x+18)/2',
        'main_entrypoint': 'LuRazClosure.closure_cardinality_for_every_x',
        'statement_entrypoints': [n for n in expected if n.startswith('LuRazSubmission.')],
        'omitted_row_uniqueness': 'proved from the other printed rows and printed uniform frequency',
        'arbitrary_nonempty_subfamily_correspondence': 'proved',
        'finite_class_comparisons': finite['class_comparisons'],
        'finite_source_rows_compared': finite['source_rows_compared'],
        'finite_complete_closure_comparisons': finite['totals'],
        'author_erratum_confirmed': False,
        'global_first_contribution_confirmed': False,
        'prize_eligibility_confirmed': False,
        'reward_amount_confirmed': False,
        'local_path_prefixes_redacted_in_public_log': True,
        'seconds': round(time.time()-start, 3)
    }
    (reports/'reproduction.json').write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items() if k not in {'axiom_closures', 'kernel_replayed_module_names'}},
                     ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
