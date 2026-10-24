"""Reproduce the full six-row extension with an already installed Lean 4.35.0."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def cache_digests(build, modules):
    return {module: {p.name:digest(p) for p in sorted(build.glob(module+'.olean*'))}
            for module in modules}

def executable(name):
    found = shutil.which(name)
    if found:
        return found
    candidate = Path.home() / '.elan/bin' / (name+'.exe' if os.name=='nt' else name)
    if candidate.is_file():
        return str(candidate)
    raise RuntimeError(name+' is not installed')

def redact(text):
    for prefix, replacement in [(str(ROOT), '<PROJECT>'), (str(Path.home()), '<HOME>')]:
        for variant in [prefix, prefix.replace('\\','/')]:
            text = re.sub(re.escape(variant),lambda match:replacement,text,flags=re.I)
    return text

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--toolchain', default='leanprover/lean4:v4.35.0')
    parser.add_argument('--workers', type=int, choices=range(1,5), default=4)
    args = parser.parse_args()
    manifest = json.loads((ROOT/'extension-manifest.json').read_text(encoding='utf-8'))
    expected = json.loads((ROOT/'extension-theorems.json').read_text(encoding='utf-8'))
    manifest_sha=digest(ROOT/'extension-manifest.json')
    for name, sha in manifest['sha256'].items():
        if digest(ROOT/name) != sha:
            raise RuntimeError('File hash changed: '+name)
        if name.endswith('.lean'):
            source = re.sub(r'/\-.*?\-/','',(ROOT/name).read_text(encoding='utf-8-sig'),flags=re.S)
            source = re.sub(r'--[^\n]*','',source)
            if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b|#eval!',source):
                raise RuntimeError('Proof bypass: '+name)
    modules = manifest['topological_modules']
    assert len(modules)==len(set(modules))==341
    assert len(expected['names'])==len(set(expected['names']))==8720
    assert expected['topological_modules']==modules
    assert all(manifest['sha256'][name]==sha for name,sha in expected['source_sha256'].items())
    assert digest(ROOT/'AuditAllSubmission.lean')==expected['generated_audit_sha256']
    assert {'extension-theorems.json','AuditAllSubmission.lean','reproduce_extension.py'}<=set(manifest['sha256'])
    assert {module+'.lean' for module in modules}<=set(manifest['sha256'])
    build = ROOT/'.lake/build/lib/lean'
    cache_existed = build.exists() and any(build.iterdir())
    build.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '1'
    env['LEAN_PATH'] = os.pathsep.join([str(build),str(ROOT)])
    started = time.time()
    compile_records=[]; replay_records=[]
    log_path = ROOT/'extension-reproduction.log'
    with log_path.open('w',encoding='utf-8') as log:
        def run(command, timeout=1800):
            result = subprocess.run(command,cwd=ROOT,env=env,capture_output=True,
                text=True,encoding='utf-8',errors='replace',timeout=timeout)
            output=result.stdout+result.stderr
            log.write(redact('$ '+' '.join(map(str,command))+'\n'+output+'\n'));log.flush()
            if result.returncode:
                raise RuntimeError(redact('Command failed: '+output[-6000:]))
            return result.stdout
        installed=run([executable('elan'),'toolchain','list'])
        if args.toolchain not in {line.split()[0] for line in installed.splitlines() if line.strip()}:
            raise RuntimeError('Requested toolchain is not already installed; no download attempted')
        lean=[executable('lean'),'+'+args.toolchain]
        if 'version 4.35.0' not in run(lean+['--version']):
            raise RuntimeError('Lean 4.35.0 is required')
        for index,module in enumerate(modules,1):
            run(lean+['-o',str(build/(module+'.olean')),str(ROOT/(module+'.lean'))])
            compile_records.append({'module':module,'returncode':0,
                'source_sha256':digest(ROOT/(module+'.lean')),
                'olean_sha256':digest(build/(module+'.olean'))})
            print('Compiled',index,'/',len(modules),module,flush=True)
        fresh_artifacts=cache_digests(build,modules)
        audit=run(lean+[str(ROOT/'AuditAllSubmission.lean')])
        parsed={name:[value.strip() for value in values.split(',') if value.strip()]
            for name,values in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]",audit,re.M)}
        parsed.update({name:[] for name in re.findall(r"^'([^']+)' does not depend on any axioms",audit,re.M)})
        if set(parsed)!=set(expected['names']) or any(set(values)-ALLOWED for values in parsed.values()):
            raise RuntimeError('Axiom audit incomplete or unexpected axiom')
        prefix=Path(run(lean+['--print-prefix']).strip())
        checker=prefix/'bin'/('leanchecker.exe' if os.name=='nt' else 'leanchecker')
        if not checker.is_file():
            raise RuntimeError('Bundled leanchecker unavailable')
        def replay(module):
            result=subprocess.run([str(checker),'--verbose',module],cwd=ROOT,env=env,
                capture_output=True,text=True,encoding='utf-8',errors='replace',timeout=1800)
            output=result.stdout+result.stderr
            names=re.findall(r'^replaying (\S+)',result.stdout,re.M)
            if result.returncode or names!=[module]:
                raise RuntimeError('Kernel replay incomplete: '+module+'\n'+redact(output[-6000:]))
            return module,output
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            for future in as_completed([pool.submit(replay,module) for module in modules]):
                module,output=future.result();log.write(redact(output));log.flush()
                replay_records.append({'module':module,'returncode':0,
                    'olean_sha256':digest(build/(module+'.olean'))})
                print('Kernel replay',len(replay_records),'/',len(modules),module,flush=True)
    assert cache_digests(build,modules)==fresh_artifacts,'Artifacts changed during audit/replay'
    assert {item['module']:item['olean_sha256'] for item in compile_records}=={
        item['module']:item['olean_sha256'] for item in replay_records}
    for name,sha in manifest['sha256'].items():
        assert digest(ROOT/name)==sha,name
    assert digest(ROOT/'extension-manifest.json')==manifest_sha,'Manifest changed during reproduction'
    assert all(item['source_sha256']==manifest['sha256'][item['module']+'.lean'] for item in compile_records)
    report={'success':True,'modules_compiled':len(compile_records),
        'theorems_axiom_audited':len(parsed),'modules_kernel_replayed':len(replay_records),
        'project_build_cache_existed_before':cache_existed,'seconds':round(time.time()-started,2),
        'source_manifest_sha256':digest(ROOT/'extension-manifest.json'),
        'cache_artifact_sha256':fresh_artifacts,'cache_unchanged_during_audit_and_replay':True,
        'compile_records':compile_records,'replay_records':replay_records,'axiom_closures':parsed,
        'kernel':'Lean bundled kernel; upstream Std trusted; not an independent implementation',
        'external_human_review':False,'no_dependency_or_toolchain_download':True,
        'local_directory_prefixes_redacted':True}
    (ROOT/'extension-reproduction.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
    print(json.dumps({key:report[key] for key in ['success','modules_compiled','theorems_axiom_audited','modules_kernel_replayed','seconds']},indent=2))

if __name__=='__main__':
    main()
