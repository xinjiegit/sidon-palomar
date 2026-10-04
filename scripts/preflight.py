#!/usr/bin/env python3
"""Local structural checks; this is not Palomar's verifier or editorial review."""
from pathlib import Path
import argparse
import json
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
BAD_SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ilean', '.a', '.bc',
                '.dll', '.dylib', '.o', '.obj', '.so', '.trace')
AXIOMS = {'propext', 'Quot.sound', 'Classical.choice'}
errors = []
notes = []


def require(condition, message):
    if not condition:
        errors.append(message)


def after_comments(text):
    """Strip a leading sequence of whitespace and nested ordinary Lean comments."""
    text = text.lstrip()
    while text.startswith('--') or text.startswith('/-'):
        if text.startswith('--'):
            text = text.partition('\n')[2].lstrip()
        else:
            # Module doc comments must come after `module`.
            if text.startswith('/-!'):
                break
            depth, i = 1, 2
            while i < len(text) and depth:
                if text[i:i+2] == '/-':
                    depth += 1
                    i += 2
                elif text[i:i+2] == '-/':
                    depth -= 1
                    i += 2
                else:
                    i += 1
            text = text[i:].lstrip()
    return text


def load_json(path):
    try:
        return json.loads(path.read_text(encoding='utf-8'))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        errors.append(f'{path.name}: {exc}')
        return {}


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--release', action='store_true',
                    help='also reject unresolved metadata placeholders')
args = parser.parse_args()
files = []
for path in ROOT.rglob('*'):
    relative = path.relative_to(ROOT)
    if '.lake' in relative.parts or '.git' in relative.parts:
        continue
    if path.is_file() or path.is_symlink():
        files.append(path)
        require(not path.is_symlink(), f'{relative}: symbolic link in source package')
        require(not str(path).endswith(BAD_SUFFIXES), f'{relative}: compiled artifact')
        if path.suffix == '.lean':
            text = path.read_text(encoding='utf-8')
            require(len(text.splitlines()) <= 10000, f'{relative}: exceeds 10,000 lines')
            if path.name != 'lakefile.lean':
                require(re.match(r'module(?:\s|$)', after_comments(text)),
                        f'{relative}: missing module header')
        if path.stat().st_size < 1024:
            require(not path.read_bytes().startswith(b'version https://git-lfs.github.com/spec/v1'),
                    f'{relative}: Git LFS pointer')
require(not (ROOT/'.gitmodules').exists(), 'Git submodules are not permitted')
require(sum((ROOT/name).is_file() for name in ['lakefile.toml', 'lakefile.lean']) == 1,
        'exactly one Lake configuration is required')
require((ROOT/'LICENSE').is_file(), 'repository-root LICENSE is required')

toolchain = (ROOT/'lean-toolchain').read_text().strip()
match = re.fullmatch(r'leanprover/lean4:v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?', toolchain)
require(match is not None, 'lean-toolchain is not a pinned Lean release')
if match:
    release = tuple(map(int, match.groups()[:3]))
    rc = int(match.group(4)) if match.group(4) else 10**6
    require((release, rc) >= ((4, 35, 0), 2), 'below audited Palomar minimum v4.35.0-rc2')
manifest = load_json(ROOT/'lake-manifest.json')
require(manifest.get('packagesDir') == '.lake/packages', 'nonportable packagesDir')
seen = set()
for package in manifest.get('packages', []):
    name = package.get('name')
    require(name not in seen, f'duplicate dependency name: {name}')
    seen.add(name)
    require(package.get('type') == 'git', f'{name}: expected public Git dependency')
    require(re.fullmatch(r'[0-9a-f]{40}', package.get('rev', '')), f'{name}: unpinned revision')
    require(re.fullmatch(r'https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+',
                         package.get('url', '')), f'{name}: unsupported public GitHub URL')
require('mathlib' in seen, 'mathlib missing from lock file')
mathlib_toolchain = ROOT/'.lake/packages/mathlib/lean-toolchain'
if mathlib_toolchain.exists():
    require(mathlib_toolchain.read_text().strip() == toolchain,
            'resolved mathlib toolchain differs from project')
else:
    notes.append('resolved mathlib toolchain will be checked after dependency retrieval')

config = load_json(ROOT/'comparator.json')
required = {'challenge_module', 'solution_module', 'theorem_names', 'permitted_axioms'}
require(required <= config.keys(), 'missing required Comparator field')
require(config.keys() <= required | {'definition_names', 'enable_nanoda'},
        'unsupported submitter Comparator field')
require(config.get('challenge_module') != config.get('solution_module'),
        'Challenge and Solution must be distinct')
module_pattern = r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
for key in ['challenge_module', 'solution_module']:
    module = config.get(key, '')
    require(isinstance(module, str) and re.fullmatch(module_pattern, module), f'invalid {key}')
    path = ROOT/Path(*module.split('.')).with_suffix('.lean')
    require(path.is_file(), f'{key}: source is missing')
    if key == 'challenge_module' and path.is_file():
        text = path.read_text()
        require(path.stat().st_size <= 100*1024, 'Challenge exceeds 100 KiB')
        require(len(text.splitlines()) <= 1000, 'Challenge exceeds 1000 lines')
        imports = re.findall(r'^(?:public )?import\s+(\S+)', text, flags=re.M)
        require(all(name.startswith(('Mathlib.', 'Lean.', 'Init.', 'Std.')) or
                    name in {'Mathlib', 'Lean', 'Init', 'Std'} for name in imports),
                'Challenge has an import outside the intended core/mathlib boundary')
require(isinstance(config.get('theorem_names'), list) and bool(config['theorem_names']),
        'theorem_names must be nonempty')
for key in ['theorem_names', 'definition_names']:
    require(isinstance(config.get(key, []), list) and
            all(isinstance(x, str) and x for x in config.get(key, [])), f'invalid {key}')
require(isinstance(config.get('permitted_axioms'), list) and
        set(config['permitted_axioms']) <= AXIOMS, 'unsupported permitted axiom')
metadata = ROOT/'formalization.yaml'
require(metadata.is_file(), 'formalization.yaml is required')
if metadata.exists() and re.search(r'PENDING|TODO|REPLACE_ME', metadata.read_text()):
    if args.release:
        errors.append('human identity or other metadata placeholders remain')
    else:
        notes.append('metadata contains placeholders: --release will reject until completed')
for note in notes:
    print('NOTE:', note)
for error in errors:
    print('ERROR:', error, file=sys.stderr)
print(f'Preflight: {len(files)} source/package files, {len(seen)} pinned Git dependencies; '
      f'{len(errors)} error(s).')
raise SystemExit(bool(errors))
