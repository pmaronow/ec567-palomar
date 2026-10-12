"""Reject placeholders and require real aggregate/private-audit module imports."""
import re
from pathlib import Path


def lean_code(text: str) -> str:
    """Remove nested comments and strings while preserving lines/token separation."""
    output, depth, string, index = [], 0, False, 0
    while index < len(text):
        char = text[index]
        if depth:
            if text.startswith('/-', index):
                depth += 1
                output.extend('  ')
                index += 2
            elif text.startswith('-/', index):
                depth -= 1
                output.extend('  ')
                index += 2
            else:
                output.append('\n' if char == '\n' else ' ')
                index += 1
        elif string:
            if char == '\\' and index + 1 < len(text):
                output.extend('  ')
                index += 2
            else:
                output.append('\n' if char == '\n' else ' ')
                string = char != '"'
                index += 1
        elif text.startswith('/-', index):
            depth = 1
            output.extend('  ')
            index += 2
        elif text.startswith('--', index):
            end = text.find('\n', index)
            end = len(text) if end < 0 else end
            output.extend(' ' * (end - index))
            index = end
        elif char == '"':
            string = True
            output.append(' ')
            index += 1
        else:
            output.append(char)
            index += 1
    return ''.join(output)


root = Path(__file__).resolve().parents[1]
files = [root / 'RankCertificates.lean', root / 'AxiomAudit.lean', root / 'EC567Solution.lean']
files += sorted((root / 'RankCertificates').rglob('*.lean'))
errors = []
aggregate = lean_code((root / 'RankCertificates.lean').read_text())
audit_source = lean_code((root / 'AxiomAudit.lean').read_text())
imports = set(re.findall(r"(?m)^public import (RankCertificates(?:\.[A-Za-z0-9_']+)+)\s*$", aggregate))
audit_imports = set(re.findall(r"(?m)^import all (RankCertificates(?:\.[A-Za-z0-9_']+)*)\s*$", audit_source))
if 'RankCertificates' not in audit_imports:
    errors.append('AxiomAudit.lean: missing direct import all of aggregate RankCertificates')
if not re.search(r'(?m)^import all EC567Solution\s*$', audit_source):
    errors.append('AxiomAudit.lean: missing direct private import of final EC567Solution')
for path in files:
    if path.is_symlink():
        errors.append(f'{path.relative_to(root)}: Lean source is a symbolic link')
    if path.parent != root:
        module = '.'.join(path.relative_to(root).with_suffix('').parts)
        if module not in imports:
            errors.append(f'{path.relative_to(root)}: missing public aggregate import')
        if module not in audit_imports:
            errors.append(f'{path.relative_to(root)}: missing direct import all in private-declaration audit')
    text = path.read_text()
    source = lean_code(text)
    if not source.lstrip().startswith('module'):
        errors.append(f'{path.relative_to(root)}: missing module command')
    if len(text.splitlines()) > 10000:
        errors.append(f'{path.relative_to(root)}: exceeds 10000 physical lines')
    for forbidden in [r'\bsorry\b', r'\badmit\b', r'\bsorryAx\b', r'\bnative_decide\b',
                      r'Lean\.ofReduceBool', r'(?m)^\s*(?:private\s+|public\s+)?axiom\s',
                      r'debug\.skipKernelTC']:
        if re.search(forbidden, source):
            errors.append(f'{path.relative_to(root)}: forbidden pattern {forbidden}')
challenge = root / 'EC567Challenge.lean'
if challenge.is_symlink():
    errors.append('EC567Challenge.lean: source is a symbolic link')
challenge_text = challenge.read_text()
challenge_code = lean_code(challenge_text)
if not challenge_code.lstrip().startswith('module'):
    errors.append('EC567Challenge.lean: missing module command')
if len(challenge_text.splitlines()) > 1000 or len(challenge_text.encode()) > 100 * 1024:
    errors.append('EC567Challenge.lean: exceeds Palomar statement size limit')
challenge_imports = re.findall(r'(?m)^(?:public\s+)?import\s+(\S+)', challenge_code)
if not challenge_imports or any(not name.startswith('Mathlib.') for name in challenge_imports):
    errors.append('EC567Challenge.lean: imports outside the Mathlib statement closure')
if len(re.findall(r'\bsorry\b', challenge_code)) != 1:
    errors.append('EC567Challenge.lean: expected exactly one deliberate selected-theorem hole')
selected = 'infiniteGeometricClasses_exactRanksFiveThroughSeven'
signature = r'theorem\s+' + selected + r'\s*\n\s*\(hGTZ : ConditionalPrimePatterns\.FiniteComplexityPrimeAsymptotic\)\s*:\s*\n\s*RanksFiveThroughSeven'
for path in [challenge, root / 'EC567Solution.lean']:
    if not re.search(signature, lean_code(path.read_text())):
        errors.append(f'{path.name}: selected conditional theorem signature is missing')
for forbidden in [r'\badmit\b', r'\bnative_decide\b', r'Lean\.ofReduceBool',
                  r'(?m)^\s*(?:private\s+|public\s+)?axiom\s', r'debug\.skipKernelTC']:
    if re.search(forbidden, challenge_code):
        errors.append(f'EC567Challenge.lean: forbidden pattern {forbidden}')
known = {path.relative_to(root) for path in files + [challenge]}
for path in root.rglob('*.lean'):
    relative = path.relative_to(root)
    if any(part in {'.git', '.lake'} for part in relative.parts):
        continue
    if relative not in known:
        errors.append(f'{relative}: unexpected Lean source outside the audited submission profile')
if errors:
    raise SystemExit('\n'.join(errors))
print(f'Source audit passed: {len(files)} proof/audit files without placeholders, plus one independent Mathlib-only Challenge with its selected statement hole; complete aggregate/private imports and module/size rules.')
