#!/usr/bin/env python3
"""Guard proof trust mechanisms, independently of successful type-checking.

No termination overrides are allowed.
This scanner is a regression guard, not an Agda parser or consistency proof.
"""

from collections import Counter
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
LEGACY_OVERRIDES = {}
POSTULATE_BLOCKS = {
    "Core/Syntax.agda": 1,
    "Proof/Soundness.agda": 1,
}
SAFE_OPTIONS = {"--safe", "--without-K", "--guardedness"}
UNSAFE_PRAGMAS = {
    "TERMINATING",
    "NON_TERMINATING",
    "NO_TERMINATION_CHECK",
    "NO_POSITIVITY_CHECK",
    "NO_UNIVERSE_CHECK",
    "NO_COVERAGE_CHECK",
    "NO_CATCHALL",
    "POLARITY",
    "REWRITE",
}


def code_and_pragmas(source):
    """Mask strings and nested comments while retaining line positions."""
    chars = list(source)
    pragmas = []
    i = 0
    depth = 0
    quoted = False
    while i < len(source):
        if depth:
            if source.startswith("{-", i):
                chars[i : i + 2] = "  "
                depth += 1
                i += 2
            elif source.startswith("-}", i):
                chars[i : i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if chars[i] != "\n":
                    chars[i] = " "
                i += 1
        elif quoted:
            if source[i] == "\\" and i + 1 < len(source):
                chars[i : i + 2] = "  "
                i += 2
            else:
                quoted = source[i] != '"'
                if chars[i] != "\n":
                    chars[i] = " "
                i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            chars[i:end] = " " * (end - i)
            i = end
        elif source.startswith("{-#", i):
            end = source.find("#-}", i + 3)
            if end < 0:
                raise ValueError("unterminated pragma")
            pragmas.append((source.count("\n", 0, i) + 1, source[i + 3 : end].split()))
            end += 3
            chars[i:end] = ["\n" if c == "\n" else " " for c in source[i:end]]
            i = end
        elif source.startswith("{-", i):
            chars[i : i + 2] = "  "
            depth = 1
            i += 2
        elif source[i] == '"':
            chars[i] = " "
            quoted = True
            i += 1
        else:
            i += 1
    if depth or quoted:
        raise ValueError("unterminated comment or string")
    return "".join(chars), pragmas


def inspect_source(path, source):
    errors = []
    overrides = Counter()
    code, pragmas = code_and_pragmas(source)
    if "{!" in code or "!}" in code or re.search(r"(?<![\w?])\?(?![\w?])", code):
        errors.append(f"{path}: interactive hole or unsolved question-mark meta")
    blocks = len(re.findall(r"\bpostulate\b", code))
    if blocks != POSTULATE_BLOCKS.get(path, 0):
        errors.append(f"{path}: unreviewed postulate block count {blocks}")
    if re.search(r"\bprimitive\b", code):
        errors.append(f"{path}: unreviewed primitive declaration")
    for line, tokens in pragmas:
        if not tokens:
            continue
        kind = tokens[0]
        if kind in UNSAFE_PRAGMAS:
            overrides[kind] += 1
        if kind == "OPTIONS":
            unreviewed = set(tokens[1:]) - SAFE_OPTIONS
            if unreviewed:
                errors.append(f"{path}:{line}: unreviewed options {sorted(unreviewed)}")
    if overrides != LEGACY_OVERRIDES.get(path, Counter()):
        errors.append(f"{path}: changed check-bypass surface {dict(overrides)}")
    return errors


def proof_sources(root=ROOT):
    """Include generated fixtures and future source directories, not just Core/Proof."""
    return sorted(root.rglob("*.agda"))


def main():
    errors = []
    paths = proof_sources()
    seen = set()
    for path in paths:
        relative = path.relative_to(ROOT).as_posix()
        seen.add(relative)
        try:
            errors.extend(inspect_source(relative, path.read_text()))
        except ValueError as error:
            errors.append(f"{relative}: {error}")
    for missing in (LEGACY_OVERRIDES.keys() | POSTULATE_BLOCKS.keys()) - seen:
        errors.append(f"{missing}: reviewed trust-root file missing")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Proof hygiene OK: {len(paths)} modules; no new holes or check bypasses.")
    remaining = "; ".join(
        f"{path} ({sum(counts.values())})" for path, counts in LEGACY_OVERRIDES.items()
    )
    print(f"UNRESOLVED legacy bypasses: {remaining or 'none'}.")
    print("This guard does not establish satisfiability of theorem parameters.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
