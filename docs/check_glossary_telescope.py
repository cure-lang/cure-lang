#!/usr/bin/env python3
"""Guard that docs/GLOSSARY.md stays *telescope-sorted*.

A glossary is telescope-sorted when every definition uses only terms defined
*above* it — read top to bottom and you never meet a word you haven't seen. This
script lints that invariant over the definition prose and flags any entry whose
text references a headword defined *later* in the file.

It is a heuristic lint, on purpose:

  * Fenced ``` code blocks (the worked examples) are skipped — examples are
    illustrative, and the ordering guarantee is about the definition prose.
  * `inline code` spans are stripped before matching.
  * STOPLIST holds headwords that are also ordinary English words ("type",
    "match", "scope", …); they appear constantly as plain prose, so treating
    every occurrence as a cross-reference would drown real findings. Tune it if
    a genuinely distinctive term gets a false positive.

So it will not catch a forward reference made purely through a stoplisted common
word, and it does not police example code — but it does catch ordering rot for
the distinctive vocabulary (telescope, elaboration, metavariable, normalization,
propositional, canonicity, …), which is exactly where reordering mistakes hide.

Usage:  python3 docs/check_glossary_telescope.py
Exit 0 if clean, 1 if any forward reference is found.
"""

import pathlib
import re
import sys

GLOSSARY = pathlib.Path(__file__).with_name("GLOSSARY.md")

# Headwords that are also common English words — excluded from being treated as
# references. Kept lowercase. This is the one knob you tune.
STOPLIST = {
    "type", "kind", "sort", "value", "family", "match", "scope", "hole",
    "instance", "witness", "check", "spine", "context", "universe", "coverage",
    "reduction", "conversion", "coercion", "application", "binder", "proof",
    "total", "opaque", "primitive", "decidable", "pattern", "index", "proposition",
    "abstraction", "successor", "zero", "neutral", "reify", "record", "process",
    "message", "effect", "spawn", "kernel", "opaque", "constructor", "scrutinee",
    "exhaustiveness", "termination", "positivity", "canonicity", "list", "map",
    "set", "show", "combine",
}

# Minimum length for a bare name to be considered (kills stray one/two letter
# matches). Distinctive short terms are allow-listed back in SHORT_KEEP.
MIN_LEN = 4
SHORT_KEEP = {"pi", "fin", "nat", "eta", "uip", "whnf", "gadt", "iota", "beta",
              "zeta", "refl", "ctor", "qtt"}

HEADWORD_RE = re.compile(r"^\*\*(?P<title>[^*].*?)\*\*(?P<rest>.*)$")
BOLD_RE = re.compile(r"\*\*(.+?)\*\*")
INLINE_CODE_RE = re.compile(r"`[^`]*`")
EM_DASH = "—"


def is_headword(line: str):
    """Return the raw headword segment (text before the em dash) or None."""
    m = HEADWORD_RE.match(line)
    if not m:
        return None
    # A definition line has an em dash separating headword from gloss.
    if EM_DASH not in line:
        return None
    # Everything up to the first em dash is the headword region (may hold
    # several bold aliases and italic "(also **x**)" notes).
    return line.split(EM_DASH, 1)[0]


def names_from(headword_region: str):
    """All lowercase names a headword introduces (split slash-separated forms)."""
    names = set()
    for bold in BOLD_RE.findall(headword_region):
        for part in bold.split("/"):
            n = part.strip().lower()
            n = n.strip(" .:,")
            if n:
                names.add(n)
    return names


def keep(name: str):
    if name in STOPLIST:
        return False
    if name in SHORT_KEEP:
        return True
    return len(name) >= MIN_LEN


def parse_entries(lines):
    """Yield entries as dicts: {idx, names, prose, line_no}. Skips code fences."""
    entries = []
    in_fence = False
    cur = None
    for lineno, raw in enumerate(lines, 1):
        stripped = raw.lstrip()
        if stripped.startswith("```"):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        head = None if in_fence else is_headword(raw)
        if head is not None:
            if cur is not None:
                entries.append(cur)
            cur = {"idx": len(entries), "names": names_from(head),
                   "prose": [], "line_no": lineno}
        elif cur is not None:
            cur["prose"].append(INLINE_CODE_RE.sub(" ", raw))
    if cur is not None:
        entries.append(cur)
    return entries


def main():
    if not GLOSSARY.exists():
        print(f"error: {GLOSSARY} not found", file=sys.stderr)
        return 2
    lines = GLOSSARY.read_text(encoding="utf-8").splitlines()
    entries = parse_entries(lines)

    # name -> earliest entry index that defines it
    defined_at = {}
    for e in entries:
        for n in e["names"]:
            defined_at.setdefault(n, e["idx"])

    # Build match patterns for every keepable name.
    patterns = {}
    for name, idx in defined_at.items():
        if keep(name):
            patterns[name] = (idx, re.compile(r"(?<![a-z0-9_])" +
                                              re.escape(name) + r"(?![a-z0-9_])"))

    findings = []
    for e in entries:
        text = " ".join(e["prose"]).lower()
        for name, (def_idx, pat) in patterns.items():
            if name in e["names"]:
                continue  # self-reference
            if def_idx > e["idx"] and pat.search(text):
                used = sorted(e["names"])[0] if e["names"] else "?"
                findings.append((e["line_no"], used, name, def_idx))

    if not findings:
        print(f"OK — {len(entries)} entries, telescope order holds "
              f"({len(patterns)} distinctive terms checked).")
        return 0

    print(f"FORWARD REFERENCES ({len(findings)}):\n")
    for line_no, used, name, def_idx in sorted(findings):
        def_line = entries[def_idx]["line_no"]
        print(f"  line {line_no}: entry '{used}' references '{name}', "
              f"which isn't defined until line {def_line}")
    print("\nEither move the referenced term earlier, reword to avoid it, or — "
          "if it is genuinely common English — add it to STOPLIST.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
