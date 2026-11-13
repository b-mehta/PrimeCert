"""Catch docstrings that are not attached to a declaration.

Inserting a definition just above an existing one is easy to get wrong: the anchor is the `def`
line, but what sits immediately above it is the previous declaration's docstring, so new text lands
between that docstring and the thing it documents. Lean then reports `unexpected token '/--';
expected 'lemma'`, or silently attaches a docstring to the wrong declaration.

Two shapes are reported:
  stacked   a `-/` closing a `/--` docstring, with the next non-blank line opening another `/--`
  orphaned  a `/-- ... -/` whose next non-blank line is neither an attribute nor a declaration

Module docs `/-! ... -/` are not docstrings and are skipped. Usage: check_docstrings.py FILE...
Exit status is 1 if anything is reported, so it can gate a push.
"""

import re
import sys

DECL = re.compile(
    r"^\s*(@\[|public\b|private\b|protected\b|meta\b|noncomputable\b|partial\b|unsafe\b|scoped\b|"
    r"def\b|theorem\b|lemma\b|abbrev\b|instance\b|structure\b|class\b|inductive\b|opaque\b|"
    r"axiom\b|elab\b|macro\b|syntax\b|notation\b|declare_syntax_cat\b|initialize\b|example\b)"
)


def check(path):
    lines = open(path, encoding="utf-8").read().split("\n")
    bad = []
    i = 0
    while i < len(lines):
        # A docstring opens with /-- (not /-! and not /- ).
        if lines[i].lstrip().startswith("/--"):
            start = i
            # Find its close, allowing a single-line /-- ... -/.
            if lines[i].rstrip().endswith("-/") and len(lines[i].strip()) > 4:
                end = i
            else:
                end = i + 1
                while end < len(lines) and not lines[end].rstrip().endswith("-/"):
                    end += 1
            nxt = end + 1
            while nxt < len(lines) and not lines[nxt].strip():
                nxt += 1
            if nxt < len(lines):
                if lines[nxt].lstrip().startswith("/--"):
                    bad.append((start + 1, "stacked", "another docstring follows this one"))
                elif not DECL.match(lines[nxt]):
                    bad.append((start + 1, "orphaned", f"next line is: {lines[nxt].strip()[:60]}"))
            i = end + 1
        else:
            i += 1
    return bad


def main(argv):
    hits = 0
    for path in argv[1:]:
        for line, kind, why in check(path):
            print(f"{path}:{line}: {kind} docstring, {why}")
            hits += 1
    if hits:
        print(f"\n{hits} docstring(s) not attached to a declaration")
        return 1
    print("docstrings all attached")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
