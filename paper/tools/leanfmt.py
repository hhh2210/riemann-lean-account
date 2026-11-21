"""Typeset a Lean identifier or a path for a table cell: typewriter, with line breaks allowed
before each capital letter and after `.`, `/`, `_` and `:`, so that long names wrap."""
import re

_SPECIAL = {"_": r"\_", "#": r"\#", "%": r"\%", "&": r"\&", "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}",
            "^": r"\textasciicircum{}", "\\": r"\textbackslash{}", "$": r"\$",
            "₂": r"\textsubscript{2}", "₁": r"\textsubscript{1}", "…": r"\ldots{}", "'": "'"}


def leanb(text: str) -> str:
    out = []
    prev = ""
    for ch in text:
        if prev and (ch.isupper() and (prev.islower() or prev.isdigit())):
            out.append(r"\allowbreak{}")
        out.append(_SPECIAL.get(ch, ch))
        if ch in "./_:-":
            out.append(r"\allowbreak{}")
        prev = ch
    body = "".join(out)
    body = re.sub(r"[^\x00-\x7f]", "", body)  # anything else non-ASCII has no glyph in the font
    return r"\leanb{" + body + "}"
