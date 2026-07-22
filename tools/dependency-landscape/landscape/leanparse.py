"""Heuristic Lean 4 source scanner.

Extracts explicitly authored declaration commands, their namespaces, reference
tokens, and sorry counts from raw source text — no elaboration, no build. The
output is deliberately approximate ("source-resolved"): it is what a careful
reader could recover from the text alone, and the UI labels it as such.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field

DECL_KEYWORDS = (
    "theorem", "lemma", "def", "abbrev", "structure", "class", "inductive",
    "instance", "opaque", "axiom",
)

# kind → canonical display kind (index into KINDS)
KINDS = ["theorem", "definition", "type declaration", "instance", "opaque", "other"]
KIND_INDEX = {
    "theorem": 0, "lemma": 0,
    "def": 1, "abbrev": 1,
    "structure": 2, "inductive": 2, "class": 2, "class inductive": 2,
    "instance": 3,
    "opaque": 4,
    "axiom": 5,
}

_MODIFIERS = r"(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|scoped|local|public)\s+)*"
_ATTRS = r"(?:@\[[^\]\n]*\]\s*)*"
_IDENT = r"[A-Za-z_«][A-Za-z0-9_'!?«»]*(?:\.[A-Za-z0-9_'!?«»]+)*"

_DECL_RE = re.compile(
    rf"^[ \t]*{_ATTRS}{_MODIFIERS}"
    rf"(theorem|lemma|def|abbrev|structure|class inductive|class|inductive|instance|opaque|axiom)"
    rf"(?![A-Za-z0-9_'!?])[ \t]*(.*)$",
    re.M,
)
_NAME_RE = re.compile(rf"^(?:\(priority[^)]*\)\s*)?({_IDENT})")
_NAMESPACE_RE = re.compile(rf"^[ \t]*namespace\s+({_IDENT})", re.M)
_SECTION_RE = re.compile(rf"^[ \t]*(?:noncomputable\s+)?section(?:\s+({_IDENT}))?[ \t]*$", re.M)
_END_RE = re.compile(rf"^[ \t]*end(?:\s+({_IDENT}))?[ \t]*$", re.M)
_OPEN_RE = re.compile(rf"^[ \t]*open\s+(?:scoped\s+)?((?:{_IDENT}[ \t]*)+?)(?:\s+in\b|[ \t]*$)", re.M)
_IMPORT_RE = re.compile(rf"^import\s+({_IDENT})", re.M)
_TOKEN_RE = re.compile(_IDENT)
_SORRY_RE = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")

# Tokens that can never be project declaration references; skipping them keeps
# the per-declaration token sets (and resolution work) small.
_STOPWORDS = frozenset("""
by fun match with do let have show from exact intro intros apply refine rfl
simp rw omega ring norm_num decide constructor obtain rcases rintro cases
induction ext use exists calc conv unfold change generalize specialize
subst clear rename_i next all_goals any_goals first try repeat rotate_left
push_neg nlinarith linarith positivity gcongr aesop tauto trivial assumption
where deriving instance theorem lemma def abbrev structure class inductive
opaque axiom namespace section end open import set_option attribute variable
universe if then else at this fun Type Prop Sort Nat Int Real Bool True False
and or not exists forall mt of eq ne le lt ge gt add sub mul div neg inv
zero one bot top mem map comp id val prop cast coe mk fst snd left right
some none unit star h hs ht hx hy hz hn hi hj hk hd he hf hg hp hq hr
""".split())


@dataclass
class Decl:
    name: str           # fully qualified (namespace-resolved) source name
    kind: str           # raw keyword
    line: int           # 1-based line of the declaration command
    namespaces: tuple   # namespace stack at the declaration, outermost first
    opens: tuple        # cumulative `open` targets visible at the declaration
    sorry_count: int = 0
    tokens: frozenset = field(default_factory=frozenset)

    @property
    def kind_index(self) -> int:
        return KIND_INDEX.get(self.kind, 5)


@dataclass
class ParsedFile:
    imports: list
    decls: list
    sorry_count: int
    line_count: int


def strip_comments_and_strings(text: str) -> str:
    """Replace comments and string literals with spaces, preserving newlines."""
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "-" and i + 1 < n and text[i + 1] == "-":
            j = text.find("\n", i)
            j = n if j == -1 else j
            for k in range(i, j):
                out[k] = " "
            i = j
        elif c == "/" and i + 1 < n and text[i + 1] == "-":
            depth, j = 1, i + 2
            while j < n and depth:
                if text[j] == "/" and j + 1 < n and text[j + 1] == "-":
                    depth += 1
                    j += 2
                elif text[j] == "-" and j + 1 < n and text[j + 1] == "/":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            for k in range(i, j):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        elif c == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                elif text[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            for k in range(i, min(j, n)):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        else:
            i += 1
    return "".join(out)


def _structural_events(src: str):
    """Yield (offset, kind, payload) for namespace/section/end/open commands."""
    events = []
    for m in _NAMESPACE_RE.finditer(src):
        events.append((m.start(), "namespace", m.group(1)))
    for m in _SECTION_RE.finditer(src):
        events.append((m.start(), "section", m.group(1)))
    for m in _END_RE.finditer(src):
        events.append((m.start(), "end", m.group(1)))
    for m in _OPEN_RE.finditer(src):
        events.append((m.start(), "open", tuple(m.group(1).split())))
    events.sort()
    return events


def parse_lean_source(text: str) -> ParsedFile:
    src = strip_comments_and_strings(text)
    imports = [m.group(1) for m in _IMPORT_RE.finditer(src)]

    decl_matches = list(_DECL_RE.finditer(src))
    events = _structural_events(src)

    # Walk declarations and structural events in offset order, maintaining the
    # namespace/section stack and cumulative opens.
    stack = []   # entries: ("ns", parts_tuple) | ("section", name_or_None)
    opens = []
    line_of = _LineIndex(src)
    decls = []
    ei = 0
    raw = []  # (match, ns_stack_snapshot, opens_snapshot)
    for dm in decl_matches:
        while ei < len(events) and events[ei][0] < dm.start():
            _, ekind, payload = events[ei]
            ei += 1
            if ekind == "namespace":
                stack.append(("ns", tuple(payload.split("."))))
            elif ekind == "section":
                stack.append(("section", payload))
            elif ekind == "open":
                opens.extend(payload)
            elif ekind == "end":
                if payload is None:
                    if stack:
                        stack.pop()
                else:
                    # pop entries until we close the named namespace/section
                    parts = tuple(payload.split("."))
                    for idx in range(len(stack) - 1, -1, -1):
                        skind, sval = stack[idx]
                        if (skind == "ns" and sval[-len(parts):] == parts) or \
                           (skind == "section" and sval == payload):
                            del stack[idx:]
                            break
                    else:
                        if stack:
                            stack.pop()
        ns_parts = tuple(p for skind, sval in stack if skind == "ns" for p in sval)
        raw.append((dm, ns_parts, tuple(opens)))

    for i, (dm, ns_parts, decl_opens) in enumerate(raw):
        keyword = dm.group(1)
        rest = dm.group(2)
        nm = _NAME_RE.match(rest)
        line = line_of(dm.start())
        if nm and nm.group(1) not in ("this",):
            base = nm.group(1)
        elif keyword == "instance":
            base = f"inst✝{line}"
        else:
            continue  # anonymous non-instance (e.g. malformed match) — skip
        if base.startswith("_root_."):
            full = base[len("_root_."):]
        else:
            full = ".".join(ns_parts + (base,)) if ns_parts else base

        # body = everything after the declared name (same-line signature and
        # `:= …` included) up to the next declaration command
        body_start = dm.start(2) + (nm.end() if nm else 0)
        body_end = raw[i + 1][0].start() if i + 1 < len(raw) else len(src)
        body = src[body_start:body_end]
        tokens = frozenset(
            t for t in _TOKEN_RE.findall(body)
            if t not in _STOPWORDS and not t.isdigit() and (len(t) > 1 or "." in t)
        )
        decls.append(Decl(
            name=full, kind=keyword, line=line,
            namespaces=ns_parts, opens=decl_opens,
            sorry_count=len(_SORRY_RE.findall(body)),
            tokens=tokens if len(tokens) <= 600 else frozenset(sorted(tokens)[:600]),
        ))

    return ParsedFile(
        imports=imports,
        decls=decls,
        sorry_count=len(_SORRY_RE.findall(src)),
        line_count=src.count("\n") + 1,
    )


class _LineIndex:
    def __init__(self, src: str):
        self._starts = [0]
        for i, c in enumerate(src):
            if c == "\n":
                self._starts.append(i + 1)

    def __call__(self, offset: int) -> int:
        import bisect
        return bisect.bisect_right(self._starts, offset)


def module_name_from_path(path: str, lean_root: str) -> str:
    """lean/DLNFibre/Core/Foo.lean → DLNFibre.Core.Foo"""
    rel = path[len(lean_root):].lstrip("/")
    return rel[:-len(".lean")].replace("/", ".")
