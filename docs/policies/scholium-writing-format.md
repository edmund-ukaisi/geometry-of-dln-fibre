# Scholium writing format

This policy records how reader-facing markdown should be shaped for the
`scholium` viewer and comment apparatus. It is a formatting policy, not a
prose-style policy.

The working split is:

- the markdown body is clean exposition;
- anchored discussion lives in the neighboring `.data.yaml` sidecar;
- the viewer resolves comment anchors at render time.

## File pair

A document usually appears as a pair:

```text
expositions/example.md
expositions/example.data.yaml
```

The `.md` file contains frontmatter and the exposition body. The `.data.yaml`
file contains scholia: anchored comments, discussion threads, replies, links,
and imported-comment metadata. Do not hand-write comment markers into the
markdown body.

For non-markdown source files, scholium can store frontmatter in the sidecar.
For our expositions, put frontmatter directly in the markdown file.

## Frontmatter

Start exposition files with YAML frontmatter. Use enough metadata to make the
document searchable and refactorable.

```yaml
---
title: "Short Descriptive Title"
status: draft
source: original
topics: [quivers, linear-networks]
created: "2026-06-12T00:00:00"
updated: "2026-06-12T00:00:00"
---
```

Use scholium's status vocabulary:

- `scratch`: rough capture, not yet shaped as exposition;
- `draft`: coherent enough to read, still freely editable;
- `polished`: human-read and blessed; edit carefully;
- `archived`: retained for record, not actively maintained.

## Section Shape

Open with a short framing paragraph. For longer expositions, follow it with a
short "story" list:

```markdown
The story is short:

1. First move.
2. Second move.
3. Payoff.
```

Use ordinary headings for the main line:

```markdown
## 1. The Multiplication Map

## 2. Rank Patterns
```

For stable anchors, attach explicit ids with `attr_list`:

```markdown
## 2. Rank Patterns {: #rank-patterns}
```

Manual anchors are useful when comments, cross-references, or external notes
need to survive heading edits.

## Main Line And Collapsibles

Top-level prose should carry one clean reading line. Put derivations,
proof details, technical side conditions, and optional background in
collapsibles.

Collapsed by default:

```markdown
??? note "Why this condition is necessary"
    Explanation with **markdown**, lists, and $\TeX$.
```

Open by default:

```markdown
???+ proof "Proof details"
    The detailed proof goes here.
```

Non-collapsible callout:

```markdown
!!! warning "Convention"
    This convention is used throughout the note.
```

Prefer `???` / `???+` over raw `<details>` blocks. Scholium can render
`<details markdown="1">`, but the `???` syntax composes better inside lists
and has viewer styling.

## Theorem-Like Blocks

Scholium styles custom admonition types. Use them for textbook structure:

```markdown
!!! definition "Definition 2.1 (Rank Pattern)"
    A rank pattern is ...

!!! theorem "Theorem 3.4"
    Statement.

??? proof "Proof sketch"
    Proof sketch or full proof.

!!! example "Example 3.5"
    Worked example.
```

Supported useful types include `definition`, `theorem`, `lemma`,
`proposition`, `corollary`, `proof`, `example`, `remark`, `question`,
`note`, `info`, `tip`, `warning`, and `danger`.

Scholium does not auto-number theorem environments. If numbering matters,
write the number in the title and add a manual anchor:

```markdown
!!! theorem "Theorem 4.1 (Permutation Invariance)" {: #thm-permutation-invariance}
    ...
```

Then cross-reference with an ordinary link:

```markdown
See [Theorem 4.1](#thm-permutation-invariance).
```

## Mathematics

Write mathematical notation as TeX, never as code spans.

Inline math:

```markdown
The product rank is $r_{0N}$.
```

Display math:

```markdown
The multiplication map is

$$
\operatorname{mult}(A_1,\ldots,A_N)=A_N\cdots A_1.
$$

This map is equivariant.
```

For reliability, write display math as a block: blank line before and after,
with `$$` fences on their own lines. The renderer can handle some compact
forms, but block form is easier to read and harder to break when nested in
callouts.

Inside a `???` or `!!!` block, indent every line of the display:

```markdown
??? proof "Computation"
    We compute:

    $$
    C=\sum_i e_i^2.
    $$

    This gives the desired formula.
```

Use KaTeX-supported commands. Avoid unsupported TeX macros unless we define
a local convention and verify the viewer renders them.

## Code Blocks

Top-level fenced code blocks (triple backticks) render normally. Inside a `???`
or `!!!` callout, scholium does **not** parse a fenced code block: the fences
appear as literal backticks and the code spills out as prose. A language tag
(e.g. ` ```lean `) is not recognised and does not help.

Inside a callout, use an **indented code block** — indent the code four spaces
beyond the callout body (eight spaces from the margin), with a blank line before
and after:

```markdown
??? info "Formalised in Lean"

        def baseChange (P) (A) := ...
        instance : MulAction ... where ...

    A prose gloss follows, back at the four-space callout-body indent.
```

The indented block renders as monospace. This is the same family as the
display-math rule: a callout reparses its body as markdown, and code must be
handed to that reparse as an indented block, not a fence.

## Lists And Nested Callouts

Put a blank line before every list. Wrapped continuation lines of a list item
should be indented.

When placing a collapsible inside a list item, indent the marker one level
deeper than the list content and indent the body another four spaces:

```markdown
- **Main point.**

    ??? note "Unpacked"
        Details.

        - subpoint
        - subpoint
```

This indentation matters. With too little indentation, the marker may render
as literal text or the body may become a code block.

## Footnotes

Use footnotes for short asides that attach to one sentence:

```markdown
The rank condition is closed.[^rank-closed]

[^rank-closed]: It is cut out by minors.
```

Use collapsibles instead when the aside becomes a derivation, proof, or
paragraph-scale explanation.

## Tables, Task Lists, And Definition Lists

Scholium supports:

```markdown
| object | meaning |
|---|---|
| $\underline d$ | dimension vector |
| $C$ | codimension |
```

```markdown
- [ ] unresolved point
- [x] settled point
```

```markdown
Rank pattern
:   The upper-triangular array of ranks of all interval compositions.
```

Use tables sparingly in exposition; they are best for notation, examples, and
comparisons. Task lists are useful in planning notes, less useful in polished
textbook exposition.

## Wikilinks And Cross-References

Scholium resolves `[[wikilinks]]` by filename. Use them for vault-level links
when the target is another document:

```markdown
See [[rank-patterns-and-orbits]].
```

Use ordinary markdown links for section anchors:

```markdown
See [the QIP section](#qip).
```

## Images

Use ordinary markdown images with relative paths:

```markdown
![Lace diagram](images/lace-diagram.png)
```

Scholium rewrites relative image paths for the viewer. Supported sizing:

```markdown
![Small diagram](images/lace.png){: .fig-narrow }
![Fixed-width diagram](images/lace.png){: width=400 }
![Wide figure](images/lace.png){: .fig-wide }
![Inline icon](images/star.png){: .fig-inline }
```

Do not use inline `style="..."`; the sanitizer strips it. Use image classes
or width and height attributes.

## Comment Sidecars

A sidecar thread has this shape:

```yaml
threads:
  - id: c-a1b2c3d4
    kind: anchored
    status: open
    anchor: "phrase in the document"
    anchor_prefix: "text before "
    anchor_suffix: " text after"
    created_at: "2026-06-12T00:00:00"
    updated_at: "2026-06-12T00:00:00"
    posts:
      - id: p-1a2b3c4d
        author: edmund
        date: "2026-06-12T00:00:00"
        text: "Question or comment."
        labels: [addressed]
```

Thread kinds:

- `anchored`: tied to a text selection;
- `discussion`: not tied to a selection and shown as a document-level thread.

Thread statuses:

- `open`: unresolved;
- `resolved`: done.

Use `addressed` as a post label, not as a thread status. Scholium treats
status and labels differently; the UI owns resolving and reopening threads.
Codex may add tags or replies when useful, but the human reader normally
resolves comments in the viewer.

The body should not contain synthetic `<mark>` tags. Scholium computes
highlight marks from the sidecar.

## Table Of Contents

Do not write explicit `[TOC]` blocks in exposition files. Scholium should
provide the left-sidebar table of contents from markdown headings; a bespoke
TOC duplicates the viewer apparatus.

## Editing Discipline

Use scholium mainly as a read/comment viewer. Edit markdown files with normal
file tools. If collaborative editing becomes part of the active workflow, revise
this policy after testing the current viewer behavior.

When comments identify a problem, resolve them by changing the markdown body
and, when useful, adding a sidecar reply or label. Do not answer substantial
comments only in the sidecar if the result belongs in the exposition. The
human reader handles final resolve/reopen actions in the UI.
