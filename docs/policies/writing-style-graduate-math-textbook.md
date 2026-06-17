# Writing style: graduate math textbook

This policy governs expositions that we are developing as graduate-level
mathematics notes. The target reader is a general mathematics graduate
student: mathematically mature, but not assumed to know the paper's particular
mix of quiver representations, algebraic geometry, singular learning theory,
and deep linear networks.

The voice is a hybrid of graduate textbook and lecture notes: polished enough
to stand alone, patient enough to teach, and direct enough to preserve the
shape of the argument.

## Purpose

The point of an exposition is to make a mathematical object, theorem, or proof
usable by a reader who did not participate in our discussion.

The priorities are:

1. **Correct.** Claims state exactly what is known, under the hypotheses where
   it is known. Caveats appear next to the claims they qualify.
2. **Elementary.** The exposition builds from precise simple objects introduced
   locally in the document.
3. **Structured.** The reader can see the main line first and open details on
   demand.
4. **Memorable.** Examples, diagrams, and repeated motifs make the abstraction
   stick.
5. **Concise.** Brevity matters only after the preceding four conditions are met.

Never trade correctness for elegance, or elegance for brevity.

## Elementary, Precisely

"Elementary" does not mean informal, vague, or simplified past the point of
truth. It means:

- introduce the objects before using them;
- state the local hypotheses before invoking a result;
- prefer a sequence of small exact statements to one dense compressed one;
- use notation only after assigning it a meaning;
- avoid relying on background the reader has not been given in the document;
- use analogies only when they are exact enough to carry mathematical weight.

For example, do not write that "a tuple is a quiver representation" and move
on. First name the quiver, the vector spaces, and the maps:

$$
V_0 \xrightarrow{A_1} V_1 \xrightarrow{A_2} \cdots
\xrightarrow{A_N} V_N.
$$

Then say that this chain is a representation of the equioriented type-A
quiver.

## Reader Model

Assume the reader knows standard graduate linear algebra and has seen basic
abstract algebra. Do not assume familiarity with:

- Dynkin quivers or Gabriel's theorem;
- algebraic group actions and orbit stratifications;
- Ext groups as normal slices;
- equivariant cohomology;
- real log-canonical thresholds;
- singular learning theory.

These topics may be used, but each needs either a local definition, a
conceptual reminder, or a collapsible background note.

Judge prerequisites from the position of a fresh reader who opened this
exposition without the rest of the repo context. The reader is not clueless:
they are choosing to read this mathematical section, and they can follow
graduate-level prose. But bespoke notation, conventions, or constructions
introduced elsewhere in the repo should be recapped before use.

Use a visible prerequisites box only when it helps. Often a short local recap
in the opening paragraphs is better than a formal prerequisite list.

## Voice

Use academic "we":

```markdown
We now encode the tuple as a representation of a quiver.
```

Use it to guide the reader through the construction, not to narrate our work
process. Prefer object-level statements:

```markdown
The condition $A_N\cdots A_1=0$ is the condition that the longest composition
has rank zero.
```

Avoid meta-selling:

```markdown
Importantly, this amazing observation unlocks the entire story.
```

Write instead:

```markdown
This observation reduces the geometric question to a finite orbit
combinatorics problem.
```

## Register

The target is a classical graduate mathematics text — Arnold's expository books
are the model: object-level, direct, and motivated by the mathematics itself.
State the object, the claim, and the geometry that makes the claim true, and let
those carry the reader. Motivation comes from *what the mathematics is*, not from
rhetoric about the reader or about the exposition.

This is not the register of popular-mathematics writing. Do not narrate the
exposition ("the road is short", "we now observe that…"), address the reader's
supposed level ("the answer every schoolchild knows", "recall from your first
course"), or substitute a metaphor for the mathematics ("coordinates are a
distraction", "the machine that counts them"). A leading rhetorical question
("What is the simplest chain?") is scaffolding — cut it and state the answer.
Vividness is earned by an exact picture or a sharp example, not by tone.

## Structure Of An Exposition

A typical file should have:

1. A framing paragraph: what object we study and why.
2. A short story list for longer notes: the main moves.
3. Definitions and notation before theorem statements.
4. A small running example.
5. Main claims with proof sketches.
6. Full derivations or background in collapsibles.
7. Cross-references to source paper sections, related exposition files, and
   formal artifacts if they exist.

One file should have one main topic, and expositions should be mostly
standalone. A reader should be able to open a file directly and understand its
local object, notation, and goal without first reading a linear sequence of
previous chapters. Cross-links are for enrichment, alternate routes, and
follow-up detail, not for hiding prerequisites that the current exposition
needs.

If a section starts becoming an independent lesson, split it into its own
exposition and cross-link. When a later exposition depends on a prior one,
include a short local recap before using the dependency.

Do not add end-of-note "what to remember" summaries by default. Use a closing
paragraph only when the exposition genuinely needs to hand the reader to the
next object or related note.

## Main Line And Details

The top-level prose carries the reader's attention. It should answer:

- What is the object?
- What is the claim?
- Why should the claim be true?
- Where does the proof use real input?
- What example should the reader keep in mind?

Put the following one layer down in collapsibles:

- index-heavy computations;
- proof details after a proof sketch;
- optional background;
- alternative formulations;
- sanity checks;
- edge cases;
- historical or bibliographic side notes.

Inline proof sketches should be short enough that a reader can keep the main
argument in working memory. When a proof wants several pages of bookkeeping,
write the conceptual proof inline and put the bookkeeping in a collapsible.

## Definitions

Definitions should be explicit and local. A good definition block usually has:

- the ambient objects;
- the formal condition;
- the notation introduced;
- one sentence saying what the definition is meant to capture.

Example:

```markdown
!!! definition "Rank pattern"
    Let $\underline d=(d_0,\ldots,d_N)$ and let
    $A_i:k^{d_{i-1}}\to k^{d_i}$. The rank pattern of $A_\ast$ is the
    upper-triangular array

    $$
    r_{ij}=\operatorname{rank}(A_jA_{j-1}\cdots A_{i+1})
    \qquad 0\leq i\leq j\leq N,
    $$

    with $r_{ii}=d_i$. It records the ranks of all interval compositions.
```

Do not define by name alone. If the reader needs to know what a Kostant
partition is, give the array condition before relying on the term.

## Theorems And Claims

State claims in a form that makes their dependencies visible.

Good:

```markdown
!!! theorem "Permutation invariance of the top invariants"
    Fix $r$ and a dimension vector $\underline d$. The codimension $C$ and the
    number $\theta$ of top-dimensional irreducible components of
    $\overline{\Sigma}^r_{\underline d}$ depend only on the multiset
    $\{d_0,\ldots,d_N\}$.
```

Avoid:

```markdown
The answer is symmetric.
```

If the paper has a typo, ambiguity, or convention mismatch, put the correction
next to the statement where it matters.

When restating a theorem, lemma, proposition, or equation from the paper, use
the paper's numbering where possible and say that it is the paper's numbering:

```markdown
!!! theorem "Theorem 5.1 of the paper (QIP formula)"
    ...
```

If the exposition introduces an auxiliary local claim, use a descriptive title
instead of pretending it is part of the paper's numbered structure:

```markdown
!!! lemma "Local bookkeeping lemma"
    ...
```

This keeps source traceability visible while leaving room for exposition-level
claims that are not in the paper.

## Proof Style

Use this default pattern:

1. State the idea in one paragraph.
2. Give a proof sketch inline.
3. Put the full proof or technical computation in a collapsible.

Example:

```markdown
The proof has two moves. First, Gabriel's theorem replaces matrix tuples by
finitely many orbit types. Second, the rank-zero condition selects the orbit
types whose longest interval does not occur.

??? proof "Details"
    Full details here.
```

When a proof uses an advanced theorem, say what the theorem contributes in
this setting before invoking its name.

## Examples

Examples should do real work. Use small examples early and return to them.

Preferred running examples for this project:

- $(1,1,1)$: two scalar factors whose product is zero;
- $(2,2,2)$: the first reducible matrix example;
- $(2,3,2)$ and $(2,4,2)$: how changing the middle width changes components;
- constant width $(d,\ldots,d)$: asymptotic behavior and DLN intuition.

An example should usually include:

- the concrete matrices or dimensions;
- the geometric condition;
- the orbit/rank/lace interpretation;
- the value of $C$ and $\theta$ when relevant;
- a sanity check against the general formula.

Put long computations in collapsibles, but keep the conclusion visible.

## Exercises And Checkpoints

Use checkpoints when they help the reader test understanding before the next
abstraction.

Good checkpoint forms:

```markdown
!!! question "Checkpoint"
    For $\underline d=(1,1,1)$, identify the two irreducible components of
    $\Sigma^0_{\underline d}$.
```

```markdown
??? tip "Solution"
    The equation is $a_2a_1=0$, so either $a_1=0$ or $a_2=0$.
```

Do not overload the exposition with exercises. Use them where a reader's next
step genuinely depends on internalizing the current object.

## Footnotes And Collapsibles

Use footnotes for short attention-preserving asides. Use collapsibles for
substantial material.

Good footnote:

```markdown
The orbit closure order is entrywise comparison of rank patterns.[^rank-order]

[^rank-order]: This is special to equioriented type-A quivers.
```

Good collapsible:

```markdown
??? note "Why Ext appears as a normal slice"
    Background explanation.
```

Do not hide essential hypotheses in footnotes. If a hypothesis qualifies a
claim, keep it in the main sentence.

## Notation Discipline

Use the paper's notation when it is clear and useful. Introduce it explicitly:

- $\underline d=(d_0,\ldots,d_N)$ for the dimension vector;
- $\operatorname{Rep}_{\underline d}$ for the space of matrix tuples;
- $\operatorname{mult}$ for the multiplication map;
- $\Sigma^r_{\underline d}$ for product-rank strata;
- $C$ for top codimension;
- $\theta$ for the number of top-dimensional components.

If a notation is overloaded or likely to confuse the reader, say so once and
then use a consistent local convention.

Notation tables are optional. Add one only when the note is notation-heavy
enough that the table reduces real reader load.

## Source Traceability

Each substantial claim should be traceable to one of:

- a theorem, lemma, definition, or equation in the paper;
- a local derivation in the exposition;
- a computation shown in the document;
- a formal theorem, when we later add formalization;
- an explicit caveat saying the claim is conjectural or interpretive.

Use inline references when they help the reader locate the source of a claim:

```markdown
The orbit closure order is entrywise comparison of rank patterns
(Theorem 2.8 of the paper).
```

Do not cite every sentence. Once a paragraph or subsection is clearly working
through one source result, cite the result at the point where it first becomes
load-bearing. Use a final "Sources and cross-references" section for broader
pointers and related exposition files.

## Co-Discussion Mode

During interactive learning, do not dump the whole paper at once. Work in
small layers:

1. Identify the object currently under discussion.
2. Give the simplest nontrivial example.
3. State the local claim.
4. Ask whether to expand the proof, compute an example, or move on.

The exposition can accumulate details over time, but the discussion should
respect attention capacity. If a topic branches, park the branch in a note or
collapsible rather than forcing it into the current conversational thread.

## Things To Avoid

Avoid:

- compressed theorem-first exposition when the objects are still unfamiliar;
- analogies that are not mathematically exact;
- unexplained notation imported from the paper;
- proof details inline when they break the main line;
- vague evaluative prose such as "deep", "remarkable", or "natural" without
  saying what mathematical role the fact plays;
- citations as substitutes for explanation;
- narration about the exposition itself ("the road is short", "we now turn to",
  roadmap flourishes) — let the section headings do this work;
- condescension or appeals to the reader's level ("every schoolchild knows",
  "this is easy", "recall from undergrad");
- leading rhetorical questions used as scaffolding — state the answer instead;
- metaphors that stand in for the mathematics rather than an exact, load-bearing
  picture (a barcode drawn from the actual decomposition earns its place; "the
  machine that counts them" does not).

Use the paper as source material, but write the exposition as a teaching text.
