---
title: "Draft Policy: Semantic Auditing"
status: draft
source: original
topics: [formalisation, review, semantic-audit, lean, research-program]
created: "2026-06-08T18:45:33"
updated: "2026-06-08T18:45:33"
---

# Draft policy: semantic auditing

This is a draft policy. The goal is to make the formal verification in this repo into a useful
mathematical artifact, not merely a collection of Lean files that compile.

Lean checks that a theorem follows from its definitions and hypotheses. It does not, by itself,
check that the definitions are the mathematical objects we intended, that the theorem is the
research-useful theorem, or that the API is shaped so later mathematics can be stated cleanly.
Semantic auditing is the process that checks those things.

The output is a parallel artifact:

- the Lean artifact: definitions, lemmas, theorems, proofs;
- the math-facing artifact: elementary statement cards, scope notes, dependency notes, and gap
  ledgers explaining what the Lean means and why it is the right object.

## Basic principle

Every important formal statement should answer three questions.

1. What exact mathematical statement does the Lean prove?
2. Is that statement the one the research programme needs, or only a nearby one?
3. Are the definitions and APIs carrying the right mathematical boundaries?

This is a semantic check, not only a proof check. A theorem can compile and still be the wrong
artifact: it may have a too-strong hypothesis, a vacuous antecedent, an accidental convention, a
missing non-vacuity witness, or an API that forces irrelevant structure into later results.

## Statement cards

The basic unit is a statement card. It should be written in elementary mathematical language, using
the style rules in [`writing-style.md`](writing-style.md). It should be precise enough that a human
reviewer can compare it against the Lean signature.

For a theorem, record:

```text
Lean name:
Exact informal statement:
Mathematical object being formalised:
Main hypotheses:
Conclusion:
Why this is useful:
What it does not say:
Non-vacuity witness or example:
Used by:
Known mismatch with intended paper statement:
```

For a definition, record:

```text
Lean name:
Intended meaning:
Actual formal content:
Canonical examples:
Canonical non-examples:
Is it too strong?
Is it too weak?
Does it include accidental structure?
Used by:
Known mismatch with intended paper object:
```

The existing policy [`statement-cards.md`](statement-cards.md) gives the traceability format for
claim-to-Lean cards. This draft policy adds the semantic questions those cards should answer when
the object is mathematically load-bearing.

## Bottom-up audit

Start from the leaves of the Lean dependency forest. For each file, identify the main exported
definitions and theorems. Produce statement cards for the objects that later files rely on.

The bottom-up pass should not only translate Lean into prose. It should test the local mathematical
meaning of each object:

- Are the hypotheses natural?
- Is the theorem non-vacuous?
- Does the theorem prove what its name suggests?
- Is the definition too specific?
- Is the definition too general?
- Does the API include a convention that belongs somewhere else?
- Does later code use the result for exactly the purpose the card records?

The RLCT-vs-codimension boundary is the model example. One can prove `codim mult⁻¹(B) = C` and name
the result `rlct_eq`, and the theorem is true — but the object computed is the *codimension*, a purely
geometric quantity, while the identity `rlct = C/2` rests on a cited analytic bound (Aoyagi / Watanabe)
the Lean does not reprove. A semantic card makes the mismatch explicit:

```text
Intended: real log-canonical threshold of the square-Frobenius DLN loss.
Actual: codimension of the multiplication fibre mult⁻¹(B) (geometric only).
Consequence: "RLCT = C/2" holds only via the cited rlct ≤ ½·codim bound, not proved here.
```

## Dependency audit

For each important theorem, record conceptual dependencies, not only Lean imports. Examples:

```text
fixed target matrix B
square Frobenius loss
multiplication map mult
type-A quiver translation
Gabriel / interval-module decomposition
Ext(M,M) normal-slice codimension
orbit-closure partial order
cited rlct ≤ ½·codim bound (Aoyagi)
```

This makes hidden assumptions visible. It also makes it easier to see which assumptions are
mathematical content and which are API artifacts.

## Top-down audit

Separately write the desired research theorem in elementary terms, before matching it against the
Lean.

For this repo, examples of top-level targets include:

- the zero-product / rank-`r` locus should decompose as a finite union of quiver orbits;
- the codimension `C` and component count `θ` should follow from the `Ext` computation plus the
  orbit-closure order;
- `C` and `θ` should be invariant under arbitrary permutations of the dimension vector;
- the RLCT of the square-Frobenius loss should equal `C/2` (via the cited analytic bound).

Then compare each current Lean theorem against the desired statement:

```text
Desired theorem:
Current Lean theorem:
Difference:
Is the difference harmless, conservative, or serious?
Next fix:
```

This catches the case where the formalisation is correct locally but climbing toward the wrong
global statement.

## API audit

The API audit checks whether definitions are shaped around the right mathematical boundaries.

Ask:

- Does this abstraction make the next theorem easier to state?
- Does it force irrelevant hypotheses into later results?
- Are two files formalising the same object in different ways?
- Is a definition bundled with assumptions that should be separate?
- Is a hypothesis only present because an intermediate theorem targets an overly strong object?
- Should a repeated pattern be abstracted, or is it better kept concrete for now?

The output is not always a refactor request. Sometimes the right answer is to document a conservative
condition and name the sharper successor. The important point is that the mismatch is visible.

## Non-vacuity rule

Every major hypothesis should have a formal or documented non-vacuity witness.

If a theorem says "under condition H, conclusion C holds", then the audit should ask for at least
one example where H holds, unless H is obviously inhabited from the surrounding mathematics. For
important results, prefer a Lean witness. Documentation-only witnesses are acceptable for early
drafts, but they should be marked as such.

This prevents impressive-looking theorems whose assumptions are impossible, irrelevant, or never
shown to occur in the intended setting.

## Agent roles

Do not rely on one agent to both explain and bless a statement. Use separate roles where possible.

- Extractor: turns Lean definitions and theorem signatures into elementary statement cards.
- Skeptic: looks for vacuity, too-strong hypotheses, hidden assumptions, accidental conventions,
  and wrong-object statements.
- Programme reviewer: checks whether the theorem matters for the research direction.
- API reviewer: checks whether definitions are modular and future-proof enough for the next layer.
- Formaliser: turns accepted fixes back into Lean.

The skeptic should not simply trust the extractor's interpretation. The point is independent
semantic pressure.

## Gap ledger

Maintain a living ledger for important mismatches:

```text
Intended result:
Current formal result:
Gap:
Severity:
Conservative or unsound:
Proposed repair:
Owner or next expedition:
Status:
```

Use plain severity labels:

- low: harmless mismatch or documentation cleanup;
- medium: theorem is useful but meaningfully weaker, stronger, or less general than intended;
- high: theorem can be misread as proving a research claim it does not prove;
- blocker: later work would rest on the wrong statement.

The ledger should distinguish conservative over-strength from unsoundness. A too-strong hypothesis
may be acceptable if documented and if it still supports a useful next theorem. A wrong mathematical
object is not acceptable.

## Process shape

The full semantic audit has two directions.

Bottom-up:

```text
Lean dependency forest
  -> statement cards
  -> local semantic audit
  -> dependency audit
```

Top-down:

```text
research-goal cards
  -> desired theorem statements
  -> comparison against current Lean
  -> gap ledger and API repairs
```

The two passes meet at the gap ledger. The bottom-up pass says what has really been formalised. The
top-down pass says whether that formalisation serves the research programme.

## Completion standard

A semantic audit is complete for a layer when:

- the important Lean definitions and theorems have statement cards;
- the cards distinguish proved, assumed, cited, and deferred content;
- major hypotheses have non-vacuity witnesses or documented examples;
- conceptual dependencies are recorded;
- known mismatches with the intended mathematics are in the gap ledger;
- API concerns are either fixed, explicitly deferred, or documented as harmless;
- the top-level research relevance of the layer is stated in elementary terms.

This policy is expected to change. The first goal is not bureaucracy. The first goal is to make it
hard for the repo to contain a theorem that compiles, looks important, and is nevertheless not the
mathematics we care about.

---

## Appendix A — design discussion (2026-06-09), to revisit with fresh eyes

*Raw capture of a controller/operator discussion, appended for a later pass. Not yet integrated into
the policy body above; exploratory, and some of it is half-formed (the top-down side especially).
Provenance: this draft predates the Stage-5 re-audit that prompted the discussion — the simmering
worry is the **semantic–syntactic bridge**: Lean carries the syntactic/logical-correctness side, but
the conceptual/mathematical side is not yet covered.*

### Framing — AI comparative advantage; rising sea vs dependable bedrock

- The scale of semantic auditing should be **comparable to the scale of the formalisation effort
  itself** — not a light checklist. What makes that affordable: make each audit unit cheap, isolated,
  parallel, and cached, so comparable-scale *coverage* becomes affordable. Continuous with *fill the
  layer / completion is comparative advantage* (`bedrock.md`, `CLAUDE.md`): semantic auditing at full
  scale is that principle applied to the **conceptual** layer, not the proof layer.
- The scarce resource is taste / direction; the abundant resource is *intelligent attention to small
  details* (parallel, exhaustive, fresh). The design problem is an **AI-ergonomic** way to spend the
  abundant one to protect the scarce one.
- Caveat (operator): most of what follows is **dependable bedrock**, not the rising sea proper. The
  generative "magic" of the rising sea should NOT be prematurely frozen into a harness — codify it
  wrong and the rails point away from where the real moves happen. The harness targets only the
  bedrock-grade moves with **clear success criteria**: writing out basic properties, illustrative
  examples, stress-testing examples, generalisation, abstraction, specialisation. None requires the
  harness to have taste.
- Rising-sea note (parked, contested): the rising-sea *method* is breadth-bulk-heavy (build the
  ambient theory until the result falls out) and was historically labor-bottlenecked — exactly the
  bottleneck AI removes; Lean forces the whole sea to be real (no hand-waved "routine"). So AI's
  comparative advantage is plausibly strongest at the rising-sea *style*. [Operator: there is more to
  Grothendieck's magic than the labor profile — sidebar for another time.]

### What AI is structurally good at in the semantic layer
(each a thing humans ration and AI can saturate)
- **coverage / exhaustiveness**; **cheap decorrelation** (fresh readers on demand, no
  frame-attachment); **register-translation** (Lean <-> elementary prose <-> paper <-> research goal —
  the semantic-syntactic bridge *is* a translation problem); **uniform care** (no skipped "obvious"
  step — where holes hide); **constructive probing at volume** (witnesses / non-examples to test
  vacuity).

### The reframe — semantic auditing IS sea-raising, not QA bolted on
- Carding every object bottom-up (what it really says, elementary, with examples / non-examples /
  dependencies) *builds the elementary theory of the formalisation*. The forest is the ambient
  structure / bedrock the next result stands on. Catching overclaims is a *side effect* of genuinely
  building the ambient understanding.
- "Not in spikes" is the safety discipline matched to AI's failure mode: AI cheaply produces plausible
  *spikes* (impressive results hiding conceptual holes Lean can't see). Spending the abundant coverage
  to keep the rise level is what makes AI-built theory safe to build on. Advantage and risk are the
  same coin; the level rise does the conversion.
- Twist on the scarce side: exhaustive bottom-up construction lays out the terrain so taste operates
  cheaply (taste over a carded landscape beats taste over fog) and surfaces the next question. AI helps
  the scarce layer not by having taste but by **lowering the cost of exercising it**. The irreducibly
  human input shrinks toward one thing: the **direction the sea should rise**.

### Harness design (the concrete machine)
- **Substrate is mostly free.** Per-declaration name / signature / docstring / source / referenced
  declarations is what **doc-gen4** already extracts from the `Environment`. Piggyback rather than
  write a metaprogram from scratch. It yields the forest skeleton (nodes + dependency edges +
  docstrings to separate out).
- **Forest = Merkle DAG over the Lean dependency graph.** One card per declaration; node key = hash of
  (normalized signature + set of constants the proof term references + children hashes). Coarse enough
  that cosmetic proof tweaks don't over-invalidate, precise enough that real dependency changes
  propagate upward. Change a leaf -> only ancestors re-audit. Audit cost tracks *change*, not repo
  size. Persistent, cached, incremental — built upon over time.
- **Decorrelation cut: standards yes, claims no.** The bottom-up auditor gets the *policies* (bedrock,
  precision — how to audit) + the stripped Lean (signature + proof term; names KEPT but "names may lie,
  derive from the body") + its children's own reconstructed cards. It does NOT get the campaign
  synthesis, our docstrings, or our statement cards. The diff between its reconstruction and our
  narration IS the name=content / overclaim report (e.g. "weakest" falls out — the body never says it
  and the auditor was never told it). Frame capture is impossible by construction.
- **Bias audit OUTPUTS toward Lean-checkable artifacts, not prose** (the load-bearing insight — makes
  "audit = sea-raising" concrete and dissolves card-drift). Map the moves to outputs: basic properties
  -> formalized basic-property lemmas; examples / specialisation -> actual Lean terms at the simplest
  case; stress-tests -> constructed non-examples / boundary witnesses; non-vacuity -> a witness decl
  that typechecks. All build-checked -> self-maintaining (a drifted witness *breaks the build*; a
  drifted prose card merely lies). The prose card is a thin layer over a thick base of checkable
  artifacts, used only where judgment is irreducible (name-vs-content, conservative-vs-decorative,
  research-relevance). Consequence: the audit literally produces more Lean / raises the sea — that is
  the concrete sense in which "audit" and "theory-development" collapse into one activity.
- **Mechanical / agent boundary** (spend abundance, concentrate judgment). Pure metaprograms,
  forest-wide, cheap: unused-binder -> candidate-decorative; vacuous antecedent; bare-`Prop` fields;
  name-token flags (`rlct` / `eq` / `iff` / `weakest` / `general` / `complete`); does the claimed
  non-vacuity witness typecheck; do reverse-dependency edges match the card's "used by". Agents touch
  only the flagged residue + the irreducibly-semantic cards. Note the spectrum: *mechanical* catches
  fully-decorative (unused binder); *semantic* catches conservative-not-decorative (F1: the output-!=0
  WAS used, but only for an over-strong target — mechanical detection misses this).

### Bottom-up vs top-down
- Bottom-up (what's really proved) = abundant parallel attention: thousands of isolated, cached,
  decorrelated card tasks. Top-down (what the programme needs — research-goal cards) = scarce taste.
  They meet at the **gap ledger** (severity low / medium / high / blocker; conservative-vs-unsound
  distinguished). The asymmetry is the point: saturate bottom-up, reserve judgment for the ledger's
  flagged dozen.
- **Top-down is under-developed** (operator): the research-vision doc is living, judgment-laden, with
  unresolved communication issues — not assumed resolved. Top-down may be OK for API-design issues,
  though even there "we leave X unoptimised for future use" complicates it. Top-down might also be a
  way to *sharpen* vision (bottom-up reveals what you have; that sharpens what you want) — noted, not
  resolved.

### Open decisions (for the fresher-eyes return)
1. **Card store format** — structured store (queryable, diffable, machine-cross-checked against Lean)
   + readable projection, vs markdown cards mirroring modules. Lean toward structured, *because* the
   valuable parts are the Lean-checkable artifacts + cross-checks, with prose minimized.
2. **Agent granularity** — per-declaration (max isolation / decorrelation, thousands of tiny tasks) vs
   per natural cluster (a def + its immediate API lemmas). Likely: Merkle node per-declaration, but an
   agent cards a tight cluster per pass.
3. **Feedback routing (flagged load-bearing)** — audit team *advises*, controller decides, formaliser
   edits (the independent-taste-review precedent) — OR the audit team adds its own Lean (witnesses / basic-property
   lemmas) directly behind a green-gate. Since the audit's best outputs ARE Lean, this decision most
   shapes the two-team relationship.

### Two-team shape (process; roles deferred)
- A formalisation team (builds Lean + narration) and a separate, decorrelated **semantic-audit team**
  (consumes stripped Lean, builds the card forest bottom-up + the checkable artifacts, maintains the
  ledger). They meet at the ledger. Roles deliberately deferred — this was a process discussion.
