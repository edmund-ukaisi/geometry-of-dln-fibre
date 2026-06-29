# Library-building — growing a foundation to Mathlib-grade

*The operational discipline for the disposition's "build the buildable": when to build a
well-established-maths library rather than cite, how to shape it for reuse, and when to extract it. The
**why** lives in [`../../CLAUDE.md`](../../CLAUDE.md) § Disposition and
[`../../.agent-team/roles/controller.md`](../../.agent-team/roles/controller.md); the standard it must meet
is [`bedrock.md`](bedrock.md).*

## The build-vs-cite test

Before citing an external result as an interface, ask — and answer in writing on the card:

1. **Is it well-established?** Standard textbook / monograph material, not a research frontier.
2. **Is its proof detail-at-scale, or a monument?** Patient and decomposable, no single deep insight that
   is itself a research achievement (resolution of singularities; the deep analytic SLT core) → *monument,
   cite it*. Otherwise → *buildable*.
3. **Does Mathlib already have it?** Verify by grepping `.lake/packages/mathlib` — do not guess from memory.
   Distinguish exists-and-reusable / exists-but-wrong-shape / absent.
4. **Is it reused?** A foundation many results tag to earns a clean general library; a one-off can stay
   local (still named honestly).

Buildable + absent-or-wrong-shape + reused ⟹ **build it** as a Mathlib-grade library. Monument ⟹ **cite it**
as a thin named interface — never fold the citation into a theorem name ([`precision.md`](precision.md)).

The discriminator is **detail-at-scale vs monument**, never *in-Mathlib-vs-not*: that Mathlib lacks a
standard result is the opening, not a risk. The failure mode is **timidity disguised as rigor** ("not in
Mathlib, therefore risky"). The guardrail keeps boldness informed — still cite the genuine monuments.

## Mathlib-grade API discipline

Held to [`bedrock.md`](bedrock.md) § Form, sharpened for *reuse* — and to **upstream-grade quality** (built
to the standard Mathlib would accept, even when we are not running the upstream PR process now):

- **General statements** — the natural generality the maths supports (general field / `Type u`), not the
  narrowing the first call site happened to need.
- **Searchable names** — Mathlib naming conventions; name = content.
- **Minimal hypotheses** — carry the weakest that suffice; drop the decorative.
- **Docstring hygiene** — every public declaration documented to Mathlib standard.
- **`iff` characterizations** and usable API over incidence-only or easiest-to-prove forms.
- **Generality is a completion move** — generalising the bespoke form surfaces the holes it hid
  (fill-the-layer, [`bedrock.md`](bedrock.md)); it is *do*, not defer.

## Build the foundation, then the interface — and whether to build a foundation at all

**(1) Foundation library, or keep it local?** Depends on *how well-established the mathematics is* and *how
bespoke the in-context need is*:

- *well-established and reusable beyond the immediate call site* → **build it as a clean general
  foundation** — the foundation is the deliverable, finalised first (green, axiom-clean, upstream-grade); the
  in-context theorems then **tag to it** (the interface). The default for a genuine foundation.
- *bespoke / narrow to the current proof* → keep it local, prove it where used, don't over-generalise
  (YAGNI). Name it honestly either way ([`precision.md`](precision.md)).

The more established and less bespoke, the stronger the pull to a foundation; the tie-breaker for the
in-between is reuse — does anything beyond this one theorem tag to it?

**(2) Producing the core — fresh vs generalise-existing** (a tactic *within* building the foundation, set by
whether a clean version already exists):

- *none exists* → **build fresh** in the clean namespace.
- *a clean bespoke version already exists* → **generalise and re-home it** (strip the context-specific
  narrowing — field, dimension, indexing), rather than re-prove from scratch.

Either way the sequencing is foundation-first: finalise the general core, then retrofit the consumers to tag
to it, keeping the build green per step.

## Extraction / packaging trigger

CLAUDE.md's standing rule: *extract a `Core` library to its own package iff a second consumer appears.*
Factor general libraries into a namespace designed for that extraction from the start (mirror the Mathlib
target namespace, so the eventual lift is a file-move not a rewrite). When a second consumer is real (e.g. a
sibling repo), surface the package-extraction as a **knowing decision** for the operator — do not cut the
package silently.

## In-repo kin

[`bedrock.md`](bedrock.md) · [`precision.md`](precision.md) · [`expedition.md`](expedition.md). Disposition:
[`../../CLAUDE.md`](../../CLAUDE.md). Lean conventions: [`../../lean/CLAUDE.md`](../../lean/CLAUDE.md).
