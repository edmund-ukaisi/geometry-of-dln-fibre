# Claims

A **claim** is a precise mathematical statement under investigation, with named
hypotheses and an explicit **kill-condition** — the observation or counterexample
that would refute it. Claims are produced and sharpened inside **explore** threads
and, once stable, formalised by **formalisation (tide)** threads.

## A claim card carries

- **Statement** — precise; hypotheses named. Name what is *proved* vs *assumed* vs *deferred*, not the impressive reading ([`precision.md`](precision.md)).
- **Kill-condition** — the specific case or observation that would refute it, stated *before* hunting confirming examples.
- **Status** — `open` / `stress-tested` / `survived` / `refined` / `refuted` (new tier); `verified` (established tier).
- **Tier** — `new` (ours) or `established` (published, or already proved in a cited source).
- **Evidence** — computations or sources supporting it; link to the explore thread.

## Two-tier discipline

- **New claims** (our framing, our lemmas) get a **full stress-test**: hunt
  counterexamples against the kill-condition — degenerate cases, edge cases,
  boundary/closure issues — before any tide. Reach `survived` or `refined` first.
- **Established claims** (a lemma a cited paper already proves) get a **light
  step**: verify the statement against the primary source and transcribe it
  faithfully, then go straight to a tide. The source carries the burden, so skip
  the counterexample hunt.

**Tide-eligible:** a new claim at `survived` or `refined`; an established claim at `verified`.

The universal non-skippable gate is the formalisation **AUDIT**: for either tier,
the Lean statement must match the claim (fidelity). A light path to the tide does
not weaken the AUDIT.

## Kill-conditions

State the kill-condition before looking for confirming examples — the guard
against confirmation bias. An explore thread that only accumulates supporting cases
has not tested the claim. A claim with no statable kill-condition is too vague to
formalise.

## Refuted claims stay

A refuted or refined claim keeps its card with the refuting case recorded. It is
the trail: the next iteration reads it rather than re-deriving the dead end.
