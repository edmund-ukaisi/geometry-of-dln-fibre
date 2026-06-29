# Brief — `dimension-stack` expedition

## Central question

> **Grow the foundational commutative-algebra / affine-geometry libraries the DLN programme built bespoke
> inside `DLNFibre.Core` into clean, general, Mathlib-grade reusable libraries — the affine dimension stack
> (catenary + integral-extension dimension invariance + the height↔dim codimension bridge) and the
> smoothness ⟹ regular-local-ring stack.**

This is the programme's **first Mathlib-foundation build**. The §§2–8 DLN geometry is done (PR #13, on
`dev`); the next value is hardening the *reusable engine* under it to Mathlib grade, so future results —
here and in the sibling neuroalgebraic/ReLU programme (the "second consumer" — its terrain is toric/AG of
fibres + singularities cashing out via SLT interfaces) — stand on it without re-opening it.

**Disposition: this is "build the buildable"** ([`../../CLAUDE.md`](../../CLAUDE.md) § Disposition;
[`../../docs/policies/library-building.md`](../../docs/policies/library-building.md)). These dimension facts
are well-established, detail-at-scale, and Mathlib-absent (grep-verified at `v4.29`) — so we build them, and
cite only the genuine monuments (the analytic SLT core stays Cited).

## Scope — two entries, one expedition

**Entry 1 — the affine dimension stack** (headline; field-general, `Tuple`-free):
- the **catenary equality** `height p + dim(R/p) = dim R` (Mathlib has only the `≤` inequality);
- **integral-extension dimension invariance** `ringKrullDim_eq_of_integral_injective`;
- the **height↔dim codimension bridge** (`varietyDim`, `height(vanishingIdeal Z) + varietyDim Z = card`).

**Entry 2 — smoothness ⟹ regular-local-ring** (sits on entry 1):
- smooth point ⟹ regular local ring; the étale local-dimension bridge; `height_eq_under_of_etale`;
- the generalisation win **`[IsAlgClosed] → [PerfectField]`**.

**Out of scope / cite.** Toric / monomial / polyhedral (not used here); real-AG semialgebraic; the analytic
SLT **monument** (`rlct = ½·codim` stays Cited). The orbit-geometry capstone, type-A Gabriel/`Ext`, and the
q-series library stay DLN-local (recon ladder entries 3–5 — fused to `Tuple`/box-moves; a later expedition).

## Execution discipline — foundation-first

Per [`../../docs/policies/library-building.md`](../../docs/policies/library-building.md):
- **Build the general core first** (the deliverable, in `DLNFibre.Core.Dimension.*`); then **retrofit** the
  DLN consumers to tag to it; keep the build green per rung. No bespoke dimension proof left un-retrofitted
  at close.
- **Tactic = generalise-and-re-home** (not build-fresh): the clean bespoke proofs already exist in `Core`;
  strip the context-specific narrowing (`RepCoord d`/`Tuple`, `Type 0`, `[IsAlgClosed]` where avoidable),
  rather than re-prove. Generalising surfaces holes — fill them.
- **Upstream-grade quality** — Mathlib naming, docstring hygiene, minimal hypotheses — built to the standard
  Mathlib would accept, but **not** running the upstream PR process now, and **not blocked** on it.
- **Namespace mirrors the Mathlib target** (`DLNFibre.Core.Dimension.*` ↔
  `Mathlib.RingTheory.KrullDimension.{Integral,Catenary}` / `Mathlib.AlgebraicGeometry.Codimension`) so an
  eventual package extraction is a file-move.

## The ladder

Rung 0 (gate) → entry-1 rungs R1–R4 → entry-2 rungs → retrofit + review. Rungs and VOI in
[`priorities.md`](priorities.md). **Probe-first**: rung 0 pins the extraction boundary before the full
ladder commits.

## Closing criteria

- Entry-1 + entry-2 libraries built to Mathlib grade in `DLNFibre.Core.Dimension.*`: general statements,
  minimal hypotheses, docstrings; green, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`;
  reviewed (fidelity + hardener + decorrelated Codex on the crux).
- DLN consumers retrofitted to tag to the general core (no duplicated bespoke dimension proofs); the build
  `dev`-mergeable green.
- name = content throughout; the `[IsAlgClosed] → [PerfectField]` generalisation landed where claimed.
- The disposition docs (this expedition's folded change: `library-building.md` + CLAUDE.md/controller.md
  bullets) integrated.
- Exposition + final synthesis; PR against `dev` (signal-and-wait; operator-gated).

## Provenance

Built on the `rlct-bridge` close (PR #13, merged to `dev` `65b6e729`). Library ladder from the
AG-foundations recon (scout, 2026-06-28) — summarised in [`priorities.md`](priorities.md). **Blind** to the
parallel `expedition/aoyagi-full` line (decorrelation), as before.
