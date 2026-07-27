# Gate-2 prototype brief — the corank-2 Encoding-I `hideal` (the go/no-go measurement)

**Role of this build (READ FIRST).** This is the **elder gate (i)** before the full Encoding-I fold fires
(compass §"THE COUPLED-B BUILD PHASE"). It is a **MEASUREMENT**, not the full build: does the paper's
one-line ideal argument (unimodular Schur-clearing `Q,P`, polynomial cofactors) render as a concrete
`Chart.hideal_fwd`/`hideal_bwd` **without a hidden Mathlib ideal-membership tax**? A green-enough prototype
→ the controller commits the general-`d` swap. A surprise (a Mathlib wall, a cast blow-up, a fidelity crack)
→ re-scope. **So the TAX REPORT is as important a deliverable as the green build** (see §6).

Operator go given 2026-07-24. The Lean BUILD is authorized for THIS unit only (the corank-2 prototype).

## 1. Target — a concrete corank-2 chart's dom-wide ideal identity, both directions

Build, sorry-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`), for a **genuinely corank-2**
DLN witness `d` (see §3), the two `Chart` fields (`Core/Aoyagi/ProductResolution.lean:112-116`):

- `hideal_fwd : RegionRepresents (fun i ↦ F i ∘ g) (monomialFam bexp) nbhd`   (`⟨(∏C)∘g⟩ ⊆ ⟨diag b⟩`)
- `hideal_bwd : RegionRepresents (monomialFam bexp) (fun i ↦ F i ∘ g) nbhd`   (`⟨diag b⟩ ⊆ ⟨(∏C)∘g⟩`)

where `F = coreGen d e` (the reduced-width layer-product family `(∏ₛ C⁽ˢ⁾)ᵢ`), `g` = the blow-up chart
map, `bexp` = the diagonal-monomial exponents the Schur-clearing produces, `nbhd` = an OPEN set with
`hdom_sub : dom ⊆ nbhd`. **DOM-WIDE**, coefficients **continuous on `nbhd`** — a `RegionRepresents`, NOT a
germ at 0. (`RegionRepresents G H V` = `∃ a, (∀ i j, ContinuousOn (a i j) V) ∧ ∀ u ∈ V, G i u = ∑ⱼ a i j u · H j u`.)

Packaging the full `Chart` (the other fields — `hg_analytic`/`hjac`/`hcover`/…) is NOT required for the gate;
`hideal_fwd`/`hideal_bwd` are the measured objects. Do state them at the real `Chart`-field types (real `F`,
real `g`, `monomialFam bexp`) so the tax is the true tax, not a toy's.

## 2. Start from — the `-PROTO` symbolic spine (already sorry-free + axiom-clean)

Base your worktree on **`expedition/aoyagi-engine-PROTO`** (has `Core/Aoyagi/Corank2Proto.lean`, commit
`05c35eb8a`). That module already proves, symbolically over a general comm ring `R`, corank-2 (clear one
pivot → 2×2 residual `Δ`):
- **§2 [QP]** `Q1_C1_Q2_eq_diag : Q1 · C1 · Q2 = diag1Delta` (the L-A matrix identity), `det_Q1 = det_Q2 = 1`
  (unipotent), `Q1inv_mul_Q1`/`Q2inv_mul_Q2`/`Q2_mul_Q2inv`/`reconstruct_C1` (polynomial inverses — NO
  rational inverse, NO degeneration).
- **§4 [I⇒][I⇐]** `regionRepresents_of_matrix_mul` (a matrix identity `M = A·N` over the ambient function
  ring, cofactors `A i j` continuous on `V`, ⟹ `RegionRepresents (flat M) (flat N) V`) + `regionRepresents_P_peeled`
  / `regionRepresents_peeled_P` (BOTH ideal directions for the abstract peeled forms).
- **§1 [g]** `chartG = sh ∘ blockBlowupMap`, `chartG_zero`, `continuous_chartG`, `analyticOnNhd_chartG`.

**The gate work = the bridge from these symbolic bricks to the concrete `Chart` fields:** instantiate the
symbolic ring `R` at the ambient function ring, the symbolic entries `c··/m··` at the pulled-back layer-
matrix entries `(∏C)ᵢⱼ ∘ g`, and `diag1Delta` at `monomialFam bexp`; carry the cofactor continuity on the
open `nbhd`; compose both `RegionRepresents` directions (guardrail 4). `regionRepresents_of_matrix_mul` is
the atom that turns the instantiated identity into the two fields.

Also reusable (trunk): `Core.SchurGauge`/`SchurRankZero`/`SchurProductFactor`/`ChartSchurConnect`,
`RingTheory.Determinantal.Schur`; `Core.Aoyagi.ConjResolution` (a PROVEN chart-with-`hideal` template —
mine it for the packaging idiom); `Core.Aoyagi.{BlockBlowup, PathAtoms, OriginBlowup}` (the blow-up atoms,
`jacDet_blockBlowupMap` etc.). Survey banked state before rebuilding anything (compass counsel).

## 3. The witness — genuinely corank-2 (not a shallow-instance confound)

Use the **smallest `d` whose minimiser step is genuinely corank-2** (a 2×2 residual `Δ` that is NOT
diagonal — real coupling). The `corank2-cert/` scripts + the render illustrate; `(3,3,4)` is the banked
coupled frontier (minAdm=8, coupled-ONLY — two coupled/equal divisors). Confirm the concrete `coreGen d e`
shape from the Lean `coreGen` def (grep it); pick the witness so the Schur clear leaves a genuinely coupled
`Δ`. **A diagonal/uncoupled `Δ` is the (2,2,2,2)-clean confound (compass F3) — it does NOT exercise the
gate.** Verify corank-2-genuine before building on it.

## 4. The four build guardrails (rev-render §8 — non-negotiable, each a known failure mode)

1. **`D_J`/`Δ` stays a genuine RUNNING COORDINATE BLOCK** — the residual is the actual next-layer coordinate
   block, never an arbitrary pulled-back residual ÷ pivot. (The divide-by-pivot substitution is the retired
   fold's bug class; Encoding-I has NO substitution.)
2. **No row-mix `b'_p ∤ b'_i`, no simultaneous non-triangular block op** — clear pivots ONE at a time
   (successive 1×1 clears); corank≥2 is the SAME step iterated, the coupling carried in `Δ`.
3. **Derive the `b`-exponents (`bexp`) from the `~t`-formula**, not an assumed chain — the `b`-chain is
   construction-automatic (each clear multiplies the run from `J+1`); it should reduce to one scalar exponent
   lemma, not a threaded hypothesis. The b-chain is LOAD-BEARING for the maintenance (charter §3), not read-off.
4. **Compose BOTH `RegionRepresents` directions** — the ideal EQUALITY needs the unipotent inverse
   (`P·B = B·L` with `P⁻¹` a sign-flip; `-PROTO`'s `Q1inv`/`Q2inv` are the polynomial inverses). One
   direction is not the `hideal`.

The genuine-bypass exact algebra (rev-render-verified, for orientation): `B = diag`, `b'_i = b'_p·r_i`,
clean elim `L = I − ∑ d''_{ip} E_{ip}`, weighted `P = I − ∑ r_i d''_{ip} E_{ip}` satisfy `P·B = B·L` ⟹ both
inclusions; the only denominator (`b'_p`) is killed by the b-chain.

## 5. OUT OF SCOPE (do not build; do not let the gate secretly depend on these)

- **The terminal single-chain PRINCIPALITY** (`⟨∏C⟩=⟨b₁⟩`, L-C — the value read-off) is flagged
  **open-in-source** at deep-mixed coupled instances (render §81-86, worked.tex:651-664). The operator chose
  the **value path (V)** to route around it. The gate measures the **`hideal` MONOMIALISATION** (`⟨(∏C)∘g⟩ =
  ⟨diag b⟩`, a diagonal-monomial identity) — which is L-A/L-B, verified sound+general — NOT principality. If
  you find yourself needing principality to close `hideal`, **STOP and report** (that would be a scope
  finding, not a lemma to push).
- The **general-`d` fold** (the (S,J) recursion over `buildTree`) — that is the full build, gated on THIS.
- The **cover** (`hcover`/L7) — separately probed (GREEN-on-math, route-(a) full fan); not this unit.
- Do NOT touch `expedition/aoyagi-full` anything.

## 6. Deliverable + gate

- **The two fields** (`hideal_fwd`/`hideal_bwd`) sorry-free, in a new module (e.g.
  `Core/Aoyagi/Corank2HidealProto.lean` or extend `Corank2Proto.lean`), pushed to a feature branch off
  `-PROTO` (e.g. `expedition/aoyagi-engine-gate2`). Green-gate the FULL `scripts/lb DLNFibre` (name-clash
  guard, lean/CLAUDE.md) + `#print axioms` on both fields (FORCE elaboration — a stale olean can mask a
  `sorryAx`).
- **THE TAX REPORT** (the gate's real output — a short markdown note in your branch): (a) did the symbolic→
  concrete instantiation render cleanly, or did Mathlib ideal-membership / `RegionRepresents` / cast machinery
  fight? (b) line count + the heaviest single obligation; (c) any guardrail that was awkward to honour; (d)
  the honest verdict: **is the general-`d` reproduction "bounded but large" (GREEN — commit the swap) or did
  a hidden tax surface (YELLOW/RED — re-scope)?** Name specific Mathlib lemmas/walls, not a vibe.

Report back to the controller (peer request, not approval): the branch SHA, `#print axioms` output, and the
tax report. The controller re-derives the gate (re-runs `#print axioms` on a fresh build) before believing
"done" and takes the commit-the-swap decision to the operator (wait-for-explicit-go on the full build).
