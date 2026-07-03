# D1 (★): is Aoyagi's Step-1 full-loss→core reduction bounded, or the constant-rank/splitting wall? (genm-d1reduce)

Read-only pen-and-paper adjudication + exact sympy algebra + decorrelated PDF-grounded Codex (xhigh).
The last of three D1 de-risks (with `genm-d1lower-aoyagi`/d1route = the method trace, `genm-d1thm4` =
Theorem-4 feasibility/banked, `genm-d1uniform-aoyagi`/d1kc2 = the blow-up ∀-v uniformity).

## VERDICT: REDUCTION-BOUNDED — the (★) is a current-Lean-route artefact, not a genuine wall.

Aoyagi's Step-1 block reduction (Lemma 2 + Theorem 3) is a genuinely EXPLICIT, ∀-L, ∀-fibre-point,
formalizable route. The current Lean route's "constant-rank / Morse–Bott splitting" framing
over-generalizes — the SAME mis-scoping that demoted Morse–Bott. With Theorem 4 banked
(`deepest_le_of_homogeneous_core`) + d1kc2's blow-up-uniform verdict, **D1 de-conditionalizes to a
large-but-bounded formaliser build.**

## The single load-bearing invariant (the DLN-specific replacement for the abstract splitting lemma)
`rank(∏_{s≤S} A^(s)) ≥ r` at EVERY partial product, EVERY fibre point v (the full product factors
through every partial ⟹ `rank(partial) ≥ rank(full) = r`). ⟹ an invertible `r×r` minor of every partial
product ALWAYS exists ⟹ Aoyagi's iterated corner-elimination NEVER STALLS — a fixed row/col permutation
moves a nonzero minor into the corner. (Exact-verified L=2,3 at deepest + higher strata.)

## The pivotal structural fact (nReg constant over the fibre)
Theorem 3 peels the SAME `r×r` FINAL-rank corner at every fibre point v, NOT the point's local-rank
block. Consequence: `nReg = r(H⁰+Hᴸ⁺¹) − r²` is CONSTANT over the whole fibre. A higher-stratum v's
extra rank (`r^(s)_v > r`) stays INSIDE the core `∏C^(s)` as a nonzero core-basepoint — it does NOT
enlarge the peeled block. The additive split at v is `λ_v(full) = nReg/2 + λ_v(∏C^(s))`, and Theorem 4
gives `λ_v(core) ≥ λ_0(core)` (deepest core = origin = worst), so `λ_v ≥ nReg/2 + λ_0(core) =
λ_deepest`. That is EXACTLY the one-sided (★) `nReg/2 + coreV ≤ Lv` — delivered WITHOUT a general
splitting lemma. (Soundness margin `nReg_v ≥ nReg`, equality iff v deepest — matches DeepestMinRlct.lean's
disarmed kill-condition.)

## Why bounded — each Step-1 piece + DLNFibre/Mathlib feasibility
1. **Iterated corner never stalls ∀v** (the invariant above). No fibre point forces a constant-rank branch.
2. **Pivot selection = a FINITE combinatorial atlas**, not a parametrized constant-rank existence theorem:
   ≤ C(H^(s),r)² explicit rational charts per layer (denominators = the chosen minor det, nonzero on the
   chart), covering the fibre. Same SHAPE as S2's "min over charts U". (Codex: reduction is "explicit on
   each chart… a single rational/analytic family on the open set where the chosen r×r block is invertible".)
3. **Smooth-additivity ALREADY BANKED:** `rlct_additive_smooth_block` (Skeleton S1.5, L217–240, PROVEN):
   `λ(Σxᵢ² + G(y)²) = n/2 + λ(G²)`, guarded `hGmeas + hGne`. The transverse block {C₁−E_r, F₂, F₃} = nReg
   nondeg coords disjoint from the core (peel map = unipotent local ISO, unit Jacobian); F₃F₂ drops by
   Lemma 1 (ideal-invariance). Nondeg-quadratic RLCT = ½·#coords is elementary.
4. **Theorem 4 core-comparison BANKED:** `deepest_le_of_homogeneous_core` (DeepestMinRlct.lean, zero
   sorries) — the core `∏C^(s)` is homogeneous degree-L at every core-basepoint (exact-verified), so it
   applies unconditionally ∀ stratum.

## Reconcile with the L=2 Lean (★) — L=2 is NOT special
The Lean `deepest_le_of_optimal_via_L2_ge` / `deepest_regular_core_normal_form` are wired to need ONE
abstract constant-rank diffeo at arbitrary v (Gromoll–Meyer; Mathlib v4.29 lacks it). Aoyagi REPLACES that
single abstract lemma with the finite explicit-matrix atlas + banked Thm4. The ∀-L lift = the finite
pivot-atlas iterated over layers (same block-elim, r held at FINAL rank), NOT an L=2 square/rectangular
collapse.

## Honest residual (bounded, NOT a wall) — the Lean build
The (★) is REDUCTION-BOUNDED but not free. The per-v reduction is a FINITE family of explicit charts (one
per invertible-r-minor), not a single uniform formula. Lean cost:
- (a) prove `deepest_regular_core_normal_form` (sorry at Skeleton:1124) as the explicit unipotent
  gauge-slice iso iterated across the product — banked S1.5 gives the additivity; residual = the explicit-
  iso construction (~600–1500 lines, a Codex-sized formaliser tide).
- (b) lift to general v via the finite pivot-atlas + banked Thm4 (close `rlctAt_deepest_le_of_optimal`,
  sorry at Skeleton:1172).
Kill-condition RULED OUT: `rank(partial) ≥ r` always ⟹ the atlas covers.
Re-scope the obligation OFF "constant-rank/Morse–Bott splitting" ONTO "explicit iterated-corner block-elim
atlas" (`block_elimination` L1, Skeleton L244–360, PROVEN, is the r-corner primitive), iterated across the
product, consuming banked S1.5 + banked `deepest_le_of_homogeneous_core`. A formaliser tide, NOT a Mathlib
research contribution.

## Speculation (register as such — for a formaliser's check)
- The load-bearing invariant `rank(∏_{s≤S}A) ≥ r ∀S∀v` is the DLN-specific replacement for the abstract
  splitting lemma.
- The finite-atlas "min over charts" for D1 may share machinery with R1's per-chart `monomialThreshold`
  min — a possible unification (and, more broadly, a unified Aoyagi-blow-up formalisation might subsume
  the R1-UPPER `RouteMBoxThresholdFinite` finiteness too — a follow-up question).

## Source / artefacts
Source on `origin/expedition/aoyagi-full`: `theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex` (Lemma 2
§3.1, Thm 3 §3.2, Thm 4 §3.3); `...-extracted-text.txt` L509–862. Lean: `Skeleton.lean` (L1
`block_elimination` PROVEN L244–360; L2/D1 sorries L1124/1172; S1.5 PROVEN L217–240);
`DeepestMinRlct.lean` (the (★) statements + the prior Codex wall-claim, overturned).
Exact-algebra scripts: `/tmp/aoyagi_{onesided,corner_always,thm3_higher_verify,core_homog,additivity_check,mid_confirm,higher_stratum,uniform_pivot,pivot_finite}.py`.
Decorrelated Codex (xhigh, PDF-grounded, converged independently): `/tmp/codex-star/{prompt,answer}.md`.

*(Captured to canonical by the controller, 2026-07-03, from genm-d1reduce's report.)*
