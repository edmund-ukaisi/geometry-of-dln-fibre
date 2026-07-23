<task>
I am formalising (Lean 4 / Mathlib) the DEEPEST derived obligation of a resolution-of-singularities
monument for deep-linear-network fibres. I need you to adjudicate whether ONE arm of a theorem is
PROVABLE FROM THE STATED HYPOTHESES, or whether it requires content NOT in those hypotheses (in which
case the statement is under-hypothesised / "suspect"). This is a math-adjudication task; ignore Lean
syntax details and reason about the mathematics.

## Setup (all defs are exact)

Fix N and a dimension vector d : Fin(N+1) → ℕ. Flat coordinate space is ℝ^D where D = flatDim d.
Each flat coordinate decodes (bijection `tupIdxEquiv`) to a triple `(layer ∈ Fin N, row ∈ Fin d_{layer+1},
col ∈ Fin d_layer)`. Define:

- `layerCoords d ℓ` = { flat coords whose decoded layer = ℓ }  (empty for ℓ ≥ N).
- `blockCoords d ℓ` = { flat coords at layer ℓ with col < widthMinUpto d ℓ }  ⊆ layerCoords d ℓ.
- A path `p` (a `TreePath`) carries a combinatorial state `p.conState` with fields `layer S`, `cleared J`.
- `supportAt d S J : Finset (Fin D) := if J = 0 then blockCoords d S else if S+1 < N then blockCoords d (S+1) else ∅`.
  (KEY: the moment `cleared` goes 0→1, the support JUMPS from layer S to layer S+1 — the "descent".)
- `supportLayerOf s := if s.cleared = 0 then s.layer else s.layer + 1`.

- `AffineOn f X V` := ∃ a, b, (a ignores coords X on V) ∧ (∀ x∈X, b x ignores X on V) ∧
    (∀ u∈V, f u = a u + ∑_{x∈X} b x u · u x).   [total degree ≤ 1 in the X-coordinates]
- `PerLayerDeg1From d f fromLayer V := ∀ ℓ ≥ fromLayer, AffineOn f (layerCoords d ℓ) V`.
- `Deg1SupportedSlot d resid j S fromLayer V` :=
    (∃ c, (∀ i, ContinuousOn (c i) V) ∧ (∀ u∈V, resid j u = ∑_{i∈S} c i u · u i))   [clause1: support-decomp]
    ∧ PerLayerDeg1From d (resid j) fromLayer V.                                       [clause2]
  Throughout, V = foldRegion = Set.univ (so "on V" is unconditional).

## The fold residual and the step map

`foldResid d e p : Fin(foldNR d p) → (ℝ^D → ℝ)` is defined by recursion on the path. At the root it is
`coreGen d e` (the DLN fibre defining equations — matrix-product entries). One interior step
`p.extend ed` (edge `ed` with `center`, `pivot ∈ center`, `case`, shear `shearφ`):

  stepMap u = blockBlowupMap center pivot (edgeShear u),  where
    blockBlowupMap S p w j = if j=p then w p else if j∈S then w p * w j else w j   [spectators j∉S fixed]
    edgeShear = id (case11/rollover) or blockShear φ (case12/case2), blockShear φ u = u + φ u.

Let δ := [p.conState.cleared = 0]. Then (for a non-terminal child):
  δ=0:  foldResid (p.extend ed) j u = foldResid p (cast j) (stepMap u)            [pure PULLBACK]
  δ=1:  foldResid (p.extend ed) j u = foldResid p (cast j) (qm u),                [STRICT TRANSFORM]
         where qm u k := blockBlowupCoordQuot pivot k (edgeShear u) = if k=pivot then 1 else edgeShear u k.
  (The δ=1 form removes the blow-up's single u_pivot factor: `foldResid p j (stepMap u) = u_pivot · foldResid p j (qm u)`.)

## Transition law (from the oracle)

- case11:  child.layer = p.layer,   child.cleared = p.cleared     (KEEP cleared)
- case12/case2: child.layer = p.layer, child.cleared = p.cleared + 1 (ADVANCE)
- rollover: child.layer = p.layer+1, child.cleared = 0             (fires only when cleared ≥ 1, so δ=0)

## The pins available as hypotheses (all TRUE / banked; NOT stubs)

`hbranch : (p.extend ed).IsRealBranch e` gives, via banked projections:
- centerPin: `ed.center = canonCenterOf …`.  At δ=1 case12/case2, `ed.center = blockCoords d p.layer` (= supportAt at J=0).
- ShearWithinCarve (III forms), with sl := supportLayerOf(child):
   (I)  write-side: shearφ u i = 0 for all i ∈ layerCoords d ℓ, ℓ ≥ sl.
   (II) read-side: for ℓ ≥ sl, (u ↦ shearφ u i) ignores layerCoords d ℓ.
- CanonicalSchurStep: `shearφ u k ≠ 0 ⟹ decoded k is at layer p.layer, row>cleared, col>cleared`
   (so shearφ WRITES only strict-interior layer-p.layer coords; reads only layers ≤ p.layer).
- `deg1SupportedOn_center_of_hslot` (banked, sorry-free): at δ=1 case12/case2, produces
   `Deg1SupportedOn (foldResid p) ed.center` = ∀ j ∃ c, (resid j u = ∑_{i∈ed.center} c i u · u i) with
   each c i IGNORING ed.center (= blockCoords d p.layer).

## THE THEOREM (statement is FINAL / locked; I may not weaken it)

Given `hslot : ∀ j, Deg1SupportedSlot d (foldResid p) j (supportAt d p.layer p.cleared) (supportLayerOf p) univ`,
prove `∀ j, Deg1SupportedSlot d (foldResid (p.extend ed)) j (supportAt d child.layer child.cleared) (supportLayerOf child) univ`.

There is ONE known on-cone stub for the δ=1 **case11** arm: `realBranch_boostReady_case11` produces
`Deg1SupportedOn (foldResid p) ed.center`. The project's GATE expects the ONLY sorry in the final proof
to be that case11 stub — i.e. the δ=1 **case12/case2** arm is expected to close WITHOUT a new sorry.

## MY CONCERN (the δ=1 case12/case2 arm)

At δ=1 case2 (p.cleared=0 → child.cleared=1), the child support DESCENDS from blockCoords(p.layer) to
S' = blockCoords(p.layer+1) (a DEEPER layer). The child residual is `foldResid p j (qm u)`. Using
`deg1SupportedOn_center_of_hslot`: `foldResid p j v = ∑_{i∈blockCoords(p.layer)} c_i(v) v_i`, c_i ignore
blockCoords(p.layer). So `foldResid p j (qm u) = ∑_{i∈blockCoords(p.layer)} c_i(qm) (qm)_i`, and
(qm)_pivot = 1, (qm)_i = edgeShear u i (i≠pivot). The **pivot term** is `c_pivot(qm) · 1` — a term with
NO factor of any S'-coordinate.

For the child clause1 (support S' = blockCoords(p.layer+1)) the residual must satisfy
`foldResid child j u = ∑_{k∈S'} c'_k(u) u_k`, hence VANISH when all S'-coordinates are 0. But the pivot
term c_pivot(qm)·1 need not vanish there.

CONCRETE would-be counterexample: suppose `foldResid p j = (u ↦ u_pivot)` (just the pivot coord). It
satisfies hslot: clause1 `= 1·u_pivot` supported on blockCoords(p.layer) with c=1; clause2 PerLayerDeg1From
holds (u_pivot is degree-1 in layer p.layer, degree-0 elsewhere). Its strict transform is
`foldResid child j u = (qm u)_pivot = 1` (constant). Then child clause1 fails (const 1 ≠ ∑ over S' at u=0).

So: FROM hslot ALONE (+ the banked shear/center pins), the δ=1 case2/case12 descent looks UNPROVABLE —
it seems to need Schur/cofactor content: that the REAL foldResid p (a coreGen block-matrix entry) has its
strict transform equal to the deeper block C^{(S+1)}, which is NOT captured by Deg1SupportedSlot.

## QUESTIONS (answer each explicitly)

1. Is my counterexample analysis correct — i.e. is the δ=1 case2/case12 arm UNPROVABLE from hslot +
   the banked pins alone? Or am I missing a way the pivot/constant term is forced to vanish on S'
   (e.g. from PerLayerDeg1From at layer p.layer+1 combined with the strict transform, or from some
   interaction I've overlooked)?

2. If it IS unprovable from the stated hypotheses: what is the WEAKEST additional obligation (a stub, in
   the spirit of `realBranch_boostReady_case11`) that would close it — stated precisely — and is it
   TRUE for the real DLN residuals (i.e. legitimate to add as an on-cone stub)? Concretely: is the right
   stub "the δ=1 case12/case2 strict transform is Deg1SupportedSlot on the descended block S'", i.e. the
   descent itself is the stub content?

3. If it IS provable, give the exact decomposition: how the pivot/constant term is handled, and how the
   double sum `∑_{i∈blockCoords(p.layer)} c_i(qm)·(edgeShear u)_i` becomes `∑_{k∈S'} c'_k(u) u_k`
   graded over the DEEPER block S' = blockCoords(p.layer+1). (This looks impossible without extra input,
   since the two index sets live in DISJOINT layers.)

4. Separately confirm the EASY arms are provable from hslot + pins alone: (a) δ=0 (all subcases:
   case11/case12/case2/rollover) where child support = parent support and residual is the pullback; and
   (b) δ=1 case11 where child support = parent support (blockCoords(p.layer)) and the strict transform
   preserves it — does δ=1 case11 also hit the pivot-term-vanishing issue, and does the boostReady stub
   (`Deg1SupportedOn ed.center`) actually resolve the conjunct-B descent, or only conjunct-A?
</task>

<output_contract>
Answer Q1–Q4 in order, each under its own header. For Q1: a crisp YES/NO on whether the arm is provable
from hslot alone, with the decisive reason. For Q2: the precise stub statement (if needed) and its
truth-status. For Q3: either the decomposition or a clear "impossible, because …". For Q4: per-subcase
provability verdict. Be terse and decisive; flag any step that is inference vs. certain.
</output_contract>

<grounding_rules>
Reason from the exact defs given; do not assume Mathlib lemmas. Distinguish "provable from the stated
hypotheses" (a formal-logic question — is the conclusion a consequence of hslot + the listed pins for
ARBITRARY functions foldResid satisfying them?) from "true for the real DLN residual" (a math fact about
coreGen). The theorem must hold for all foldResid satisfying the hypotheses, so a single admissible
counterexample kills provability-from-hypotheses. State explicitly which notion each answer uses.
</grounding_rules>
