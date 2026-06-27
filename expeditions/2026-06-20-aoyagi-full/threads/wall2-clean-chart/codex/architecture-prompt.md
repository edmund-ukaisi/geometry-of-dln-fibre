<task>
I am formalising in Lean 4 + Mathlib (v4.29) a "boundary-clean achiever chart" for a deep-linear-network
RLCT computation. I need an architecture decision on how to build a flat-coordinate blow-up chart for
ARBITRARY layer-width vector M, given a banked validate-small instance and banked generic machinery.

## The objects (all already defined / proved in the repo)

- `M : Fin (L+1) → ℕ` (layer widths). `Params M := ∀ s : Fin L, Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) ℝ`
  — a tuple of L matrices A^(0),...,A^(L-1).
- `prod M A : Matrix (Fin (M 0)) (Fin (M (last))) ℝ` — the matrix product A^(0)·A^(1)·...·A^(L-1).
- `dlnLoss M 0 A := ∑ i ∑ j (prod M A i j)^2` — squared Frobenius norm of the product (B = 0 here).
- `flatDim M := Fintype.card (FlatIdx M)` where `FlatIdx M := Σ (q : Σ s : Fin L, Fin (M s.castSucc)), Fin (M q.1.succ)`
  (one index per matrix entry across all layers).
- `routeMAmbient M := flatDim M`.
- `paramsEquivFlat M : Params M ≃ᵐ (Fin (flatDim M) → ℝ)` — measure-preserving flattening, built as
  two `MeasurableEquiv.piCurry` collapses then `arrowCongr' (Fintype.equivFin (FlatIdx M))`. NOTE: it uses
  the NONCOMPUTABLE `Fintype.equivFin (FlatIdx M)`, so per-coordinate decode is opaque.
- `routeMCore M : (Fin (routeMAmbient M) → ℝ) → ℝ := fun x => dlnLoss M 0 ((paramsEquivFlat M).symm x)`.
  KEY identity: `routeMCore M (paramsEquivFlat M A) = dlnLoss M 0 A` (symm/apply cancel).

- Generic blow-up `pivotBlowupOn (active : Finset (Fin N)) (p : Fin N) (x) := fun i => if i = p then x p
  else if i ∈ active then x p * x i else x i`. Banked lemmas: fderiv `pivotBlowupOnDeriv`, det
  `(pivotBlowupOnDeriv active p x).det = (x p)^(active.card - 1)` (for p ∈ active), InjOn off {x p = 0},
  the full geometric change-of-variables c-o-v already used in the validate-small.

- Banked reshape MP (`measurePreserving_paramsPack_of_flatIdxEquiv`): a `pack : (Fin N → ℝ) → Params M`
  specified by an EXPLICIT `e : Fin N ≃ FlatIdx M` with slot equation `pack w q.1.1 q.1.2 q.2 = w (e.symm q)`
  is measure-preserving; and `continuousLinearMap_abs_det_eq_one_of_measurePreserving` gives |det|=1 for a
  measure-preserving linear self-map.

- Banked bricks for the clean class: `deepestCoords M hL : Finset (Fin (routeMAmbient M))` = the flat coords
  whose FlatIdx layer is the deepest layer L-1 (defined via the opaque `equivFin`/cast). `deepestPivot M hL`
  (TODO: I will pick the flat coord = deepest layer entry (0,0)). `deepestCoords_card_eq_minAdm` :
  `(deepestCoords M hL).card = minAdm M` (the codimension), under hypotheses `NoInteriorBothDrop M` and
  `deepRank M = deepRows M` (the clean condition).

## The validate-small anchor (M = (4,4,2,2), L=3, N=28, minAdm=4 — ALL banked sorry-free)

It builds `phi4422 := paramsEquivFlat M4422 ∘ chartParams4422` where `chartParams4422 : (Fin 28 → ℝ) →
Params M4422` is an EXPLICIT Fin.cons of three matrices: A^(0) (4x4, free coords), A^(1) (4x2, free),
A^(2) (2x2) = `!![u0, u0·u1; u0·u2, u0·u3]` (the deepest factor radially blown up by pivot u0). The rate
`routeMCore (phi4422 u) = u0² · U` is PURE Params-side algebra (`dlnLoss_chartParams4422`): each product
entry = u0·(unblown entry), so the squared-Frobenius = u0²·‖A0·A1·M2bar‖². For the det/cov it factors
`chartParams4422 = pack4422 ∘ pb4422` where `pb4422 = pivotBlowupOn {0,1,2,3} 0` and `pack4422` uses an
EXPLICIT `decide`-based `fin28EquivFlatIdx4422 : Fin 28 ≃ FlatIdx M4422`. So
`phi = (paramsEquivFlat ∘ pack) ∘ pb`, det = |det Q|·|det pb| = 1·|u0|³ (Q4422CLM measure-preserving).

## The ∀M goal (WALL 2)

Build a `NodeAchieverChart M` for clean-boundary M (hypothesis `NoInteriorBothDrop M`), with fields:
`phi`, pivot `p`, `leafH` (= minAdm-1 on pivot, 0 else), rate `routeMCore M (phi u) = (u p)²·U`,
`U ≢ 0` a.e. (MvPolynomial null-set), det/cov via the generic pivotBlowupOn lemmas, Ubound, image_subset.

## THE DECISION I need

For ARBITRARY M, I cannot hand-build a `decide`-based slot bijection `e : Fin N ≃ FlatIdx M` like the
validate-small does (N is opaque). Two candidate architectures:

OPTION A ("flat→flat, pivot=blowup directly"): set `phi := pivotBlowupOn (deepestCoords M) (deepestPivot M)`
(no outer reshape — Q = identity). Then det/cov are DIRECTLY the generic pivotBlowupOn lemmas at
`active.card = minAdm`, trivially. The COST is the RATE: `routeMCore M (phi u) = dlnLoss M 0
((paramsEquivFlat M).symm (pivotBlowupOn (deepestCoords M) p u))`, and I must decode the opaque
`(paramsEquivFlat M).symm (pb u)` per-coordinate to show its deepest layer = u_p·M̄ and earlier layers free,
threading the product through the opaque `equivFin`. This is the "opaque-equiv rate decode" the spawn prompt
flags as the likely hard spot.

OPTION B ("Params-side chart, factor through pack"): build `chartParamsClean : (Fin N → ℝ) → Params M`
DIRECTLY (mirroring chartParams4422 but ∀M): deepest layer A^(L-1)(i,j) = u_{p} · (a fresh angular coord),
earlier layers = fresh free coords. Set `phi := paramsEquivFlat ∘ chartParamsClean`. The rate is then PURE
Params-side algebra (no opaque decode) exactly like the validate-small. For det/cov I must factor
`chartParamsClean = pack ∘ pb` with a GENERIC `pack`/`e`. Question: can I take `e := (Fintype.equivFin
(FlatIdx M)).symm` (so `pack = (paramsEquivFlat).symm`) and `pb = pivotBlowupOn (deepestCoords M) p`, making
`phi = paramsEquivFlat ∘ (paramsEquivFlat).symm ∘ pb = pb`? Then chartParamsClean would have to EQUAL
`(paramsEquivFlat).symm ∘ pb` — which is again the opaque decode. So Option B's "free coord assignment"
(which coord lands in which matrix slot) is FORCED to agree with `paramsEquivFlat`'s opaque layout, OR I
must build a separate generic measure-preserving reshape whose layout I control.

## Specific questions (rank + answer each)

1. Is there a THIRD option that avoids the opaque decode entirely? Specifically: can I keep `phi` on the
   Params side as `paramsEquivFlat ∘ chartParamsClean` with chartParamsClean built so that the deepest-layer
   coords are EXACTLY {u_p·u_c : c} for the deepest-block coords, and earlier-layer coords are the remaining
   free u's — using `paramsEquivFlat` ITSELF as the reshape so that the "which u goes where" is delegated to
   the opaque equiv but the BLOW-UP is applied to the right (deepest) coords? Concretely: is
   `chartParamsClean u := (paramsEquivFlat M).symm (pivotBlowupOn (deepestCoords M) p u)` exactly Option A,
   and is there any way to get the rate WITHOUT decoding per-coord — e.g. by proving `prod M ((paramsEquivFlat
   M).symm (pb u)) = u_p · prod M ((paramsEquivFlat M).symm (markZeroPivot u))` via a SCALAR-HOMOGENEITY
   argument on the deepest layer that does not name individual coords?

2. For Option A's rate decode: what is the cleanest Lean strategy to show the deepest layer of
   `(paramsEquivFlat M).symm (pivotBlowupOn (deepestCoords M) p u)` equals `u_p •` (its pivot-stripped form)
   and that earlier layers are untouched, GIVEN that `deepestCoords M` is defined precisely as
   `{c | ((equivFin (FlatIdx M)).symm (cast c)).1.1 = deepLayer}`? The per-coordinate decode lemma is
   `((paramsEquivFlat M).symm x) q.1.1 q.1.2 q.2 = x ((equivFin (FlatIdx M)) ... )`-ish. Can I prove a
   layer-level statement "for the deepest layer s = L-1, `A^(s) i j = u_p · A^(s)_unblown i j`; for s < L-1,
   `A^(s) = unblown`" by reducing `pivotBlowupOn (deepestCoords M) p (· at flat coord c)` using ONLY the
   membership `c ∈ deepestCoords ↔ layer(c) = L-1`, never naming coords?

3. Once the deepest layer factors as `u_p • M̄^(L-1)` and earlier layers are free, the product
   `prod M A = A^(0)·...·A^(L-2)·(u_p • M̄) = u_p • (A^(0)·...·M̄)`. Is `Matrix.mul_smul` / `smul` pull-out
   through the `prodAux` recursion (only the LAST factor carries the scalar) clean? The repo notes
   `prodAux_succ` peels the product; the last factor is the deepest.

4. Given the cov for Option A is the EASY part (generic pivotBlowupOn c-o-v at active=deepestCoords,
   det |u_p|^{minAdm-1} directly), and the rate is the hard part — do you AGREE Option A is the right call,
   or is there a reason to prefer building a generic controllable reshape (Option B with a custom `e`)?
   The validate-small chose Params-side + explicit pack because N was concrete; for opaque N, which way?

</task>

<output_contract>
Answer the 4 numbered questions in order. For Q1, give a yes/no on whether a decode-free rate exists and
the one-line reason. For Q2/Q3, give the concrete Lean lemma/tactic skeleton (lemma names from Mathlib
v4.29 where you can). For Q4, give a single recommendation (Option A / B / third) with the decisive reason.
End with a 3-bullet "build order" for the chosen option. Be concrete; this is a build plan, not prose.
</output_contract>

<grounding_rules>
You do not have the repo. Treat all definitions above as ground truth. Where you propose a Mathlib lemma
name you are not certain exists at v4.29, flag it as "verify exists". Distinguish "this should work" from
"this is the standard idiom". Do not invent repo lemma names beyond those I listed.
</grounding_rules>
