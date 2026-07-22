<task>
Lean 4 + Mathlib (v4.29) proof-route review. I must prove a "base atom": the flattened matrix-product
generator `coreGen` is degree-1-homogeneous in each single network layer's coordinates. I have a route;
I want it red-teamed for the CLEANEST Lean idiom on the one fiddly step (a dependent-sigma reindexing),
and whether a slicker route exists. Diagnosis > code.

## Objects (all exist, on canonical)

`d : Fin (N+1) → ℕ` is a dimension vector. A tuple `A : Tuple d = ∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) ℝ`
is N matrices; `A i` is the layer-`i` matrix, shape `d_{i+1} × d_i`.

- `mult d A : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ` — the product `A_{N-1} · … · A_0`.
- `submult d A i j (hij : i ≤ j) : Matrix (Fin (d j)) (Fin (d i)) ℝ` — the sub-product `A_{j-1}···A_i`
  (layers `i..j-1`). Lemmas available:
  - `mult_eq_submult : mult d A = submult d A 0 (Fin.last N) (Fin.zero_le _)`
  - `submult_self d A i : submult d A i i _ = 1`
  - `submult_succ d A i (p : Fin N) (hip : i ≤ p.castSucc) : submult d A i p.succ _ = A p * submult d A i p.castSucc _`
  - `submult_comp d A i j (hij : i ≤ j) (m) (hjm : j ≤ m) : submult d A i m _ = submult d A j m hjm * submult d A i j hij`

- `flatDim d = ∑ i : Fin N, d i.succ * d i.castSucc`. `tupIdx d := Σ q : (Σ i : Fin N, Fin (d i.succ)), Fin (d q.1.castSucc)`
  (a flat index = `⟨⟨layer, row⟩, col⟩`). `tupIdxEquiv d : tupIdx d ≃ Fin (flatDim d)`.
- `canonFlatten d : (Fin (flatDim d) → ℝ) ≃ₜ Tuple d`, the coordinate reindexing. KEY rfl (to confirm):
  `(canonFlatten d u) i row col = u (tupIdxEquiv d ⟨⟨i, row⟩, col⟩)`.
- `coreGen d e (k : Fin (d (Fin.last N) * d 0)) (u) : ℝ := (mult d (e u)) (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2`.
- `layerCoords d ℓ : Finset (Fin (flatDim d)) := (Finset.univ.filter (fun q : tupIdx d => (q.1.1 : ℕ) = ℓ)).image (tupIdxEquiv d)`.
- `IgnoresCoords (a : (Fin D → ℝ) → ℝ) (X : Finset (Fin D)) (V : Set _)` : `a` depends only on coords OUTSIDE `X`
  on `V`. Bridge lemma: `ignoresCoords_univ_iff_agree a X : IgnoresCoords a X univ ↔ ∀ u v, (∀ s ∉ X, u s = v s) → a u = a v`.
- `AffineOn (f) (X : Finset (Fin D)) (V) : Prop := ∃ a b, IgnoresCoords a X V ∧ (∀ x ∈ X, IgnoresCoords (b x) X V) ∧ (∀ u ∈ V, f u = a u + ∑ x ∈ X, b x u * u x)`.
- `HomogeneousDeg1On f X V : Prop := AffineOn f X V ∧ ∀ u ∈ V, (∀ x ∈ X, u x = 0) → f u = 0`.

## Target

```
theorem coreGen_layerHomogeneous' (d : Fin (N+1) → ℕ) (i : Fin (d (Fin.last N) * d 0)) (ℓ : ℕ) (hℓ : ℓ < N) :
    HomogeneousDeg1On (coreGen d (canonFlatten d) i) (layerCoords d ℓ) Set.univ
```
Math fact (sympy-verified): each monomial of a `mult`-entry carries exactly one factor from each layer, so
`coreGen` is LINEAR (degree 1, no constant) in the layer-ℓ coordinates, and vanishes when all layer-ℓ coords
are 0. (FALSE for a general linear `e`; the `canonFlatten` reindex pin is load-bearing.)

## My proposed route

Let `ℓ' : Fin N := ⟨ℓ, hℓ⟩`, `A := canonFlatten d u`. Write `(a,b) := finProdFinEquiv.symm i`.
1. 3-split isolating the layer-ℓ matrix: via `submult_comp` twice, `mult d A = M * (A ℓ' * R)` where
   `M := submult d A ℓ'.succ (last)`, `R := submult d A 0 ℓ'.castSucc`, and `A ℓ' = submult d A ℓ'.castSucc ℓ'.succ`
   (one layer, via `submult_succ` + `submult_self`).
2. `(mult d A) a b = ∑_{c1} ∑_{c2} M_{a,c1} · (A ℓ')_{c1,c2} · R_{c2,b}` (two `Matrix.mul_apply`).
3. `(A ℓ')_{c1,c2} = (canonFlatten d u) ℓ' c1 c2 = u (tupIdxEquiv d ⟨⟨ℓ', c1⟩, c2⟩)` — a single layer-ℓ flat coord.
4. Sub-lemma S1: `(∀ x ∈ layerCoords d p, u x = v x) → (canonFlatten d u) p = (canonFlatten d v) p` (funext + the rfl + decode).
5. Sub-lemma S2: `M_{a,c1}` and `R_{c2,b}` are `IgnoresCoords (layerCoords d ℓ)` — a submult over an interval NOT
   containing ℓ agrees when u,v agree off layerCoords ℓ (induction on submult via submult_succ, each peeled
   `A p` has `p ≠ ℓ` so S1 applies).
6. AffineOn: set `a := 0`; the `∑ x ∈ layerCoords d ℓ, b x u * u x` form comes by reindexing the double sum
   `∑_{c1,c2}` onto `layerCoords d ℓ` (= image of tupIdxEquiv over `{q | q.1.1 = ℓ}`), with
   `b (tupIdxEquiv ⟨⟨ℓ',c1⟩,c2⟩) u := M_{a,c1}(u) · R_{c2,b}(u)`.
7. Vanishing: all layerCoords-ℓ coords 0 ⟹ each `(A ℓ')_{c1,c2} = 0` ⟹ every term 0.

## Questions

1. STEP 6 is the fiddly one: reindexing `∑ (c1 : Fin (d ℓ'.succ)) (c2 : Fin (d ℓ'.castSucc)), F c1 c2 * u (tupIdxEquiv ⟨⟨ℓ',c1⟩,c2⟩)`
   into `∑ x ∈ layerCoords d ℓ, b x u * u x`, AND defining `b : Fin (flatDim d) → (Fin (flatDim d) → ℝ) → ℝ`
   with the correct dependent typing (the coefficient `b x` must be well-defined for `x ∈ layerCoords d ℓ`,
   where `x = tupIdxEquiv ⟨⟨ℓ',c1⟩,c2⟩`, and `IgnoresCoords`). What is the CLEANEST Mathlib idiom? Options I see:
   (a) `Finset.sum_image` (tupIdxEquiv injective) to go `∑ x ∈ image` → `∑ q ∈ filter`, then a
       `Finset` bijection `{q : tupIdx | q.1.1 = ℓ} ≃ Fin (d ℓ'.succ) × Fin (d ℓ'.castSucc)`; or
   (b) define `b x u := M_{a, row(x)}(u) · R_{col(x), b}(u)` extracting `row/col` from `(tupIdxEquiv d).symm x`
       with the dependent-Fin cast (layer of `x` = ℓ), and prove the repr directly.
   Which avoids the dependent-`Fin`-cast pain? Any `Fintype.sum_bijective` / `Equiv.sum_comp` pattern that
   sidesteps the sigma-filter bijection?

2. Is there a SLICKER route than the submult 3-split? E.g. is "mult-entry is multilinear, one factor per
   layer" cleaner via a direct `multPrefix` induction, or via a scaling characterization
   (`f (single-layer scale by t) = t · f`)? I must still land AffineOn's explicit `∃ a b`, so scaling alone
   won't suffice — but maybe a helper reduces the coefficient bookkeeping.

3. Any correctness trap in the 3-split (Fin (N+1) index arithmetic: `ℓ'.castSucc ≤ ℓ'.succ`, `ℓ'.succ ≤ last`
   needs `ℓ < N` — fine; but `submult d A ℓ'.castSucc ℓ'.succ = A ℓ'` — is the `submult_succ` + `submult_self`
   reduction clean, or is there a cast issue between `Fin (d ℓ'.succ)`/`Fin (d ℓ'.castSucc)` and the matrix
   shape of `A ℓ'`?).
</task>

<output_contract>
Three sections, matching the three questions. For Q1: pick ONE recommended idiom (a/b/other), give the
key Mathlib lemma names, and the 1-2 line shape of the reindexing step. For Q2: yes/no + the single best
alternative if yes, else confirm the 3-split is right. For Q3: flag any specific cast/index trap + the fix.
Terse. Name Mathlib v4.29 lemmas precisely (flag if unsure a name exists at this pin).
</output_contract>

<grounding_rules>
Flag inference vs. known-fact. If you are unsure a Mathlib lemma exists at v4.29, say so explicitly rather
than assert it. Do not invent lemma names.
</grounding_rules>
