import DLNFibre.DLN.RLCT.Validate.RouteMFrontPeel

/-!
# `RouteMSuffixBridge` — `Chain.suffix 0 = prod M A` (the chain ↔ DLN-product bridge)

The general achiever chart consumes `Chain.chain_telescope_zero` (`C_0 · suffix_0 = u • Hmat_0`); with
`C_0 = 1` this reads `suffix_0 = u • Hmat_0`. To turn that into the chart identity `prod M A = u • H` we
must identify the abstract chain suffix `c.suffix 0` (a right-associated front-peel fold over abstract
widths `c.Wwid : ℕ → ℕ`) with the genuine DLN layer product `prod M A` (a left-associated PREFIX fold,
but with the banked FRONT-peel `prod_front_peel`).

Both folds peel the SAME front layer (`Chain.suffix_succ : suffix s = A_s · suffix (s+1)` vs
`prod_front_peel : prod M A = A 0 · (reindex …) prod (Mtail M)(Atail M A)`), so they match by induction
on the layer count `L`. The obstacle is the recursion SHAPE mismatch: `Chain.suffix` recurses by
incrementing the slot `s` in a FIXED chain, while `prod` drops to the SHORTER family
`(Mtail M, Atail M A)`. We dissolve it with a `rawProd` engine — a family-SHIFT recursion
(`rawProd (W∘succ)(a∘succ)` for the tail) internally CAST-FREE (the shifted width family absorbs the
index shift) that matches `prod`'s recursion exactly:

* `rawProd W a L` — the front-peel product of `L` raw layers; `rawProd W a 0 = 1`,
  `rawProd W a (L+1) = a 0 · rawProd (W∘succ)(a∘succ) L`.
* `rawProd_reindex_eq_prod` — `reindex (rawProd c.Wwid c.A L) = prod M A` (induction on `L`, the banked
  `prod_front_peel` + `reindex_finCongr_mul` + `Atail_apply`; all casts at the equiv level).
* `suffix_zero_eq_rawProd` — `c.suffix 0 = rawProd c.Wwid c.A L` (the slot-shift ↔ family-shift
  congruence via `shiftChain`; `suffix` reads only `Wwid`/`A`).
* `Chain.suffix_zero_reindex_eq_prod` — the plug-in bridge. The per-`M` chart instance supplies only the
  width match `hW` and the layer match `hA`; the bridge closes `reindex (c.suffix 0) = prod M A`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators
open Matrix

variable {L : ℕ}

/-! ## The raw front-peel product engine (family-shift recursion, cast-free) -/

/-- The front-peel product of `L` raw layers `a 0, a 1, …, a (L−1)` over a width family `W : ℕ → ℕ`:
`rawProd W a 0 = 1`, `rawProd W a (L+1) = a 0 · rawProd (W∘succ)(a∘succ) L`. The shifted width family
`W∘succ` absorbs the index shift, so the recursion needs NO cast — it matches `prod`'s front-peel and
`Chain.suffix`'s slot-peel simultaneously. -/
def rawProd (W : ℕ → ℕ) (a : (k : ℕ) → Matrix (Fin (W k)) (Fin (W (k + 1))) ℝ) :
    (L : ℕ) → Matrix (Fin (W 0)) (Fin (W L)) ℝ
  | 0 => (1 : Matrix (Fin (W 0)) (Fin (W 0)) ℝ)
  | L + 1 =>
      (a 0 : Matrix (Fin (W 0)) (Fin (W 1)) ℝ) *
        rawProd (fun k => W (k + 1)) (fun k => a (k + 1)) L

/-- `rawProd` at length `0` is the identity. -/
@[simp] theorem rawProd_zero (W : ℕ → ℕ)
    (a : (k : ℕ) → Matrix (Fin (W k)) (Fin (W (k + 1))) ℝ) :
    rawProd W a 0 = (1 : Matrix (Fin (W 0)) (Fin (W 0)) ℝ) := rfl

/-- `rawProd` front-peel (the literal `L+1` recursion equation). -/
theorem rawProd_succ (W : ℕ → ℕ)
    (a : (k : ℕ) → Matrix (Fin (W k)) (Fin (W (k + 1))) ℝ) (L : ℕ) :
    rawProd W a (L + 1)
      = (a 0 : Matrix (Fin (W 0)) (Fin (W 1)) ℝ) *
          rawProd (fun k => W (k + 1)) (fun k => a (k + 1)) L := rfl

/-! ## `rawProd` (matching the DLN data) reindexes to `prod` -/

/-- **The raw product reindexes to the DLN layer product.** For a width family `W` matching the DLN
widths `M ⟨·,_⟩` on `[0, L]` (`hW`) and a layer family `a` whose reindex to those widths IS the DLN layer
`A ⟨·,_⟩` (`hA`), the raw front-peel product reindexes to `prod M A`. Induction on `L`: the banked
`prod_front_peel` peels `A 0` off `prod`, `rawProd_succ` peels `a 0` off `rawProd`; `reindex_finCongr_mul`
distributes the endpoint reindex over the rawProd product, `hA 0` matches the front factors, and the IH
on `(Mtail M, Atail M A)` (with the shifted `W∘succ`, `a∘succ`) matches the tails. All cast bookkeeping at
the equiv level (`finCongr_refl` → `reindex_refl_refl`). -/
theorem rawProd_reindex_eq_prod :
    ∀ (L : ℕ) (M : Fin (L + 1) → ℕ) (A : Params M)
      (W : ℕ → ℕ) (a : (k : ℕ) → Matrix (Fin (W k)) (Fin (W (k + 1))) ℝ)
      (hW : ∀ k (hk : k ≤ L), W k = M ⟨k, Nat.lt_succ_of_le hk⟩)
      (hA : ∀ k (hk : k < L),
        Matrix.reindex (finCongr (hW k (le_of_lt hk))) (finCongr (hW (k + 1) hk))
            (a k)
          = (A ⟨k, hk⟩ :
              Matrix (Fin (M (⟨k, Nat.lt_succ_of_le (le_of_lt hk)⟩ : Fin (L + 1))))
                (Fin (M (⟨k + 1, Nat.succ_lt_succ hk⟩ : Fin (L + 1)))) ℝ)),
      Matrix.reindex (finCongr (hW 0 (Nat.zero_le L))) (finCongr (hW L (le_refl L)))
          (rawProd W a L)
        = prod M A := by
  intro L
  induction L with
  | zero =>
      intro M A W a hW hA
      -- both products are the identity; reindex of `1` along a single equiv `e e` is `1`.
      rw [rawProd_zero]
      rw [Matrix.reindex_apply, Matrix.submatrix_one_equiv]
      -- `prod M A = 1` at `L = 0` (the empty layer product).
      show _ = prodAux M A 0 (Nat.lt_succ_self 0)
      rfl
  | succ L ih =>
      intro M A W a hW hA
      -- front-peel both sides.
      have emid : Mtail M (0 : Fin (L + 1)) = M ((0 : Fin (L + 1)).succ) := rfl
      have ecol : Mtail M (Fin.last L) = M (Fin.last (L + 1)) := rfl
      rw [prod_front_peel M A emid ecol]
      rw [rawProd_succ]
      -- distribute the outer reindex over the rawProd product (middle interface `W 1 = M 1`).
      have hmid : W 1 = M (⟨1, by omega⟩ : Fin (L + 1 + 1)) := hW 1 (by omega)
      rw [reindex_finCongr_mul (hW 0 (Nat.zero_le _)) hmid (hW (L + 1) (le_refl _))
        (a 0) (rawProd (fun k => W (k + 1)) (fun k => a (k + 1)) L)]
      -- the IH on the tail chain `(Mtail M, Atail M A)` with shifted families `W∘succ`, `a∘succ`.
      have hWt : ∀ k (hk : k ≤ L), (fun k => W (k + 1)) k = (Mtail M) ⟨k, Nat.lt_succ_of_le hk⟩ := by
        intro k hk
        show W (k + 1) = M ⟨k + 1, by omega⟩
        rw [hW (k + 1) (by omega)]
      have hAt : ∀ k (hk : k < L),
          Matrix.reindex (finCongr (hWt k (le_of_lt hk))) (finCongr (hWt (k + 1) hk))
              ((fun k => a (k + 1)) k)
            = (Atail M A ⟨k, hk⟩ :
                Matrix (Fin ((Mtail M) (⟨k, Nat.lt_succ_of_le (le_of_lt hk)⟩ : Fin (L + 1))))
                  (Fin ((Mtail M) (⟨k + 1, Nat.succ_lt_succ hk⟩ : Fin (L + 1)))) ℝ) := by
        intro k hk
        -- `Atail_apply` exposes the tail layer as a reindex of `A ⟨k+1,_⟩`; rewrite by `hA (k+1)`
        -- (flipped), then both sides reindex `a (k+1)` and the index maps agree value-wise.
        have eA : M (((⟨k, hk⟩ : Fin L).succ : Fin (L + 1)).castSucc)
            = Mtail M ((⟨k, hk⟩ : Fin L).castSucc) := rfl
        have eB : M (((⟨k, hk⟩ : Fin L).succ : Fin (L + 1)).succ)
            = Mtail M ((⟨k, hk⟩ : Fin L).succ) := rfl
        rw [Atail_apply M A ⟨k, hk⟩ eA eB]
        show _ = Matrix.reindex (finCongr eA) (finCongr eB) (A ⟨k + 1, by omega⟩)
        rw [← hA (k + 1) (by omega)]
        simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix]
        congr 1 <;> · ext x; simp [finCongr]
      have htail := ih (Mtail M) (Atail M A) (fun k => W (k + 1)) (fun k => a (k + 1)) hWt hAt
      -- rewrite the `prod` tail by the IH (flipped), then split front/tail and reconcile reindexes.
      rw [← htail]
      refine congrArg₂ (· * ·) ?_ ?_
      · -- front factor: `reindex (a 0) = A 0` is exactly `hA 0`.
        exact hA 0 (by omega)
      · -- tail factor: `reindex (rawProd tail) = reindex (reindex (rawProd tail))`. Unfold both to
        -- `submatrix`, collapse the RHS double-`submatrix`, then the index maps agree value-wise
        -- (every `finCongr`/composite is the value-preserving `Fin` bijection).
        simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix]
        congr 1 <;> · ext x; simp [finCongr]

/-! ## Linking `Chain.suffix` to `rawProd`

`Chain.suffix` recurses by INCREMENTING the slot `s` in a FIXED chain; `rawProd` recurses by SHIFTING the
width family. To match them we drop, per layer, to the `shiftChain` (the chain with widths/layers shifted
by one), whose own slot-`0` suffix IS the parent's slot-`1` suffix — a UNIFORM `+1` shift, so no
`s+(k+1)`-vs-`(s+1)+k` index mismatch arises. `suffix` ignores the `C/B/E/R/step/base` fields, so the
`shiftChain` carries trivial ones (zeros). -/

/-- The shifted chain: widths/layers shifted by one (`Wwid k = c.Wwid (k+1)`, `A k = c.A (k+1)`), one
layer shorter. The telescope fields are trivial (`suffix` reads only `Wwid`/`A`). -/
def shiftChain {n : ℕ} {u : ℝ} (c : Chain (n + 1) u) : Chain n u where
  Wwid := fun k => c.Wwid (k + 1)
  Twid := fun _ => 0
  A := fun k => c.A (k + 1)
  C := fun _ => 0
  B := fun _ => 0
  E := fun _ => 0
  R := 0
  step := by intro k hk; simp
  base := by simp

/-- `suffixAux` of `c` at slot `s+1` equals `suffixAux` of `shiftChain c` at slot `s`: the recursion
shifts uniformly by one, absorbed into `shiftChain`'s own widths/layers (no index-arithmetic mismatch). -/
theorem suffixAux_shiftChain {n : ℕ} {u : ℝ} (c : Chain (n + 1) u) (d : ℕ) :
    ∀ (s : ℕ) (h : (s + 1) + d = n + 1) (h' : s + d = n),
      c.suffixAux d (s + 1) h = (shiftChain c).suffixAux d s h' := by
  induction d with
  | zero =>
      intro s h h'
      have hs : s = n := by omega
      subst hs
      rfl
  | succ d ih =>
      intro s h h'
      rw [Chain.suffixAux_succ, Chain.suffixAux_succ, ih (s + 1) (by omega) (by omega)]
      rfl

/-- `suffix` of `c` at slot `s+1` equals `suffix` of `shiftChain c` at slot `s` (the top-level form). -/
theorem suffix_shiftChain {n : ℕ} {u : ℝ} (c : Chain (n + 1) u) (s : ℕ) (hs : s + 1 ≤ n + 1) :
    c.suffix (s + 1) hs = (shiftChain c).suffix s (by omega) := by
  unfold Chain.suffix
  rw [suffixAux_shiftChain c (n + 1 - (s + 1)) s (by omega) (by omega)]
  exact Chain.suffixAux_congr _ (by omega) _ _

/-- **`c.suffix 0 = rawProd c.Wwid c.A n`.** The abstract chain's full suffix product is the raw
front-peel product over its widths/layers. Induction on `n`: the base is the identity; the step peels the
front layer `c.A 0` off `c.suffix 0` (`suffix_succ`) and off `rawProd` (`rawProd_succ`), then matches the
tails via the IH on `shiftChain c` (whose slot-`0` suffix is `c`'s slot-`1` suffix, `suffix_shiftChain`). -/
theorem suffix_zero_eq_rawProd :
    ∀ (n : ℕ) (u : ℝ) (c : Chain n u),
      c.suffix 0 (Nat.zero_le n) = rawProd c.Wwid c.A n := by
  intro n
  induction n with
  | zero =>
      intro u c
      rw [rawProd_zero]
      exact Chain.suffix_last c
  | succ n ih =>
      intro u c
      rw [Chain.suffix_succ c 0 (by omega), rawProd_succ]
      -- the tail: `c.suffix 1 = (shiftChain c).suffix 0 = rawProd (c.Wwid∘succ)(c.A∘succ) n`.
      rw [suffix_shiftChain c 0 (by omega), ih u (shiftChain c)]
      rfl

/-! ## The plug-in bridge -/

/-- **`reindex (c.suffix 0) = prod M A`** — the chain ↔ DLN-product bridge. For a `Chain L u` `c` whose
widths match the DLN widths (`hW : c.Wwid k = M ⟨k,_⟩` on `[0,L]`) and whose layers, reindexed to those
widths, ARE the DLN layers (`hA`), the chain's full suffix product reindexes to the DLN layer product
`prod M A`. Combines `suffix_zero_eq_rawProd` (`c.suffix 0 = rawProd c.Wwid c.A L`) with
`rawProd_reindex_eq_prod`.

The per-`M` achiever chart instance supplies only `hW` and `hA`; feeding `c.suffix 0` (from
`chain_telescope_zero` with `C_0 = 1`) through this bridge yields the chart identity `prod M A = u • H`. -/
theorem Chain.suffix_zero_reindex_eq_prod {L : ℕ} {u : ℝ} (c : Chain L u)
    (M : Fin (L + 1) → ℕ) (A : Params M)
    (hW : ∀ k (hk : k ≤ L), c.Wwid k = M ⟨k, Nat.lt_succ_of_le hk⟩)
    (hA : ∀ k (hk : k < L),
      Matrix.reindex (finCongr (hW k (le_of_lt hk))) (finCongr (hW (k + 1) hk))
          (c.A k)
        = (A ⟨k, hk⟩ :
            Matrix (Fin (M (⟨k, Nat.lt_succ_of_le (le_of_lt hk)⟩ : Fin (L + 1))))
              (Fin (M (⟨k + 1, Nat.succ_lt_succ hk⟩ : Fin (L + 1)))) ℝ)) :
    Matrix.reindex (finCongr (hW 0 (Nat.zero_le L))) (finCongr (hW L (le_refl L)))
        (c.suffix 0 (Nat.zero_le L))
      = prod M A := by
  rw [suffix_zero_eq_rawProd L u c]
  exact rawProd_reindex_eq_prod L M A c.Wwid c.A hW hA

end DLNFibre.DLN.RLCT
