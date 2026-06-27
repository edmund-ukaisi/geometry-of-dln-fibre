**Q1**

Rank: **(c) > (a) > (b)**.

Use **(c), but as a restricted two-coordinate family**, not as “the full `Xvec` polynomial entry equals `e*ω`”. In the full flat polynomial, other free coordinates can contribute extra terms, so exact `Hmat0 i j = e*ω` is unlikely to be the clean statement. The clean statement is: specialize all coordinates to the identity/zero pattern except the deepest `E` coordinate `e` and matching `W` coordinate `ω`, then prove the selected `Hmat0` entry is `e * ω`; instantiate `e = ω = 1` for the existing existential witness. **INFERENCE:** this is Lean-easier than proving a coefficient statement for the full polynomial. Direct numeric (a) is second-best, but it hides the mechanism and makes every block fact an `if idx = idx₀` proof. Product route (b) is worst: it reintroduces suffix/product reindexing and only sees `u • H`, while `Hmat_succ` exposes the surviving `Rmat · A` term directly.

**Q2**

```lean
-- Known API: `Chain.Hmat_succ`, `Chain.Hmat_last`, `Chain.suffix_last`.
structure DeepSlot (M : Fin (L+1) → ℕ) (hL2 : 2 ≤ L) where
  k : Fin L              -- intended `L-2`
  hkW : k.val + 1 < L
  er : Fin (Text M (tach M) (k.val+1) - Text M (tach M) (k.val+2))
  ec : Fin (Wext M (k.val+1) - Text M (tach M) (k.val+2))
  j  : Fin (Wext M (k.val+2))

def wEW (σ : DeepSlot M hL2) (e ω : ℝ) : Fin (routeMAmbient M) → ℝ := ...
theorem wEW_blocks : K = 1 ∧ X = 0 ∧ N = 0 ∧ otherE = 0 ∧ otherW = 0 ∧ deepE σ = e ∧ deepW σ = ω := ...

def rowPath (σ) : (s : ℕ) → s ≤ σ.k.val+1 → Fin (Text M (tach M) s) := ...
theorem B_rowPath_basis : B_s (rowPath s) q = if q = rowPath (s+1) then 1 else 0 := ...
theorem E_rowPath_zero_before : s < σ.k.val+1 → (c.toChain.E s) (rowPath s) q = 0 := ...
theorem deep_E_entry : (c.toChain.E (σ.k.val+1)) (rowPath _ le_rfl) σ.j = e * ω := ...

theorem H_entry_survives :
  ∀ s (hs : s ≤ σ.k.val+1),
    c.toChain.Hmat s (by omega) (rowPath σ s hs) σ.j = e * ω
```

The induction is downward along `Hmat_succ`: base at the chosen boundary uses `Hmat_last`, `suffix_last`, `Rfin = 0`, and `deep_E_entry`; the step uses `B_rowPath_basis`, `E_rowPath_zero_before`, and `Finset.sum_eq_single`. The row index is carried by `rowPath`, built from symbolic kept-row embeddings, so the proof avoids per-node `⟨_, by decide⟩` casts.

**Q3**

Known API/definition: the structured decoder has `Rfin := 0`, so for `L = 1` the dead-leaf chain has `Hmat 1 = 0` and the only possible `E_0` term is killed by `Rmat 0 = 0`; hence `achieverUfun ≡ 0`. Therefore the witness is false for the dead-leaf `L=1` chart. The right scope is `2 ≤ L` for this dead-leaf positivity, with `L=1` handled by a live-leaf decoder or a separate pure-radial single-layer chart. I do not see a dead-leaf trick for `L=1`.

**Recommended Path**

Implement route **(c)** as `wEW e ω`, prove `Hmat0(rowPath 0, j) = e*ω`, then set `e = ω = 1` and use the sum-of-squares lower bound. Biggest dependent-width risk: `2 ≤ L` gives the boundary, but not automatically that the chosen deepest `E/W` residual `Fin` types are inhabited. If there is no existing lemma proving those widths positive at `L-2`, either add that active-slot hypothesis or choose an active boundary from `sum_rBlock_cBlock_eq_minAdm` plus `1 ≤ minAdm`.