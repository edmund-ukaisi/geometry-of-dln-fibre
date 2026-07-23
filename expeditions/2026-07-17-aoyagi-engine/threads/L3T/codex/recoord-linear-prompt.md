# Consult: the recoord X-linearity lemma (Lean 4 / Mathlib v4.29)

I am formalising a "degree-1 homogeneity survives a support-LINEAR coordinate change" step.
I have a PROVEN helper (below). I need to supply its `hlin`/`hC` inputs for a specific map
`blockShear (canonNormalizationOf d s pv)` on the block `X = layerCoords d (s.layer+1)`.
Please sanity-check my coefficient `C` and recommend the CLEANEST v4.29 route for the sum-reindex.

## The proven consumer (do not reprove — I need to FEED it)

```lean
theorem homogeneousDeg1On_comp_of_linear
    (g : (Fin D → ℝ) → ℝ) (X : Finset (Fin D))
    (σ : (Fin D → ℝ) → (Fin D → ℝ))
    (C : (Fin D → ℝ) → Fin D → Fin D → ℝ)
    (hagree : ∀ u v, (∀ s, s ∉ X → u s = v s) → ∀ s, s ∉ X → σ u s = σ v s)
    (hlin : ∀ u, ∀ x ∈ X, σ u x = ∑ j ∈ X, C u x j * u j)
    (hC : ∀ x ∈ X, ∀ j ∈ X, IgnoresCoords (fun u => C u x j) X Set.univ)
    (hg : HomogeneousDeg1On g X Set.univ) :
    HomogeneousDeg1On (fun u => g (σ u)) X Set.univ
```

`IgnoresCoords c S univ  ↔  ∀ u v, (∀ s, s∉S → u s = v s) → c u = c v`  (proven `ignoresCoords_univ_iff_agree`).

## The objects

- `tupIdx d := Σ q : (Σ i : Fin N, Fin (d i.succ)), Fin (d q.1.castSucc)` — a flat coord decodes (via the
  OPAQUE equiv `tupIdxEquiv d : tupIdx d ≃ Fin (flatDim d)`) to `⟨⟨layer i, row⟩, col⟩`. Only
  `Equiv.symm_apply_apply` / `apply_symm_apply` reason about it (no computable formula).
- `layerCoords d ℓ := (univ.filter (fun q : tupIdx d => (q.1.1:ℕ) = ℓ)).image (tupIdxEquiv d)`.
- `blockEntryFlat d S row col : Option (Fin (flatDim d))` = `some (tupIdxEquiv ⟨⟨⟨S,hS⟩,⟨row,hr⟩⟩,⟨col,hc⟩⟩)`
  if `S<N ∧ row<d_{S+1} ∧ col<d_S`, else `none`.  (nat indices; sidesteps dependent-Fin casts)
- `readEntry d u S row col : ℝ` = `match blockEntryFlat d S row col with | some fc => u fc | none => 0`.
- `blockShear φ u := u + φ u`  (so `blockShear φ u x = u x + φ u x`).
- `canonNormalizationOf d s pv u k` (`qp := decode pv`, `q := decode k`):
  * guard-1: `q.1.1 = s.layer ∧ q.1.2≠qp.1.2 ∧ q.2≠qp.2 ∧ cleared≤q.1.2 ∧ cleared≤q.2` →
    `-(readEntry d u s.layer q.1.2 qp.2) * readEntry d u s.layer qp.1.2 q.2`
  * else guard-2: `q.1.1 = s.layer+1 ∧ q.2 = qp.1.2` →
    `∑ i ∈ Finset.range (d q.1.1.castSucc), if i = q.2 then 0
        else readEntry d u s.layer i qp.2 * readEntry d u (s.layer+1) q.1.2 i`
  * else `0`.

## The claim (my target lemma)

For `X = layerCoords d (s.layer+1)`, `hℓN : s.layer+1 < N`: exhibit `C` with
`blockShear (canonNormalizationOf d s pv) u x = ∑ j∈X, C u x j * u j` for `x∈X`, and each `C · x j`
ignores `X`.

Reasoning: for `x∈X`, `decode x . 1.1 = s.layer+1`, so guard-1 is FALSE (layer S+1 ≠ S) and
`canonNormalizationOf … u x = if (decode x).2 = (decode pv).1.2 then (∑ i∈range(d ℓ'.castSucc), if i=(decode x).2 then 0 else readEntry d u s.layer i (decode pv).2 * readEntry d u (s.layer+1) (decode x).1.2 i) else 0`.
The factor `readEntry d u (s.layer+1) (decode x).1.2 i` equals `u (that flat coord at layer s.layer+1, row=(decode x).1.2, col=i)` — an X-coord; the factor `readEntry d u s.layer i (decode pv).2` reads layer `s.layer` (X-free). So it is X-linear.

Proposed `C u x j` (writing `rx := ((decode x).1.2:ℕ)`, `cx := ((decode x).2:ℕ)`, `a := ((decode pv).1.2:ℕ)`, `b := ((decode pv).2:ℕ)`):
```
C u x j = (if j = x then 1 else 0)
  + (if cx = a
     then ∑ i ∈ Finset.range (d ℓ'.castSucc),
            (if blockEntryFlat d (s.layer+1) rx i = some j ∧ i ≠ cx
             then readEntry d u s.layer i b else 0)
     else 0)
```
Then `∑ j∈X, C u x j * u j = u x + [cx=a]·∑ i∈range,i≠cx readEntry(S,i,b)·u(blockEntryFlat(S+1,rx,i))`
via `Finset.sum_comm` + `Finset.sum_ite_eq` (each `blockEntryFlat(S+1,rx,i) ∈ X`), and
`u(blockEntryFlat(S+1,rx,i)) = readEntry(S+1,rx,i)` matches guard-2's sum.

## Questions
1. Is `C` correct, and is the `sum_comm`+`sum_ite_eq` reindex (mirroring a proven `coreGen` lemma that
   used `bcoeff x u := ∑ p, if enc p = x then coeff p u else 0`) the cleanest route, or is there a slicker one?
2. The range bound in guard-2 is `d (decode x).1.1.castSucc` but my `C` writes `d ℓ'.castSucc`
   (`ℓ' := ⟨s.layer+1, hℓN⟩`). For `x∈X`, `(decode x).1.1 = ℓ'`. What is the cleanest way to bridge these
   (the decoded layer is `ℓ'`) — `Fin.ext` on `(decode x).1.1`? Any traps with the range/`d _.castSucc`
   term appearing under the `∑ if i=q.2`?
3. For `hC`: `C u x j` reads `u` only through `readEntry d u s.layer i b` (layer S ≠ S+1 = ℓ, off X). Best
   way to prove `IgnoresCoords` here — via `ignoresCoords_univ_iff_agree` + a helper
   "`readEntry d u S i b = readEntry d v S i b` when `u,v` agree off `layerCoords d ℓ`, `S≠ℓ`"
   (since `blockEntryFlat d S i b = some fc ⟹ fc ∈ layerCoords d S`, disjoint from `layerCoords d ℓ`)? Any subtlety?
4. Any v4.29 name/idiom traps (`Finset.sum_ite_eq` vs `sum_ite_eq'`, `Finset.sum_range`/`Fin.sum_univ_eq_sum_range`, `Finset.sum_image` injectivity side-goal)?
