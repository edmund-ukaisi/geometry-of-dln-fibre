Inference from your description, not repo inspection.

**Rank**
1. **A, but certificate-first.** Work in the genuine dependent layer spaces and prove the telescope as a reusable abstract lemma. This is the cheapest because it proves exactly the statement needed by `prod M A`; no padded-product bridge, no recursive chart-gluing invariant.
2. **C.** Mathematically attractive because it mirrors `minAdmRec`, but Lean-cost is high: the recursive chart has to transport tail widths, coordinates, and the glued rank pivot through each peel.
3. **B.** I would avoid this. Padding to `W × W` proves the wrong product first. The bridge back to the genuine dependent `prod M A` is not conceptually hard, but it creates a second full indexing layer: max-width inequalities, active-block projections, zero-extension invariants, and block splits inside the active block.

**Top Crux Lemma**
Do not prove the telescope while expanding concrete block entries. Prove this once for an abstract rectangular chain.

Lean-ish orientation below uses `A s : Matrix (W s) (W (s+1)) ℝ`, so transpose/adapt if your existing layer convention is `Matrix (Fin (M (s+1))) (Fin (M s)) ℝ`.

```lean
structure TelescopeCert (L : ℕ) (u : ℝ) where
  W T : Fin (L+1) → Type
  instW : ∀ s, Fintype (W s)
  decW  : ∀ s, DecidableEq (W s)
  instT : ∀ s, Fintype (T s)
  decT  : ∀ s, DecidableEq (T s)

  A : (s : Fin L) →
    Matrix (W s.castSucc) (W s.succ) ℝ

  C : (s : Fin (L+1)) →
    Matrix (T s) (W s) ℝ

  B : (s : Fin L) →
    Matrix (T s.castSucc) (T s.succ) ℝ   -- the P_s K_s part

  E : (s : Fin L) →
    Matrix (T s.castSucc) (W s.succ) ℝ   -- the u-error part

  R : Matrix (T (Fin.last L)) (W (Fin.last L)) ℝ

  step :
    ∀ s,
      C s.castSucc * A s =
        B s * C s.succ + u • E s

  base :
    C (Fin.last L) = u • R
```

Then define the suffix product and quotient recursively:

```lean
-- suffix s = A_s A_{s+1} ... A_{L-1}
def suffix : (s : Fin (L+1)) →
    Matrix (W s) (W (Fin.last L)) ℝ := ...

def H : (s : Fin (L+1)) →
    Matrix (T s) (W (Fin.last L)) ℝ
| last => R
| s    => B s * H s.succ + E s * suffix s.succ
```

The theorem is:

```lean
theorem telescope_divisible :
  ∀ s,
    C s * suffix s = u • H s := by
  -- reverse induction on s
  -- base: simp [suffix, H, TelescopeCert.base]
  -- step:
  calc
    C s.castSucc * suffix s.castSucc
        = (C s.castSucc * A s) * suffix s.succ := by
            simp [suffix, Matrix.mul_assoc]
    _ = (B s * C s.succ + u • E s) * suffix s.succ := by
            rw [step s]
    _ = B s * (C s.succ * suffix s.succ)
          + u • (E s * suffix s.succ) := by
            simp [Matrix.add_mul, Matrix.mul_assoc]
    _ = B s * (u • H s.succ)
          + u • (E s * suffix s.succ) := by
            rw [ih]
    _ = u • (B s * H s.succ + E s * suffix s.succ) := by
            simp [Matrix.mul_smul, smul_add]
```

If Mathlib’s exact names differ, the proof still only needs associativity, distributivity, and scalar compatibility for matrix multiplication.

The one dependent-cast bite is the bridge between this abstract suffix and your existing `prod M A`. Kill it with a single `Fin.cons` peel lemma. Define the tail widths by `Mtail i := M i.succ`, define tail layers by `simpa [Mtail] using A i.succ`, and prove once:

```lean
@[simp] theorem prod_cons :
  prod (Fin.cons m0 Mtail) (Fin.cons A0 Atail)
    = prod Mtail Atail * A0 := by
  simp [prod, prodAux, Fin.cons_zero, Fin.cons_succ, Matrix.mul_assoc]
```

Then never unfold `prodAux` in the main chart proof again.

**Fourth Encoding**
Yes: the cheaper fourth encoding is really **A′: local-certificate telescope over abstract finite types**, then instantiate with `W s = Fin (M s)` and `T s = Fin (tLike s)`. This is not padding and not recursion. It separates the global telescope from the brutal block construction.

For block splits, keep another local equivalence layer:

```lean
split s : Fin (M s) ≃ Fin (t s) ⊕ Fin (M s - t s)
```

using `finCongr` plus `finSumFinEquiv` if those names are available in your Mathlib. If not, prove that equivalence once. Do all `fromBlocks` work after `Matrix.reindex`; do not hand-index `Fin (M s)`.

**Cost Verdict**
**ROADMAP.** The general atom is not a bounded `<1500` line push unless substantial reusable block/reindex infrastructure already exists. The telescope lemma itself is small; the chart map, arbitrary block construction, split-coordinate reindexing, and connection to existing `prod M A` are the multi-pass part.

Most likely wrong ROADMAP assumption: that your current fixed examples are mostly hand-expanded entries rather than already factoring through reusable `fromBlocks`/split APIs.

Most likely wrong BUILD-NOW assumption: that `simp` will naturally normalize the `Fin` transports from `t_s + (M_s - t_s) = M_s` and the `Fin.succ` tail products. It usually will not unless those transports are hidden behind named equivalences and one peel lemma.

**Best Increment To Bank Now**
Bank the abstract `TelescopeCert` plus `telescope_divisible`, sorry-free, and one bridge lemma from its `suffix` to your existing `prod M A`. That gives future work a stable target: each layer construction only has to prove the local identity

```lean
C_s * A_s = B_s * C_{s+1} + u • E_s
```

instead of reproving the global product telescope inside arbitrary dependent block algebra.