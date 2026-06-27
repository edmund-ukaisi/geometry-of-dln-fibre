**Q1.** Yes, ROUTE 1 is the right route. The clean reusable lemma should be coefficient-polymorphic:

```lean
theorem prodAux_map
    {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+* S)
    (A : ∀ s : Fin L,
      Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) R) :
    ∀ (k : ℕ) (hk : k ≤ L),
      (prodAux M A k hk).map f =
        prodAux M (fun s => (A s).map f) k hk := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp [prodAux]
  | succ k ih =>
      intro hk
      have hk' : k ≤ L := Nat.le_of_succ_le hk
      rw [prodAux_step, prodAux_step]
      rw [Matrix.map_mul, ih hk']
```

Adjust the `hk` shape to your actual `prodAux`, but keep the theorem quantified as `∀ k hk` so the induction hypothesis accepts the predecessor proof.

`Matrix.map_mul` does exist in current Mathlib docs as a rectangular matrix lemma for ring-hom-like maps; verify the exact availability/name in pinned v4.29. Fallback is entrywise:

```lean
ext i j
simp [Matrix.mul_apply, map_sum]
```

For the dependent `Eq.mpr`/cast issue: do not fight it inside the main induction. Introduce/use a `prodAux_step` lemma first, with the casts hidden in its proof. If a homogeneous `prodAux_step` statement will not typecheck cleanly, make the step lemma in `HEq`/cast form and immediately rewrite both sides through it. Directly unfolding `prodAux` may work after `simp`, but the step-lemma route is much more robust.

For evaluation, use a ring hom, e.g. `MvPolynomial.eval₂Hom (RingHom.id ℝ) u` or the local alias if available; verify the exact alias.

**Q2.** Yes: define the polynomial parameter chain directly. Since repo `Params M` is hardcoded to `ℝ`, use a bare coefficient-polymorphic chain or bespoke `prodPoly`.

One-line construction:

```lean
def unblownParamsPoly :
    ∀ s : Fin L,
      Matrix (Fin (M s.castSucc)) (Fin (M s.succ))
        (MvPolynomial (Fin N) ℝ) :=
  fun s => Matrix.of fun i j =>
    unblownFlatPoly (flatCoordOf M ⟨⟨s, i⟩, j⟩)
```

Then prove entrywise:

```lean
(unblownParamsPoly s).map (MvPolynomial.eval₂Hom (RingHom.id ℝ) u)
  = unblownParams M hL hne u s
```

by `ext i j`, DECODE, and

```lean
simp [unblownParamsPoly, unblownFlatPoly, unblownFlat]
```

**Q3.** The most robust witness is `u₁ : Fin N → ℝ := fun _ => 1`.

Reason: `unblownFlat u₁` is also constantly `1`, including at the pivot. By DECODE, every entry of `unblownParams M hL hne u₁` is `1`. So you reduce nonvanishing to a generic, coordinate-free lemma: the product of all-one rectangular matrices has a positive entry, assuming the architecture widths are nonzero. Pick the `(0,0)` product entry; induct over layers using `Matrix.mul_apply` and positivity of a finite sum over a nonempty `Fin (M t)`. Then `dlnLoss` is positive because it is a sum of squares containing that positive square.

This avoids identifying the pivot preimage, avoids rectangular identity bookkeeping, and does not reuse the rate identity backwards.

Build order:

- Define `unblownParamsPoly`, `UPolyClean`, and prove `eval u UPolyClean = U u` using `prodAux_map`.
- Prove `UPolyClean ≠ 0` by evaluating at `u₁ := fun _ => 1` and the all-ones product positivity lemma.
- Apply `MvPolynomial.ae_eval_ne_zero`; combine with `U = eval UPolyClean` and `U ≥ 0` to get `U > 0` a.e. on the box, with boundedness handled separately by the finite polynomial/box bound.