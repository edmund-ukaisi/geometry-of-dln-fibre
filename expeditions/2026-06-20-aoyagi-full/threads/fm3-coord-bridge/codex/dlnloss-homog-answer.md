**1. Product Scaling**
Use induction on `prodAux`, but prove the prefix invariant:
```lean
prodAux H (scaleLayer c s A) k hk =
  (if (s : ℕ) < k then c else 1) • prodAux H A k hk
```
Then `prod` follows by `simp [prod, s.2]`.

At the successor step, split only on whether the current layer is `s`:
```lean
let t : Fin L := ⟨k, hkL⟩
by_cases h : t = s
```
If `h`, use `Function.update_self` and `Matrix.mul_smul`. If not, use `Function.update_of_ne h` and `Matrix.smul_mul`; prove the `if` condition is unchanged by `omega`/`Fin.ext`.

**2. Cast Handling**
Define:
```lean
def scaleLayer (c : ℝ) (s : Fin L) (A : Params H) : Params H :=
  Function.update A s (c • A s)
```
This is the right dependent-function idiom. Then first prove a local step lemma hiding the `e1/e2` mess once:
```lean
@[simp] lemma prodAux_succ ... :
  prodAux H A (k+1) hk =
    prodAux H A k (Nat.lt_of_succ_lt hk) *
      A ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := ...
```
After that, the main proof only sees a `Fin L` index, so `Function.update_self`, `Function.update_of_ne`, `Fin.ext`, `Fin.ext_iff`, and `omega` do the work. Don’t try to make `scaleLayer` commute definitionally with the matrix-dimension casts.

**3. Easier Target**
Directly proving the loss identity by entry-level induction is not easier; it redoes the product-scaling proof inside every entry and sum.

The clean sufficient target is either `(1)` or its entry corollary:
```lean
(prod H (scaleLayer c s A)) i j = c * (prod H A) i j
```
derived from `(1)` using `Matrix.smul_apply` and `smul_eq_mul`. Arbitrary-`s` `(1)` is a thrash trap only if proved directly for `prod`; the `prodAux` prefix invariant is the clean route.

**4. Lemma Names**
Use these in v4.29:

- Matrix scalar-out: `Matrix.smul_mul`, `Matrix.mul_smul`.
- Matrix/extensional cleanup: `Matrix.ext`, `Matrix.smul_apply`, `Matrix.mul_apply` if going entrywise.
- Update: `Function.update_self`, `Function.update_of_ne`.
- Fin/casts/arithmetic: `Fin.ext`, `Fin.ext_iff`, `Nat.lt_of_succ_lt`, `Nat.lt_of_succ_lt_succ`, tactic `omega`.
- Squares/sums: `mul_pow`, `pow_two` or `sq`, `smul_eq_mul`, `Finset.mul_sum`, `Finset.sum_mul`; if using scalar action form, `Finset.smul_sum`.