<task>
Lean 4 + Mathlib v4.29.0 (toolchain pinned). Prove ONE lemma: the recursively-defined matrix
product `prodAux` is continuous in its parameter argument. I've failed 3 times on the cast in the
definition. I need a WORKING proof (compiles at this pin), not a sketch.

The definitions (in namespace `DLNFibre.DLN.RLCT`, `variable {L : ℕ}`):

```lean
def Params (H : Fin (L + 1) → ℕ) : Type :=
  ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ
-- Params has TopologicalSpace via inferInstanceAs (Pi of Pi of ℝ); the instance
-- `instTopologicalSpaceParams` is in scope (imported).

def prodAux (H : Fin (L + 1) → ℕ) (A : Params H) :
    (k : ℕ) → (hk : k < L + 1) → Matrix (Fin (H 0)) (Fin (H ⟨k, hk⟩)) ℝ
  | 0, _ => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
  | k + 1, hk => by
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      refine (prodAux H A k hk') * ?_
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by
        apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by
        apply Fin.ext; simp [Fin.succ]
      rw [e1, e2]; exact A ⟨k, hkL⟩
```

GOAL lemma:
```lean
theorem continuous_prodAux (H : Fin (L + 1) → ℕ) (k : ℕ) (hk : k < L + 1) :
    Continuous (fun A : Params H => prodAux H A k hk) := by
  sorry
```

What I tried and the exact failures:
1. Per-entry via `continuous_matrix` + `show (prodAux H A k hk' * _) i j = _; rw [Matrix.mul_apply]`:
   the `show` fails — "Function expected at `prodAux H A k hk' * ?m` but this term has type `?m`"
   (the `prodAux (k+1)` body does NOT syntactically reduce to a `*` because of the `rw [e1,e2]` cast).
2. Whole-matrix `hfun : (fun A => prodAux (k+1)) = fun A => (prodAux k) * (cast layer)` then
   `(ih hk').matrix_mul ...`: the explicit cast ascription `Fin.castSucc_castSucc ▸ ...` —
   `Fin.castSucc_castSucc` is an unknown constant; and `e1 ▸ e2 ▸ A ⟨k,hkL⟩` ascribed to the product's
   column type.
3. `set layer := fun A => e1 ▸ e2 ▸ A ⟨k,hkL⟩; hfun by funext A; rfl` (this `rfl` SEEMED to work — no
   error on hfun), then transport continuity `e1 ▸ e2 ▸ hbase`: FAILS with
   "invalid `▸` notation, failed to compute motive for the substitution" (casting a `Continuous _` prop
   along the Fin equalities).

So: `hfun` via `rfl` (whole-matrix `= (prodAux k) * (e1 ▸ e2 ▸ A ⟨k,hkL⟩)`) is the right shape and
DEFEQ-CLOSES. The remaining blocker is ONLY: prove
`Continuous (fun A : Params H => (e1 ▸ e2 ▸ A ⟨k, hkL⟩ : Matrix (Fin (H ⟨k,hk'⟩)) (Fin (H ⟨k+1,hk⟩)) ℝ))`
given `Continuous (fun A => A ⟨k, hkL⟩)`. The two factors compose by `Continuous.matrix_mul`
(`[Fintype n][Mul R][AddCommMonoid R][ContinuousAdd R][ContinuousMul R]`, present for ℝ).

Available, confirmed-present Mathlib lemmas at this pin:
- `continuous_matrix : (∀ i j, Continuous (fun a => f a i j)) → Continuous f`
- `Continuous.matrix_elem (hA : Continuous A) (i) (j) : Continuous (fun x => A x i j)`
- `Continuous.matrix_mul (hf) (hg) : Continuous (fun a => f a * g a)` (Topology.Instances.Matrix)
- `continuous_apply (i) : Continuous (fun f => f i)`
- `Continuous.congr`, `Continuous.comp`
- There is NO `continuous_cast`.

Key question for you: what is the clean way to discharge the continuity of the
`e1 ▸ e2 ▸ A ⟨k,hkL⟩` cast-transported layer (an `Eq.mpr`/cast of a continuous coordinate projection
along two `Fin` index equalities `e1 : (⟨k,hk'⟩ : Fin (L+1)) = castSucc ⟨k,hkL⟩`,
`e2 : (⟨k+1,hk⟩) = succ ⟨k,hkL⟩` that change the `H`-index inside `Matrix (Fin (H _)) (Fin (H _)) ℝ`)?
Options to consider: `subst`/`cases` on the Fin-mk equalities (they may not be `subst`-able since the
LHS is a `Fin.mk` not a variable); `Matrix.reindex`/`Matrix.submatrix` as a continuous linear/Homeomorph
map; rewriting the GOAL with `e1`/`e2` (via `congr`/`simp only [e1, e2]`) BEFORE introducing the cast so
no cast appears; or restructuring `continuous_prodAux` to avoid the cast entirely (e.g. generalize the
column index, or prove `Continuous (fun A => prodAux H A k hk i j)` per-entry by first `rw`-normalizing
the `prodAux (k+1)` definitional equation via its auto-generated equation lemma `prodAux.eq_def` /
`prodAux_succ`).
</task>

<output_contract>
Give, in this order:
1. The SINGLE cleanest strategy (one paragraph: which of the above, why it dodges the cast).
2. A COMPLETE Lean proof of `continuous_prodAux` that compiles at v4.29 — the full `by` block,
   not an outline. If a helper lemma is needed, give it complete too.
3. If your proof uses any lemma whose exact v4.29 name you're unsure of, FLAG it explicitly and give
   the fallback (e.g. "if `X` is not found, use `Y`").
Keep prose minimal; the load-bearing deliverable is compiling code.
</output_contract>

<grounding_rules>
You cannot run Lean here; mark any lemma name you are not certain exists at the v4.29 pin as
UNVERIFIED and provide an alternative. Do not invent lemma names. Prefer lemmas from the
confirmed-present list above. Distinguish "this should work" (inference) from "this is the standard
idiom" (recalled fact).
</grounding_rules>
