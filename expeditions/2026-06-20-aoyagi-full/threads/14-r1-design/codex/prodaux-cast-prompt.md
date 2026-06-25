<task>
Lean 4 + Mathlib v4.29. I need to prove `prod H222 A = A 0 * A 1` (or get `(prod H222 A) i j` into an
explicit cast-free `∑`/polynomial form) but `prod`/`prodAux`'s dependent recursion introduces `cast`s
(from `rw`-in-definition) that resist `rfl`/`simp`/`cast_eq`. Give me the cleanest IDIOM to kill these
casts (exact tactic/lemma sequence), or a cleaner reformulation. I write/run the Lean.

## The definitions (fixed, in the repo; I can ADD lemmas but prefer not to change these)
```lean
def Params (H : Fin (L + 1) → ℕ) : Type := ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ

def prodAux (H : Fin (L + 1) → ℕ) (A : Params H) :
    (k : ℕ) → (hk : k < L + 1) → Matrix (Fin (H 0)) (Fin (H ⟨k, hk⟩)) ℝ
  | 0, _ => (1 : Matrix (Fin (H 0)) (Fin (H 0)) ℝ)
  | k + 1, hk => by
      have hk' : k < L + 1 := Nat.lt_of_succ_lt hk
      have hkL : k < L := Nat.lt_of_succ_lt_succ hk
      refine (prodAux H A k hk') * ?_
      have e1 : (⟨k, hk'⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).castSucc := by apply Fin.ext; simp [Fin.castSucc]
      have e2 : (⟨k + 1, hk⟩ : Fin (L + 1)) = (⟨k, hkL⟩ : Fin L).succ := by apply Fin.ext; simp [Fin.succ]
      rw [e1, e2]; exact A ⟨k, hkL⟩

def prod (H : Fin (L + 1) → ℕ) (A : Params H) : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ :=
  prodAux H A L (Nat.lt_succ_self L)

def H222 : Fin 3 → ℕ := fun _ => 2   -- L = 2, all widths 2
```

## The target
`prod H222 A = A (0:Fin 2) * A (1:Fin 2)` — or, sufficient for my use,
`(prod H222 A) i j = ∑ k : Fin 2, (A 0) i k * (A 1) k j`.
For H222 ≡ 2 ALL the Fin-bounds are 2, so every `Matrix (Fin (H222 ...)) (Fin (H222 ...)) ℝ` is
*definitionally* `Matrix (Fin 2)(Fin 2) ℝ` — `prod H222 A : Matrix (Fin 2)(Fin 2) ℝ` coerces by `rfl`.

## What I've tried (all fail)
- `show prodAux H222 A 2 _ = A 0 * A 1; rfl` → fails (the e1/e2 `rw`-casts aren't rfl-collapsible; also
  the STATEMENT `A 0 * A 1` sometimes HMul-dim-mismatches: `(0:Fin 2).succ` vs `(1:Fin 2).castSucc`).
- `rw [prodAux]; simp [Matrix.mul_apply, prodAux, eq_mpr_eq_cast, cast_eq, one_apply, Fin.sum_univ_two]`
  → reaches `∑ x, (∑ x_1, 1 i x_1 * cast⋯(cast⋯(A ⟨0,_⟩)) x_1 x) * cast⋯(cast⋯(A ⟨1,_⟩)) x j = RHS`.
  `eq_mpr_eq_cast` fires (mpr→cast) but `cast_eq` does NOT (the cast proof is e1's `congrArg`, not `rfl`),
  and `1 *` (the base-case identity) doesn't simplify.
- Confirmed `H222 ⟨0,_⟩ = H222 (0:Fin 2).castSucc` is `rfl`, and `(⟨0,_⟩:Fin 3) = (0:Fin 2).castSucc` by
  `decide` — so the cast IS over defeq types, but the cast's proof term isn't syntactically rfl.
- Secondary friction: `A 0` (layer index `0 : Fin 2`) sometimes fails `OfNat (Fin 2) 0` synth in
  compound expressions (works in isolation as `A (0:Fin 2)`).

## The questions
1. THE CAST KILLER: what's the exact idiom to collapse `cast (h : T = T') M` when `T = T'` are
   *definitionally equal* but `h` is not syntactically `rfl` (it's `congrArg (Matrix _ _) e1`)? Options I
   know of: `cast_eq` (needs rfl proof — doesn't fire), `eqRec_eq` / `Eq.mpr_eq`, `Subsingleton.elim`
   on the proof + `cast_eq`, `Matrix.ext` + per-entry `cast_apply`-style, or `Fin.cast`/`finCongr`
   normalization. Which actually works here, and the exact rewrite sequence?
2. Is there a Mathlib lemma `Matrix.cast_apply` / `(cast h M) i j = M (cast .. i) (cast .. j)` that lets
   me push the cast to the indices (where it becomes `Fin`-cast = identity for equal bounds)?
3. CLEANER REFORMULATION (if 1/2 are painful): is the right move to ADD a general lemma to Loss.lean —
   e.g. `prodAux_succ : prodAux H A (k+1) hk = prodAux H A k _ * (cast-free A-term)` stated to AVOID the
   casts, or a `prod_two_layer (A : Params H) (hL : L = 2) : prod = A 0 * A 1` with the dims handled by
   `finCongr`/`Matrix.reindex`? What's the least-painful general statement?
4. The `A 0` OfNat-synth friction: best way to write the layer index so it's robust in compound exprs
   (`(0 : Fin 2)`, `⟨0, by omega⟩`, `Fin.mk`, or an abbrev)?

## Output
Q1: the exact cast-killer tactic/lemma sequence (most important). Q2: the Matrix.cast_apply lemma name
(confident-v4.29 or "unverified—grep"). Q3: cleaner-reformulation verdict + the lemma statement if yes.
Q4: the robust layer-index form. Terse; concrete syntax. Mark lemma names confident vs unverified.
</task>

<output_contract>
Q1: exact tactic sequence for the cast-kill (≤6 lines). Q2: lemma name + confidence. Q3:
reformulate? yes/no + statement. Q4: index form. Concrete syntax, not prose.
</output_contract>

<grounding_rules>
Mark lemma names confident-v4.29 vs unverified. If the honest answer is "cast surgery here is
genuinely painful, reformulate via <X>", say that plainly. Don't invent lemma names.
</grounding_rules>
