<task>
Lean 4 + Mathlib v4.29.0 formalisation design decision. I am defining a matrix-side
"sub-product" object in a quiver-rank-pattern engine.

CONTEXT (existing, reviewed, must import — cannot edit):
- `Tuple d := ∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k` for `d : Fin (N+1) → ℕ`,
  `[CommRing k]`. So factor `A i` maps `Fin (d i.castSucc) → Fin (d i.succ)`, i.e. `A_i : Fin d_{i-1} → Fin d_i`.
- `multPrefix d A : (j : Fin (N+1)) → Matrix (Fin (d j)) (Fin (d 0)) k`
  = `Fin.induction (1 : Matrix (Fin (d 0)) (Fin (d 0)) k) (fun i prev => A i * prev)`.
  with `rfl`-step lemmas: `multPrefix_zero : multPrefix d A 0 = 1` and
  `multPrefix_succ : multPrefix d A i.succ = A i * multPrefix d A i.castSucc` (both `rfl`).
- `mult d A := multPrefix d A (Fin.last N)`  (the full ordered product `A_N ⋯ A_1`).

TARGET: a new module defining
  `submult d A i j : Matrix (Fin (d j)) (Fin (d i)) k`  for `i ≤ j` (both `i j : Fin (N+1)`),
  = the interval sub-product `A_j ⋯ A_{i+1}`, with the empty product at `i = j` equal to
  `1 : Matrix (Fin (d i)) (Fin (d i))`. This generalises `multPrefix` (the `i = 0` slice).
Then: bridge theorem `mult d A = submult d A 0 (Fin.last N)`; `rankPattern d A i j := (submult d A i j).rank`;
fact `rankPattern d A i i = d i` (rank of identity on `Fin (d i)`); and if affordable a clean
composition/step lemma analogous to `multPrefix_succ`.

OBSTACLE (probed): any recursion whose empty-product base sits at the *variable* lower index `i`
(rather than the fixed `0`) forces a dependent cast. E.g. defining `submultAux i ℓ : Matrix (Fin (d ⟨i+ℓ⟩)) (Fin (d i))`
by Nat-rec on ℓ: the base `ℓ=0` needs `d ⟨i+0⟩ = d i`, and `(⟨i+0,_⟩ : Fin (N+1)) = i` is NOT rfl
(needs `Fin.ext; simp`). So `multPrefix`'s clean `rfl`-step pattern does not transfer directly.

TWO CANDIDATE ROUTES (from the deferred note):
(a) SHIFTED-TAIL: define shifted dim vector `d' : Fin (N-i+1) → ℕ`, `d' t = d ⟨i+t⟩` (typechecks),
    shifted tuple `A' : Tuple d'` with each factor `A (i+t)` reindexed by `finCongr` casts (since
    `(i+t).succ` vs the shifted successor index differ definitionally), then
    `submult d A i j := (finCongr/reindex) (multPrefix d' A' ⟨j-i, _⟩)`. Bridge proved by reindexing.
(b) LIST.PROD/FOLD: factors `A_{i+1}…A_j` have heterogeneous matrix types (different Fin dims), so
    a literal `List.prod` (needs a Monoid) is impossible; it would be a dependent `foldr` with
    casts per step.

`Matrix.rank_reindex (em : m ≃ m₀) (en : n ≃ n₀) (A) : (reindex em en A).rank = A.rank` exists.
`finCongr : n = m → Fin n ≃ Fin m` exists.

QUESTION: Which route gives the *cleanest, most localised cast*? Is there a THIRD encoding I'm
missing that makes `submult` and its step lemma `rfl` or near-`rfl` — e.g.
  - recursing on the UPPER index `j` by `Fin.induction` with `i` held fixed, returning
    `Matrix (Fin (d j)) (Fin (d i))`, using a guard `if j ≤ i then 1 else A_j * (rec on j.pred)`?
  - defining `submult d A i j` directly as `multPrefix d A j` "divided" — no, no inverses.
  - a `Finset.prod`-style or `List`-of-dependent encoding that Mathlib has sugar for?
Concretely: rank the routes, name the single bridge lemma each needs, and say which keeps the
identity-base and the composition step closest to `rfl`. I care most about (1) only ONE cast site,
(2) `rankPattern d A i i = d i` being clean, (3) the bridge `mult = submult 0 last` being clean.
</task>

<output_contract>
1. Recommended route (one of a/b/third), 2-4 sentence rationale.
2. The exact `submult` definition shape (Lean pseudo-signature + body sketch).
3. The single cast/bridge lemma it needs, named.
4. How `rankPattern d A i i = d i` and `mult = submult 0 last` discharge under that route.
5. Whether a `multPrefix_succ`-analog is `rfl` or needs a cast; if it needs one, say so plainly.
Keep under ~400 words. Lean 4 / Mathlib v4.29 idioms.
</output_contract>

<grounding_rules>
Flag any lemma name you are not sure exists in Mathlib v4.29 as "verify". Distinguish
"this is definitionally rfl" (a claim I will test) from "this should reduce" (a guess).
</grounding_rules>
