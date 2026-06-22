# Lean 4 + Mathlib strategy: prove a flat constrained-ℕ-vector q-series sum equals a list recursion

I am formalising a q-series identity in Lean 4 (Mathlib, lean v4.29). I have a FLAT sum over
constrained ℕ-vectors that I must prove equals a NESTED list recursion. I need the CLEANEST Lean
proof strategy (exact tactics / Mathlib lemmas), NOT a full proof. Decorrelated second opinion wanted.

## The objects (all LANDED, sorry-free)

`P : ℕ → ℤ⟦X⟧` (a power series, `P d` has constant term 1).

`transferRHS : List ℕ → ℕ → ℤ⟦X⟧` (the target nested recursion):
  transferRHS [] d = P d
  transferRHS (b0 :: bs) d = ∑ x0 ∈ Finset.range (min b0 d + 1),
      X^((b0-x0)*(d-x0)) * P(b0-x0) * P(x0) * transferRHS bs (d-x0)
and I have `transferRHS_eq : transferRHS b d = P d * (b.map P).prod`.

`admissibleXs (m' : Fin (N+1) × Fin (N+1) → ℕ) (dlast : ℕ) : Finset (Fin (N+2) → ℕ)` :=
  (Fintype.piFinset (fun I => Finset.range (boundX m' dlast I + 1))).filter (fun x => ∑ I, x I = dlast)
where `boundX m' dlast I = Fin.lastCases dlast (fun I' => m' (I', Fin.last N)) I`
(so for a row `I = (I':Fin(N+1)).castSucc`, the bound is `b_{I'} := m'(I', Fin.last N)`; for the
corner row `I = Fin.last (N+1)`, the bound is `dlast`).

`innerSum (m' ) (dlast) : ℤ⟦X⟧` :=
  ∑ x ∈ admissibleXs m' dlast,
    X ^ (Δ x).toNat * (∏ I : Fin (N+2), P (x I)) * (∏ I' : Fin (N+1), P (m' (I', Fin.last N) - x I'.castSucc))
where `(Δ x).toNat` is provably equal to the ℕ quantity
  `∑_{0 ≤ a < u ≤ N+1} (b_a - x_{a}) * x_{u}`  (b_a = m'(a, last N), x indexed by Fin(N+2) rows;
   I can already evaluate the codimForm-derived Δ to this via landed entry-eval lemmas `extendℤ_rebuild_colN`,
   `extendℤ_rebuild_colNp1` — those give `x at col N+1 = x_row`, `at col N = b_row - x_row`).

## The goal

Prove `innerSum m' dlast = transferRHS (List.ofFn (fun i : Fin (N+1) => m' (i, Fin.last N))) dlast`
(equivalently, since I can use transferRHS_eq, prove `innerSum m' dlast = P dlast * ∏_{i:Fin(N+1)} P (m'(i,last N))`).

## What I need from you

1. The CLEANEST induction skeleton. Is it better to induct on `N` (generalizing `m'`, `dlast`), or to
   reformulate `innerSum` over a `List ℕ` of block-bounds and induct on the list (matching transferRHS)?
2. The KEY hard step: reorganizing the flat `∑ x ∈ admissibleXs` (a `piFinset` filtered by `∑ = dlast`)
   into a peel of the first block `x_0` then the residual `∑ x' ∈ admissibleXs'` with `∑ x' = dlast - x_0`.
   What is the cleanest Mathlib idiom? Options I see: `Finset.piAntidiag` + `piAntidiag_cons` (heavy,
   disjiUnion over antidiagonal); eliminate the corner via `∑ = dlast` (corner = dlast - ∑ blocks) and
   sum over blocks with `∑ blocks ≤ dlast`; `Fin.cons`/`Fin.consEquiv` to split the first coordinate;
   or a `Finset.sum_bij`/`sum_nbij'` to a `Finset.range (min b0 dlast + 1) ×ˢ (residual set)`. Which is
   least painful, and the precise lemma names?
3. The Δ per-step split: `Δ(b,x) = (b_0 - x_0)*(dlast - x_0) + Δ'(b', x')` where the residual uses
   `∑_{u>0} x_u = dlast - x_0`. Any pitfalls (ℕ subtraction, the `.toNat`)?
4. Then the inner step is exactly `durfee`-shaped (I have a `durfee` lemma: P a * P b = ∑_r ...). Confirm
   the closing.

Give a concrete tactic-level skeleton (def reformulation if needed + the bijection/peel lemma + the
induction). Flag the single most likely Lean pain point. Be concrete about Mathlib lemma names for the
constrained-vector peel — that is the crux.
