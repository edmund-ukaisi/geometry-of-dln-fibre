<task>
Lean 4 + Mathlib formalisation. I must prove a generating-function identity by induction on N,
peeling the LAST vertex. I need the cleanest Lean STRUCTURE for the type-changing peel (the
residual lives on a strictly smaller index type). NO proof, just the structuring decision.

CONTEXT (real landed definitions, namespace DLNFibre.Core, PowerSeries ℤ written ℤ⟦X⟧):

* Dimension vector: `d : Fin (N+1) → ℕ`. Vertices are `Fin (N+1)`.
* A "Kostant partition" is `m : Fin (N+1) × Fin (N+1) → ℕ`, vanishing off `i ≤ j`, with
  `d k = ∑_{i ≤ k ≤ j} m (i,j)` at every vertex k. Encoded as a Finset:
    `kostantPartitions d r = (Fintype.piFinset (fun p => if p.1 ≤ p.2 then range (d p.1 + 1) else range 1)).filter (fun m => (∀ k, kostantAt d m k) ∧ m (0, Fin.last N) = r)`
  (corner-graded by r = m(0,last)). There is `mem_kostantPartitions` unfolding membership.
* `codimForm N (mz : ℤ → ℤ → ℤ) = ∑_{1≤i≤u≤j≤v≤N} mz (i-1)(j-1) * mz u v` (ℤ-indexed nested Finset.Icc).
* `extendℤ m : ℤ → ℤ → ℤ` zero-pads m off the box `0≤a≤b≤N`.
* `P s : ℤ⟦X⟧` = ∏_{k=1}^s geomFactor k (inverse q-Pochhammer, P 0 = 1).
* `Pm N m = ∏_{p : i≤j} P (m p)`;  `Pmult d = ∏_i P (d i)`.
* LANDED engine: `transferRHS (b : List ℕ) (d : ℕ) : ℤ⟦X⟧` (a recursion peeling List head),
  with PROVED `transferRHS_eq : transferRHS b d = P d * (b.map P).prod`.

TARGET THEOREM (Thm 5.6, "5gon"), corner-free single sum over ALL Kostant partitions of d:
  `Pmult d = ∑_{m ∈ <all Kostant partitions of d>} X^{(codimForm N (extendℤ m)).toNat} · Pm N m`.
("All Kostant partitions" = biUnion over r of `kostantPartitions d r`.)

VERIFIED FACTS (exact arithmetic, all hold) — peeling the last vertex `Fin.last N`:
  - bijection: m ↔ (m', x) where m' is a Kostant partition of d↾{0..N-1} obtained by MERGING
    column N into N-1 (m'_{i,N-1} = m_{i,N-1}+m_{i,N}), and x = last-column data
    (x_i = m_{i,N} for i<N, x_N = m_{N,N}), with 0≤x_i≤b_i:=m'_{i,N-1}, ∑x = d_N.
  - codimForm split: codimForm N (extendℤ m) = codimForm (N-1) (extendℤ m') + Δ_b(x),
    Δ_b(x) = ∑_{0≤a<u≤N}(b_a - x_a) x_u.
  - Pm split + the inner sum over x of X^Δ · (last-column P-factors) = transferRHS b d_N = P d_N · ∏ P b_i.
  - inductive step collapses to Pmult d = P(d (last)) · Pmult(d↾{0..N-1}), × IH.

THE QUESTION — how to STRUCTURE the type-changing peel in Lean 4 + Mathlib so the residual m'
is genuinely a `kostantPartitions` of a smaller vector, given the index type is `Fin (N+1)`
shrinking to `Fin N`. Specifically:
  (1) Should the induction be on N with the residual reindexed via `Fin.castSucc`/`Fin.init`
      (d : Fin (N+2) → ℕ, peel to d ∘ Fin.castSucc : Fin (N+1) → ℕ), or via a different scheme?
  (2) The bijection's forward map sends m : Fin(N+2)² → ℕ to (m' : Fin(N+1)² → ℕ, x). What is the
      cleanest Lean realisation of m' — a function defined by `Fin.lastCases` / `Fin.castSucc`
      pattern-matching, merging the two columns? What pitfalls (DecidableEq, the if i≤j support,
      the merge at the boundary column)?
  (3) The block data b : List ℕ for transferRHS must be the column `i ↦ m'_{i, last}` for
      i = 0..N-1. Is `List.ofFn (fun i : Fin (N+1) => m' (i, Fin.last N))` the right bridge, or
      should I avoid List and restate transferRHS over a `Fin`-indexed family? (transferRHS is
      already landed over List ℕ.)
  (4) Which Finset lemma carries the bijection-sum: `Finset.sum_bij'`, `Finset.sum_nbij'`, a
      `Finset.sum_sigma` / `Finset.sum_fiberwise` over the m'-fibres, or a `Fintype.sum_prod`
      reindex? The sum is over a biUnion (Finset of functions), reorganised as
      ∑_{m'} ∑_{x in fibre(m')}. Recommend ONE and say why.

DELIVER your independent recommendation. Do NOT assume my framing is right; if peeling the FIRST
vertex (Fin 0) or a different residual scheme is cleaner in Lean, say so.
</task>

<output_contract>
1. RECOMMENDED induction scheme (one sentence: on what, peel which vertex, residual reindex map).
2. The forward map m ↦ m' in Lean terms (the construction; flag the boundary-column merge pitfall).
3. List-vs-Fin bridge for transferRHS's block data — one recommendation.
4. The ONE Finset summation lemma to carry the bijection, and the fibrewise reorganisation; name it.
5. The single Lean step you predict is hardest, and why.
Keep it under ~500 words. Flag inference vs. fact.
</output_contract>

<grounding_rules>
You may rely on standard Mathlib API (Fin.lastCases, Fin.castSucc, Fin.init, Finset.sum_bij',
Finset.sum_fiberwise, Fintype.piFinset, List.ofFn). Flag any lemma you are UNSURE exists in
current Mathlib as "(verify exists)". Distinguish a structural recommendation (your judgement)
from a claim about what Mathlib provides (must be checkable).
</grounding_rules>
