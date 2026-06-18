<task>
Lean 4 + Mathlib (v4.29). I am proving the final theorem of a closed-form codimension result
(Lehalleur–Rimányi Thm 7.10): the NUMBER of minimisers θ = Nat.choose m |δ|. I need a PROOF STRATEGY
(not code) for the minimiser-count bijection, and in particular how to prove the integer-square
EQUALITY-CASE rigidity that it rests on.

COMMITTED / PROVEN Lean facts (all sorry-free, building):
- `qipMin d = cValue d` (the QIP minimum equals the closed form) — DONE.
- `qipMinimiser_support (e feasible) (Gqip d e = cValue d) : ∀ i, qipM d ≤ i → e i = 0`
  (every minimiser is supported on the m-prefix qipLow = {i : Fin N | (i:ℕ) < m}, |qipLow| = m).
- `qipMinimiser_sumSq (e feasible) (Gqip d e = cValue d) : ∑_{i ∈ qipLow} (t_i)^2 = |δ|`
  where t_i := qipT d (↑e) i = e_i + d_{i+1} − a (integer), and (proven separately)
  `∑_{i ∈ qipLow} t_i = δ` for prefix-supported feasible e.
- `isLeast_sumSq (m) (δ) (|δ| ≤ m) : IsLeast { v | ∃ t : Fin m → ℤ, ∑ t = δ ∧ ∑ t² = v } |δ|`
  — the VALUE of the min is |δ|, attained. I have NOT proven the equality-case (which t attain it).
- A witness `qipWitness d : Fin N → ℕ`, feasible, with Gqip = cValue (one explicit minimiser).
- `|δ| ≤ m`, `1 ≤ m ≤ N` available.

GOAL:
`((qipFeasible d).filter (fun e ↦ Gqip d e = qipMin d hne)).card = Nat.choose m |δ|.natAbs`.

THE MATH (verified numerically): a feasible e is a minimiser IFF it is prefix-supported AND, writing
t_i = e_i + d_{i+1} − a on qipLow, the t-vector is "{0, ε}-valued with exactly |δ| nonzero coords"
(ε = sign δ): i.e. ∑t = δ AND ∑t² = |δ| TOGETHER force each t_i ∈ {0, ε} (rigidity). Then the minimiser
is determined by the SET A ⊆ qipLow of nonzero coords, |A| = |δ|; and e_i = a − d_{i+1} + (ε if i∈A else 0)
must be ≥ 0 (in-face nonnegativity, which I have: d_i ≤ a for δ≥0, d_i ≤ a−1 for δ<0). So minimisers ↔
{A ⊆ Fin m : |A| = |δ|}, card = C(m, |δ|).

KEY SUB-PROBLEM (the crux): the integer-square EQUALITY-CASE rigidity. For t : Fin m → ℤ with
∑ t = δ and ∑ t² = |δ| (and |δ| ≤ m), prove each t_i ∈ {0, sign δ}, equivalently
0 ≤ ε·t_i ≤ 1 (ε = sign δ), equivalently t_i·(t_i − ε) = 0 for all i. Numerically: ∑(t_i² − ε·t_i) =
∑t² − ε·∑t = |δ| − ε·δ = |δ| − |δ| = 0, and each term t_i² − ε·t_i = t_i(t_i − ε) ≥ 0 for INTEGER t_i
(since for integers, t(t−ε) ≥ 0 always when ε ∈ {−1,0,1}? check: ε=1: t(t−1)≥0 for all int t ✓;
ε=−1: t(t+1)≥0 for all int t ✓; ε=0: t²≥0 ✓). So a sum of nonnegative integer terms = 0 ⟹ each = 0
⟹ t_i(t_i − ε) = 0 ⟹ t_i ∈ {0, ε}. THIS is the clean route — no exchange argument needed!
</task>

<output_contract>
1. Confirm or correct the rigidity route: is "∑(t_i² − ε t_i) = 0 with each term ≥ 0 (integer
   t(t−ε)≥0) ⟹ each t_i ∈ {0,ε}" fully correct, including the δ=0 case (ε=0 ⟹ all t_i=0, so the
   unique minimiser, C(m,0)=1)? Flag any boundary issue (δ=0, |δ|=m).
2. The single cleanest Lean decomposition of the count bijection: which Mathlib lemma for the bijection
   minimiser-set ↔ powersetCard (e.g. Finset.card_bij / card_nbij' / a card_eq via an explicit
   Equiv to `Finset.powersetCard |δ| (qipLow d)`). Name the Mathlib API for |{A ⊆ s : |A|=k}| = C(|s|,k)
   (powersetCard card).
3. The map both ways: minimiser e ↦ its nonzero-t support A; A ↦ the e built from A (e_i = a−d_{i+1}+
   indicator). State exactly what must be checked for each (well-defined, feasible, minimiser, mutually
   inverse) and which is hardest in Lean v4.29.
4. Flag any GAP: e.g. does "t_i ∈ {0,ε}, ∑t=δ" really pin |A|=|δ| (count of nonzero = δ/ε = |δ|)? Does
   the e↦A↦e roundtrip need the nonnegativity (to land in ℕ) — i.e. is the ℕ-vs-ℤ direction a hidden
   obligation in the bijection, not just in existence?
</output_contract>

<grounding_rules>
Flag mathematical FACT (verified by your reasoning) vs INFERENCE about Mathlib v4.29 API names (I will
check locally). For the integer inequality t(t−ε) ≥ 0, give the cleanest case-free or omega-friendly
justification. If you see a cleaner route than the support-set bijection (e.g. directly counting via a
Finset.card_image), say so.
</grounding_rules>
