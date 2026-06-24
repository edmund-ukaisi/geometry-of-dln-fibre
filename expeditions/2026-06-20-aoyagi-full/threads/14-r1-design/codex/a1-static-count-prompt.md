<task>
Spell the cleanest Lean 4 proof of ONE lemma (`static_count`), from named GREEN lemmas. The statement is
TRUE (verified 0/13332). I want the cleanest derivation that AVOIDS a fragile case-split.

SETUP (exact ints). aS = M sorted ascending (aS_0≤…≤aS_L). c = achiever index, P = Sprefix(c+1) = aS_0+…+aS_c,
b = ⌊P/c⌋, r = P mod c. Yvec : Fin L → ℤ — the achiever target, with Yvec_k = (balanced β-block for k<c:
c−r copies of b then r copies of b+1) and Yvec_k = aS_{k+1} for c≤k<L (the sorted tail). Ymulti = the
multiset of Yvec. Mwidths = [M^1,…,M^L] (positional). ws_i = Mwidths.drop(i+1) = [M^{i+2},…,M^L] (positional
suffix). cLt(S,τ) = #{s∈S : s<τ}. uTel_i = a level (u_0=M^0, u_{k+1}=M^{k+1}+u_k−q_k).

GREEN lemmas (proven, exact):
- cLt_ofFn : cLt(ofFn f, τ) = #{k : f_k < τ}.   [count of an ofFn multiset]
- cLt_le_of_pointwise : (∀k, A_k ≤ B_k) → cLt(ofFn B, τ) ≤ cLt(ofFn A, τ).   [pointwise ⟹ reversed count]
- aS_succ_le_Yvec : aS_{k+1} ≤ Yvec_k  (∀ k : Fin L).
- aS_le_bp1 : 1≤i≤c → aS_i ≤ b+1.
- count_bp1_le : #{i∈[1,c] : aS_i = b+1} ≤ r.
- good_floor_core : 1≤m≤c → c·aS_m ≤ Sprefix(c+1) + (m−1).
- Yvec_lowerfit : smallestK L m Yvec ≤ Sprefix(m+1)   (m≤L; smallestK = sum of m smallest).
- eraseIter_dom : Dom(Mwidths.drop i, R_i)  (the tight chain; Dom b R := |b|=|R| ∧ ∀τ cLt R τ ≤ cLt b τ).
- cLt_mono, cLt_erase (cLt(M,τ)=cLt(M.erase a,τ)+[a<τ]).

THE LEMMA (static_count): for M^{i+1} < τ ≤ uTel_i (with i < L),
    cLt(Ymulti, τ) ≤ cLt(ws_i, τ).

VERIFIED FACTS (exact, exhaustive 0/13332 in region A):
- cLt(Ymulti,τ) ≤ cLt(Mwidths,τ) always (= dom_Mtail STEP-1, from aS_succ_le_Yvec + cLt_le_of_pointwise,
  since the multiset {aS_1,…,aS_L} = {Mwidths}).
- In region A, exactly ONE of M^1,…,M^{i+1} is < τ (namely M^{i+1}); M^1,…,M^i ≥ τ. So
  cLt(Mwidths,τ) = cLt(ws_i,τ) + 1. Hence the target ⟺ the STRICT bound cLt(Ymulti,τ) ≤ cLt(Mwidths,τ) − 1.
- The β-block count #{β-value < τ} is EXACT by construction: 0 (τ≤b), c−r (τ=b+1), c (τ>b+1).
- The tail (aS_{c+1},…,aS_L) contributes 0 to cLt(Ymulti,τ) in MOST region-A cases (12821/13332) but NOT
  all (511 have a tail value < τ).
- The strict −1 holds for MIXED reasons across the 13332: a uniform "the pointwise aS_{k+1}≤Yvec_k is strict
  at one index" covers only ~1039; the rest are cLt(Ymulti,τ)=0 trivially or strict elsewhere. So a single
  strict-pointwise step does NOT uniformly give the −1.
</task>

<output_contract>
1. Give the CLEANEST green-expressible proof of static_count that does NOT rely on the fragile mixed-reason
   strict −1. Candidates: (a) a smallestK/Yvec_lowerfit count argument (m := cLt(Ymulti,τ); the m smallest
   Yvec are < τ ⟹ smallestK L m Yvec < m·τ; combine with Yvec_lowerfit and good_floor_core to force
   cLt(ws_i,τ) ≥ m); (b) a direct β+tail count handling the 511 tail-contributing cases uniformly;
   (c) something else. Name the exact green lemmas and the order.
2. The positional-suffix obstruction: cLt(ws_i,τ) counts a POSITIONAL suffix [M^{i+2},…,M^L], NOT a sorted
   slice. How do you bound it below by cLt(Ymulti,τ) when ws_i isn't sorted? (Note cLt is permutation-
   invariant on a multiset, so cLt(ws_i,τ) = cLt(sorted ws_i, τ) — does that help reduce to a sorted
   comparison?)
3. Is the smallestK route (a) clean — does "m smallest Yvec < τ" + Yvec_lowerfit + good_floor_core give
   cLt(ws_i,τ) ≥ m without the case-mix? Spell it if so.
4. Flag any gap or hidden case-split.
</output_contract>

<grounding_rules>
- Exact ints. static_count is TRUE (0/13332). I need the cleanest PROOF avoiding the fragile strict-−1 mix.
- ws_i is a POSITIONAL suffix (drops M^1..M^{i+1}); cLt is permutation-invariant so you may sort it.
- The β-block count is EXACT by construction (not count_bp1_le, which bounds the SORTED-WIDTH b+1 count).
- Distinguish PROVED from CONJECTURE. Prefer a uniform argument (smallestK or direct β+tail) over the
  mixed-reason strict-pointwise.
