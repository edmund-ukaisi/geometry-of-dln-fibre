<task>
A Lean index-bookkeeping check for ONE inequality (the only remaining care-spot in an otherwise-complete
proof). The inequality is TRUE (verified 0/13332); I need the cleanest index-correct derivation from named
green lemmas, and a check that the β-block index alignment has no off-by-one.

CONTEXT: forwardMax greedy on a FIXED pool Ymulti. R_i = Ymulti after i picks. ws_i = Mwidths.drop(i+1) =
[M^{i+2},…,M^L] (POSITIONAL suffix). aS = M sorted ascending (aS_0≤aS_1≤…≤aS_L). c = achiever index,
P = Sprefix(c+1) = aS_0+…+aS_c, b = ⌊P/c⌋, r = P mod c. Ymulti = (balanced β-block: c values, with
exactly r copies of b+1 and c−r copies of b) ⊎ (the tail aS_{c+1},…,aS_L). cLt(S,t)=#{s∈S: s<t}.

GREEN lemmas (proven, exact names + statements):
- aS_le_bp1 : 1≤i≤c ⟹ aS_i ≤ b+1.    [the β-values cap]
- count_bp1_le : #{i ∈ [1,c] : aS_i = b+1} ≤ r.   [at most r of the sorted widths hit b+1]
- good_floor_core : 1≤m≤c ⟹ c·aS_m ≤ Sprefix(c+1) + (m−1).
- aS_succ_le_Yvec : aS_{i+1} ≤ Yvec_i  (the i-th balanced target dominates the (i+1)-th sorted width).
- dom_Mtail_Yvec : Dom(Mwidths, Ymulti), i.e. ∀t cLt(Ymulti,t) ≤ cLt(Mwidths,t).
- the green tight chain eraseIter_dom : Dom(Mwidths.drop i, R_i).

THE TARGET (the achiever core, region A, verified 0/13332): for M^{i+1} < τ ≤ u_i (a level; u_i ≥ M^{i+1}+1 here),
    cLt(Ymulti, τ) ≤ cLt(ws_i, τ).
KNOWN STRUCTURE (verified): in this region, exactly ONE of the dropped widths M^1..M^{i+1} is < τ (namely
M^{i+1}); M^1..M^i ≥ τ. So cLt(Mwidths,τ) = cLt(ws_i,τ) + 1. Hence the target ⟺ the STRICT bound
cLt(Ymulti,τ) ≤ cLt(Mwidths,τ) − 1. The β-count: #{β-value < τ} = 0 if τ≤b, c−r if τ=b+1, c if τ>b+1.
</task>

<output_contract>
1. THE β-COUNT INDEX CHECK: spell #{Ymulti < τ} for M^{i+1} < τ ≤ u_i, splitting Ymulti = β-block ⊎ tail.
   #{β-block < τ} = 0 / c−r / c by the three τ-bands (τ≤b / τ=b+1 / τ>b+1) — confirm these counts are
   index-exact (does count_bp1_le give #{β = b+1} = r exactly, or ≤ r? the β-block is CONSTRUCTED with
   exactly r copies of b+1, so #{β < b+1} = c−r exactly — confirm). #{tail < τ}: the tail is aS_{c+1}..aS_L;
   how many are < τ? Relate to cLt(Mwidths,τ) and the −1.
2. THE STRICT −1: confirm cLt(Ymulti,τ) ≤ cLt(Mwidths,τ) − 1 in region A is index-correct. The −1 must come
   from: dom_Mtail_Yvec gives cLt(Ymulti,τ) ≤ cLt(Mwidths,τ); the extra −1 is the achiever strictness. Is it
   cleanest to prove the target DIRECTLY (β-count ≤ ws_i-count) rather than via the strict dom_Mtail? Name the
   index-exact derivation. Caveat I found: the −1 holds for MIXED reasons (sometimes cLt(Ymulti,τ)=0 trivially,
   sometimes the pointwise aS_succ_le_Yvec is strict) — does a DIRECT β-count proof avoid this case-mix?
3. THE OFF-BY-ONE: the β-block has c values indexed how (Yvec_0..Yvec_{c-1})? aS_succ_le_Yvec ties Yvec_i to
   aS_{i+1} (note the +1 index shift). count_bp1_le is over aS_1..aS_c (1-indexed). Is there an off-by-one
   between the β-block's c values, the aS_1..aS_c the count bounds, and the ws_i = drop(i+1) positional
   suffix indexing? Pin the exact index alignment.
4. Give the cleanest index-correct Lean derivation of cLt(Ymulti,τ) ≤ cLt(ws_i,τ) for M^{i+1}<τ≤u_i.
</output_contract>

<grounding_rules>
- Exact ints. The inequality is TRUE (0/13332). I need the index-EXACT derivation + any off-by-one flag.
- The β-block is CONSTRUCTED with exactly r copies of b+1 (so #{β=b+1}=r exactly, #{β<b+1}=c−r exactly);
  count_bp1_le bounds the SORTED-WIDTH count #{aS_i=b+1, i∈[1,c]} ≤ r (a different count — be careful which).
- ws_i = Mwidths.drop(i+1) is positional, drops M^1..M^{i+1}. Distinguish from the sorted aS.
- Distinguish PROVED from CONJECTURE. Focus on index-exactness and the off-by-one (point 3).
