<task>
A Lean lemma proof I need spelled cleanly. The statement is TRUE (verified 0/135609 exhaustive); I need
the cleanest proof decomposition and to confirm where the achiever fact (good_floor_core) enters.

SETUP (exact ints): forwardMax greedy picks q_0,q_1,... left-to-right from a FIXED pool Ymulti (multiset
of L ints). R_i = Ymulti after erasing q_0..q_{i-1} (= eraseIter i). ws_i = Mwidths.drop(i+1) =
[M^{i+2},...,M^L]. Mwidths = [M^1,...,M^L]. cLt(S,t)=#{s∈S: s<t}. u_i telescopes (u_0=M^0,
u_{i+1}=M^{i+1}+u_i-q_i). head'_i = max(u_i, M^{i+1}) (i≥1; head'_0=max(M^0,M^1)).
Ymulti = (balanced β-block: c values in {b,b+1}, r=P mod c copies of b+1, b=⌊P/c⌋) ⊎ (L-c largest sorted
widths). GREEN facts available:
  - eraseIter_dom: Dom(Mwidths.drop i, R_i) for all i [the "tight chain", propagated by maxPick_spec;
    Dom(b,R) := |b|=|R| ∧ ∀t cLt(R,t)≤cLt(b,t)]. Note Mwidths.drop i = M^{i+1} :: ws_i.
  - aS_succ_le_Yvec: aS M (i+1) ≤ Yvec M c i (the i-th sorted width ≤ the i-th balanced target).
  - good_floor_core: c·aS_m ≤ Sprefix(c+1)+(m-1) for 1≤m≤c (achiever; aS=sorted widths, Sprefix=prefix sums).
  - submultiset: cLt(R_i,t) ≤ cLt(Ymulti,t) (R_i ⊆ Ymulti).

THE LEMMA (strongCount): for τ ≤ head'_i,  cLt(R_i, τ) ≤ cLt(ws_i, τ).

MY VERIFIED DECOMPOSITION (0/135609):
- Region T (τ ≤ M^{i+1}): the tight chain eraseIter_dom gives cLt(R_i,τ) ≤ cLt(M^{i+1}::ws_i, τ) =
  cLt(ws_i,τ) + [M^{i+1}<τ] = cLt(ws_i,τ) (since [M^{i+1}<τ]=0). Done, NO achiever.
- Region A (M^{i+1} < τ ≤ head'_i): here head'_i = u_i (since τ>M^{i+1} and τ≤head'_i=max(u_i,M^{i+1})
  forces head'_i=u_i>M^{i+1}). The tight chain gives only cLt(ws_i,τ)+1 (off by one). The ACHIEVER closes
  it: the static count cLt(Ymulti,τ) ≤ cLt(ws_i,τ) HOLDS here (0/13332), and submultiset gives
  cLt(R_i,τ) ≤ cLt(Ymulti,τ) ≤ cLt(ws_i,τ). This static count is the ONLY achiever content.
</task>

<output_contract>
1. Confirm the two-region decomposition (T: tight chain; A: achiever static count) is the cleanest proof
   of strongCount, or give a cleaner one.
2. For region A, the achiever core is: cLt(Ymulti, τ) ≤ cLt(ws_i, τ) for M^{i+1} < τ ≤ u_i. Spell how
   good_floor_core proves it. The β-block of Ymulti has #{β < τ} = 0 (τ≤b), c−r (τ=b+1), c (τ>b+1). The
   widths side cLt(ws_i,τ) counts positional suffix widths < τ. Name exactly which inequality
   (good_floor_core / aS_succ_le_Yvec / count_bp1_le) bounds #{Ymulti<τ} ≤ #{ws_i<τ}, and why it holds on
   M^{i+1}<τ≤u_i. NOTE: ws_i = Mwidths.drop(i+1) is POSITIONAL (not sorted) and is MISSING the first i+1
   widths — so cLt(ws_i,τ) ≤ cLt(all-widths,τ); does the achiever count survive dropping the first i+1
   positional widths? (This is the subtle part — Ymulti is the full pool but ws_i is a suffix.)
3. Is there hidden circularity: region A uses head'_i=u_i, and u_i depends on the picks q_0..q_{i-1};
   does the static count cLt(Ymulti,τ)≤cLt(ws_i,τ) depend on u_i, or is it τ-pointwise independent of u_i
   (u_i only sets the RANGE M^{i+1}<τ≤u_i, not the inequality)?
4. Flag any gap.
</output_contract>

<grounding_rules>
- Exact ints. The lemma is TRUE (0/135609). I need the cleanest PROOF + the exact good_floor_core entry.
- ws_i = Mwidths.drop(i+1) = [M^{i+2},...] is POSITIONAL and a SUFFIX (missing first i+1 widths). Do NOT
  assume it's sorted or the full width set.
- The static count cLt(Ymulti,τ)≤cLt(ws_i,τ) for M^{i+1}<τ≤u_i is verified 0/13332. Explain WHY via the
  achiever, esp. the subtlety that ws_i drops the first i+1 positional widths.
- Distinguish PROVED from CONJECTURE.
