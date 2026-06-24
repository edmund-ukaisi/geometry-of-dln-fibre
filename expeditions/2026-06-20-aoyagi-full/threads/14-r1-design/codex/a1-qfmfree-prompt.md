<task>
ADJUDICATE one structural question for a Lean proof: is a lemma `static_count` provable WITHOUT a
qFM-dependent "band" fact, or does it genuinely require it? The lemma is TRUE (0/13332). I need a
DEFINITIVE yes/no + the cleanest correct proof structure. NOT a counterexample hunt.

SETUP (exact ints). M : Fin(L+1)→ℕ. aS = M sorted ascending (aS_0≤…≤aS_L). c = achiever index (1≤c≤L).
P = aS_0+…+aS_c, b=⌊P/c⌋, r=P mod c. Yvec : Fin L→ℤ — achiever target: for k<c a BALANCED-SPLIT value
(c−r copies of b, r copies of b+1; NOTE these are b/b+1, NOT the sorted widths aS_1..aS_c — same SUM P but
different values); for c≤k<L, Yvec_k = aS_{k+1}. Ymulti = multiset of Yvec. ws_i = Mwidths.drop(i+1) =
[M^{i+2},…,M^L] (the POSITIONAL suffix widths, i.e. positions i+2..L of the ORIGINAL unsorted M, NOT a
sorted slice). cLt(S,τ) = #{s∈S : s<τ}. qFM = forwardMax greedy on (Mwidths, Ymulti). uTel_i = a "level"
telescoping from the qFM picks (u_0=M^0, u_{k+1}=M^{k+1}+u_k−qFM_k). The BAND at j is "qFM_j ≥ uTel_j".

THE LEMMA: static_count (i<L) (hlo: M^{i+1}<τ) (hhi: τ ≤ uTel_i) : cLt(Ymulti,τ) ≤ cLt(ws_i,τ).

ESTABLISHED FACTS (exact, exhaustive):
- The GOAL multisets (Ymulti, ws_i) are qFM-FREE (data, given i). uTel_i in hhi IS qFM-dependent.
- cLt is permutation-invariant, so cLt(ws_i,τ) = cLt(sorted(ws_i),τ), sorted(ws_i) = sorted [M^{i+2}..M^L].
- The i-INDEPENDENT bound cLt(Ymulti,τ) ≤ cLt(sorted-global-tail aS_{i+1..L}, τ) FAILS ~11% (the global
  sorted tail differs from the positional suffix ws_i).
- The target cLt(Ymulti,τ) ≤ cLt(ws_i,τ) holds 0/13332.
- One known route (the "−1 / positional closer"): cLt(ws_i,τ) = cLt(Mwidths,τ) − #{M^1..M^{i+1}<τ}, and in
  the window #{M^1..M^{i+1}<τ}=1 (only M^{i+1}<τ; M^1..M^i ≥ τ). Then cLt(Ymulti,τ) ≤ cLt(Mwidths,τ)−1.
  BUT "M^1..M^i ≥ τ" ⟺ "M^k ≥ uTel_k ∀k≤i" ⟺ "qFM_{k-1} ≥ uTel_{k-1} ∀k≤i" = the BAND at indices <i
  (verified equivalent; feasibility qFM_j≥M^{j+1} is NOT enough — uTel_j>M^{j+1} in 8652/48458). So THIS
  route is qFM-dependent (needs band-at-<i).
- An alternative route avoiding M^1..M^i≥τ: prove cLt(Ymulti,τ) ≤ cLt(sorted(ws_i),τ) DIRECTLY from the
  achiever structure (Ymulti = β-block ⊎ {aS_{c+1}..aS_L}; ws_i = positional suffix). Region split:
  (a) τ≤b+1: #{β<τ} small, bounded via good_floor_core/aS_le_bp1/aS_succ_le_Yvec.
  (b) b+1<τ≤uTel_i: #{β<τ}=c (all β saturated), then c + #{aS_{c+1..L} < τ} ≤ cLt(ws_i,τ).
</task>

<output_contract>
1. DEFINITIVE: is static_count provable WITHOUT band-at-<i (i.e. a qFM-free proof, using hhi:τ≤uTel_i only
   as an opaque upper bound on τ, NOT unfolding qFM)? YES or NO, with the reason.
2. If YES: give the qFM-free proof — specifically, does the alternative route (prove cLt(Ymulti,τ) ≤
   cLt(sorted(ws_i),τ) directly) work, and how does region (b)'s "c + #{aS_{c+1..L}<τ} ≤ cLt(ws_i,τ)"
   avoid needing M^1..M^i≥τ? The crux: ws_i is the POSITIONAL suffix (drops M^1..M^{i+1}), so cLt(ws_i,τ)
   could be SMALLER than the global tail count — how is it still ≥ the achiever count without knowing
   M^1..M^i≥τ? Is there a qFM-free reason the positional suffix ws_i has enough small widths?
3. If NO (band-at-<i genuinely required): then static_count is NOT standalone-provable and needs an in-order
   induction supplying band-at-<i. Confirm, and confirm the in-order induction is well-founded (band at
   strictly <i).
4. The deciding sub-question: cLt(ws_i,τ) vs the achiever count. ws_i drops the first i+1 positional widths.
   Does the achiever majorization cLt(Ymulti,τ) ≤ cLt(ws_i,τ) hold because the DROPPED widths M^1..M^{i+1}
   are mostly ≥τ (needs the band), or for a qFM-free structural reason? This is the whole question.
</output_contract>

<grounding_rules>
- Exact ints. static_count is TRUE (0/13332). The question is the PROOF's qFM-dependence, not truth.
- "M^k ≥ uTel_k ⟺ qFM_{k-1} ≥ uTel_{k-1} (band at k-1)" is VERIFIED (pure uTel recurrence). Feasibility
  qFM_j≥M^{j+1} is NOT enough for the band (uTel_j>M^{j+1} in ~18%).
- ws_i = [M^{i+2}..M^L] is the POSITIONAL suffix of the ORIGINAL M, not sorted, not the global tail.
- Distinguish PROVED from CONJECTURE. The decisive question is point 4: is the positional-suffix count
  bound qFM-free or band-dependent?
