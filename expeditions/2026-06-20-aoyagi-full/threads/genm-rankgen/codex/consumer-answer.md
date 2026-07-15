**Q1 — SOUND.** [FACT] The strong IH covers every shorter chain, so choosing `u_outer = bindingCut(M)` is legitimate.

**Q2 — YES, provided `u_outer + 1` is legal (with endpoints handled separately).** [FACT] Write \(P(u)=\mathrm{peelCharge}(u)\), \(R(u)=\minAdm(\mathrm{redChain}_u M)\), and \(D=\mathrm{deepTailMin}(M)\). Argminimality gives
\[
P(u)+R(u)\le P(u+1)+R(u+1),
\]
hence
\[
(M_0-u)+(M_1-u)-1=P(u)-P(u+1)
 \le R(u+1)-R(u)\le D.
\]
Since legality of \(u+1\) gives \(M_0-u\ge1\), every shell satisfies
\[
b=M_1-(u+j)\le M_1-u
 \le (M_0-u)+(M_1-u)-1\le D.
\]
[INFERENCE] Thus argminimality is exactly the needed source. However, under the literal setup, if \(u=\min(M_0,M_1)\), the \(u+1\) comparison is unavailable. The case \(M_1\le M_0\) is harmless because \(b=0\); if \(M_0<M_1\), an additional endpoint lemma, orientation assumption, or proof that this shell is vacuous is required.

**Q3 — Architecture hygiene, but a false universal lemma is a real local gap.** [FACT] Using only the argmin instance salvages the induction, but does not make a false universally quantified shell lemma sound. [INFERENCE] Clean fix: add the binding/argmin hypothesis (or directly assume \(b\le D\)), or specialize the lemma to `u = bindingCut(M)` and prove the auxiliary bound before invoking the shell estimate.