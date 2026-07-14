[INFERENCE] Q1 — VERDICT: SOUND.  
[FACT] \(G\) is Borel, since ordered eigenvalues depend continuously on \(Z_{\rm deep}Z_{\rm deep}^{\mathsf T}\).  
[FACT] A measurable frame exists: choose lexicographically the first \(m\) independent projected coordinate vectors and apply Gram–Schmidt. Dimension jumps cause only a finite Borel partition.  
[FACT] On \(G\) the spectral frame gives rank and PSD floor; off \(G\), \(V=\varepsilon'[I_m;0]\) with the corresponding coordinate frame satisfies both.

[INFERENCE] Q2 — VERDICT: SOUND.  
[FACT] Among the \(M_2\) eigenvalues of \(ZZ^{\mathsf T}\), at most \(M_2-m\) are \(<\varepsilon'^2\) iff at least \(m\) are \(\ge\varepsilon'^2\).  
[FACT] Off \(G\) the agreement implication has a false antecedent, so it imposes no condition on the fixed \(V\).

[INFERENCE] Q3 — VERDICT: SOUND.  
[FACT] For \(j<r\), the shell gives exactly \(j\) weak eigenvalues of \(Z_{\rm full}Z_{\rm full}^{\mathsf T}\), hence \(M_1-j\) strong directions.  
[FACT] \(m=\min(M_1,n)-j\le M_1-j\); when \(M_1>n\), this is conservative because \(j\) already counts the structural zero directions.  
[FACT] For every \(i\le m\), \(\varepsilon\le\sigma_i(Z_{\rm full})\le\sqrt{M_1M_2}\,\sigma_i(Z_{\rm deep})\), hence \(\sigma_i(Z_{\rm deep})\ge\varepsilon'\).  
[FACT] Thus at least \(m\) eigenvalues are strong, equivalently \(\operatorname{weakEigCount}_{\varepsilon'}(Z_{\rm deep})\le M_2-m\).

[INFERENCE] Q4 — VERDICT: SOUND.  
[FACT] At \(j=r\), \(u=\min(M_0,M_1)\), so \((a,b)=((M_0-M_1)_+,(M_1-M_0)_+)\) and \(\min(a,b)=0\).  
[FACT] If \(a=0\), the determinant exponent is zero; if \(b=0\), the Gram matrix is \(0\times0\) with determinant \(1\). The corank weight is therefore identically \(1\).  
[FACT] Rank-drop singularities remain in the honest reduced-chain comparator, which is independent of the fake off-\(G\) value of \(Z_f\).  
[INFERENCE] D must prove this as a separate saturated branch; it must not assert the false shell-\(\subseteq G\) containment there.

[INFERENCE] Q5 — VERDICT: SOUND.  
[FACT] For \((2,4,4)\), the three recursion candidates are \(8,7,8\), so \(\minAdm=7>2\min(3,4,4)=6\); hpiv excludes the witness.  
[FACT] The absorbed linear map consists of \(u\) copies of \(x\mapsto xQ\), hence has rank \(u\rho\); its local integral converges exactly for \(c''<u\rho/2\).  
[FACT] hpiv and the strict comparator range give \(c''<\minAdm/2\le u\rho/2\), including dimensional equality \(6=6\) at the anchor.  
[INFERENCE] This suffices for a finite per-exponent \(C_{\rm hle}\); uniformity as the exponent reaches the critical endpoint would require an additional ratio estimate, but D does not state such uniformity.

[INFERENCE] Q6 — VERDICT: SOUND.  
[FACT] \(m\le n\) follows from its definition, hrange supplies \(m\le M_2\), and \(\varepsilon'>0\) follows from positive widths and \(\varepsilon>0\); hence F applies.  
[FACT] D receives exactly F’s witnesses and all their properties, including agreement. Ordinary theorem application then yields the parent inequality.  
[INFERENCE] The only remaining coverage obligation is proving hpiv, hcvg, and hrange wherever the parent invokes D; that is not a semantic gap between F and D.

[INFERENCE] HEADLINE — CONTRACT-SOUND under the stated gates and strict exponent range. No statement repair is needed; D’s proof must branch at \(j=r\) and use the exponent-zero/empty-corner argument instead of shell containment.