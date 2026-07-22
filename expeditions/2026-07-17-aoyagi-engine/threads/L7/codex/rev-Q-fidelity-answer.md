1. **VERDICT — TRUE.** Choose \(p\in S\) maximizing \(|x_p|\).
If \(|x_p|>0\), set \(w_p=x_p\), \(w_q=x_q/x_p\) for \(q\in S\setminus\{p\}\), and \(w_j=x_j\) for \(j\notin S\).
Then \(|w_p|<1\), \(|w_q|=|x_q|/|x_p|\le1\), and \(|w_j|<1\) for spectators.
If \(|x_p|=0\), maximality gives \(x_q=0\) for every \(q\in S\); set \(w=0\) on \(S\) and \(w=x\) off \(S\).
This maps to \(x\) and lies in the closed unit cube. For \(|S|=1\), there are simply no ratio coordinates.

2. **VERDICT — TIGHT uniformly, but NOT TIGHT for singleton \(S\).**
For radius \(R>0\), the same witness has pivot size \(<R\), center-ratios \(\le1\), and spectator size \(<R\); hence \(\max(R,1)\) always suffices.
If \(R<1\) and \(|S|\ge2\), take \(x_q=R/2\) on \(S\) and \(0\) elsewhere: every pivot forces another \(w_q=1\), so source radius \(R\) fails.
If \(R>1\), take \(x_q=(R+1)/2\) on \(S\): every pivot forces \(|w_p|>1\), so source radius \(1\) fails.
Thus the exact radius is \(\max(R,1)\) when \(|S|\ge2\), but only \(R\) when \(|S|=1\).

3. **VERDICT — TRUE: no hidden hypotheses.**
Nonemptiness supplies a pivot; finiteness supplies a maximizer. Ties may be broken arbitrarily.
The condition \(p\in S\) is already built into the indexed union; neither \(2\le D\) nor distinctness is needed.
Indeed \(R>0\) is only needed for the nontrivial radius argument: for \(R\le0\), the open ball is empty.
When \(D=0\), no nonempty \(S\subseteq\mathrm{Fin}\,0\) exists, so the assumed statement is vacuous.
Without `S.Nonempty`, it is false: the unit ball contains \(0\), whereas the union over \(S=\varnothing\) is empty.

4. **VERDICT — recovers.**
For \(S=\mathrm{univ}\), every nonpivot coordinate lies in \(S\), so there are no spectator branches.
Thus `blockBlowupMap univ p w j` is \(w_p\) when \(j=p\) and \(w_pw_j\) otherwise, exactly `blowupMap p`.
The union over \(p\in\mathrm{univ}\) is the union over all \(p:\mathrm{Fin}\,D\).
The only subtlety is \(D=0\): `univ.Nonempty` fails, and the corresponding empty-index cover is itself false.

Overall: **Yes**—the Lean statement faithfully captures Q; its radius is uniformly sharp, though oversized for singleton \(S\) when \(R<1\).