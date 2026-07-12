## POINT A

VERDICT: SOUND

- [inferred] Let \(K\) be all Kostant partitions and \(H=\operatorname{im}(mOfE)\). Since \(H\subseteq K\),
  \[
  \min_K\operatorname{codimForm}\le \min_H\operatorname{codimForm}.
  \]
  The hard inequality in `cCodim_eq_qipMin` proves the reverse inequality by producing an HL global minimizer. Thus routing through \(H\) loses nothing.

- [inferred] Existence of one HL global minimizer suffices; proving every minimizer is HL is stronger. The inspected converse does the latter using a strictly decreasing concat move.

- [computed] For \(M=(2,2,2)\): there are 6 Kostant partitions but only 3 HL partitions/QIP points. Their codimensions are respectively
  \[
  \{3,4,4,5,5,8\},\qquad \{3,4,4\}.
  \]
  Hence no literal bijection with all Kostant partitions can exist.

- [computed] Exhaustive enumeration of 92 small monotone dimension vectors found no all-Kostant/HL minimum gap.

- [inferred] The all-width result is sound because the actual proof first handles monotone \(M\), then applies permutation invariance to sorted \(M\). The Adm–QIP transport would not by itself justify arbitrary unsorted \(M\).

This verdict assumes the banked `cCodim_eq_qipMin` with its displayed exact statement. I inspected its minimizer/HL proof structure, but did not independently re-prove every internal Finset lemma.

## POINT B

VERDICT: SOUND

- [computed] The right-column algebra is exact:
  \[
  \begin{aligned}
  q_u-q_{u-1}
   &= (M_u-\rho_u)-(M_{u-1}-\rho_{u-1})\\
   &= (\rho_{u-1}-\rho_u)+(M_u-M_{u-1})\\
   &=e_{u-1}+(M_u-M_{u-1}).
  \end{aligned}
  \]
  There is no sign or index error.

- [computed] In the first factor, \(j-1\le L-1\), so the last column is impossible; its boundary support can only be \(i-1=0\), namely \(i=1\). This gives \(e_{j-1}\).

- [computed] In the second factor, \(u\ge1\), so row \(0\) is impossible; its boundary support can only be \(v=L\). This gives \(e_{u-1}+M_u-M_{u-1}\). Thus the orientation is not swapped.

- [computed] Monotonicity is genuinely required for the current `ℕ`-valued `mOfE`. For the admissible example \(L=1\), \(M=(2,1)\), \(T=(0)\):
  \[
  \operatorname{diffRank}(1,1)=1,\qquad
  mOfE(1,1)=2+(1\mathbin{\dot-}2)=2.
  \]
  The right-column agreement fails, while the first-factor agreement remains \(2=2\). Monotonicity makes `Nat` subtraction cast to the signed difference. Its absence from the first agreement is harmless.

- [computed] Every `codimForm` summand uses exactly those two read families. The corner \((0,L)\) is never read: the first factor never has second index \(L\), and the second never has first index \(0\). Moreover, under admissibility it equals \(\rho_L=0\) on the `diffRank` side anyway.

- [computed] All read agreements and resulting codimension equalities held for 231 small monotone admissible \((M,T)\) pairs.

The last bridge to `Gqip` assumes the banked `codimForm_mOfE` at its monotone type; its inspected source uses precisely these two collapses.