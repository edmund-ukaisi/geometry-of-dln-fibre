<task>
Red-team TWO corner cases of a finiteness proof (Lehalleur–Rimanyi DLN formalisation). I withhold my
tentative view. WITHHOLD nothing about the math.

SETUP. Chain M=(M0,...,M_last), prod = product of layer matrices (A_i is M_i x M_{i+1}), frobSq = sum of
squares. Target proved by induction on #layers given "plain IH" hIH = box-finiteness of every SHORTER chain:
  RouteMBoxThresholdFinite(M): for c'<minAdm(M)/2, INT_{A in box} frobSq(prod M A)^(-c') < inf.
minAdm(M)=min_t (M0-t)(M1-t)+minAdm(redChain t M), redChain t M=(t,M2,...) (collapses first TWO widths).
Cut-soundness (proved): minAdm(M) <= (M0-t)(M1-t)+minAdm(redChain t M).

At a pivot cut t (a=M0-t, b=M1-t, u=t), after a measure-preserving weld+shear the per-cut integral is
  INT_{A'} INT_{x=(P,B12,C)} INT_{Gamma} (freedSchurLoss)^(-c'),
with P (uxu invertible box), B12 (uxb), C (axu), Gamma (axb); tail product Q (rows Fin u (+) Fin b, q=M_last
cols); Q_p=top u rows, Q_b=bottom b rows (BOTH are PRODUCTS of the deep layers, not free); Qtil=Q_p+P^{-1}B12 Q_b;
w=frobSq(P*Qtil)=frobSq([P|B12]*Q); freedSchurLoss = w + frobSq(C*Qtil + Gamma*Q_b).
We focus on d=min(a,b)=1, b=1 (Q_b a single 1xq row, Gamma=gamma an a-vector), a>=u.

ESTABLISHED (a prior red-team, PROVEN): dispatching by ABSOLUTE sigma_min(Qtil)<delta is UNSOUND — the radial
corner {Qtil->0 radially, all singular values comparably small, Q_b=O(1)} (positive measure) gets routed to the
"bounded" branch (INT_Gamma <= w^{-c'} vol, drops the corank charge ab/2) whose majorant DIVERGES on the window
c' in (minAdm((u,M1,M2,...))/2, minAdm(M)/2). FIX (PROVEN for the FREE arity-3 case M=(4,3,2)): a RADIAL-PEEL
sub-branch — polar blow-up Qtil=rho*Theta (rho=||Qtil||, Theta in sphere); on the sphere the pivot coefficient
||P*Theta||^2 >= sigma_min(P)^2 > 0 (P injective, Theta != 0; does NOT need Theta full rank), so the peel
(gammaAtom, R=Q_b) applies uniformly and the radial integral INT rho^{uq+1-2c'} drho converges for c'<(uq+2)/2 =
full minAdm(M)/2, KEEPING the corank charge. Banked: gammaAtom (INT_Gamma (w+frobSq(Gamma R+S))^-c' =
det(RR^T)^{-p/2} Cresid (w+frobSq(S(I-P_R)))^{-(c'-pq/2)}, R full row rank, w>0, c'>pq/2), and _inner_peel emits
the CORANK Gram ||Q_b||^{-a}=det(Q_b Q_b^T)^{-a/2} (NOT the pivot Gram). The socket Gamma-domain is a finite box
(so gammaAtom, stated over all of R^{ab}, is an UPPER BOUND).

TWO CORNERS TO VERIFY before this goes to a formaliser:

CORNER (i) — DEEPER ARITY, Q_p a PRODUCT. The radial-peel's shell count INT rho^{uq-1} drho assumed Qtil is a
FREE coordinate (true only at arity 3, where the tail is a single free layer). For arity >= 4, Q_p (hence Qtil)
is a PRODUCT of deep layers, so the corner {Qtil->0} is reached via a deep-tail/front cancellation, and the
shell measure {||Qtil||~eps} in deep-param space is the pushforward density of the deep product, NOT eps^{uq-1}.
QUESTION: does the radial-peel + hIH still reach the FULL minAdm(M)/2 at deeper arity? Specifically: (a) is the
KEY sphere bound ||P*Theta||^2>=sigma_min(P)^2>0 arity-independent (P is always the uxu pivot outer-variable)?
(b) does the residual pivot term w^{-(c'-ab/2)}=frobSq([P|B12]*Q)^{-(c'-ab/2)} reduce to hIH(redChain u M) at the
shifted charge (cut-soundness gives c'-ab/2 < minAdm(redChain u M)/2)? (c) does the deep-tail degeneracy sub-corner
(Qtil->0 WITH Q_p near its own rank-drop) get absorbed by hIH(redChain u M), or can it create a WORSE shell
measure that breaks the threshold? Give the cleanest discriminating check for (c).

CORNER (ii) — Q_b -> 0 (the corank tail row vanishes). The peel emits ||Q_b||^{-a}; near {Q_b=0} (codim q, Q_b a
product row) this weight -> inf, but the TRUE INT_Gamma -> (w+frobSq(C*Qtil))^{-c'} vol (finite: Gamma decouples
as Q_b->0). So the peel is a LOOSE upper bound there. QUESTION: (a) how is {Q_b->0} correctly handled — by a
bounded-in-Gamma branch (drop corank, <= w^{-c'} vol, then reduce w via hIH at the FULL c', i.e. pivot-only
threshold minAdm((u,M1,M2,...))/2), and does that pivot-only threshold SUFFICE near {Q_b->0} (where the corank
carries no charge)? Or (b) is {Q_b->0} better seen as a rank-drop of the EXTENDED tail Qhat=[Qtil; Q_b] ((u+1)xq):
note frobSq(C*Qtil+gamma(x)Q_b)=frobSq([C|gamma]*Qhat), [C|gamma] a FREE a x(u+1) block, so the whole corank is a
Wishart of the free [C|gamma] against Qhat, and {Q_b->0} is a rank-(u+1)->u drop of Qhat handled by a joint
(r,s) source-incidence atlas WITHOUT any ||Q_b||^{-a} artifact? Adjudicate which resolution is sound, and whether
there is a c' window near {Q_b->0} that diverges under (a) [the pivot-only cap] that only (b) [the joint atlas]
closes. Cheapest discriminating computation.
</task>

<output_contract>
  Two sections "Corner (i)" and "Corner (ii)". Each: answer sub-parts (a),(b),(c) tersely; PROVEN/ARGUED/GUESS
  per claim; a one-line VERDICT {ABSORBED-NATIVE / NEEDS-EXTRA-MECHANISM / GAP}. If NEEDS-EXTRA or GAP, name the
  minimal missing mechanism precisely (dims + what it asserts). For Corner (ii), state explicitly whether
  resolution (a) [bounded-in-Gamma, pivot-only cap] suffices or whether (b) [joint [C|gamma] atlas over the
  extended tail Qhat] is required. End with the single cheapest discriminating computation per corner. Concrete
  dims/charges; no hedging.
</output_contract>

<grounding_rules>
  Reason from the exact objects. hIH is plain (undecorated) box-finiteness of shorter chains only. A weight
  det(product-Gram)^(-w) on the reduced box is NOT absorbable by plain hIH. "Absorbed-native" requires either a
  free-box qbox at a single level, or a determinantal blow-up whose exceptional Jacobian is a pure monomial
  reducing each stratum to plain hIH. State inference vs fact; do not rubber-stamp.
</grounding_rules>
