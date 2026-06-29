1. **Observed-from-the-given-facts:** \(A_k=\begin{bmatrix}C_{k+1}-N_kW_k\\ W_k\end{bmatrix}\), so the assembly step is layer-local and has no cross-boundary products. **Inference:** in a square work-coordinate layout, the telescope is realized by the factors
\[
F_{\mathrm{work}}
=U_0\circ G_1\circ U_1\circ G_2\circ\cdots\circ G_{L-1}\circ U_{L-1}\circ G_L
\]
with rightmost factor first. Here \(G_L\) writes \(P_{L-1}=uR_{\mathrm{fin}}=C_L\); \(G_k\) writes \(P_{k-1}=B_k[I\ N_k]+uR_k=C_k\); and \(U_k(P_k,N_k,W_k)=(P_k-N_kW_k,N_k,W_k)\), so the final \(A_k\)-slot is \(\begin{bmatrix}P_k-N_kW_k\\W_k\end{bmatrix}\).

2. **Inference:** the running-output subtlety is not a mathematical obstruction if the layout is chosen so that \(G_{k+1}\) writes \(C_{k+1}\) into the top slot \(P_k\) before \(U_k\) fires, while \(N_k\) and \(W_k\) remain in live slots. **But:** \(\phi_{\mathrm{Gen}}\) as written is not naturally an endomorphism of the labelled raw coordinates \((B,N,W,R,u,R_{\mathrm{fin}})\) into labelled output coordinates \((A_0,\dots,A_{L-1})\). An honest self-map statement needs a fixed linear reindex/layout identification, or equivalently
\[
\phi_{\mathrm{Gen}}=\rho_{\mathrm{out}}\circ F_{\mathrm{work}}\circ \rho_{\mathrm{in}}.
\]
If the work layout is declared as the flat coordinate order from the start, the reindex is just bookkeeping; without it, the coordinate names do not match.

3. **Observed-from-the-given-facts:** the only polynomial identities needed are local: \(G_k\) computes \(C_k\), and \(U_k\) computes \(A_k\) from \(C_{k+1},N_k,W_k\). **Inference:** correctness is proved by backward induction with invariant: after processing layers \(>k\), their \(A_j\)-slots are final, \(P_k=C_{k+1}\), and the raw slots needed for layers \(\le k\) are still live. The one global fact still needed is a static no-alias/read-write support lemma: the chosen layout must ensure each factor touches only its declared block and does not overwrite a still-live input or finalized output. This is case **(b)**: a clean per-layer induction plus a true, finite support-disjointness check; it is not irreducibly prefix-invariance-shaped.

4. **Derived from the definitions:** no width pattern makes additive separability fail; \(A_k=\begin{bmatrix}C_{k+1}-N_kW_k\\W_k\end{bmatrix}\) holds uniformly, with zero-size blocks harmless. **Inference:** the construction breaks only on coordinate logistics: non-square parameter/output dimension, or a layout with slot contention. The minimal visible obstruction is a live \(N_k\) sharing the slot that must already hold \(C_{k+1}\) or \(W_k\) when \(U_k\) fires; at the left edge this is especially exposed if \(c_0>0\) and no carrier slot for \(N_0\) is reserved. With a square no-alias layout, there is no further multilinear obstruction.

VERDICT: WITNESS: sound non-prefix proof structure exists (backward in-place telescope induction with static support-disjointness).