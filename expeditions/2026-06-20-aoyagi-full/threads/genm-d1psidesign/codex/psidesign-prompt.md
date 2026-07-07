<task>
Exact block-matrix algebra question about existence of a "joint move" on a layered matrix chain.
Please reason it out independently (block-LDU / Schur-complement algebra); a short sympy check on
your own is welcome but not required. Do NOT assume any particular answer.

SETUP.
Fix an integer r >= 1 (pivot size) and core widths m_0,...,m_L >= 1 (take all m_s = m for concreteness).
An L-layer chain is a list of block matrices, layer s (s = 0..L-1):

    C_s = [[ A_s , Y_s ],
           [ Z_s , T_s ]]        A_s: r x r invertible (A_s = I + X_s, X_s small),
                                  Y_s: r x m,  Z_s: m x r,  T_s: m x m.

Full product  P = C_0 C_1 ... C_{L-1}   (block shape (r+m_0) x (r+m_L)).
Write P in blocks  P = [[P11, P12],[P21, P22]].

Two readouts on the chain:
 (R) the "regular residual"    E(chain) := ( P11 - I_r ,  P12 ,  P21 )   -- three blocks.
 (C) the "core readout"        F(chain) := product of the per-layer Schur complements
                                           S_0 * S_1 * ... * S_{L-1},   S_s := T_s - Z_s A_s^{-1} Y_s.

Everything is a germ near the DEEPEST point: all of X_s, Y_s, Z_s, T_s are analytic and vanish at the
origin (parametrise by a scalar eps: X,Y,Z,T = eps * (generic)). At eps=0 each layer is diag(I_r, 0),
P = diag(I_r, 0), E = 0.

Known Schur-complement recursion (I have verified this, take it as given):
    blockSchur(P) := P22 - P21 P11^{-1} P12  =  S_0 (I-K_1) S_1 (I-K_2) S_2 ... (I-K_{L-1}) S_{L-1}
where  K_s := Z_s (partProd(s+1)_11)^{-1} (partProd(s)_12),  partProd(j) = C_0..C_{j-1},  K_0 = 0.
Call the RHS "coreProd".

THE MOVE. I want an analytic self-map psi of the chain (edit the layer blocks, as an analytic germ
fixing the origin) that achieves BOTH of the following simultaneously:

 (B)  F(psi(chain)) = coreProd .   I.e. the plain product of the NEW per-layer Schur complements equals
      the twisted product coreProd. The natural per-layer target is to make the new layer s have Schur
      complement  S~_s = S_0 for s=0 and  S~_s = (I - K_s) S_s  for s >= 1  (so their plain product
      telescopes to coreProd). K_s, S_s are computed from the ORIGINAL chain.

 (A)  E(psi(chain)) = E(chain).    I.e. the full-product blocks (P11, P12, P21) are UNCHANGED by the move
      (only P22 / the core may change).

QUESTION (this is the whole ask):
 1. Editing a layer's blocks so that its Schur complement equals a prescribed target S~_s leaves gauge
    freedom (you may still change A_s, Y_s, Z_s and compensate T_s). Using ONLY that gauge freedom
    (i.e. holding all S~_s at the (I-K_s)S_s targets), does a choice of per-layer edits exist that makes
    (A) hold, as an analytic germ near the origin? Or is there an obstruction?
 2. If it exists: WHICH per-layer degrees of freedom are actually required to make (A) hold -- e.g. is
    editing only the "up" block Y_s enough (this suffices at L=2), or must one also edit the pivot A_s
    and/or the "down" block Z_s? Does the answer differ between scalar cores (m=1) and non-scalar (m>=2)?
 3. Give the cleanest explicit form of the required edit you can (a closed form or a layer-recursion),
    and state to what order in eps the edit starts (this controls whether D(psi - id)(0) = 0).

CONTEXT (why it matters, no need to address): this is the "Step Psi" joint move in a formalisation of the
RLCT of deep linear networks; (A) is a reg-energy-preservation germ, (B) is a core-untwisting germ. At
L=2 the known construction edits only the last layer's Y block. The worry is whether the L=2 construction
generalises or whether interior-layer core edits (needed for L>=3) break (A) irreparably.
</task>

<output_contract>
Four short sections:
 [VERDICT] "correction EXISTS (germ)" or "OBSTRUCTED", with confidence.
 [DOF] which per-layer freedoms (A_s pivot / Y_s up / Z_s down) are necessary/sufficient for (A);
        scalar vs non-scalar cores if different.
 [FORM] the cleanest explicit edit / recursion you can give, and the eps-order at which it starts.
 [CHECK] the single cheapest exact-algebra test that would confirm or refute your verdict.
Be concrete and block-algebraic. If you are unsure, say so and give the discriminating computation.
</output_contract>

<grounding_rules>
Reason from block-LDU / Schur-complement algebra. State clearly what is a proof vs a heuristic vs a guess.
Do not assume the L=2 (up-only) construction generalises -- decide it. Non-commutative matrices; mind that
S_s, K_s are matrices and the cores are rectangular in general (m_s x m_{s+1}).
</grounding_rules>
