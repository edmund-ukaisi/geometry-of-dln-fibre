<task>
Adjudicate two questions about an exact matrix-integral reassembly (RLCT / real-log-canonical-threshold
finiteness). Argue whichever way the algebra points; do NOT assume the reassembly is clean or broken.
This is for a deep-linear-network zero-fibre RLCT recursion. Answer with exact algebra (Wishart /
Selberg-type matrix integrals, coarea/Jacobian, local-zeta / determinantal-variety lct).
</task>

<setup>
Fix a "chain" M = (M0, M1, M2, ..., M_last) of positive integer widths (>=3 widths). Define n = M_last.
A cut u (1 <= u <= min(M0,M1)); set a = M0 - u, b = M1 - u.
Deep factor: Z = A_2 A_3 ... A_{last-1}, an (M2 x n) matrix (product of the deep layers), generic rank
k = min(M2,...,M_last) =: dtm.  "Good branch" means dtm <= M1 and (binding cut) a+b <= dtm - 1 < dtm.
Reduced chain M' = (u, M2, M3, ..., M_last) — ONE FEWER layer.  A0' is the reduced first layer (u x M2).
- Q_p = A0' Z          (u x n)   [the "pivot rows"; = product of reduced chain]
- A_cor : b x M2 (free box);  Q_b = A_cor Z   (b x n)   [the "corank rows"]
- hsQ = (Q_p ; Q_b), an (u+b) x n matrix.  Front block T = [P | B12], plus a transverse block C.
Front loss (after an exact Gamma-peel that produces the charge det(Q_b Q_b^T)^{-a/2} and shifts the
exponent c' -> q = c' - ab/2):
    frontLoss(z, A_cor) = ∫_{front x=(P,B12,C)} ( E_top + E_tr )^{-q},
    E_top = ||P Q_p + B12 Q_b||_F^2,   E_tr = ||C Q_p (I - Πb)||_F^2,  Πb = Q_b^T (Q_b Q_b^T)^{-1} Q_b.
The FULL LHS to reassemble:
    G = ∫_{z=(A0',deep params)} ∫_{A_cor∈box} det(Q_b Q_b^T)^{-a/2} · frontLoss(z, A_cor).
The claimed target ("comparator"):
    Comp(q) = ∫_{z'=(A0', deep params)} ∫_{v0∈[0,1]} |v0|^{minAdm(M')-1-2q} · ( ||A0' Z||_F^2 )^{-q},
where minAdm(M') is a combinatorial value; Comp(q) is FINITE for q < minAdm(M')/2 (an induction hypothesis
on the shorter chain M', taken as GIVEN). The descent needs a CONSTRUCTIVE domination
    G  <=  K · Comp(q)     with K < ∞ per fixed q < (minAdm(M) - ab)/2 =: T1q,
where "constructive" means the bound must be derivable so that Comp(q) finite ⟹ G finite (NOT the reverse;
using "G finite" as an input would be circular — G finite to T1q is separately known but circular to invoke).
Note minAdm(M) <= ab + minAdm(M') (a proven gate), so T1q <= minAdm(M')/2.
</setup>

<questions>
Q1. Compute the "A_cor-Wishart" integral in isolation:  I(Z) = ∫_{A_cor∈box} det((A_cor Z)(A_cor Z)^T)^{-a/2} dA_cor.
   Give the EXACT dependence on Z: which determinant of Z (full M2xM2 Gram Z Z^T, or the k x k Gram, or
   pseudo-determinant of Z Z^T) and to which EXACT power, and the exact convergence criterion. Be careful
   about the case M2 > k (Z rank-deficient as an M2 x M2 Gram).

Q2. The MAIN question. In G, both the charge AND the front loss depend on A_cor (through Q_b = A_cor Z),
   and the loss/charge depend on z only through Q_p = A0' Z and Q_b = A_cor Z (which lie in row(Z)).
   Reduce G by a change of variables (row(Z) coordinates / coarea). Does G reassemble as
       G  =  ∫_{deep} [some power of a Z-Gram determinant] · [a leaf-type integral over A0', A_cor, front]
   and, after bounding the leaf-type integral by the leaf comparator ||A0' Z||^{-2q}, does an UNCOMPENSATED
   deep-Gram factor det(...)^{-b/2} remain that is NOT present in Comp(q)? If so, is that residual
   (i) always bounded/harmless, (ii) integrable for some (a,b) but not others (which?), or (iii) does the
   constructive domination G <= K·Comp still close by some mechanism that avoids the residual? Distinguish
   the case where Z is a scalar/identity (M2 = n, single trivial deep layer) from a genuine deep product.
   State clearly whether the CONSTRUCTIVE (non-circular) domination onto Comp as written holds for a
   genuine deep factor, and if not, what the correct comparator loss should carry.

Q3. σ-bank / biquadratic corner. On the stratum where the incidence coordinate W = Q_p·N has rank 0 (the
   "corner"), the residual front loss is biquadratic g(Y,W) = ||Y·W||_F^2 (degree 2 in Y = (P;C), degree
   2 in W), plus an H̃-fibre term ||H̃||^2. There is a banked lemma `twoBlock_radial_le`:
       ∫_{ball_du × ball_dv} (κ²||u||² + σ²||v||²)^{-q} <= C·σ^{-α'},  C σ-independent, on 0<σ<=B,
       for max(0,2q-du) < α' < dv.
   Question: can the corner ∫_{H̃,Y,W}(||H̃||² + ||Y W||²)^{-q} be closed by twoBlock_radial_le + an outer
   radial integral over σ (fed with σ = ||W|| from an intrinsic polar-in-W, and the H̃-fibre as the
   κ-stable block), WITHOUT any externally-supplied orthonormal frame / Loewner floor on the front pivot?
   Or is such a frame genuinely required to put g into two-radius form? Identify du, dv, the σ-charge α'
   gate, and whether the outer W-radial ∫ σ^{dW-1-α'}dσ absorbs it (dW = dim W).
</questions>

<output_contract>
For each question: a verdict line (FACT / INFERENCE), the exact powers/criteria, and the key algebraic
identity. For Q2 explicitly: does an uncompensated det(Z-Gram)^{-b/2} residual survive, yes or no, and is
the constructive domination onto Comp (loss = ||A0' Z||^2, no deep-Gram factor) sound for a genuine deep
product? For Q3: (a) frame DROPPABLE or (b) frame NEEDED, with the α' gate.
</output_contract>

<grounding_rules>
Exact algebra only for load-bearing claims. Wishart/matrix-T integrability = determinantal-variety local
integrability (lct of det of a b×k Gram is (k-b+1)/2). Coarea Jacobian of a linear surjection A: R^m->R^n
(m>=n) is sqrt(det(A A^T)). Distinguish a FIXED-exponent weight (det^{-b/2}, independent of q) from a
q-dependent loss. Keep pseudo-determinant vs full determinant distinct when the Gram is rank-deficient.
</grounding_rules>
