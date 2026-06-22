# OBSTRUCTION CATALOGUE — synthesis of the three confounds + scoped conditions.
print("""
CONFOUND (i) MISSED/SPURIOUS STRATUM:
  - MISSED: NO. recursion_branches == Adm on 12 cases (incl non-square, L=3,4). Each node's
    first-factor rank governs t_j; Schur forces t_j<=t_{j-1}; product-target caps t_j<=M^{j+1}.
    The complete adm nesting is realized. Later-factor rank drops appear as the REDUCED first
    factor's rank at the next node (rank(C1..Cj) = reduced-first-factor rank). NOT missed.
  - SPURIOUS: the codim-1 raw stratum {rank C1=1} is a candidate ratio-1/2 divisor BUT is
    generically OFF {prod=0} (P(prod!=0 | rank C1=1)=1.0): core is a UNIT there, no threshold
    divisor. The blow-up divisor's (k,h) reads core∘φ=u²·resid + Jac=u^{c-1}; threshold-relevant
    only where E meets the strict transform of {prod=0} = an admissible stratum, codim Mval>=minAdm.
  => NO undershoot. SCOPED CONDITION C1: read every exceptional (k,h) from the FULL pulled-back
     density on the strict transform of {prod=0}, NOT the raw first-factor codim.

CONFOUND (ii) MULTIPLICITY-2 DIVISOR:
  - k_E = 1 on EVERY blow-up: first factor (all widths 2/3/4, depths L=2,3), step-2 residual,
    terminal cone -- all u-order EXACTLY 2. Composed blow-ups give SEPARATE k=1 divisors
    (u1²·u2²·…), never one u^4 (k=2). The (x²+y²)² trap needs a center where the strict transform
    is a SQUARE of a SoS; the matrix-chain SoS never produces this along a coordinate stratum
    (each factor vanishes to order exactly 2 transverse to a coordinate center).
  => NO k_E>=2 divisor. SCOPED CONDITION C2: every center a COORDINATE subspace (the det-1 Schur
     straighten is what guarantees this -- #121); a non-coordinate center could break order-2.

CONFOUND (iii) NON-TERMINATION / STUCK:
  - ΣM drops by exactly 2 per Schur step; depth L drops by 1 per node; base L=1 smooth block.
    No stuck/non-dropping chain over 10+ shapes incl width-1 pinches.
  - WIDTH-1 / PINCH layers: the chain SEPARATES (‖C1 C2‖²=‖C1‖²‖C2‖² for rank-1 middle), a FUBINI
    PRODUCT, not a coupled blow-up. (3,1,3): one C1-blow-up gives u²·(Σd²)·unit -- residual is a
    FRESH smooth block needing its own resolution. The first-factor blow-up does NOT close as a
    single chain descent here.
  => TERMINATES, value correct (minAdm/2), BUT mechanism differs. SCOPED CONDITION C3: the
     recursion must BRANCH on layer structure -- blow-up for coupled layers, Fubini product-min
     for separating (width-1/pinch) layers. A naive 'always blow up first factor' STALLS at an
     empty Schur complement (width-1).

THIN-PRODUCT (g34-g35 subtlety, re-audited):
  - (4,3,2) origin: gen-Jacobian/Hessian rank 8 < Mval 12. The blow-up uses the GEOMETRIC codim
    (Mval=12, exact: {C1=0} is 12 coordinate eqns), h=11, ratio 6=Mval/2. The gen-Jac rank is the
    loss 2-jet rank (different object). SCOPED CONDITION C4: read h from the GEOMETRIC codim
    (=Mval), NOT the generator-Jacobian rank.

VERDICT: CLEAN ROUTE HOLDS for the VALUE rlct=½·minAdm Mval. No confound breaks it. Four scoped
conditions (C1-C4) an implementation must respect; all are construction-discipline, not math walls.
""")
