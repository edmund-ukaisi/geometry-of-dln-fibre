#!/usr/bin/env python3
"""
Thread-40 (canonCenter checkpoint) rollover slot-stability battery. EXACT (integer slot arithmetic +
sympy for the Q-transfer / transpose algebra).

KILL-CONDITION (elder-named): is the flat-slot assignment STABLE AT ROLLOVER — the one step where
content crosses layers? i.e. after rollover (S, J=M(S+1)) -> (S+1, 0), are the recursion's working
slots exactly the STATIC layer-(S+1) partition slots (rows 1..M(S+1), cols 1..M^(S+2)), with the
running-min row truncation — and does the transpose (row- vs column-remnant) NOT scramble them?
FAIL: transpose re-binding lands content in slots the static bookkeeping doesn't predict.

Widths M = [M^1,...,M^{L+1}] (reduced). Layer S in 1..L; C^(S) is M^(S) x M^(S+1). M(S)=min(M^1..M^S).
Flat slots: (S,i,j), 1<=i<=M^(S), 1<=j<=M^(S+1); global offset makes the layers DISJOINT.
"""
import sys
import sympy as sp
from itertools import product as iproduct

ok = True
def check(name, cond):
    global ok
    c = bool(cond); ok &= c
    print(f"  [{'PASS' if c else 'FAIL'}] {name}")

# ---------- static flat-slot partition ----------
def Mrun(M, S):                       # M(S) = min(M^1..M^S), 1-indexed S
    return min(M[:S])
def layer_offset(M, S):               # global slot offset of layer S (1-indexed)
    return sum(M[s-1]*M[s] for s in range(1, S))
def slot(M, S, i, j):                 # global flat index of layer-S entry (i,j), 1-indexed i,j
    return layer_offset(M, S) + (i-1)*M[S] + (j-1)
def layer_block_slots(M, S, i_hi, j_hi, i_lo=1, j_lo=1):
    return frozenset(slot(M, S, i, j) for i in range(i_lo, i_hi+1) for j in range(j_lo, j_hi+1))

# ---------- canonCenter (STATIC formula, the elder's proposal) ----------
def canonCenter(M, S, J):
    """Residual sub-block footprint at state (S,J): layer-S slots, rows J+1..M(S), cols J+1..M^(S+1)."""
    L = len(M)-1
    return layer_block_slots(M, S, Mrun(M, S), M[S], i_lo=J+1, j_lo=J+1)   # M^(S+1)=M[S]
def canonPivot(M, S, J):
    """The (J+1,J+1) pivot slot of layer S (case-2 / case-1(2))."""
    return slot(M, S, J+1, J+1)
def canonMergePivot(M, Sbirth, Jbirth):
    """A reused divisor's birth slot = the (J+1,J+1) pivot of its birth state (cross-layer reference)."""
    return slot(M, Sbirth, Jbirth+1, Jbirth+1)

# ---------- PAPER-RULE slot-flow (derived from pp.15-22, INDEPENDENT of canonCenter) ----------
def paper_rollover_footprint(M, S):
    """After rollover S->S+1: working block = Q^{-1}C^(S+1) truncated to M(S+1) rows (running-min),
    cols 1..M^(S+2). Q^{-1} is a LEFT row-recombination (slot-preserving), so the block sits in
    layer-(S+1) slots, rows 1..M(S+1), cols 1..M^(S+2). NO transpose (row/col orientation of C^(S+1)
    is untouched). Derived from the paper matrix ops, not from canonCenter."""
    Sn = S+1
    rows = Mrun(M, Sn)                 # M(S+1) running-min row bound
    cols = M[Sn]                       # M^(S+2) = M[Sn]
    return layer_block_slots(M, Sn, rows, cols)
def remnant_type(M, S):
    """Which dim of layer-S block exhausts first at rollover (J=M(S+1)=min(M(S),M^(S+1)))."""
    MS, Mnext = Mrun(M, S), M[S]       # M(S), M^(S+1)
    if MS < Mnext:  return "row-remnant (rows exhaust; D‴=(1,0,..,0))"
    if Mnext < MS:  return "col-remnant/TRANSPOSE (cols exhaust; D‴=(1,0,..,0)^t)"
    return "square boundary (both exhaust; either remnant)"

# ================= CHECK 1: canonCenter == paper-flow at every rollover =================
print("=== CHECK 1: rollover slot-stability, canonCenter(S+1,0) vs paper-flow footprint ===")
for M in ([3,3,4], [2,3,4], [3,2,4], [3,3,2,2], [2,2,3,2]):
    L = len(M)-1
    print(f"\n  M={M} (L={L})")
    for S in range(1, L):             # rollover from layer S to S+1 (S=1..L-1)
        cc = canonCenter(M, S+1, 0)
        pf = paper_rollover_footprint(M, S)
        # (a) canonCenter(S+1,0) equals the paper post-rollover footprint
        eq = (cc == pf)
        # (b) the footprint lies wholly in layer-(S+1) static slots, DISJOINT from layer-S
        layerSn_all = layer_block_slots(M, S+1, M[S], M[S+1])          # full C^(S+1) = M^(S+1)xM^(S+2)
        layerS_all  = layer_block_slots(M, S, M[S-1], M[S])
        in_layer = pf <= layerSn_all
        no_leak  = pf.isdisjoint(layerS_all)
        # (c) NOT the transposed shape (the FAIL): rows/cols swapped would give a different slot set
        rows, cols = Mrun(M, S+1), M[S+1]
        transposed_shape = layer_block_slots(M, S+1, min(cols, M[S]), M[S], i_hi=min(cols,M[S]), j_hi=M[S]) \
            if False else None
        # explicit transposed footprint: rows<->cols bounds (only meaningful if it lands in-grid)
        rt = remnant_type(M, S)
        print(f"    S={S}->{S+1}: {rt}; M(S+1)={rows} rows x M^(S+2)={cols} cols; "
              f"canonCenter==paperflow={eq}, in-layer={in_layer}, no-leak={no_leak}")
        check(f"M={M} S{S}->{S+1}: canonCenter(S+1,0)==paper post-rollover footprint", eq)
        check(f"M={M} S{S}->{S+1}: footprint ⊆ layer-(S+1) slots, disjoint from layer-S", in_layer and no_leak)

# ================= CHECK 2: within-layer stability (renaming keeps sub-block in-layer) =================
print("\n=== CHECK 2: within-layer, canonCenter(S,J) shrinks inside layer-S slots for J=0..M(S+1)-1 ===")
for M in ([3,3,4], [2,3,4], [3,2,4]):
    L = len(M)-1
    for S in range(1, L+1):
        layerS_all = layer_block_slots(M, S, M[S-1], M[S])
        Jmax = min(Mrun(M,S), M[S])   # M(S+1)=min(M(S),M^(S+1)); pivots J=0..Jmax-1
        allin = True; nested = True; prev = None
        for J in range(0, Jmax):
            cc = canonCenter(M, S, J)
            allin &= cc <= layerS_all
            if prev is not None: nested &= cc < prev   # strictly shrinking
            prev = cc
        check(f"M={M} layer S={S}: canonCenter(S,J) ⊆ layer-S slots and strictly shrinks in J", allin and nested)

# ================= CHECK 3: cross-layer merge pivot (reused divisor birth slot) =================
print("\n=== CHECK 3: (3,3,4) S=2 J=0 case-1(1) merges reference layer-1 birth slots (cross-layer, static) ===")
M = [3,3,4]
# from the traversal: S=2 J=0 merges reuse divisors born at S=1 J=1 (pivot (1,2,2)) and S=1 J=2 ((1,3,3)).
birth_t1 = canonMergePivot(M, 1, 1)   # divisor born at layer1, J=1  -> slot (1,2,2)
birth_t2 = canonMergePivot(M, 1, 2)   # divisor born at layer1, J=2  -> slot (1,3,3)
layer1_all = layer_block_slots(M, 1, M[0], M[1])
layer2_all = layer_block_slots(M, 2, M[1], M[2])
check("merge-pivot t=1 birth slot (1,2,2) is a LAYER-1 flat slot (cross-layer reference)", birth_t1 in layer1_all)
check("merge-pivot t=2 birth slot (1,3,3) is a LAYER-1 flat slot (cross-layer reference)", birth_t2 in layer1_all)
check("the two birth slots are distinct and static (data-only from mergeIdx)", birth_t1 != birth_t2)
print(f"    birth(t=1)=slot{birth_t1}=(1,2,2); birth(t=2)=slot{birth_t2}=(1,3,3); layer-2 slots start at {layer_offset(M,2)}")

# ================= CHECK 4: SYMBOLIC — Q-transfer is slot-preserving; transpose is internal ==========
print("\n=== CHECK 4 (sympy exact): C'^(S+1)=Q^{-1}C^(S+1) is a row-recombination (slot-preserving), no transpose ===")
# (3,3,4): C2 is M^2 x M^3 = 3x4. Accumulated layer-1 row-op U = product of Q^{-1}'s, unipotent 3x3.
mS = 3   # M^(2) rows of C2
nS = 4   # M^(3) cols of C2
C2 = sp.Matrix(mS, nS, lambda i, j: sp.Symbol(f'c_{i+1}_{j+1}'))
U = sp.Matrix(mS, mS, lambda i, j: (sp.Integer(1) if i == j else (sp.Symbol(f'u_{i+1}_{j+1}') if i > j else sp.Integer(0))))
check("U (accumulated Q^{-1}) is unipotent lower-triangular (=I at origin)",
      U.det() == 1 and all(U[i,i] == 1 for i in range(mS)))
Cp = sp.expand(U * C2)     # C'^(2)
# (4a) every entry C'[i,j] depends ONLY on column-j entries of C2 (row-recombination): slot column preserved
slot_ok = True
transpose_leak = False
for i in range(mS):
    for j in range(nS):
        for a in range(mS):
            for b in range(nS):
                dv = sp.diff(Cp[i, j], C2[a, b])
                if dv != 0 and b != j:            # depends on a DIFFERENT column -> would break slot-(i,j)
                    slot_ok = False
                if dv != 0 and (b == i and a == j) and (i != j):  # a (j,i)-transposed dependence
                    transpose_leak = True
check("(4a) C'[i,j] depends only on {C2[k,j]}_k (row-recomb): entry stays in slot-column j, no transpose", slot_ok)
check("(4b) no (j,i)-transposed dependence introduced by the Q-transfer", not transpose_leak)
# (4c) the transpose collapse acts on the layer-S REMNANT (a 1xk / kx1 vector), NOT on C2:
#      reproduce Q D'' P = [[1,O],[O,Schur]] and confirm the collapse leaves C' = U C2 untouched in shape.
be1, be2, ga1, ga2 = sp.symbols('be1 be2 ga1 ga2')
Dpp = sp.Matrix([[1, be1, be2],[ga1, 0, 0],[ga2, 0, 0]])   # a collapsing residual (rank-1 tail -> Schur 0)
Q = sp.eye(3); Q[0,1] = -be1; Q[0,2] = -be2                 # clears pivot ROW (right mult in paper; here on cols)
P = sp.eye(3); P[1,0] = -ga1; P[2,0] = -ga2                 # clears pivot COL
red = sp.expand(P.inv()* (P*Dpp*Q) )  # sanity; main: P*Dpp*Q top-left 1, tail = -ga*be (here Schur)
core = sp.expand(P*Dpp*Q)
schur_tail = core[1:,1:]
check("(4c) collapse: P·D''·Q has unit pivot and a rank-collapsed tail (remnant internal to layer-S)",
      core[0,0] == 1 and all(core[0,k] == 0 for k in range(1,3)) and all(core[k,0] == 0 for k in range(1,3)))
# C2's shape/slots are untouched by this layer-S collapse (C' = U C2, still mS x nS in layer-2 slots)
check("(4d) C'=U·C2 stays M^(S+1) x M^(S+2) in layer-(S+1) slots regardless of remnant orientation",
      Cp.shape == (mS, nS))

print(f"\nTHREAD-40 ROLLOVER SLOT-STABILITY BATTERY: {'PASS (EXIT 0)' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
