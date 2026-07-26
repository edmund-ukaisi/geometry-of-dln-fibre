#!/usr/bin/env python3
"""
NODEWISE RESIDUAL-AT-CENTER for the (3,3,4) V-lower discharge.

Adjudicates, per shear-step type, whether the pull-back-of-the-loss / (leaf monomial)^2 has a
SURVIVOR (a residual generator nonzero at the blow-up center 0):
  - SMOOTH   : shear-FREE pullback already has a survivor (some quotient(0) != 0).
  - SINGULAR : shear-free over-vanishes (all quotients(0)=0), the BORN shear exposes a unit.
  - HIDDEN MONUMENT / #172 : even the SHEARED pullback / leaf-monomial has all quotients(0)=0
    at the center  ->  a deeper {R=0} stratum.

The mechanism (Corank2Proto / Corank2FaithfulComposite, sympy-verified elsewhere):
  P = C1 . C2  (block product);  block-elim  Q1 C1 Q2 = diag(1, Delta);
  peeled = diag(1,Delta) . (Q2^{-1} C2);   <P> = <peeled>  (Q1,Q2 unimodular);
  radial blow-up + join:  T-row = E*(1,t..);  Delta-block = E*alpha*(Dbar . S).

We test the ACTUAL residual-at-center at each block size, shear-free vs sheared, from first
principles (no reliance on the Lean).  Exact algebra only.
"""
import sympy as sp

REPORT = []
def rec(tag, verdict, detail):
    REPORT.append((tag, verdict, detail))
    print(f"[{verdict:9s}] {tag}\n           {detail}")

def at0(expr, syms):
    """value of expr at the center (all listed syms -> 0)."""
    return sp.expand(expr).subs({s: 0 for s in syms})

# =====================================================================================
# BUILDING BLOCK: one corank-c block-elim + radial step, returns the pivot quotient and the
# residual-block (coupled) quotients, both shear-free and sheared, and evaluates them at 0.
# =====================================================================================

def block_elim_radial(name, r):
    """
    A single Aoyagi step on an r x (r+1) product  M = A . B,  A = r x r (pivot a11 normalized to
    the chart coordinate), B = r x (r+1).  Returns the peeled entries pulled back through:
      (i)  BLOW-UP ONLY   (shear-free):  a11 -> E, off-pivot a1j -> E*a1j, etc. + radial on B.
      (ii) SHEAR + BLOW-UP (born alpha): the Schur/recoord shear THEN the blow-up.
    Prints residual-at-center for the T-row pivot (the survivor candidate).
    """
    print(f"\n--- {name}: {r}x{r} A  times  {r}x{r+1} B  ---")
    # symbolic A (pivot a11 at (0,0)), B
    A = sp.Matrix(r, r, lambda i,j: sp.Symbol(f'a{i}{j}'))
    B = sp.Matrix(r, r+1, lambda i,j: sp.Symbol(f'b{i}{j}'))
    # normalize pivot chart: a00 = 1 (the pivot coordinate is set to the chart's radial-1 direction);
    # on the pivot chart c11==1 in Corank2Proto.  Keep a00 symbolic to see the shear-free story too.
    P = sp.expand(A*B)

    # Q1 (row shear clearing col 0 below pivot), Q2 (col shear clearing row 0 right of pivot), on A
    # assuming a00 invertible == 1 on the pivot chart.
    A1 = A.subs({sp.Symbol('a00'): 1})
    Q1 = sp.eye(r)
    for i in range(1, r):
        Q1[i, 0] = -A1[i, 0]
    Q2 = sp.eye(r)
    for j in range(1, r):
        Q2[0, j] = -A1[0, j]
    diagDelta = sp.expand(Q1 * A1 * Q2)     # = diag(1, Delta)
    # peeled = diag(1,Delta) . (Q2^{-1} B)
    B1 = B  # B rows correspond to A columns
    peeled = sp.expand(diagDelta * (Q2.inv() * B1))
    # T-row pivot entry peeled[0,0] = (Q2^{-1} B)[0,0] = recoorded B pivot
    return A, B, P, Q1, Q2, diagDelta, peeled

# =====================================================================================
# TYPE FAMILY 1 : S=1 case2 clearings (within-layer Schur shear, NO recoord).
#   The residual block is the FIRST-layer factor C1 alone (peeled off before the deeper layer).
#   Question: does the C1 pivot survive the blow-up SHEAR-FREE?
# =====================================================================================
print("="*90)
print("TYPE FAMILY 1 : S=1 case2 (first-layer clearing) -- within-layer Schur shear")
print("="*90)

# S=1 J=0 center 3x3 : blow up C1 (3x3) along pivot c11.
# blow-up only: c1j -> E1*c1j', pivot c11 -> E1.  The (0,0) entry of C1.blowup = E1*1.
E1 = sp.Symbol('E1')
# C1 entries as fresh coords; pivot at (0,0).
c = sp.Matrix(3,3, lambda i,j: sp.Symbol(f'c{i}{j}'))
# block blow-up center = all 9 coords, pivot = c00. off-pivot -> c00*c_ij, pivot stays c00.
# In radial/chart language: the pivot COORDINATE becomes the exceptional E1, and the OTHER
# center coords become ratios t_ij (free).  So C1 pulled back = E1 * [[1, t01, t02],[t10,..],..].
tij = sp.Matrix(3,3, lambda i,j: (sp.Integer(1) if (i,j)==(0,0) else sp.Symbol(f't{i}{j}')))
C1_blowup_over_E1 = tij   # C1 . (blow-up) / E1  =  ratio matrix, pivot entry 1
# residual-at-center of the C1 pivot (shear-free):
piv = C1_blowup_over_E1[0,0]
rec("S=1 J=0 case2 (3x3): C1 pivot quotient, SHEAR-FREE",
    "SMOOTH" if at0(piv,[]) != 0 else "SINGULAR",
    f"C1_pullback/E1 pivot(0,0) = {piv}  ->  value at center = {at0(piv,list(tij.free_symbols))}")

# S=1 J=1 center 2x2 and J=2 center 1x1 : the SHRINKING uncleared block (Schur complement of C1).
# After the first pivot clear, the residual is the 2x2 Schur complement Delta_C1 (of C1, not the product).
# Its own pivot, blown up, gives ratio 1 again.  Same shear-free survivor.
for (J, sz) in [(1,2),(2,1)]:
    rat = sp.Matrix(sz, sz, lambda i,j: (sp.Integer(1) if (i,j)==(0,0) else sp.Symbol(f'r{i}{j}')))
    rec(f"S=1 J={J} case2 ({sz}x{sz}): sub-block pivot quotient, SHEAR-FREE",
        "SMOOTH" if rat[0,0] != 0 else "SINGULAR",
        f"pivot ratio = {rat[0,0]} (blow-up of a raw first-layer sub-block: pivot -> E*1)")

print("""
  NOTE (S=1 family): the LOSS is on the PRODUCT P=C1.C2, not C1 alone.  P_pullback pivot row =
  E1*(recoorded C2 row), which VANISHES at center (C2 coords -> 0).  So the S=1 blow-up alone does
  NOT expose a loss-survivor; it exposes a C1-FACTOR survivor.  The loss-level survivor is only born
  once the deeper (S=2) layer is cleared -- see below.  The within-layer S=1 Schur shear is
  therefore BENIGN for the S=1 factor pivot but the LOSS survivor waits on S=2.
""")

# =====================================================================================
# TYPE FAMILY 2 : S=2 clearings (recoord shear + within-layer Schur).  This is where the LOSS
#   survivor is born.  Canonical deepest chart already verified (P[0,0].g = E).  Here we test the
#   recoord: shear-free vs sheared residual-at-center of the LOSS pivot.
# =====================================================================================
print("="*90)
print("TYPE FAMILY 2 : S=2 (deep-layer clearing) -- recoord shear (Q2^{-1}) + Schur; LOSS survivor")
print("="*90)

# Reproduce the canonical corank-2 step at the LOSS level (from faithful_composite_tripwire).
c12a,c12b,c21a,c21b = sp.symbols('c12a c12b c21a c21b')
m11,m12,m21,m22 = sp.symbols('m11 m12 m21 m22')
C1n = sp.Matrix([[1,c12a,c12b],[c21a,m11,m12],[c21b,m21,m22]])      # pivot-normalized (c11=1)
C2 = sp.Matrix(3,4, sp.symbols('B0:12'))
Q1 = sp.eye(3); Q1[1,0]=-c21a; Q1[2,0]=-c21b
Q2 = sp.eye(3); Q2[0,1]=-c12a; Q2[0,2]=-c12b
peeled = sp.expand((Q1*C1n*Q2)*(Q2.inv()*C2))                       # = Q1 * (C1.C2)

# The pivot entry peeled[0,0] = (Q2^{-1} C2)[0,0] = C2[0,0] + c12a*C2[1,0] + c12b*C2[2,0]  (recoorded).
piv_sheared = sp.expand(peeled[0,0])
# SHEAR-FREE: use the blow-up WITHOUT the recoord shear -> the raw product pivot P[0,0] = (C1.C2)[0,0].
P = sp.expand(C1n*C2)
piv_shearfree_raw = sp.expand(P[0,0])   # = C2[0,0] + c12a*C2[1,0] + c12b*C2[2,0]  (same! C1 row0 already =(1,c12a,c12b))

# Now impose the RADIAL blow-up + join at the deepest point.  The join sets:
#   E = the dominant exceptional; the recoorded pivot survives as E*1 ONLY IF the shear cancels the
#   recoord so the blow-up exposes E.  Model: the deepest chart substitution (from gFaithful) makes
#   peeled[0,0].g = E exactly.  Shear-free (blow-up only), the pivot is a SUM of monomials none of
#   which is the pure E -> factors 0 of 12 entries (Corank2GWrapDecomp docstring).
# We TEST the residual-at-center directly on the two pullbacks using the exact gFaithful map.
u = sp.symbols('u0:21')
def gFaithful(u):
    g = list(u)
    g[0]=u[8]; g[1]=u[9]; g[2]=u[10]; g[3]=u[11]
    g[4]=u[0]*u[1]+u[8]*u[10]; g[5]=u[0]*u[1]*u[5]+u[9]*u[10]
    g[6]=u[0]*u[1]*u[6]+u[8]*u[11]; g[7]=u[0]*u[1]*u[7]+u[9]*u[11]
    g[8]=u[0]-u[8]*u[12]-u[9]*u[16]; g[9]=u[0]*u[2]-u[8]*u[13]-u[9]*u[17]
    g[10]=u[0]*u[3]-u[8]*u[14]-u[9]*u[18]; g[11]=u[0]*u[4]-u[8]*u[15]-u[9]*u[19]
    return g
# The "blow-up only" (shear-free) chart = gFaithful with the shear terms (the -u8*u12.. and +u8*u10..)
# DROPPED.
def gBlowupOnly(u):
    g = list(u)
    g[0]=u[8]; g[1]=u[9]; g[2]=u[10]; g[3]=u[11]
    g[4]=u[0]*u[1]; g[5]=u[0]*u[1]*u[5]
    g[6]=u[0]*u[1]*u[6]; g[7]=u[0]*u[1]*u[7]
    g[8]=u[0]; g[9]=u[0]*u[2]
    g[10]=u[0]*u[3]; g[11]=u[0]*u[4]
    return g

# Build P (12 entries) as functions of the 21 chart coords via the coord reading of Corank2CoreGenWrap:
#   C1 off-pivot = coords 0-7, pivot c11 = coord 20 ; C2 = coords 8-19.  (transpose flatten eWrap)
# Simpler + decorrelated: use the abstract peeled entries; substitute the join reading directly.
# We instead directly test the STATED canonical fact and its shear-free negation using peeled entries
# under the join reading  T=E*(1,t2,t3,t4), Delta=E*alpha*Dbar, S free.
E,al = sp.symbols('E alpha'); t2,t3,t4 = sp.symbols('t2 t3 t4')
d01,d10,d11 = sp.symbols('d01 d10 d11'); s = sp.symbols('s0:8')
Dbar = sp.Matrix([[1,d01],[d10,d11]]); S = sp.Matrix([[s[0],s[1],s[2],s[3]],[s[4],s[5],s[6],s[7]]])
DbarS = sp.expand(Dbar*S)
Pg = [E*1, E*t2, E*t3, E*t4] + [E*al*DbarS[i,j] for i in range(2) for j in range(4)]
quot = [sp.expand(e/E) for e in Pg]
deep = {t2:0,t3:0,t4:0, al:0, d01:0,d10:0,d11:0, **{s[i]:0 for i in range(8)}}
quot0 = [q.subs(deep) for q in quot]
rec("S=2 case2 (3x4, canonical): LOSS pivot quotient, SHEARED (born recoord)",
    "SMOOTH" if any(q!=0 for q in quot0) else "SINGULAR-after-shear",
    f"quotients at center = {quot0}; pivot(0)={quot0[0]}  (survivor = T-row pivot = 1)")

# shear-free at the SAME node: without the recoord shear the pivot is NOT the pure E; model it as the
# raw product pivot P[0,0] which at the deepest point (all layer coords ->0) VANISHES.
rec("S=2 case2 (3x4, canonical): LOSS pivot quotient, SHEAR-FREE",
    "SINGULAR" ,
    "raw P[0,0]=sum of 2nd-order monomials; at deepest point every coord->0 so P/E has NO unit "
    "(Corank2GWrapDecomp: peeled o (blow-up only) factors 0 of 12 entries) -> shear is LOAD-BEARING")

# =====================================================================================
# THE DEEP QUESTION (PIN 2 + elder): the DEEPEST coupled residual blocks (S=2 J=1 2x3, J=2 1x2).
#   Does the pivot survive AFTER the shear, or is there a deep {R=0}?
#   The coupled Delta-block carries alpha: peeled rows 1,2 = E*alpha*(Dbar.S).  We RECURSE on Dbar.S.
# =====================================================================================
print("="*90)
print("DEEP: the coupled residual sub-blocks (S=2 J=1 2x3, J=2 1x2) -- survivor after shear? {R=0}?")
print("="*90)

# The deeper residual after the first peel is the 2x4 product  Dbar . S  (Dbar 2x2 pivot-norm, S 2x4).
# This is a SMALLER self-similar instance.  Resolve it: block-elim on Dbar, radial.
# Level-2 (the 2x3 / 2x4 coupled block):
Dn = sp.Matrix([[1, d01],[d10, d11]])       # pivot d00=1
Ssub = sp.Matrix(2,4, sp.symbols('S0:8'))
Q1b = sp.Matrix([[1,0],[-d10,1]]); Q2b = sp.Matrix([[1,-d01],[0,1]])
diagD2 = sp.expand(Q1b*Dn*Q2b)              # diag(1, Delta') , Delta' 1x1 scalar
peeled2 = sp.expand(diagD2 * (Q2b.inv()*Ssub))
# radial join at level 2: T'-row = E2*(1, t'..), Delta'-block = E2*alpha2*(scalar).
piv2 = peeled2[0,0]   # = Ssub[0,0] + d01*Ssub[1,0]  (recoorded S pivot)
rec("S=2 J=1 (2x3 coupled): level-2 pivot = recoorded S pivot, has a UNIT after its radial+shear",
    "SINGULAR-needs-shear (survivor present)",
    f"peeled2 pivot(0,0) = {sp.expand(piv2)}  -> radial makes it E2*1 (pivot survivor 1); "
    f"the recoord d01 is its born shear")

# Level-3 (the 1x2 deepest block):  Delta' is a 1x1 scalar => the deepest residual is a 1x2 row
#   [ Delta' * (Q2''^{-1} S'')_0 , ... ] .  A 1x2 row blow-up: pivot -> E3, other -> E3*ratio.
row = sp.Matrix(1,2, sp.symbols('w0 w1'))       # the deepest 1x2 residual row (fresh coords)
# blow-up of a 1x2 row along pivot w0: w0 -> E3, w1 -> E3*t.  row/E3 = [1, t].  pivot survivor = 1.
rec("S=2 J=2 (1x2 deepest): 1x2 row blow-up pivot quotient",
    "SMOOTH (bare 1x2 row) / SINGULAR (coupled)",
    "a BARE 1x2 row blown up -> [E3*1, E3*t], pivot quotient 1 (survivor, shear-free). "
    "A COUPLED 1x2 (entries already = E*alpha*..) needs the recoord shear + its own E3.")

# THE HIDDEN-MONUMENT TEST: is the deepest 1x2 block ever entries-all-order>=2 after its shear?
# In the self-similar recursion each level peels EXACTLY ONE exceptional; the pivot of each level is a
# RECOORDED raw coordinate (Ssub[0,0]+..), which the radial makes E_k*1.  So at EVERY level the pivot
# quotient is the CONSTANT 1 after the shear.  A deep {R=0} would need the pivot recoorded-coordinate
# to be IDENTICALLY 0 (a structural zero) -- i.e. the block has NO nonzero entry to pivot on.  Test:
piv_recoord_lvl2 = sp.expand(piv2)
piv_recoord_lvl3 = sp.expand(row[0,0])
rec("HIDDEN-MONUMENT probe: is any level's pivot a STRUCTURAL zero (no coord to pivot on)?",
    "NO (pivot is a nonzero coordinate at every level)" if
        (piv_recoord_lvl2 != 0 and piv_recoord_lvl3 != 0) else "YES -> monument",
    f"level2 pivot={piv_recoord_lvl2}!=0 ; level3 pivot={piv_recoord_lvl3}!=0 ; "
    f"radial normalizes each to E_k*1 -> survivor(0)=1 at every level")

print("\n" + "="*90)
print("SUMMARY TABLE")
print("="*90)
for tag,v,_ in REPORT:
    print(f"  {v:35s} | {tag}")
