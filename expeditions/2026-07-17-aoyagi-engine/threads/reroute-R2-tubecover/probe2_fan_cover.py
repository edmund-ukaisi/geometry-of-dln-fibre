#!/usr/bin/env python3
"""TUBE-COVER PROBE #169, step 2: WHICH born-siblings escape the {1+pd=0} tube?

Terminal residual ideal (3,3,3,2,2), original coords:
  X = C3*C4  (C3 3x2, C4 2x2),  residual ideal I = < X_row0 , d2*X_row1 , d1*X_row2 >
  loss = ||X_row0||^2 + d2^2 ||X_row1||^2 + d1^2 ||X_row2||^2 .
The unit "1+pd" = X[0,0]/(C3[0,0]*C4[0,0]) (canonical pivot). {1+pd=0} = {X[0,0]=0}.

Two DIFFERENT fan notions:
 (A) RADIAL-PIVOT fan: vary which ENTRY of C3 / of C4 is the dominant radial, but ALWAYS keep
     X[0,0] as the rank-survivor.  Unit_chart = X[0,0]/monomial_chart.
 (B) SURVIVOR-ENTRY fan: vary which GENERATOR of the residual ideal is the pivot (X[0,0] vs X[0,1]
     vs weighted rows).  Unit_chart = X[pivot_entry]/monomial_chart.

TEST: does {1+pd=0}={X[0,0]=0} get covered?  A single generator's zero locus is chart-independent
(X[0,0] is a fixed polynomial); only a chart keeping a DIFFERENT generator can be nonzero there.
"""
import sympy as sp
import random

# original coords (canonical chart: C3[0,0], C4[0,0] are the pivots -> = radials w,y)
C300,C301,C310,C311,C320,C321 = sp.symbols('C300 C301 C310 C311 C320 C321', real=True)
C400,C401,C410,C411 = sp.symbols('C400 C401 C410 C411', real=True)
C3 = sp.Matrix([[C300,C301],[C310,C311],[C320,C321]])
C4 = sp.Matrix([[C400,C401],[C410,C411]])
X = C3*C4
print("X = C3*C4 (3x2), entries:")
for i in range(3):
    for j in range(2):
        print(f"  X[{i},{j}] = {sp.expand(X[i,j])}")

# --- (A) the four "keep-X[0,0]" radial-pivot siblings: units on the SAME numerator X[0,0] ---
print("\n=== (A) RADIAL-PIVOT siblings that all keep X[0,0] as survivor ===")
pivots_A = {
  "canonical (C300,C400)": C300*C400,
  "swap C3 col (C301,C400)": C301*C400,
  "swap C4 row (C300,C410)": C300*C410,
  "swap both (C301,C410)":   C301*C410,
}
for name,mono in pivots_A.items():
    unit = sp.simplify(X[0,0]/mono)
    print(f"  {name:26s}: unit = X[0,0]/({mono}) = {unit}")
print("  ALL have numerator X[0,0]  =>  ALL vanish exactly on {X[0,0]=0}={1+pd=0}.")
print("  => a fan that only varies the RADIAL pivot does NOT cover the {1+pd=0} tube. [FACT]")

# --- (B) the survivor-ENTRY sibling: keep X[0,1] instead ---
print("\n=== (B) SURVIVOR-ENTRY sibling keeps X[0,1] (different generator) ===")
print(f"  X[0,1] = {sp.expand(X[0,1])}")
# On {X[0,0]=0}: is X[0,1] generically nonzero?  Parametrize {X[0,0]=0}.
# X[0,0] = C300*C400 + C301*C410 = 0  =>  C400 = -C301*C410/C300 (C300!=0).
sub0 = {C400: -C301*C410/C300}
X01_on = sp.simplify(X[0,1].subs(sub0))
print(f"  X[0,1] on {{X[0,0]=0}} = {X01_on}")
print("   generically NONZERO => the X[0,1]-pivot sibling is VALID on the {X[0,0]=0} tube. [FACT]")

# --- common zero of BOTH unweighted survivors: {X_row0 = 0} ---
print("\n=== common zero of the unweighted survivors {X[0,0]=0, X[0,1]=0} = {X_row0=0} ===")
sol = sp.solve([X[0,0], X[0,1]], [C400,C401], dict=True)
print("  solve(X_row0=0 for C4 col-images):", sol)
print("  X_row0 = C3[0,:]*C4 = 0  <=>  C3[0,:] in left-kernel(C4)  => CODIM 2 (generic). [FACT]")

# --- generic delta: common zero of the FULL ideal = {X=0}, codim 4 ---
print("\n=== generic d1,d2 != 0: full-ideal common zero = {X=0}=(C3*C4=0) codim 4 ===")
solX = sp.solve([X[i,j] for i in range(3) for j in range(2)], [C400,C401,C410,C411], dict=True)
print("  solve(C3*C4=0 for C4):", solX, " (C4=0: codim 4; kept '1'-pivots forbid a fatter locus)")

# --- MONTE CARLO (GUIDE ONLY): does the (B) fan cover a nbhd, incl. the {X[0,0]~0} tube? ---
print("\n=== MC GUIDE: coverage of the {X[0,0]~0} tube by the survivor-entry fan (box R) ===")
def eval_all(vals):
    s = {C300:vals[0],C301:vals[1],C310:vals[2],C311:vals[3],C320:vals[4],C321:vals[5],
         C400:vals[6],C401:vals[7],C410:vals[8],C411:vals[9]}
    Xv = [[float(X[i,j].subs(s)) for j in range(2)] for i in range(3)]
    return Xv
random.seed(3)
# generators of the residual ideal (take d1=d2=1 so all 6 are active survivors)
def gens(Xv): return [Xv[0][0],Xv[0][1],Xv[1][0],Xv[1][1],Xv[2][0],Xv[2][1]]
R=4.0  # box ratio tolerance
for scenario,desc in [("tube","points with X[0,0]~0 (the tube)"),("generic","generic near-singular")]:
    covered=0; total=0; escapes=[]
    for _ in range(200000):
        vals=[random.uniform(-1,1) for _ in range(10)]
        Xv=eval_all(vals)
        g=gens(Xv)
        gmax=max(abs(x) for x in g)
        if gmax<1e-9: continue
        if scenario=="tube" and abs(Xv[0][0])>0.02*gmax: continue  # restrict to the tube
        total+=1
        # covered iff SOME generator g_a is dominant up to factor R: gmax <= R*|g_a| for the argmax a
        # (equivalently the argmax generator's chart has all ratios <= R): always true for a=argmax if R>=1
        # the real test: is the point in some chart's COMPACT box = {|g_b/g_a|<=R for all b}?
        a=max(range(6),key=lambda i:abs(g[i]))
        if all(abs(g[b])<=R*abs(g[a])+1e-12 for b in range(6)):
            covered+=1
        else:
            escapes.append((scenario,[round(x,3) for x in g]))
    print(f"  {desc:32s}: covered {covered}/{total} = {covered/max(total,1)*100:.2f}%  (R={R})")
    if escapes[:2]: print("     sample escapes:",escapes[:2])
print("\n  NB: argmax generator is always dominant with ratio 1<=R => survivor-entry fan covers up-to-null.")
print("  The {X[0,0]~0} tube is covered by whichever OTHER generator is the argmax there.")
