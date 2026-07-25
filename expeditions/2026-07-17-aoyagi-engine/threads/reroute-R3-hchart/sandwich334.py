import sympy as sp

# Faithful (3,3,4): C1 3x3, C2 3x4, X = C1*C2 (3x4), loss L = ||X||^2_F.
C1 = sp.Matrix(3,3, lambda i,j: sp.Symbol(f'a{i}{j}'))
C2 = sp.Matrix(3,4, lambda i,j: sp.Symbol(f'b{i}{j}'))
X  = C1*C2
L  = sum(X[i,j]**2 for i in range(3) for j in range(4))

def subs_zero(expr):
    d = {s:0 for s in expr.free_symbols}
    return expr.subs(d)

print("=== JOB1 (b): the R>0 SANDWICH, born-per-pivot from a MATCHED pivot pair ===")
# A born chart blows up a PIVOT PAIR (C1[i,k], C2[k,j]) making both radials; all other
# center coords become radial*ratio. The pair is one additive term of survivor X[i,j].
# Model: pick survivor X[0,0]. Its three matched pairs: (a00,b00),(a01,b10),(a02,b20).
# We test each matched pair p=(a1,a2): set a1=r*A_hat? No: blow-up makes a1,a2 the two
# radials r1,r2; every OTHER entry of C1 row-0 and C2 col-0 scales by the matching radial.
# Faithful block blow-up (Aoyagi): choose the pair as the two blow-up radials (r1=C1 side,
# r2=C2 side); the OTHER C1 entries in the relevant block = r1*ratio, OTHER C2 = r2*ratio.

r1, r2 = sp.symbols('r1 r2')  # the two blow-up radials

def born_chart(pi, pj, pk):
    """Blow up the matched pair (C1[pi,pk], C2[pk,pj]) as radials r1,r2.
       C1[pi,*] entries = r1 * ratio (row pi is the surviving output row);
       C2[*,pj] entries = r2 * ratio (col pj is the surviving input col).
       Off-row/off-col entries: spectators (kept)."""
    sub = {}
    # C1 row pi: pivot col pk -> r1 ; other cols -> r1 * c1ratio
    for k in range(3):
        if k==pk: sub[C1[pi,k]] = r1
        else:     sub[C1[pi,k]] = r1*sp.Symbol(f'g1_{k}')
    # C2 col pj: pivot row pk -> r2 ; other rows -> r2 * c2ratio
    for k in range(3):
        if k==pk: sub[C2[k,pj]] = r2
        else:     sub[C2[k,pj]] = r2*sp.Symbol(f'g2_{k}')
    return sub

for (pi,pj,pk) in [(0,0,0),(0,0,1),(0,0,2)]:
    sub = born_chart(pi,pj,pk)
    Xpp = X[pi,pj].subs(sub)          # survivor entry pulled back
    Lg  = L.subs(sub)                  # loss pulled back
    mono = r1*r2                       # the born monomial (the pivot pair)
    # sandwich: L = mono^2 * R  ->  R = L / mono^2 ; check R(0)
    R = sp.simplify(sp.cancel(Lg / mono**2))
    R0 = subs_zero(R)
    surv = sp.simplify(sp.cancel(Xpp/mono))
    surv0 = subs_zero(surv)
    print(f" pair (C1[{pi},{pk}],C2[{pk},{pj}]) survivor X[{pi},{pj}]:"
          f"  survivor/mono(0)={surv0}   R(0)={R0}   sandwich_ok={R0!=0}")
