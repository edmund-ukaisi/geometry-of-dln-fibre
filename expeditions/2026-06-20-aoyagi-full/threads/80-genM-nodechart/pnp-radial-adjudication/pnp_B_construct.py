import sympy as sp

def build(M_name):
    if M_name=="222":
        x=sp.symbols('x0:8',real=True);u=x[0];active=[6,7]
        A0=sp.Matrix([[x[4],x[4]*x[1]],[x[5],x[5]*x[1]+x[6]*x[0]]])
        A1=sp.Matrix([[x[0]-x[1]*x[2],x[0]*x[7]-x[1]*x[3]],[x[2],x[3]]])
        phi=[A0[0,0],A0[0,1],A0[1,0],A0[1,1],A1[0,0],A1[0,1],A1[1,0],A1[1,1]]
        return list(x),u,active,[sp.expand(e) for e in phi]
    if M_name=="3333":
        x=sp.symbols('x0:27',real=True);u=x[0];active=[13,14,24,25,26]
        B1=sp.Matrix([[x[1],x[1]*x[2]],[x[1]*x[3],x[1]*x[2]*x[3]+x[4]],[x[1]*x[3]*x[6]+x[1]*x[5],x[1]*x[2]*x[5]+x[6]*(x[1]*x[2]*x[3]+x[4])]])
        B2=sp.Matrix([[x[9]],[x[10]*x[9]]]);N1=sp.Matrix([[x[7]],[x[8]]]);N2=sp.Matrix([[x[11],x[12]]])
        W1=sp.Matrix([[x[15],x[16],x[17]]]);W2=sp.Matrix([[x[18],x[19],x[20]],[x[21],x[22],x[23]]])
        R1=sp.Matrix([[0,0,0],[0,0,0],[0,0,1]]);R2=sp.Matrix([[0,0,0],[0,x[13],x[14]]]);Rf=sp.Matrix([[x[24],x[25],x[26]]])
        C3=u*Rf;C2=B2*sp.Matrix.hstack(sp.eye(1),N2)+u*R2;C1=B1*sp.Matrix.hstack(sp.eye(2),N1)+u*R1
        A0=C1;A1=sp.Matrix.vstack(C2-N1*W1,W1);A2=sp.Matrix.vstack(C3-N2*W2,W2)
        phi=[sp.expand(A[i,j]) for A in (A0,A1,A2) for i in range(A.rows) for j in range(A.cols)]
        return list(x),u,active,phi

def pivotBlowupOn(active,p,vec):
    return [vec[p] if i==p else (vec[p]*vec[i] if i in active else vec[i]) for i in range(len(vec))]

for name in ("222","3333"):
    xs,u,active,phi=build(name)
    n=len(xs); xv=sp.Matrix(xs)
    # B(y): replace x_i for i in active by y_i directly; pivot x0 -> the bare-x0 occurrences become y0;
    #   BUT the bare-pivot terms in phi (e.g. C_L = u*Rfin has the FIXED 1 -> u*1 = bare u). 
    #   B reads: every x_active -> y_active (NOT *y0), and the PAIRED x0 that multiplied them is ALREADY
    #   absorbed. The subtlety: in phi, an active term is "x0 * x_active". Under blowup x_active->y0*y_active?? 
    #   No: pivotBlowupOn maps x_active(input) -> y0*y_active(output coord). So to get B with B(blowup(x))=phi(x):
    #   B(y) must equal phi(x) where x0=y0, x_active = y_active/y0... that's the inverse (division). 
    #   The DIVISION-FREE construction: since active terms appear as x0*x_active, and blowup output at coord
    #   'active' IS y0*y_active = x0*x_active, B should read coord 'active' of its INPUT as the WHOLE x0*x_active.
    #   i.e. B(y)[out] = phi with the substitution: wherever "x0 * x_active" appears, replace by y_active
    #   (the blown coordinate), and bare x0 -> y0, spectators -> y_j. Let me implement by substituting
    #   x_active -> y_active/y0 then multiply-through cancels (division-free because always paired). Verify no 1/y0 remains.
    y=sp.symbols(f'y0:{n}',real=True)
    sub={xs[i]: y[i] for i in range(n)}
    sub[u]=y[0]
    for i in active: sub[xs[i]] = y[i]/y[0]   # the formal inverse on actives
    B=[sp.simplify(e.subs(sub, simultaneous=True)) for e in phi]
    # check B division-free (no y0 in denominator)
    divfree=all(y[0] not in sp.denom(sp.together(e)).free_symbols for e in B)
    print(f"[{name}] B division-free (no 1/y0)? {divfree}")
    # check B(pivotBlowupOn(x)) == phi(x)
    bl=pivotBlowupOn(active,0,xs)
    Bsub={y[i]: bl[i] for i in range(n)}
    Bcomp=[sp.expand(e.subs(Bsub)) for e in B]
    ok = all(sp.simplify(Bcomp[i]-phi[i])==0 for i in range(n))
    print(f"[{name}] B ∘ pivotBlowupOn == phi (as maps)? {ok}")
    # |det DB| -- compute Jacobian of B wrt y
    JB=sp.Matrix(B).jacobian(sp.Matrix(list(y)))
    if name=="222":
        detB=sp.factor(JB.det()); print(f"[{name}] det DB = {detB}  (expect ±x4 = the engine |K|^{{r+c}})")
    else:
        # 3333 too big for full symbolic det; substitute exact rationals for non-pivot y's, keep none-symbolic
        import random; random.seed(3)
        s2={v: sp.Rational(random.randint(-9,9),random.randint(1,6)) for v in y}
        detB=JB.subs(s2).det(); print(f"[{name}] det DB at random exact rationals = {detB}")
