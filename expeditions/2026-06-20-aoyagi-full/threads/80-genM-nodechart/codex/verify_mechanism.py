"""
Verify Codex's structural mechanism on the L=4 family + 3333:
  (M1) chart Phi is AFFINE in u: Phi = P(z,h) + u*Q(z,h) (degree<=1 in u) for EACH output entry.
  (M2) For each free coord c that is a 'radial/angular' direction (appears only multiplied by u in Phi),
       the Jacobian column dPhi/dc has a common factor u.
  (M3) After dividing every such column by u, the Jacobian is u-free => det = u^q * (u-free).
We detect angular coords automatically: a coord h is 'angular' if every output entry's dependence on h
is divisible by u (i.e. d(Phi_i)/d(h) is divisible by u for all i), and h != u.
"""
import sys; sys.path.insert(0,'/tmp/radsep')
import sympy as sp
from sympy import symbols, Matrix, eye, zeros
from families import build

def run_family(label, L, M, t, blocks, NC, x, u):
    A,C = build(L,M,t,blocks,u)
    out=[]; out_layer=[]
    for k in range(L):
        Ak=A[k]
        for i in range(Ak.rows):
            for j in range(Ak.cols):
                out.append(sp.expand(Ak[i,j])); out_layer.append(k)
    coords=[x[i] for i in range(NC)]
    # M1: affine in u?
    affine = all(sp.Poly(o,u).degree()<=1 if o.has(u) else True for o in out)
    print(f"[{label}]")
    print(f"  (M1) every output entry affine (degree<=1) in u? {affine}")
    # detect angular coords: c such that d(out_i)/dc divisible by u for all i, c!=u
    angular=[]; pivot_like=[]; zcoords=[]
    for ci in range(NC):
        c=x[ci]
        if c==u:
            continue
        cols=[sp.expand(sp.diff(o,c)) for o in out]
        nonzero=[g for g in cols if g!=0]
        if not nonzero:
            continue  # inert
        all_div_u = all(sp.simplify(g/u).is_polynomial() if False else (sp.expand(g) - u*sp.expand(g/u)==0) for g in nonzero)
        # robust divisibility test: g/u has no negative u-power and substituting works:
        def div_by_u(g):
            q,r = sp.div(sp.Poly(g,u), sp.Poly(u,u))
            return r==0
        all_div_u = all(div_by_u(g) for g in nonzero)
        if all_div_u:
            angular.append(ci)
        else:
            zcoords.append(ci)
    print(f"  angular coords (col divisible by u): {angular}")
    print(f"  z coords (u-free cols): {zcoords}")
    # M3: build Jacobian, divide angular cols by u, check u-free
    n=len(out)
    if n!=NC:
        print(f"  (non-square {n} vs {NC}; skipping det)"); return
    J=sp.Matrix(n,NC, lambda i,j: sp.diff(out[i], x[j]))
    # divide angular columns by u
    Jred=J.copy()
    for ci in angular:
        for i in range(n):
            Jred[i,ci]=sp.expand(Jred[i,ci]/u)
    ufree = all(not Jred[i,j].has(u) for i in range(n) for j in range(NC))
    print(f"  (M3) Jacobian with angular cols /u is u-FREE? {ufree}")
    detJ=sp.expand(J.det())
    P=sp.Poly(detJ,u); lo=min(m[0] for m in P.monoms()); hi=P.degree()
    print(f"  det front u-power = {lo} (= #angular coords {len(angular)}? {lo==len(angular)}); single power? {lo==hi}")
    if not ufree:
        # find leaking entry
        for i in range(n):
            for j in range(NC):
                if Jred[i,j].has(u):
                    print(f"    >>> LEAK at reduced J[{i},{j}] (coord x{j}) = {sp.factor(Jred[i,j])}")
                    break
            else:
                continue
            break

# --- 3333 ---
x=symbols('x0:36',real=True); u=x[0]
L=3;M=[3,3,3,3];t=[3,2,1,0]
bl={}
bl[0]={'B':eye(3),'N':zeros(3,0),'W':zeros(0,3),'R':zeros(3,3)}
bl[1]={'B':Matrix([[x[1],x[1]*x[2]],[x[1]*x[3],x[1]*x[2]*x[3]+x[4]],
        [x[1]*x[3]*x[6]+x[1]*x[5],x[1]*x[2]*x[5]+x[6]*(x[1]*x[2]*x[3]+x[4])]]),
       'N':Matrix([[x[7]],[x[8]]]),'W':Matrix([[x[15],x[16],x[17]]]),'R':Matrix([[0,0,0],[0,0,0],[0,0,1]])}
bl[2]={'B':Matrix([[x[9]],[x[10]*x[9]]]),'N':Matrix([[x[11],x[12]]]),
       'W':Matrix([[x[18],x[19],x[20]],[x[21],x[22],x[23]]]),'R':Matrix([[0,0,0],[0,x[13],x[14]]])}
bl[3]={'Rfin':Matrix([[x[24],x[25],x[26]]])}
run_family("3333", L,M,t,bl,27,x,u)

# --- L=4 (3,3,3,3,3), two interior t=2 cores, multi-coupling R_3 ---
x2=symbols('y0:36',real=True); u2=x2[0]
L=4;M=[3,3,3,3,3];t=[3,2,2,1,0]
idx=[1]
def nx2():
    v=x2[idx[0]]; idx[0]+=1; return v
b={}
b[0]={'B':eye(3),'N':zeros(3,0),'W':zeros(0,3),'R':zeros(3,3)}
a,bb,c_,d,e,f=nx2(),nx2(),nx2(),nx2(),nx2(),nx2()
b[1]={'B':Matrix([[a,a*bb],[a*c_,a*bb*c_+d],[a*c_*e+a*f,a*bb*f+e*(a*bb*c_+d)]]),
      'N':Matrix([[nx2()],[nx2()]]),'W':Matrix([[nx2(),nx2(),nx2()]]),
      'R':Matrix([[0,0,0],[0,0,0],[0,0,1]])}
g,h,p,qq=nx2(),nx2(),nx2(),nx2()
b[2]={'B':Matrix([[g,g*h],[g*p,g*h*p+qq]]),'N':Matrix([[nx2()],[nx2()]]),'W':Matrix([[nx2(),nx2(),nx2()]]),
      'R':Matrix([[0,0,0],[0,0,1]])}
b3v,l3=nx2(),nx2()
b[3]={'B':Matrix([[b3v],[l3*b3v]]),'N':Matrix([[nx2(),nx2()]]),
      'W':Matrix([[nx2(),nx2(),nx2()],[nx2(),nx2(),nx2()]]),'R':Matrix([[0,0,0],[0,nx2(),nx2()]])}
b[4]={'Rfin':Matrix([[nx2(),nx2(),nx2()]])}
run_family("L4 (3,3,3,3,3), 2 interior t=2 cores", L,M,t,b,36,x2,u2)
