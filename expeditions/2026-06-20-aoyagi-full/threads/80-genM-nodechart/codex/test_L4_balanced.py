"""
L=4 balanced family. Each layer k owns exactly W_k*W_{k+1} coords. We allocate coords so the diagonal
block D_k is square. The owning rule (from 3333): layer k owns the coords first appearing in A_k, i.e.
the coords of B_k-core/N_k/W_k for boundary k PLUS the R/Rfin coords of boundary k+1's C that are NEW.

Cleanest faithful construction: mimic 3333 exactly but one layer deeper, keeping all widths = 3,
descent t=(3,2,1,...,0)-like with one extra interior boundary that ALSO has a t=2 core.

(3,3,3,3,3), L=4. flatDim = 9*4 = 36. We need 4 layers each owning 9 coords.
Use descent giving cores: T = [3,3,2,1,?]. Let's set t_ach=(3,3,2,1,0) -> T=[3,3,3,2,1]:
  c0 = W0-T1 = 3-3=0 (identity)
  c1 = W1-T2 = 3-3=0 (identity, NO drop)  -> too many identity boundaries
Better: t_ach=(3,2,1,1,0)? T=[3,3,2,1,1]:
  c0=3-3=0; c1=3-2=1 (B1 3x2 t=2 core); c2=3-1=2 (B2 2x1); c3=3-1=2 (B3 1x1).
Only one t>=2 core. To get a SECOND interior t=2 core deeper, need two consecutive 2-drops:
  t_ach=(3,2,2,1,0) -> T=[3,3,2,2,1]: c0=0, c1=1(B1 3x2), c2=1(B2 2x2 INTERIOR t=2!), c3=2(B3 2x1).
This is what I want. Now BALANCE: owned coords per layer must = 9.

Layer ownership (lowest layer where coord appears). Following 3333's clean partition, layer k owns:
the free entries that DEBUT in A_k. We allocate per-layer and CHECK square diagonal blocks.

Strategy: assign coords, build chart, compute owner partition, and verify each diagonal block square.
If not balanced, adjust R_k freedoms.
"""
import sys; sys.path.insert(0,'/tmp/radsep')
import sympy as sp
from sympy import symbols, Matrix, eye, zeros
from families import build, chainQ, chainA

NC = 36
x = symbols('x0:36', real=True); u=x[0]
L=4; M=[3,3,3,3,3]; t=[3,2,2,1,0]   # T=[3,3,2,2,1]

idx=[1]
def nx():
    v=x[idx[0]]; idx[0]+=1; return v

blocks={}
blocks[0]={'B':eye(3),'N':zeros(3,0),'W':zeros(0,3),'R':zeros(3,3)}

# boundary1: T1=3,T2=2,W1=3,c1=1. B1 3x2 LDU core(6), N1 2x1(2), W1 1x3(3). R1 fixed pivot (0 free).
a,b,c_,d,e,f=nx(),nx(),nx(),nx(),nx(),nx()
B1=Matrix([[a,a*b],[a*c_,a*b*c_+d],[a*c_*e+a*f,a*b*f+e*(a*b*c_+d)]])
N1=Matrix([[nx()],[nx()]]); W1=Matrix([[nx(),nx(),nx()]])
R1=Matrix([[0,0,0],[0,0,0],[0,0,1]])
blocks[1]={'B':B1,'N':N1,'W':W1,'R':R1}

# boundary2: T2=2,T3=2,W2=3,c2=1. B2 2x2 LDU core(4): [[g,gh],[gp,ghp+q]]. N2 2x1(2), W2 1x3(3).
# R2 fixed single pivot OR free? In 3333, R2 had 2 free. Budget will tell.
g,h,p,q=nx(),nx(),nx(),nx()
B2=Matrix([[g,g*h],[g*p,g*h*p+q]])
N2=Matrix([[nx()],[nx()]]); W2=Matrix([[nx(),nx(),nx()]])
# R2 2x3 with some free entries; start with a single pivot (0 free) and adjust.
R2=Matrix([[0,0,0],[0,0,1]])
blocks[2]={'B':B2,'N':N2,'W':W2,'R':R2}

# boundary3: T3=2,T4=1,W3=3,c3=2. B3 2x1(2). N3 1x2(2). W3 2x3(6). R3 2x3.
b3,l3=nx(),nx(); B3=Matrix([[b3],[l3*b3]])
N3=Matrix([[nx(),nx()]]); W3=Matrix([[nx(),nx(),nx()],[nx(),nx(),nx()]])
R3=Matrix([[0,0,0],[0,nx(),nx()]])  # 2 free couplings like 3333 R2
blocks[3]={'B':B3,'N':N3,'W':W3,'R':R3}

# leaf k=4: T4=1,W4=3, Rfin 1x3 (3 free)
Rfin=Matrix([[nx(),nx(),nx()]])
blocks[4]={'Rfin':Rfin}

print("coords used (incl u):", idx[0], " need", NC)
if idx[0]!=NC:
    print(f"  imbalance by {idx[0]-NC}; adjusting needed")

A,C=build(L,M,t,blocks,u)
# build outputs + layers
out=[]; out_layer=[]
for k in range(L):
    Ak=A[k]
    for i in range(Ak.rows):
        for j in range(Ak.cols):
            out.append(Ak[i,j]); out_layer.append(k)

def deps(ex):
    return sorted(int(str(s)[1:]) for s in ex.free_symbols)
# owner = lowest layer where coord appears
owner={}
for ci in range(idx[0]):
    for k in range(L):
        if any(ci in deps(e) for e,lk in zip(out,out_layer) if lk==k):
            owner[ci]=k; break
for k in range(L):
    no=sum(1 for lk in out_layer if lk==k)
    oc=[c for c in range(idx[0]) if owner.get(c)==k]
    print(f"  layer {k}: outputs={no}, owned={len(oc)} -> {oc}")
unowned=[c for c in range(idx[0]) if c not in owner]
print("  unowned coords:", unowned)

# Now the determinant analysis
print("\n--- DETERMINANT + LAYER FILTRATION ---")
col_order=[]
for k in range(L):
    col_order += [c for c in range(idx[0]) if owner.get(c)==k]
J = sp.Matrix(36,36, lambda i,j: sp.diff(out[i], x[col_order[j]]))
detJ = sp.expand(J.det())
print("full det J =", sp.factor(detJ))
P=sp.Poly(detJ,u); lo=min(m[0] for m in P.monoms()); hi=P.degree()
print(f"u powers {lo}..{hi}; separates(single front power)? {lo==hi}")

def block(kr,kc):
    ri=[i for i in range(36) if out_layer[i]==kr]
    cj=[c for c in range(idx[0]) if owner.get(c)==kc]
    return sp.Matrix(len(ri),len(cj), lambda a,bb: sp.diff(out[ri[a]], x[cj[bb]]))

print("\nUpper off-diagonal blocks zero (lower-triangular)?")
ok=True
for kr in range(L):
    for kc in range(kr+1,L):
        z=block(kr,kc).is_zero_matrix
        ok = ok and z
        if not z: print(f"  NONZERO upper block ({kr},{kc})")
print("  all upper blocks zero:", ok)

print("\nPer-layer diagonal block dets + u-power:")
tot=0
for k in range(L):
    dk=sp.expand(block(k,k).det())
    fk=sp.factor(dk)
    if dk==0:
        print(f"  D_{k} det = 0  (singular block!)"); continue
    Pk=sp.Poly(dk,u); uk=min(m[0] for m in Pk.monoms()); uhi=Pk.degree()
    tot+=uk
    print(f"  D_{k}: det={fk}; u-power {uk}..{uhi} (clean monomial in u? {uk==uhi})")
print(f"  sum of per-block u front-powers = {tot}; full det u-power = {lo}")
