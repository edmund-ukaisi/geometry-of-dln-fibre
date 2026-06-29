"""(3,2,2,2,2) Text=[3,3,2,2,2], L=4 DESCENT + t>=2 interior cores — the deep stress case.
   bnd0: Tk=3,Tk1=3,ck=0,rk=0 -> B0=I3 (inert,0).
   bnd1: Tk=3,Tk1=2,ck=M1-2=0,rk=1 -> B1 3x2 (schur: K 2x2 LDU + X 1x2 row).   <- descent, r=1
   bnd2: Tk=2,Tk1=2,ck=M2-2=0,rk=0 -> B2 2x2 LDU core.                            <- t=2 interior
   bnd3: Tk=2,Tk1=2,ck=M3-2=0,rk=0 -> B3 2x2 LDU core.                            <- t=2 interior
   leaf: Text4=2, M4=2 -> Rfin 2x2.
   flat=18. content: 0 + B1(6) + B2(4) + B3(4) + leaf(4-1 fixed pivot=3) + u(1) = 18.  NO N/W (all ck=0).
"""
import sympy as sp
from sympy import symbols, eye, zeros, Matrix, expand, factor, Poly
from decompose import build_direct, build_factored
from mvalidate import lduMon

def ldu2(q0,q1,l,u01):
    return Matrix([[1,0],[l,1]])*sp.diag(q0,q1)*Matrix([[1,u01],[0,1]])

M=[3,2,2,2,2]; Text=[3,3,2,2,2]; L=4
NC=18
x=symbols('x0:%d'%(NC+5),real=True); u=x[0]; i=[1]
def nx():
    v=x[i[0]];i[0]+=1;return v
bl={}
bl[0]={'B':eye(3),'N':zeros(3,0),'W':zeros(0,2),'R':zeros(3,3)}
# bnd1: B1 3x2 = LDU-extended kept block. K-core = top 2x2 (LDU); extra row = (free L-ext)*D*U
#   so the extra row CARRIES the pivots (the schurFrameDeriv 'dX -> dX*K' coupling needs this).
qa,qb,la,ua=nx(),nx(),nx(),nx(); K1=ldu2(qa,qb,la,ua)   # detK1=qa*qb, K-core (top 2 rows)
DU1=sp.diag(qa,qb)*Matrix([[1,ua],[0,1]])              # D*U part
le0,le1=nx(),nx(); Lext=Matrix([[le0,le1]])            # free L-extension row (rk=1)
Xrow=Lext*DU1                                          # extra row = Lext * D * U  (carries pivots)
B1=Matrix([[K1[0,0],K1[0,1]],[K1[1,0],K1[1,1]],[Xrow[0,0],Xrow[0,1]]])  # [K; Xrow] 3x2
bl[1]={'B':B1,'N':zeros(2,0),'W':zeros(0,2),'R':zeros(3,2)}
# bnd2: B2 2x2 LDU
qc,qd,lc,uc=nx(),nx(),nx(),nx(); K2=ldu2(qc,qd,lc,uc); detK2=expand(qc*qd)
bl[2]={'B':K2,'N':zeros(2,0),'W':zeros(0,2),'R':zeros(2,2)}
# bnd3: B3 2x2 LDU
qe,qf,le,ue=nx(),nx(),nx(),nx(); K3=ldu2(qe,qf,le,ue); detK3=expand(qe*qf)
bl[3]={'B':K3,'N':zeros(2,0),'W':zeros(0,2),'R':zeros(2,2)}
# leaf k=4: Rfin 2x2, one pivot fixed
Rfin=zeros(2,2)
for a in range(2):
    for b in range(2):
        if (a,b)==(0,0): Rfin[a,b]=1
        else: Rfin[a,b]=nx()
bl[4]={'Rfin':Rfin}
used=i[0]
print(f"===== (3,2,2,2,2) Text=[3,3,2,2,2]  L=4 DESCENT + t>=2 =====  coords={used} need={NC} square={used==NC}")
Ad,Cd=build_direct(L,M,Text,bl,u); Af,Cf,so,sh=build_factored(L,M,Text,bl,u)
eqA=all(expand(Ad[k]-Af[k])==zeros(*Ad[k].shape) for k in range(L))
print("(i) MAP equality:",eqA)
detsh=[sh[k].det() for k in range(L)]
print("(ii) shear dets:",detsh,"all 1:",all(d==1 for d in detsh))
vec=[]
for k in range(L):
    for a in range(Ad[k].rows):
        for b in range(Ad[k].cols): vec.append(Ad[k][a,b])
Xs=[x[j] for j in range(NC)]; n=len(vec)
J=Matrix(n,n,lambda r,c: sp.diff(vec[r],Xs[c])); det=expand(J.det())
print("global det =", factor(det) if det!=0 else 0)
if det!=0:
    P=Poly(det,u); lo=min(m[0] for m in P.monoms()); hi=P.degree()
    print(f"u-power [{lo}..{hi}] sep={lo==hi} front={lo}")
    # bnd1: t=2, detK1=qa*qb, r1=Text1-Text2=3-2=1, c1=M1-Text2=2-2=0 -> r+c=1. lduMon1=qa^2*qb^0=qa^2.
    # bnd2: t=2, detK2=qc*qd, r2=Text2-Text3=2-2=0, c2=M2-Text3=2-2=0 -> r+c=0 => (detK2)^0=1. lduMon2=qc^2.
    # bnd3: t=2, detK3=qe*qf, r3=Text3-Text4=2-2=0, c3=M3-Text4=2-2=0 -> r+c=0. lduMon3=qe^2.
    detK1=expand(qa*qb)
    pred=expand(u**lo * detK1**1 * lduMon([qa,qb]) * detK2**0 * lduMon([qc,qd]) * detK3**0 * lduMon([qe,qf]))
    print("predicted u^%d*(detK1)^1*lduMon1*lduMon2*lduMon3 ="%lo, factor(pred))
    ok=(expand(det-pred)==0 or expand(det+pred)==0)
    print("(iii) per-piece reproduces global det:",ok)
    if not ok: print("   residual=",factor(expand(det)/pred))
