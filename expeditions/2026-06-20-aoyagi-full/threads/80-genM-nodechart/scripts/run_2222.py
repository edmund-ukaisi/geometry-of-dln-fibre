"""(2,2,2,2) Text=[2,2,1,1], L=3, hand-built SQUARE (flatDim=12, surplus 0 -> NO R-eta fill).
   bnd0 identity(0); bnd1 [B1(2)+N1(1)+W1(2)=5]; bnd2 [B2(1)+N2(1)+W2(2)=4]; leaf Rfin(2-1=1 free); u(1) = 12."""
import sympy as sp
from sympy import symbols, eye, zeros, Matrix, expand, factor, Poly
from decompose import build_direct, build_factored
from mvalidate import lduMon

NC = 12
x = symbols('x0:%d'%(NC+2), real=True); u=x[0]
i=[1]
def nx():
    v=x[i[0]]; i[0]+=1; return v
M=[2,2,2,2]; Text=[2,2,1,1]; L=3
bl={}
bl[0]={'B':eye(2),'N':zeros(2,0),'W':zeros(0,2),'R':zeros(2,2)}
# bnd1: Tk=Text1=2,Tk1=Text2=1 -> B1 2x1 (pivot), c1=M1-Text2=2-1=1; N1 1x1; W1 1x2
p1=nx(); l1=nx(); B1=Matrix([[p1],[l1*p1]])          # detK1 = p1 (1x1 core)
N1=Matrix([[nx()]])                                   # 1x1
W1=Matrix([[nx(),nx()]])                              # 1x2
R1=zeros(2,2); R1[1,1]=nx()                            # 1 free eta (fills the fixed-pivot deficit)
bl[1]={'B':B1,'N':N1,'W':W1,'R':R1}
# bnd2: Tk=Text2=1,Tk1=Text3=1 -> B2 1x1 (pivot p2), c2=M2-Text3=2-1=1; N2 1x1; W2 1x2
p2=nx(); B2=Matrix([[p2]])                            # detK2 = p2
N2=Matrix([[nx()]])                                   # 1x1
W2=Matrix([[nx(),nx()]])                              # 1x2
R2=zeros(1,2)
bl[2]={'B':B2,'N':N2,'W':W2,'R':R2}
# leaf k=3: Rfin Text[3]=1 x M[3]=2, pivot (0,0) fixed=1, (0,1) free angular
Rfin=Matrix([[1, nx()]])
bl[3]={'Rfin':Rfin}
used=i[0]
print(f"===== (2,2,2,2) Text=[2,2,1,1] =====  coords={used} need={NC} square={used==NC}")
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
    # bnd1: detK1=p1=x1, t=1->lduMon=1, r1=2-1=1,c1=2-1=1->r+c=2
    # bnd2: detK2=p2, t=1->lduMon=1, r2=Text2-Text3=1-1=0,c2=M2-Text3=2-1=1->r+c=1
    detK1=x[1]; detK2=p2
    pred=expand(u**lo * detK1**2 * lduMon([x[1]]) * detK2**1 * lduMon([p2]))
    print("predicted u^%d*(detK1)^2*(detK2)^1 ="%lo, factor(pred))
    ok=(expand(det-pred)==0 or expand(det+pred)==0)
    print("(iii) per-piece reproduces global det:",ok)
    if not ok: print("   residual=",factor(expand(det)/pred))
