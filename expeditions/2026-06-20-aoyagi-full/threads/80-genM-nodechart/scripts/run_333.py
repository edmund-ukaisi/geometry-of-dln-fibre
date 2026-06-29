"""(3,3,3) Text=[3,3,3], L=2 — clean budget (no R-eta fudge), t=3 SQUARE K-cores (regular point).
   Every boundary k>=1: Tk=Tk1=3, ck=0, rk=0 -> B_k = 3x3 LDU core (9 coords), N/W empty.
   Tests the t=3 LDU monomial formula + the Schur frame |detK|^{r+c} with r=c=0 (=> |detK|^0=1!).
   flat = 18. bnd0 identity? Text0=3,Text1=3 -> ck=rk=0 -> B0=I (inert,0). bnd1 9. leaf Rfin 3x3? Text2=3,M2=3=9.
   So 0+9(bnd1) + leaf 9? = 18, but one pivot fixed + u... let's see budget reported need==flat.
"""
import sympy as sp
from sympy import symbols, eye, zeros, Matrix, expand, factor, Poly
from decompose import build_direct, build_factored
from mvalidate import lduMon

# budget check first
M=[3,3,3]; Text=[3,3,3]; L=2
flat=sum(M[k]*M[k+1] for k in range(L))
print("flat",flat)
# bnd0 id(0); bnd1 B=9 (3x3 LDU), N=0,W=0; leaf Rfin 3x3=9 (Text2=3,M2=3); u=1 -> 0+9+9+1=19 > 18.
# So one leaf entry must be the fixed pivot AND we are 1 over -> fix the pivot makes 8 free, total 18.
NC=18
x=symbols('x0:%d'%(NC+4),real=True); u=x[0]; i=[1]
def nx():
    v=x[i[0]];i[0]+=1;return v
bl={}
bl[0]={'B':eye(3),'N':zeros(3,0),'W':zeros(0,3),'R':zeros(3,3)}
# bnd1: 3x3 LDU core
q0,q1,q2=nx(),nx(),nx()
l10,l20,l21=nx(),nx(),nx()
u01,u02,u12=nx(),nx(),nx()
Lm=Matrix([[1,0,0],[l10,1,0],[l20,l21,1]]); Um=Matrix([[1,u01,u02],[0,1,u12],[0,0,1]])
K1=Lm*sp.diag(q0,q1,q2)*Um
bl[1]={'B':K1,'N':zeros(3,0),'W':zeros(0,3),'R':zeros(3,3)}
# leaf Rfin 3x3, one pivot fixed=1 (so 8 free)
Rfin=zeros(3,3)
for a in range(3):
    for b in range(3):
        if (a,b)==(0,0): Rfin[a,b]=1
        else: Rfin[a,b]=nx()
bl[2]={'Rfin':Rfin}
used=i[0]
print(f"===== (3,3,3) Text=[3,3,3]  t=3 K-core =====  coords={used} need={NC} square={used==NC}")
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
    # bnd1: t=3, detK1=q0*q1*q2, r1=Text1-Text2=0, c1=M1-Text2=0 -> r+c=0 => (detK1)^0=1!
    #   lduMon1 = q0^{2(3-1-0)}*q1^{2(3-1-1)}*q2^{2(3-1-2)} = q0^4 * q1^2 * q2^0 = q0^4 q1^2.
    detK1=expand(q0*q1*q2)
    pred=expand(u**lo * detK1**0 * lduMon([q0,q1,q2]))
    print("predicted u^%d * (detK1)^0 * lduMon1[q0^4 q1^2] ="%lo, factor(pred))
    ok=(expand(det-pred)==0 or expand(det+pred)==0)
    print("(iii) per-piece reproduces global det:",ok)
    if not ok: print("   residual=",factor(expand(det)/pred))
