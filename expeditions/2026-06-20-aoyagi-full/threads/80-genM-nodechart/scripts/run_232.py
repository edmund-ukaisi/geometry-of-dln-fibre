"""(2,3,2) Text=[2,2,1], L=2, hand-built SQUARE (flatDim=12), mirroring blocks_3333 discipline.
   Budget: B0=I(inert,0) + bnd1[B1(2)+N1(2)+W1(4)=8] + leaf Rfin(1 free, 1 pivot fixed) + R1eta(2) + u(1) = 12."""
import sympy as sp
from sympy import symbols, eye, zeros, Matrix, expand, factor, Poly
from decompose import build_direct, build_factored
from mvalidate import lduMon

NC = 12
x = symbols('x0:%d' % (NC+2), real=True); u = x[0]
i = [1]
def nx():
    v = x[i[0]]; i[0]+=1; return v

M = [2,3,2]; Text = [2,2,1]; L = 2
bl = {}
# bnd0 identity: Tk=2,Tk1=2 -> B0=I2, N0/W0 empty, R0=0
bl[0] = {'B': eye(2), 'N': zeros(2,0), 'W': zeros(0,3), 'R': zeros(2,2)}
# bnd1: Tk=Text1=2, Tk1=Text2=1 -> B1 2x1 (LDU: pivot p1, scaled), c1 = M1-Text2 = 3-1 = 2
p1 = nx(); l1 = nx(); B1 = Matrix([[p1],[l1*p1]])     # 2x1, K-core 1x1 = [p1], detK1 = p1
N1 = Matrix([[nx(), nx()]])                           # N1 1x2
W1 = Matrix([[nx(),nx()],[nx(),nx()]])               # W1 2x2 (c1=2 x M2=2)
# R1 2x3 (Tk=2 x Mk=M1=3): free-eta to fill 2
R1 = zeros(2,3); R1[1,1] = nx(); R1[1,2] = nx()      # 2 free eta (u-scaled)
bl[1] = {'B': B1, 'N': N1, 'W': W1, 'R': R1}
# leaf k=2: Rfin Text[2]=1 x M[2]=2, one pivot fixed=1
Rfin = Matrix([[1, nx()]])                            # pivot (0,0)=1 fixed, (0,1) free
bl[2] = {'Rfin': Rfin}

used = i[0]
print(f"===== (2,3,2) Text=[2,2,1] =====  coords used={used} need={NC} square={used==NC}")
Ad, Cd = build_direct(L, M, Text, bl, u)
Af, Cfull, schur_out, shears = build_factored(L, M, Text, bl, u)
eqA = all(expand(Ad[k]-Af[k])==zeros(*Ad[k].shape) for k in range(L))
print("(i) factored==fused MAP equality:", eqA)
detsh = [shears[k].det() for k in range(L)]
print("(ii) chain shear dets:", detsh, "-> all 1:", all(d==1 for d in detsh))
vec=[]
for k in range(L):
    for a in range(Ad[k].rows):
        for b in range(Ad[k].cols): vec.append(Ad[k][a,b])
n=len(vec)
Xs=[x[j] for j in range(NC)]
J=Matrix(n,n,lambda r,c: sp.diff(vec[r],Xs[c]))
det=expand(J.det())
print("global det =", factor(det) if det!=0 else 0)
if det!=0:
    P=Poly(det,u); lo=min(m[0] for m in P.monoms()); hi=P.degree()
    print(f"u-power [{lo}..{hi}] sep={lo==hi} front={lo}")
    # per-piece: bnd1 detK1=p1=x1, t=1 -> lduMon = p1^{2(1-1-0)}=1; r1=Tk-Tk1=2-1=1, c1=M1-Tk1=3-1=2 -> r+c=3
    detK1 = x[1]
    pred = expand(u**lo * detK1**3 * lduMon([x[1]]))
    print("predicted u^%d * (detK1)^3 * lduMon1 ="%lo, factor(pred))
    ok = (expand(det-pred)==0 or expand(det+pred)==0)
    print("(iii) per-piece reproduces global det:", ok)
    if not ok: print("   residual =", factor(expand(det)/pred))
