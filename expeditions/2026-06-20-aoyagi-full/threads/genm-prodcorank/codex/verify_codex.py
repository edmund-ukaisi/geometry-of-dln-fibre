import sympy as sp

# (1) Verify I(PZ) = (x,y,b) for Codex's normal form (n=2 balanced chart)
x,y,b,c = sp.symbols('x y b c')
P = sp.Matrix([[1,0],[0,x]])
Z = sp.Matrix([[y+b*c, b],[c,1]])
PZ = P*Z
entries = list(PZ)
print("PZ =",PZ.tolist())
print("entries (ideal gens):",entries)
# Show (x,y,b) generates the same ideal: reduce entries modulo (x,y,b)
I_target = [x,y,b]
# y+bc: subtract b*c (b in I) -> y (in I); xc: x in I -> xc in I; b in I; x in I.
# Check each entry is in (x,y,b):
from sympy import groebner, QQ
G = groebner([x,y,b], x,y,b,c, order='lex')
reductions = [G.reduce(e)[1] for e in entries]
print("each entry reduced mod (x,y,b):", reductions, "=> all zero:", all(r==0 for r in reductions))
# Conversely x,y,b in (entries)? entries = {y+bc, b, xc, x}. x and b are literally entries. y = (y+bc)-c*b.
Ge = groebner(entries, x,y,b,c, order='lex')
back = [Ge.reduce(g)[1] for g in [x,y,b]]
print("x,y,b reduced mod (entries):", back, "=> all zero:", all(r==0 for r in back))
print("=> I(PZ) = (x,y,b), codim 3 = C_2, SMOOTH joint center (alignment coord b). Confirmed.\n")

# (2) coker(dmu) dimension on balanced component = a*c = floor(k^2/4) = k^2 - C_k
def Ck(k): return k*k-(k*k)//4
print("=== balanced component: a*c (coker dim of d mu) vs floor(k^2/4)=k^2-C_k ===")
# from earlier optima: minimize a^2+c^2+e(c-a+e), e=k-c, over a>=k-c; balanced a≈c≈k/2
def best(k):
    bb=None
    for a in range(0,k+2):
        for cc in range(0,k+2):
            e=k-cc
            if e<0: e=0
            if e>a: continue
            codim=a*a+cc*cc+e*(cc-a+e)
            if bb is None or codim<bb[0]: bb=(codim,a,cc,e)
    return bb
for k in range(1,9):
    codim,a,cc,e=best(k)
    print(f" k={k}: (a,c,e)=({a},{cc},{e}) codim={codim} C_k={Ck(k)}; a*c={a*cc} floor(k^2/4)={k*k//4} k^2-C_k={k*k-Ck(k)} match={a*cc==k*k//4==k*k-Ck(k)}")

# (3) numerical coker(d mu) rank at balanced point n=4,k=4 (both factors corank 2, aligned) -> expect deficit a*c=4
import numpy as np
np.random.seed(1)
n=4
# P corank2 (ker=<e1,e2>), Z corank2 (im=<e1,e2,?>)... build both drop 2 and align 2
# ker P = span(e1,e2): P[:,0]=P[:,1]=0
P=np.random.randn(4,4); P[:,0]=0; P[:,1]=0
# coker P = span(e_last two)? make im P = span(e1,e2): rows 3,4 zero
P=np.zeros((4,4)); P[0,2]=1;P[0,3]=0.5;P[1,2]=0.3;P[1,3]=1  # rank 2, im=<e1,e2>, ker=<e1,e2>
# Z rank2, im Z = span(e1,e2) (so im Z subset ker P, alignment e=2)
Z=np.zeros((4,4)); Z[0,:]=np.random.randn(4); Z[1,:]=np.random.randn(4)  # im Z=<e1,e2>
PZ=P@Z
print("\nn=4,k=4 balanced: rank P,Z,PZ =",np.linalg.matrix_rank(P),np.linalg.matrix_rank(Z),np.linalg.matrix_rank(PZ))
# d mu image: {dP Z + P dZ}. coker dim = 16 - rank(image map)
rows=[]
for i in range(4):
  for j in range(4):
    dP=np.zeros((4,4)); dP[i,j]=1; rows.append((dP@Z).flatten())
for i in range(4):
  for j in range(4):
    dZ=np.zeros((4,4)); dZ[i,j]=1; rows.append((P@dZ).flatten())
M=np.array(rows)  # 32 x 16
img_rank=np.linalg.matrix_rank(M,tol=1e-9)
print("dim image(d mu) =",img_rank,"; coker dim =",16-img_rank,"(expect a*c=2*2=4)")
