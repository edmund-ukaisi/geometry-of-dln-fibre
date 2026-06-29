import sympy as sp
# M=(2,3,2). flatDim = 2*3 + 3*2 = 12. minAdm=4. 
# Convention from 222 (M=(2,2,2): Text=[2,2,1], single boundary k=1 with t=1, leaf k=2).
# For (2,3,2): Text = [M0=2, M0=2, drop=1]? achiever T* deepest. Text=[2,2,1]? then Text[2]=1.
# Wext=[2,3,2].
# Boundaries: k=0 identity (Text0=Text1=2, c0=Wext0-Text1=2-2=0). 
#   k=1 genuine: Text1=2, Text2=1. t (the K-core size) = Text2 = 1. r = Text1 - Text2 = 1. c1 = Wext1 - Text2 = 3-1 = 2.
#   leaf k=2: C2 = u*Rfin2,  Text2=1 rows.
# Let me just lay out the 12 free coords analogous to 222 and compute.
# Decoder blocks:
#  Bmat1: Text1 x Text2 = 2x1   (K-core column, the Schur frame)
#  Nblk1: Text2 x (Wext1 - Text2) = 1 x 2
#  Wblk1: (Wext1 - Text2) x Wext2 = 2 x 2
#  Rmat1: Text1 x Wext1 = 2 x 3  (u-scaled E block; free entries on the 'pivot' positions)
#  Rfin2: Text1 x Wext2 = ? leaf C2 = u*Rfin2, with Text? -- C2 has Text2=1 rows? 
# Actually C_{L}=C_2 = u*Rfin2 ; C2 shape = Text2 x Wext2? No: C_k shape = Text_k x Wext_k.
#   C2 shape = Text2 x Wext2 = 1 x 2. So Rfin2 is 1x2.
# E-block Rmat1: in 222, Rmat1 = [[0,0],[0,x6]] (Text1=2 x Wext1=2), ONE free entry x6 at the bottom-right.
#   The free E entries sit in the bottom-(r x c?) corner. For 222: r=1,c=1 -> 1 free E entry. minAdm=3 = 1(E)+2(leaf:1 pivot + x7).
#   Wait 222 leaf C2 = u*[1,x7] (1x2): the '1' is the FIXED pivot (gives u itself), x7 is 1 free.
#     radial active = {0(=u pivot/the '1'), 6 (E free), 7 (leaf free)} = 3 = minAdm. 
#   So #radial = 1 (the fixed-pivot 'u' direction) + #(free E entries) + #(free leaf entries).
# For (2,3,2): leaf C2 = u*Rfin2 (1x2). Rfin2 = [1, ζ]? with one fixed '1' pivot + (Wext2-1)=1 free? 
#   E block Rmat1 (2x3): free entries = r*c? with r=Text1-Text2=1, c=Wext1-Text2=2 => r*c=2 free E entries? 
# Let me just BUILD it with the same skeleton as 222 generalized and check det & radial count.
u=sp.Symbol('u',real=True)
# free params:
# K-core Bmat1 (2x1): the Schur frame K rows. Following 3333 B1 pattern (LDU-coordinatized), 
#   for t=1: K is 1x1 -> Bmat1 column = [b ; l*b] (2x1) with b the K pivot, l the X-lift.
b,l = sp.symbols('b l',real=True)
Bmat1 = sp.Matrix([[b],[l*b]])
# Nblk1 (1x2): chaining residual N
n1,n2 = sp.symbols('n1 n2',real=True); N1=sp.Matrix([[n1,n2]])
# Wblk1 (2x2): the lift W
w=sp.symbols('w0:4',real=True); W1=sp.Matrix([[w[0],w[1]],[w[2],w[3]]])
# Rmat1 (2x3) u-scaled E: free entries in the bottom r x c corner. r=1,c=2 => bottom row last 2 cols.
e1,e2=sp.symbols('e1 e2',real=True); R1=sp.Matrix([[0,0,0],[0,e1,e2]])
# leaf C2 = u*Rfin2 (1x2): Rfin2 = [1, z] (pivot 1 + 1 free)
z=sp.symbols('z',real=True); Rfin2=sp.Matrix([[1,z]])
# chainQ(N1) = [I_{Text2=1} | N1] = 1x3
qN1=sp.Matrix.hstack(sp.eye(1),N1)   # 1x3
C2 = u*Rfin2                          # 1x2
C1 = Bmat1*qN1 + u*R1                 # (2x1)(1x3)+u*(2x3) = 2x3
# A0 = C1 (boundary0 identity, c0=0): 2x3
A0 = C1
# A1: kept rows = C2 - N1 W1? wait shapes: kept = C_{2} - N_1 W_1. N1:1x2, W1:2x2 -> N1 W1:1x2. C2:1x2. kept:1x2.
#     lift rows = W1 (2x2)? but Wext2=2 cols. lift rows = W1 = (Wext1-Text2)x Wext2 = 2x2. 
#     A1 rows = Text2 + (Wext1-Text2) = 1+2 = 3 = Wext1. cols = Wext2 = 2. So A1: 3x2.
A1 = sp.Matrix.vstack(C2 - N1*W1, W1)  # (1x2 stacked over 2x2) = 3x2
allvars=[u,b,l,n1,n2,w[0],w[1],w[2],w[3],e1,e2,z]
print("num free params:", len(allvars), "(flatDim expect 12)")
F=[]
for A in (A0,A1):
    for i in range(A.rows):
        for j in range(A.cols):
            F.append(sp.expand(A[i,j]))
print("num outputs:", len(F))
F=sp.Matrix(F)
xv=sp.Matrix(allvars)
J=F.jacobian(xv)
d=sp.factor(J.det())
print("(2,3,2) chart det =", d)
print("minAdm(2,3,2)=4. radial pivot should be u to power minAdm-1 = 3.")
# radial active = {u} ∪ {free R/Rfin entries} = {u, e1, e2, z}  (4 = minAdm). check radial blowup det:
active_idx={0, allvars.index(e1), allvars.index(e2), allvars.index(z)}
def pbon(active,p,vec): 
    return sp.Matrix([vec[p] if i==p else (vec[p]*vec[i] if i in active else vec[i]) for i in range(len(vec))])
Jrad=sp.factor(pbon(active_idx,0,xv).jacobian(xv).det())
print("radial blowup det on {u,e1,e2,z} (card 4 = minAdm) =", Jrad)
print("chart det / radial det =", sp.factor(d/Jrad), " (should be u-FREE boundary part)")
print("boundary part has u?", u in sp.factor(d/Jrad).free_symbols)
