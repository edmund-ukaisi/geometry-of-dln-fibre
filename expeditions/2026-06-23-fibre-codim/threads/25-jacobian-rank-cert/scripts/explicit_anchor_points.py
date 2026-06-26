import sympy as sp
# Explicit generic top-component points + exact Jacobian rank, for the certificate.
# General construction of a generic top-component point of mult^{-1}(E), E=diag(I_r,0):
#   The top component's running-rank profile drops to r AS EARLY as the narrowest residual allows,
#   keeping the LATER factors generic full rank. Concretely (the (p1=r-at-front) profile that we
#   verified is top for (2,2,3) r=1): make the FIRST factor carry the rank to r, later factors
#   generic full-rank injective-on-the-r-channel. This is the "front bottleneck" generic point.
#
# Anchor 1: (2,2,2) r=1. A_0 rank 1, A_1 rank 2 (full), A_1 A_0 = E.
def jacrank_2fac(d, A0v, A1v):
    a=sp.symbols(f'a0:{d[1]*d[0]}'); b=sp.symbols(f'b0:{d[2]*d[1]}')
    mA0=sp.Matrix(d[1],d[0], lambda i,j: a[i*d[0]+j])
    mA1=sp.Matrix(d[2],d[1], lambda i,j: b[i*d[1]+j])
    M=mA1*mA0
    outs=[M[i,j] for i in range(d[2]) for j in range(d[0])]
    vs=list(a)+list(b)
    J=sp.Matrix([[sp.diff(o,v) for v in vs] for o in outs])
    subs={}
    for i in range(d[1]):
        for j in range(d[0]): subs[a[i*d[0]+j]]=A0v[i,j]
    for i in range(d[2]):
        for j in range(d[1]): subs[b[i*d[1]+j]]=A1v[i,j]
    return J.subs(subs).rank(), M.subs(subs)

# (2,2,2) r=1: A0 = e1 e1^T-ish rank1 with A1 A0 = E.
# Take A0 = [[1,0],[0,0]] (rank1), A1 = [[1, x],[0, y]] with A1 A0 = [[1,0],[0,0]]=E, x,y generic, y!=0 => rank2
A0=sp.Matrix([[1,0],[0,0]]); A1=sp.Matrix([[1,2],[0,3]])
rk,prod=jacrank_2fac([2,2,2],A0,A1)
print(f"(2,2,2) r=1: A0={A0.tolist()} A1={A1.tolist()} prod={prod.tolist()} rank={rk} (C+delta=4)")

# (2,2,2) r=0: A0 rank1, A1 rank1, im A0 ⊆ ker A1. A0=[[1,1],[0,0]], A1=[[0,1],[0,1]]
A0=sp.Matrix([[1,1],[0,0]]); A1=sp.Matrix([[0,1],[0,1]])
rk,prod=jacrank_2fac([2,2,2],A0,A1)
print(f"(2,2,2) r=0: A0={A0.tolist()} A1={A1.tolist()} prod={prod.tolist()} rank={rk} (C+delta=3)")

# (2,2,2) r=2: A0=A1=I (full rank), prod=I=E. 
A0=sp.eye(2); A1=sp.eye(2)
rk,prod=jacrank_2fac([2,2,2],A0,A1)
print(f"(2,2,2) r=2: A0=I A1=I prod={prod.tolist()} rank={rk} (C+delta=4)")

# (3,2,3) r=1: A0 (2x3), A1 (3x2). mult 3x3. E=diag(1,0,0). C=2,delta=5,C+delta=7. d_N d_0=9.
# top comp: A0 rank1 carries channel. A0=[[1,0,0],[0,0,0]] (2x3 rank1), A1 such that A1 A0 = E (3x3).
# A1 A0: A1 (3x2). (A1 A0)[i,j] = sum_k A1[i,k] A0[k,j]. A0 row0=(1,0,0),row1=(0,0,0).
# (A1 A0)[i,j] = A1[i,0]*A0[0,j] = A1[i,0]*(j==0). So col0 = A1[:,0], cols1,2=0. Need = E=diag(1,0,0):
# col0 = (1,0,0). A1[:,0]=(1,0,0). A1[:,1] generic => A1 rank up to 2. A1=[[1,a],[0,b],[0,c]].
A0=sp.Matrix([[1,0,0],[0,0,0]]); A1=sp.Matrix([[1,2],[0,3],[0,5]])
rk,prod=jacrank_2fac([3,2,3],A0,A1)
print(f"(3,2,3) r=1: A0={A0.tolist()} A1={A1.tolist()} prod={prod.tolist()} rank={rk} (C+delta=7)")
