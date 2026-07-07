import sympy as sp
from sympy import Rational as R
import random

def blk(A11,A12,A21,A22):
    n1=A11.shape[0]; n2=A22.shape[0]
    M=sp.zeros(n1+n2,n1+n2)
    M[:n1,:n1]=A11; M[:n1,n1:]=A12; M[n1:,:n1]=A21; M[n1:,n1:]=A22
    return M
def parts(M,n1): return M[:n1,:n1],M[:n1,n1:],M[n1:,:n1],M[n1:,n1:]
def schur(M,n1):
    A,B,C,D=parts(M,n1); return D - C*A.inv()*B
def small(): return R(random.randint(-3,3),random.randint(20,30))  # ~ +-0.1
def rand_layer(r,m):
    X=sp.Matrix(r,r,lambda i,j: small()); Y=sp.Matrix(r,m,lambda i,j: small())
    Z=sp.Matrix(m,r,lambda i,j: small()); T=sp.Matrix(m,m,lambda i,j: small())
    return blk(sp.eye(r)+X,Y,Z,T),X,Y,Z,T
def per_layer_S(r,X,Y,Z,T): return T - Z*(sp.eye(r)+X).inv()*Y

def test_2factor(r,m,ntest=5):
    ok=True
    for _ in range(ntest):
        A,XA,YA,ZA,TA=rand_layer(r,m); B,XB,YB,ZB,TB=rand_layer(r,m)
        AB=A*B; SchAB=schur(AB,r)
        SA=per_layer_S(r,XA,YA,ZA,TA); SB=per_layer_S(r,XB,YB,ZB,TB)
        P11=(AB)[:r,:r]; K=ZB*P11.inv()*YA
        rhs=SA*(sp.eye(m)-K)*SB
        if sp.simplify(SchAB-rhs)!=sp.zeros(m,m): ok=False
    print(f"2-factor r={r},m={m}: Sch(AB)=S_A(I-K)S_B, K=B21(AB)11^-1 A12 :", "HOLDS" if ok else "FAILS")

def test_recursion_L(r,m,L,ntest=4):
    # Build L layers; compute Sch(prod) and the recursive interspersed factorization
    ok=True; unitI=True
    for _ in range(ntest):
        layers=[rand_layer(r,m) for _ in range(L)]
        Cs=[l[0] for l in layers]; Ss=[per_layer_S(r,l[1],l[2],l[3],l[4]) for l in layers]
        # partial products P_k = C0..Ck ; recursion Sch(P_k)=Sch(P_{k-1})(I-K_k)Sch(C_k)
        P=Cs[0]; Sch_prev=Ss[0]
        factors=[Ss[0]]  # S0
        Ks=[]
        for k in range(1,L):
            Pk=P*Cs[k]
            P11=Pk[:r,:r]
            A12=P[:r,r:]          # (P_{k-1})_12
            B21=Cs[k][r:,:r]      # (C_k)_21 = Z_k
            Kk=B21*P11.inv()*A12  # coupling
            factors.append(sp.eye(m)-Kk); factors.append(Ss[k])
            Ks.append(Kk)
            P=Pk
        Sch_full=schur(P,r)
        prodfac=factors[0]
        for f in factors[1:]: prodfac=prodfac*f
        if sp.simplify(Sch_full-prodfac)!=sp.zeros(m,m): ok=False
    print(f"recursion r={r},m={m},L={L}: Sch(prod)=S0 (I-K1)S1 (I-K2)S2...(I-K_{{L-1}})S_{{L-1}} :", "HOLDS" if ok else "FAILS")

random.seed(3)
for (r,m) in [(1,1),(1,2),(2,1),(2,2)]: test_2factor(r,m)
print()
for (r,m) in [(1,1),(1,2),(2,2)]:
    for L in [3,4]: test_recursion_L(r,m,L)
