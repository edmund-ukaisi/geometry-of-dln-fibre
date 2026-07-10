"""
THE HEART of normalSlice_transfer: does the PRODUCT's Schur complement FACTOR as the reduced product?

Front-peel needs reduced chain (m1-q,...,mL-q) -- ALL tail widths reduced by q (verified: reduce-but-last
gives the WRONG minAdm). Geometrically: {rank P <= q} <=> {Schur(P) = 0}, Schur(P) : (m1-q)x(mL-q).
P is a PRODUCT, so Schur(P) must factor as Y1...Y_{L-1} of the reduced chain (m1-q,...,mL-q) -- the MIDDLE
widths reduce too. This factorization is the normal-slice iso.

Test:  Schur(A1 A2)  ==  Y1 . Y2 ?   with Yi the individual Schur complements (mi-q)x(m_{i+1}-q).
Block decomposition per factor: Ai = [[alpha_i, beta_i],[gamma_i, delta_i]], q + (mi-q) rows/cols.
"""
import sympy as sp
from functools import lru_cache
from itertools import product as iproduct

@lru_cache(None)
def minAdm(M):
    M=tuple(M)
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

def blk(name,r,c): return sp.Matrix(r,c,lambda i,j: sp.Symbol(f"{name}_{i}_{j}"))

def schur_of_product_factors(m1,m2,m3,q):
    """A1:(m1 x m2), A2:(m2 x m3). Block by q+(mi-q). Return Schur(A1A2) and Y1.Y2, symbolic diff."""
    A1=blk("a",m1,m2); A2=blk("b",m2,m3)
    a1=A1[:q,:q]; b1=A1[:q,q:]; c1=A1[q:,:q]; d1=A1[q:,q:]
    a2=A2[:q,:q]; b2=A2[:q,q:]; c2=A2[q:,:q]; d2=A2[q:,q:]
    P=A1*A2
    P11=P[:q,:q]; P12=P[:q,q:]; P21=P[q:,:q]; P22=P[q:,q:]
    SchurP = sp.simplify(P22 - P21*P11.inv()*P12)          # (m1-q)x(m3-q)
    Y1 = sp.simplify(d1 - c1*a1.inv()*b1)                   # (m1-q)x(m2-q)
    Y2 = sp.simplify(d2 - c2*a2.inv()*b2)                   # (m2-q)x(m3-q)
    diff = sp.simplify(SchurP - Y1*Y2)
    return diff, SchurP.shape, (Y1.shape, Y2.shape)

print("TEST 1: Schur(A1 A2) == Y1 . Y2  (naive product of Schur complements)?")
for (m1,m2,m3,q) in [(2,2,2,1),(3,3,3,1),(3,3,4,1),(4,4,4,2)]:
    diff,sh,ysh=schur_of_product_factors(m1,m2,m3,q)
    zero = diff==sp.zeros(*sh)
    print(f"   ({m1},{m2},{m3}) q={q}: Schur(P) shape {sh}, Y1,Y2 shapes {ysh}, "
          f"Schur(P)==Y1Y2? {zero}")
