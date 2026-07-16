import sympy as sp

# Exact codim of {B·W = 0} at a smooth rank-r point, via Jacobian rank over Q.
# Φ(B,W)=B·W (B: p×q, W: q×n). At B rank r (cols of W in ker B), codim = rank dΦ.
# thresholdhunt formula: codim Z_r = (p-r)(q-r) + r·n ; minAdm = min_r.
def codim_at_rank(p,q,n,r):
    # Build explicit rational B0 of rank r: diag-ish; W0 with columns in ker(B0).
    B0=sp.zeros(p,q)
    for i in range(r): B0[i,i]=1              # rank r
    # ker(B0) = columns e_r..e_{q-1}; put W0 rows: W0 is q×n, need cols of W0 in ker B0
    # B0·W0=0 => rows 0..r-1 of W0 must be 0 (since B0 picks first r rows). Put W0 nonzero in rows r..q-1.
    W0=sp.zeros(q,n)
    kk=0
    for i in range(r,q):
        for j in range(n):
            W0[i,j]=sp.Rational(1+((i*7+j*3)%5),3)   # generic-ish rationals in ker
    # differential dΦ(dB,dW)=dB·W0+B0·dW as a linear map on (dB,dW) -> p×n
    dB=sp.Matrix(p,q,lambda i,j: sp.Symbol(f'b_{i}_{j}'))
    dW=sp.Matrix(q,n,lambda i,j: sp.Symbol(f'w_{i}_{j}'))
    out=dB*W0+B0*dW
    syms=list(dB)+list(dW)
    J=sp.Matrix([[sp.diff(out[i,j],s) for s in syms] for i in range(p) for j in range(n)])
    return J.rank()

def minAdm3(M0,M1,M2):
    return min((M0-r)*(M1-r)+r*M2 for r in range(0,min(M0,M1)+1))

for (M0,M1,M2,label) in [(6,6,6,'(6,6,6)'),(4,4,4,'(4,4,4)'),(3,3,3,'(3,3,3)')]:
    mA=minAdm3(M0,M1,M2)
    argmins=[r for r in range(0,min(M0,M1)+1) if (M0-r)*(M1-r)+r*M2==mA]
    print(f"{label}: minAdm={mA} (T1={sp.Rational(mA,2)}), argmin r={argmins}")
    for r in range(0,min(M0,M1)+1):
        c=codim_at_rank(M0,M1,M2,r); form=(M0-r)*(M1-r)+r*M2
        star=' <-- MIN' if form==mA else ''
        print(f"    r={r}: Jac-codim={c}  formula (M0-r)(M1-r)+r*M2={form}  match={c==form}{star}")
