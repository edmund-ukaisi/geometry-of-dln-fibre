import numpy as np, sympy as sp
rng = np.random.default_rng(2)

print("="*72)
print("STEP 3: the weight FACTORS -> recursion made explicit (square (2,2,2))")
print("="*72)
# (b,m,q)=(2,2,2): Q=YA, det(QQ^T)=det(Q)^2, |det Q|^{-a}=|det Y|^{-a}|det A|^{-a}.
Y=sp.Matrix(2,2,lambda i,j:sp.Symbol(f'y{i}{j}'))
A=sp.Matrix(2,2,lambda i,j:sp.Symbol(f'a{i}{j}'))
Q=Y*A
lhs=sp.expand((Q*Q.T).det())
rhs=sp.expand((Y.det()*A.det())**2)
print("det(QQ^T) - (detY detA)^2 =", sp.simplify(lhs-rhs))
print("=> det(QQ^T)^{-a/2} = |detY|^{-a} * |detA|^{-a}: the A-factor is the SAME")
print("   determinantal weight one layer deeper (the Jacobian J = |detA|^{-a}).")
print("   Composite integral = (int|detY|^-a)(int|detA|^-a); each finite iff a<1.")
print("   free(2,2)=q-b+1=1, twist=1 -- all agree; threshold=1 (NOT 2).")

print()
print("="*72)
print("STEP 4: 3-layer tail  Qb = Y*A2*A3  -- does J itself recurse (product)?")
print("="*72)
# chain (b, m1, m2, q):  Y: b x m1, A2: m1 x m2, A3: m2 x q.
def gram_det_prod3(b,m1,m2,q,N):
    Y=rng.uniform(-1,1,size=(N,b,m1)); A2=rng.uniform(-1,1,size=(N,m1,m2)); A3=rng.uniform(-1,1,size=(N,m2,q))
    Q=np.einsum('nij,njk,nkl->nil',Y,A2,A3)
    G=np.einsum('nij,nkj->nik',Q,Q)
    return np.abs(np.linalg.det(G))
def est_2lct(d):
    d=d[d>0]; eps=np.array([1e-2,1e-3,1e-4,1e-5,1e-6,1e-7,1e-8])
    fr=np.array([(d<e).mean() for e in eps]); ok=fr>50/len(d)
    le,lf=np.log(eps[ok]),np.log(fr[ok])
    return 2*np.polyfit(le[-4:],lf[-4:],1)[0] if ok.sum()>=3 else np.nan
cases3=[(1,1,2,2),(1,2,1,2),(1,2,2,2),(1,2,2,1),(1,1,1,2),(2,2,3,3),(1,3,2,2)]
print(" (b,m1,m2,q): est 2lct   free(q-b+1)   twist=min(tail widths m1,m2,q)-b+1")
for (b,m1,m2,q) in cases3:
    e=est_2lct(gram_det_prod3(b,m1,m2,q,4_000_000))
    free=q-b+1; twist=min(m1,m2,q)-b+1
    print(f"  ({b},{m1},{m2},{q}): est={e:.3f}   free={free}   twist(min-b+1)={twist}")
print()
print("=> threshold tracks TWIST = min over ALL tail widths - b + 1, the minAdm")
print("   structure of the SHORTER corank chain -- a genuine deeper recursion,")
print("   NOT the free-Q value q-b+1.")
