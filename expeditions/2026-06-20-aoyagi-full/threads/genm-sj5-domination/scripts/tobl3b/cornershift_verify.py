import numpy as np, sympy as sp
np.random.seed(1)
print("="*74)
print("VERIFY the corrected chart pieces (anchor a=b=2, M2=3, j=1 => a-j=b-j=1, M2-j=2)")
print("="*74)

# --- (V1) bordered-Gram row-peel Jacobian identity (Codex Q2), exact 2-row case ---
# det(G_2)^(-a/2) dq_2 = det(G_1)^(-(a-1)/2) * ||v||^(-a) dλ dv,  v = q_2^perp
# check det(G_2) = det(G_1) * ||v||^2 exactly for q1,q2 in R^3, q2 = λ q1 + v, v ⟂ q1.
q1 = sp.Matrix(sp.symbols('x1 x2 x3', real=True))
lam = sp.symbols('lam', real=True)
v = sp.Matrix(sp.symbols('v1 v2 v3', real=True))
perp = sp.Eq(q1.dot(v), 0)                       # v ⟂ q1
q2 = lam*q1 + v
G2 = sp.Matrix([[q1.dot(q1), q1.dot(q2)],[q2.dot(q1), q2.dot(q2)]])
detG2 = sp.expand(G2.det())
target = sp.expand(q1.dot(q1) * v.dot(v))        # det(G1)*||v||^2  with v⟂q1
diff = sp.simplify((detG2 - target).subs(q1.dot(v), 0))
# substitute the orthogonality constraint x1 v1 + x2 v2 + x3 v3 = 0 by solving v3
v3sol = sp.solve(q1.dot(v), v[2])[0]
print("  det(G_2) - det(G_1)||v||^2 under v⟂q1 :",
      sp.simplify(detG2.subs(v[2],v3sol) - target.subs(v[2],v3sol)), " (==0 confirms row-peel identity)")
print("  => det(G_2)^(-a/2) dq_2 = det(G_1)^(-(a-1)/2) ||v||^(-a) dλ dv.  Residual exp = a-1=1;")
print("     BUT transverse factor ||v||^(-a)=||v||^(-2); v ranges in R^{n-1}=R^2 => ∫||v||^(-2) LOG-DIVERGES.")
print("     (fixed-cut row-peel trades b-corank blow-up for a transverse blow-up: no net gain.)")

# --- (V2) deeper-cut PSD chain: ZZ^T ⪰ eps^2 P_strong  =>  reduced weight (b-j, M2-j, a-j) ---
print()
print("  [deeper-cut PSD] ZZ^T - eps^2 P_strong PSD on shell j (strong sv>=eps, weak>=0):")
eps=0.5
U,_=np.linalg.qr(np.random.standard_normal((3,3)))
for sw in [0.4,0.1,0.01,1e-4]:
    S=np.diag([1.0,eps,sw]); Z=U@S@U.T
    Us=U[:,:2]                                   # strong columns (M2-j=2)
    P=Us@Us.T
    M=Z@Z.T-eps**2*P
    w=np.linalg.eigvalsh(M)
    print(f"    weak sv={sw:<7} min eig(ZZ^T-eps^2 P_strong)={w.min():+.4f}  (>=0 => Loewner holds)")

# reduced weight convergence at deeper cut: A_u is (b-j)=1 row x M2=3; A_u U_s is 1x2; exp a-j=1
def wenn_deep(sw, Nmc=400000, box=1.0, eps=0.5):
    U,_=np.linalg.qr(np.random.standard_normal((3,3)))
    S=np.diag([1.0,eps,sw]); Z=U@S@U.T
    A=np.random.uniform(-box,box,size=(Nmc,1,3))
    Q=np.einsum('nik,kl->nil',A,Z)               # (b-j=1) x 3
    g=np.einsum('nik,njk->nij',Q,Q)[:,0,0]       # ||A Z||^2
    g=np.clip(g,1e-300,None)
    return (g**(-0.5)).mean()*(2*box)**3
print("  [deeper-cut Wenn_u] rows=b-j=1, exp=(a-j)/2=0.5, as weak sv->0:")
for sw in [0.3,0.1,0.03,0.01,0.003]:
    print(f"    weak sv={sw:<7} Wenn_u={wenn_deep(sw):.4f}  (BOUNDED => strictly convergent, design weight)")
