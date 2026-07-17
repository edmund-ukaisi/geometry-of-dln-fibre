import numpy as np
np.random.seed(3)
print("E. ENGINE'S OWN CANONICAL EXAMPLE  M=(4,4,4,4), t=2 (a=b=2, min-corank=2)")
print("   tailChain=(4,4,4) -> Q = A1·A2, BOTH 4x4 SQUARE; n=t+b=4, q=4, a=M0-t=2")
oks=[]
for _ in range(100):
    A1=np.random.randn(4,4); A2=np.random.randn(4,4); Q=A1@A2
    lhs=np.linalg.det(Q@Q.T); rhs=np.linalg.det(A1)**2*np.linalg.det(A2)**2
    oks.append(np.isclose(lhs,rhs,rtol=1e-8))
print(f"   det(QQᵀ)=det(A1)²·det(A2)² exact: {all(oks)}  =>")
print(f"   ∫det(QQᵀ)^-a/2 = (∫|det A1|^-2)·(∫|det A2|^-2) = ∞·∞   (each factor diverges, a=2>1)")
print("   free-Q baseline (4x4): a<q-n+1=1 => a=2 diverges too; but CONSTANT-WIDTH product = ∞^(L+1).")
print("   The TRUE socket T is FINITE here (engine's own budget (4,4,4,4)@t=2 A_r=[0,1,4]->11=minAdm).")
print("   => collapsed clean-det-power obligation 2 is +∞ where the true iterated integral converges. FALSE.")
