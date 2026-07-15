import numpy as np
rng=np.random.default_rng(3)

# (3,4,5,4)@u=2:  a=1,b=2, M2=5,M3=4.  Z=A2 (5x4). A_cor (b x M2)=(2x5). Q_b=A_cor@A2 (2x4).
# charge = det(Q_b Q_b^T)^{-a/2} = det(2x2)^{-1/2}.  reassembly: residual det(A2^T A2)^{-1} DIVERGENT.
# TEST honest A_cor-box charge J(A2) as A2 -> rank drop (codim |5-4|+1=2 for full det(A2^T A2)=0).
def J_acor(A2,N=300000):
    Ac=rng.uniform(-1,1,(N,2,5))
    Qb=Ac@A2                        # N,2,4
    G=Qb@np.transpose(Qb,(0,2,1))   # N,2,2
    d=np.linalg.det(G)              # N
    val=np.where(d>1e-300, d**(-0.5), 0.0)
    return val.mean()*(2.0**10)     # box vol [-1,1]^(2x5)=2^10

# family A2 = U diag(s1,s2,s3,sigma) V^T, 5x4 (U 5x5, V 4x4), sigma->0 (rank 4->3)
U,_=np.linalg.qr(rng.standard_normal((5,5)))
V,_=np.linalg.qr(rng.standard_normal((4,4)))
print("(3,4,5,4)@u=2  a=1,b=2:  honest A_cor charge J(A2) vs sigma_min(A2)")
print(" sigma     det(A2^T A2)   J(A2)          J*det^{1}")
for sig in [1.0,0.3,0.1,0.03,0.01,0.003,0.001]:
    S=np.zeros((5,4)); S[0,0]=1.0;S[1,1]=0.8;S[2,2]=0.6;S[3,3]=sig
    A2=U@S@V.T
    dG=np.linalg.det(A2.T@A2)
    j=J_acor(A2)
    print(f" {sig:7.4f}  {dG:11.3e}   {j:11.4f}    {j*dG:9.3e}")
print(" -> if J stays BOUNDED as sigma->0, reassembly's 'det(A2^T A2)^{-1} divergent' residual is a lossy over-estimate.")
