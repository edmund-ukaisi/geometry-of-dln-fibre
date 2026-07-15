import numpy as np
rng = np.random.default_rng(0)

# (4,4,4,4) @ u=3:  a = M0-u = 1, b = M1-u = 1, M2 = 4.  A_cor is b x M2 = 1x4; A2 is 4x4.
# charge = det((A_cor A2)(A_cor A2)^T)^{-a/2} = ||A_cor A2||^{-1}   (a=1,b=1)
# TEST: does the HONEST A_cor-BOX integral J(A2) = int_{A_cor in [-1,1]^4} ||A_cor A2||^{-1} dA_cor
#       blow up as A2 -> rank drop (det A2 -> 0)?  (reassembly: ~ |det A2|^{-1}, diverges;
#       deepgate: bounded, gamma_3 = 0 inert.)

def J_acor(A2, N=400000):
    # Monte-Carlo over A_cor in box [-1,1]^(1x4), volume 2^4=16
    Ac = rng.uniform(-1,1,size=(N,4))       # rows = samples of A_cor (1x4)
    Q  = Ac @ A2                             # N x 4  = A_cor A2
    nrm = np.sqrt((Q*Q).sum(axis=1))         # ||A_cor A2||
    # charge = nrm^{-1}; guard exact zeros (measure 0)
    val = np.where(nrm>0, 1.0/nrm, 0.0)
    return val.mean()*16.0

# family: A2 = U diag(1,1,1,sigma) V^T, sigma -> 0  (rank drops 4->3, codim 1 = {det=0})
U,_ = np.linalg.qr(rng.standard_normal((4,4)))
V,_ = np.linalg.qr(rng.standard_normal((4,4)))
print("sigma      det(A2)      J(A2)=int_box ||A_cor A2||^{-1}   J*|det|")
for sigma in [1.0,0.3,0.1,0.03,0.01,0.003,0.001,0.0003,0.0001]:
    S = np.diag([1.0,1.0,1.0,sigma])
    A2 = U@S@V.T
    d  = abs(np.linalg.det(A2))
    j  = J_acor(A2)
    print(f"{sigma:8.4f}  {d:10.3e}   {j:12.5f}          {j*d:10.4e}")
