"""
The genuine blow-up atlas incidenceCell_lintegral_le: the determinantal big-cell chart for rank-l W.
W (u x d).  On the chart where the top-left l x l minor W11 is invertible:
    W = [[W11, W12],[W21, W22]],   coords (W11, W12, W21, E),  E := W22 - W21 W11^{-1} W12.
  {rank W = l}  <=>  {E = 0}.   The map W <-> (W11,W12,W21,E) is a TRANSLATION in W22 (E = W22 - const),
  so its Jacobian is IDENTICALLY 1 (explicit, C^inf on {det W11 != 0}).  E is the transverse Schur block.
Verify: (i) Jac=1; (ii) rank W = l + rank E  (so E=0 <=> rank<=l); (iii) the loss ||Y W||^2 monomializes:
  near E->0 the transverse directions are exactly the entries of E, codim contribution matches C_ls.
Also the H-tilde fiber: int_{H in R^{ub}} (||H||^2 + tau^2)^{-q} ~ tau^{ub-2q}  (standard polar/fiber CoV).
"""
import numpy as np
rng=np.random.default_rng(2)

def bigcell_check(u,d,l):
    # random W with the big-cell coords
    W11=rng.standard_normal((l,l))
    while abs(np.linalg.det(W11))<0.3: W11=rng.standard_normal((l,l))
    W12=rng.standard_normal((l,d-l)); W21=rng.standard_normal((u-l,l)); E=rng.standard_normal((u-l,d-l))
    W22=W21@np.linalg.inv(W11)@W12 + E
    W=np.block([[W11,W12],[W21,W22]])
    # (ii) rank W = l + rank E
    rW=np.linalg.matrix_rank(W); rE=np.linalg.matrix_rank(E)
    ok_rank = (rW == l+rE)
    # (i) Jacobian of (W11,W12,W21,E) -> W : identity except W22 = f(...)+E, block-triangular unit-diagonal => det 1
    #     build the linear map d(coords)->d(W) and check |det| = 1  (it's affine in coords with unit Jacobian)
    n=u*d
    J=np.zeros((n,n)); idx=0; base=[W11,W12,W21,E]
    def assembleW(W11,W12,W21,E):
        return np.block([[W11,W12],[W21, W21@np.linalg.inv(W11)@W12+E]])
    W0=assembleW(W11,W12,W21,E); eps=1e-6
    cols=[]
    for blk,shape in [('W11',(l,l)),('W12',(l,d-l)),('W21',(u-l,l)),('E',(u-l,d-l))]:
        for i in range(shape[0]):
            for j in range(shape[1]):
                p={'W11':W11.copy(),'W12':W12.copy(),'W21':W21.copy(),'E':E.copy()}
                p[blk][i,j]+=eps
                dW=(assembleW(p['W11'],p['W12'],p['W21'],p['E'])-W0)/eps
                cols.append(dW.reshape(-1))
    J=np.array(cols).T
    detJ=abs(np.linalg.det(J))
    ok_jac = np.isclose(detJ,1.0,rtol=1e-3)
    return ok_jac, ok_rank, detJ, rW, l+rE

print("=== determinantal big-cell chart W<->(W11,W12,W21,E), E=Schur transverse block ===")
for (u,d,l) in [(2,2,1),(2,4,1),(3,3,1),(3,3,2),(2,2,0),(3,4,2)]:
    if l>min(u,d): continue
    okj,okr,dj,rW,lr=bigcell_check(u,d,l)
    print(f"  u={u} d={d} l={l}: Jac=1? {okj} (|det|={dj:.4f})   rank W = l+rank E? {okr} (rankW={rW}, l+rankE={lr})")

# H-tilde fiber exponent
from scipy import integrate
def Hfiber(ub,q,tau):
    # int_{R^ub}(||H||^2+tau^2)^{-q} dH ~ C * tau^{ub-2q} (radial). numeric radial:
    val,_=integrate.quad(lambda r:(r*r+tau*tau)**(-q)*r**(ub-1),0,50,limit=200)
    return val
print("\n=== H-tilde fiber int_{R^{ub}}(||H||^2+tau^2)^{-q} ~ tau^{ub-2q} ===")
for ub in [1,2,4]:
    q=ub/2+0.4
    taus=[0.2,0.1,0.05]; vals=[Hfiber(ub,q,t) for t in taus]
    sl=np.polyfit(np.log(taus),np.log(vals),1)[0]
    print(f"  ub={ub} q={q}: fiber slope={sl:+.3f}  predict ub-2q={ub-2*q:+.3f}")
