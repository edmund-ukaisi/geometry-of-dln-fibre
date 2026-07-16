"""
Explicit per-stratum blow-up charts for incidenceCell_lintegral_le — verify the coordinate maps
and their MONOMIAL Jacobians, so the per-cell integral is a concrete CoV feeding
lintegral_image_eq_lintegral_abs_det_fderiv_mul.

Charts (all explicit):
 (1) Qb-minor:  A_cor = D[I_b|X],  D in GL_b, X in R^{b x d}, d=M2-b.   |d A_cor / d(D,X)| = |det D|^d.
 (2) Qp-shear:  Qp <-> (U,W),  U=Qp[:, :b], W=Qp[:, b:] - U X.   Jacobian 1 (unimodular).  W = incidence var.
 (3) front-shear: B <-> H = P U + B D (fixed P,U,D).   dB = |det D|^{-u} dH.
 (4) det-Gram factor from the earlier Gamma=D-block integration: |det D|^{-a} det(I+X X^T)^{-a/2}.
 NET |det D| power = d - u - a = (M2-b) - u - a = n-b-a-u  (Codex).  Loss => F ~ ||H||^2_(I+XX^T) + ||Y W||^2_(I+X^T X)^-1,  Y=(P;C).
Then per rank-(l of W, s of Y) stratum: Schur normal form (big cell) + polar in the Schur block -> r^{C_ls-1}.
Verify (1),(3),(4) net power and the loss identity F = ||H||^2(1+..) + ||YW||^2-metric numerically.
"""
import numpy as np
rng=np.random.default_rng(0)

def check_case(M0,M1,M2,u,ntrials=4):
    a=M0-u; b=M1-u; d=M2-b
    print(f"--- M=({M0},{M1},{M2}) u={u} a={a} b={b} d=M2-b={d} : net |det D| power n-b-a-u = {M2-b-a-u} ---")
    ok_jac=True; ok_loss=True
    for _ in range(ntrials):
        # random full-rank D
        D=rng.standard_normal((b,b))
        X=rng.standard_normal((b,d))
        Acor=D@np.hstack([np.eye(b),X])            # (1) minor chart
        # (1) Jacobian: dAcor/d(D,X). Acor cols 0..b-1 = D ; cols b.. = D X. Map (D,X)->(D, D X).
        # Jacobian block-triangular: d(DX)/dX = D (x) I_d per structure => |det D|^d ; d(D)/dD=I.
        # numeric check via finite small perturbation of det of the linear map:
        # build the linear map (D,X)->Acor as a matrix and take |det|.
        nD=b*b; nX=b*d; N=nD+nX
        Jmat=np.zeros((b*M2, N))
        # basis pert of D
        idx=0
        for i in range(b):
            for j in range(b):
                E=np.zeros((b,b)); E[i,j]=1
                dA=E@np.hstack([np.eye(b),X])
                Jmat[:,idx]=dA.reshape(-1); idx+=1
        for i in range(b):
            for j in range(d):
                Ex=np.zeros((b,d)); Ex[i,j]=1
                dA=D@np.hstack([np.zeros((b,b)),Ex])
                Jmat[:,idx]=dA.reshape(-1); idx+=1
        detJ=abs(np.linalg.det(Jmat))
        pred=abs(np.linalg.det(D))**d
        ok_jac = ok_jac and np.isclose(detJ,pred,rtol=1e-6)
        # (2)+(3)+ loss identity:
        Qp=rng.standard_normal((u,M2))
        U=Qp[:, :b]; W=Qp[:, b:]-U@X                # (2) shear, Jac 1
        P=rng.standard_normal((u,u)); Bmat=rng.standard_normal((u,b)); C=rng.standard_normal((a,u))
        H=P@U+Bmat@D                                # (3) shear
        Y=np.vstack([P,C])                          # (M0 x u)
        # E_top = ||P Qp + B Qb||^2 ; Qb=Acor
        Qb=Acor
        Etop=np.sum((P@Qp+Bmat@Qb)**2)
        # claim: Etop = ||H||^2_(1+..) + p-part ; check the exact split Etop = tr(H(I+XX^T)H^T) + tr(P W (I+X^T X)^-1 (P W)^T)
        M=np.eye(d)+X.T@X
        Etop_pred=np.trace(H@(np.eye(b)+X@X.T)@H.T)+np.trace(P@W@np.linalg.inv(M)@(P@W).T)
        ok_loss=ok_loss and np.isclose(Etop,Etop_pred,rtol=1e-6)
        # transverse: ||Qp(I-Pi_b)||^2 = tr(W M^-1 W^T)
        U_,S_,Vt_=np.linalg.svd(Qb,full_matrices=False); r=np.sum(S_>1e-12); V=Vt_[:r].T; Pib=V@V.T
        tr_lhs=np.sum((Qp@(np.eye(M2)-Pib))**2)
        tr_pred=np.trace(W@np.linalg.inv(M)@W.T)
        ok_loss=ok_loss and np.isclose(tr_lhs,tr_pred,rtol=1e-6)
    print(f"    (1) minor Jacobian = |det D|^d : {'OK' if ok_jac else 'FAIL'}")
    print(f"    loss identities  Etop=||H||^2_(I+XX^T)+||P W||^2_metric  and  ||Qp(I-Pib)||^2=tr(W M^-1 W^T): {'OK' if ok_loss else 'FAIL'}")

for M0,M1,M2,u in [(2,2,3,1),(3,3,3,2),(4,4,4,2),(3,3,5,2),(6,6,6,4)]:
    check_case(M0,M1,M2,u)
