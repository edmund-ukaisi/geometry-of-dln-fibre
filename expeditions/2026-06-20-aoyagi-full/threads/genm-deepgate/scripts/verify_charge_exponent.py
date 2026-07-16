"""
V1 (EXACT linear algebra): the det-charge exponent at a deep k-drop.

Claim:  Q_b = A_cor * Z,  A_cor generic b x M2,  Z (M2 x n) with rank rho and k of its singular
values scaled by t -> 0 (rank -> rho-k).  Then
    det(Q_b Q_b^T)  ~  C * t^{ 2 * max(0, k-d) },   d = rho - b
i.e. charge det^{-a/2} ~ t^{ -a * max(0, k-d) }.
Reason: Q_b's row space needs b directions; the surviving (rho-k) columns of Z supply min(b,rho-k)
of them; if b > rho-k (k>d) the remaining b-(rho-k)=k-d must come from the t-scaled columns, so the
(k-d) smallest singular values of Q_b are O(t).
Verified by log-log slope of det(Q_bQ_b^T) vs t.
"""
import numpy as np

def check(M2, n, rho, b, k, seed=0, ntrial=2):
    rng = np.random.default_rng(seed)
    d = rho - b
    predicted = 2*max(0, k-d)
    slopes=[]
    for _ in range(ntrial):
        # Z = U diag(sv) V^T, rho nonzero singular values; k of them scaled by t
        U = np.linalg.qr(rng.standard_normal((M2, M2)))[0][:, :rho]   # M2 x rho
        V = np.linalg.qr(rng.standard_normal((n, n)))[0][:, :rho]     # n x rho
        base_sv = 1.0 + rng.random(rho)                              # O(1) singular values
        Acor = rng.standard_normal((b, M2))
        ts = np.array([1e-1, 1e-2, 1e-3, 1e-4, 1e-5])
        dets=[]
        for t in ts:
            sv = base_sv.copy()
            sv[rho-k:] = base_sv[rho-k:]*t          # scale the k smallest by t
            Z = U @ np.diag(sv) @ V.T                # M2 x n, rank rho, k svals ~ t
            Qb = Acor @ Z                             # b x n
            G = Qb @ Qb.T
            dets.append(np.linalg.det(G))
        dets=np.array(dets)
        # slope of log|det| vs log t
        sl = np.polyfit(np.log(ts), np.log(np.abs(dets)), 1)[0]
        slopes.append(sl)
    return predicted, np.mean(slopes), np.std(slopes)

if __name__=="__main__":
    print("det(Q_b Q_b^T) ~ t^{exponent};  predicted exponent = 2*max(0,k-d)")
    print(f"{'M2':>3}{'n':>3}{'rho':>4}{'b':>3}{'d':>3}{'k':>3} | {'predicted':>10} {'measured':>10} {'std':>8}  verdict")
    cases = [
        # (M2,n,rho,b,k)
        (5,5,5,2,1),(5,5,5,2,2),(5,5,5,2,3),(5,5,5,2,4),(5,5,5,2,5),  # d=3: charge from k=4
        (5,6,5,3,1),(5,6,5,3,2),(5,6,5,3,3),(5,6,5,3,4),(5,6,5,3,5),  # d=2: charge from k=3
        (4,4,4,1,1),(4,4,4,1,2),(4,4,4,1,3),(4,4,4,1,4),             # d=3: charge only at k=4
        (6,4,4,2,2),(6,4,4,2,3),(6,4,4,2,4),                          # rho=4(=n), b=2, d=2
    ]
    allok=True
    for (M2,n,rho,b,k) in cases:
        pred, meas, std = check(M2,n,rho,b,k)
        ok = abs(pred-meas) < 0.15
        allok = allok and ok
        d = rho-b
        print(f"{M2:>3}{n:>3}{rho:>4}{b:>3}{d:>3}{k:>3} | {pred:>10} {meas:>10.3f} {std:>8.3f}  {'OK' if ok else '**MISMATCH**'}")
    print("ALL charge-exponent checks pass:", allok)
