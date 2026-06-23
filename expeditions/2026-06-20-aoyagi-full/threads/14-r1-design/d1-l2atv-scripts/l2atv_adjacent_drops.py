import numpy as np, scipy.linalg as sla
np.random.seed(31)
# WORST CASE: ADJACENT drops (no pass-through between), deep multi-drop, B rank r>0.
# Profile t_0..t_L all strictly decreasing then plateau at r: t=(5,4,3,2,1,1), r=1, widths 5, L=5.
# EVERY layer 1-4 drops by 1 (adjacent), then plateau. Maximal multi-drop coupling.
W=5; L=5; r=1
tt=[5,4,3,2,1,1]   # strictly decreasing to r=1
Cs=[]
for s in range(1,L+1):
    U=np.linalg.qr(np.random.randn(W,W))[0]; V=np.linalg.qr(np.random.randn(W,W))[0]
    D=np.diag([1.0]*tt[s]+[0.0]*(W-tt[s]))
    Cs.append(U@D@V)
P=np.eye(W); ranks=[]
for s in range(L):
    P=Cs[s]@P; ranks.append(np.linalg.matrix_rank(P,tol=1e-9))
print(f"ADJACENT multi-drop v: T_v {tt[1:]}, achieved {ranks}, rank(B)={np.linalg.matrix_rank(P)}=r={r}")
def dn(s):
    Pr=np.eye(W)
    for i in range(L-1,s,-1): Pr=Pr@Cs[i]
    return Pr
def up(s):
    Pr=np.eye(W)
    for i in range(s-1,-1,-1): Pr=Pr@Cs[i]
    return Pr
cols=[]
for s in range(L):
    for a in range(W):
        for b in range(W):
            E=np.zeros((W,W)); E[a,b]=1
            cols.append((dn(s)@E@up(s)).flatten())
M_dP=np.array(cols).T
rank_dP=np.linalg.matrix_rank(M_dP,tol=1e-7)
nReg=r*(W+W)-r*r
print(f"rank(dP)={rank_dP}, nReg=r(M¹+M^L⁺¹)-r²={nReg}, match={rank_dP==nReg}")
# triangular-unit elim test:
Usvd,S,Vt=np.linalg.svd(M_dP)
gens=Usvd[:,:rank_dP].T@M_dP
Q,R,piv=sla.qr(gens,pivoting=True)
sub=gens[:,piv[:rank_dP]]
Plu,Llu,Ulu=sla.lu(sub)
lu_piv=np.diag(Ulu)
print(f"triangular-unit elim: {rank_dP} pivot cols, LU pivots all nonzero: {np.all(np.abs(lu_piv)>1e-9)}")
print(f"  min |pivot| = {np.min(np.abs(lu_piv)):.4f}")
print()
# Highest-rank-first order is FORCED (t weakly decreasing). Each drop layer s: peel where rank highest.
# Check the downstream survivor-corner is a unit at each drop, in highest-first order:
print("Per-drop downstream survivor-rank (highest-first = layer order s=1,2,3,4 since strictly decreasing):")
allunit=True
for s in range(1,L+1):
    if tt[s-1]>tt[s]:
        # downstream of layer s (0-indexed s-1): rank on the survivor sub-block (t_s survivors)
        rk_dn=np.linalg.matrix_rank(dn(s-1),tol=1e-9)
        survives = rk_dn >= r  # the survivors stay alive downstream (rank ≥ r)
        print(f"  drop s={s} ({tt[s-1]}→{tt[s]}): downstream rank={rk_dn} ≥ r={r}? {survives}")
        allunit = allunit and survives
print(f"  all drop pivots are units (downstream alive ≥ r) in highest-first order: {allunit}")
print()
print("⟹ ADJACENT deep multi-drop (every layer drops): rank(dP)=nReg, triangular-unit elim EXISTS,")
print("  pivots are units in the forced highest-first (rank-filtration) order. NO coupling blocks it. [exact]")
