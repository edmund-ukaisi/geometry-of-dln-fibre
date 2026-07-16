"""(D) EDGE vs DEEP W2 bookkeeping. EDGE (k=1): SINGLE-chain — corank charge cleanly = ab/2 (s=0/s=1
sector-codim tie, both = ab), reduce to redChain u M @ c'−ab/2 (+log δ-slack); sufficient by cut-soundness
minAdm M <= ab + minAdm(redChain u M) (minAdm_le_peelCharge_add_redChain). NO multi-chain. Verified 0/377
edge cells fail. DEEP (k>=2): single-chain corank charge < ab/2 (min sector-codim shifts to deeper stratum);
the u'-cut MULTI-chain (stratum s -> redChain(u+s)M) is needed THERE only."""
def minAdmRec(M):
    M=list(M);L=len(M)
    if L==1:return 0
    if L==2:return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec([t]+M[2:]) for t in range(min(M[0],M[1])+1))
rho=lambda M: min(M[1:])
bad=tot=0
for M0 in range(1,7):
 for M1 in range(1,7):
  for M2 in range(1,7):
   for M3 in range(1,7):
    M=(M0,M1,M2,M3);r=rho(M)
    for u in range(min(M0,M1)+1):
        a=M0-u;b=M1-u
        if a>=1 and b>=1 and a+b==r+1:
            tot+=1
            if a*b+minAdmRec([u,M2,M3]) < minAdmRec(list(M)): bad+=1
print(f"EDGE cells {tot}; single-chain (ab+minAdm(redChain u M) >= minAdm M) INSUFFICIENT: {bad}")
print("=> EDGE W2 is SINGLE-chain via cut-soundness; multi-chain u'-cuts are DEEP k>=2 only.")
