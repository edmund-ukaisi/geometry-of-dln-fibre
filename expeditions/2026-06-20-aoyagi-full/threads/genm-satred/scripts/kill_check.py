"""(D) KILL check: does ANY corner shell undershoot ½minAdm via the joint (multi-chain) rank-sector?
Corner at cut u reduces stratum r∈0..min(b,ρ) to redChain u' M, u'=u+(b−r) (b=M1−u, ρ=min(M1,M2,M3)),
reachable u'∈[u+max(0,b−ρ), min(M0,M1)]. Joint corner threshold = min over that range of
[peelCharge(u')+minAdm(redChain u' M)]. Since this is a min over a SUBSET of cuts, it is ALWAYS
>= global minAdm(M) — so NO corner undershoots. Exhaustive scan confirms 0 undershoots."""
def minAdmRec(M):
    M=list(M);L=len(M)
    if L==1:return 0
    if L==2:return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec([t]+M[2:]) for t in range(min(M[0],M[1])+1))
tot=reach=over=under=0
for M0 in range(1,7):
 for M1 in range(1,7):
  for M2 in range(1,7):
   for M3 in range(1,7):
    M=(M0,M1,M2,M3); mM=minAdmRec(list(M)); rho=min(M1,M2,M3); mn=min(M0,M1)
    for u in range(mn+1):
        b=M1-u; lo=u+max(0,b-rho); hi=mn
        if lo>hi: continue
        jt=min((M0-up)*(M1-up)+minAdmRec([up,M2,M3]) for up in range(lo,hi+1)); tot+=1
        if jt==mM: reach+=1
        elif jt>mM: over+=1
        else: under+=1
print(f"corner shells (widths<=6): {tot}  reach minAdm={reach}  over-cover(>minAdm,finite)={over}  UNDERSHOOT(<minAdm)={under}")
print("UNDERSHOOT count 0 => KILL not triggered: the joint rank-sector NEVER undershoots (subset-min >= global min).")
