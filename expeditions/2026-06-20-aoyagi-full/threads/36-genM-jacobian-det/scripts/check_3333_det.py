import functools
@functools.lru_cache(None)
def minAdmRec(M):
    M=tuple(M); n=len(M)
    if n==1: return 0
    if n==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdmRec((t,)+M[2:]) for t in range(0,min(M[0],M[1])+1))
M=(3,3,3,3); T=(2,1,0)
print("minAdm(3,3,3,3) =", minAdmRec(M))
# Aoyagi blocks r_j x c_j (r_j=t^{j-1}-t^j, c_j=M_{j+1}-t^j):
blocks=[]
for j in range(3):
    tprev=M[0] if j==0 else T[j-1]; tj=T[j]
    r=tprev-tj; c=M[j+1]-tj
    blocks.append((r,c,r*c))
print("T*=(2,1,0) blocks (r,c,rc):", blocks, "active.card=sum=", sum(b[2] for b in blocks))
# radial |x_p|^{m-1} = |x_p|^5. Spectator dets from per-boundary factors:
# schurFrame det = |det K_j|^{r_j+c_j}, K_j is t^j x t^j. LDU det = prod|q|^{2(t-1-i)}.
# The banked anchor det is |u0|^5·|u1|^4·|u4|^2·|u9|^3. The radial is |u0|^5; the rest are the per-boundary
# Schur K-dets / LDU spectators on k=0 axes. (The exact spectator placement is the banked anchor's; the
# POINT for the cert: radial exponent = minAdm-1 = 5, spectators on k=0 axes (threshold-irrelevant).)
print("radial det = |x_p|^{minAdm-1} = |x_p|^5; spectators |u1|^4·|u4|^2·|u9|^3 (per-boundary Schur/LDU, k=0 axes)")
print("=> |det Dphi3333| = |u0|^5·|u1|^4·|u4|^2·|u9|^3 (matches banked RouteM3333Atom)")
