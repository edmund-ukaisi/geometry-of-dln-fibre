"""
Refined: if leaf-1 KEEPS the shell-domain, the D-B uses G's OWN top-(M1-j) frame (σ_{M1-j}(G)>=ε on the
shell), giving threshold u*(M1-j)/2 [M1-j = b+t Gram-eigenvalues >= ε², the shell's actual conditioning],
NOT the frame m=min(M1,Mlast)-j. Reaches 1/2minAdm(M) iff minAdm(M) <= ab + u*(M1-j).
Compare: frame-m threshold (Codex) vs shell-(M1-j) threshold. Which (if either) saves route alpha?
Also report the residual (shells failing EVEN the M1-j threshold => genuinely need route-beta). NO MC.
"""
from functools import lru_cache
from itertools import product
def redChain(u,M): return (u,)+tuple(M[2:])
@lru_cache(maxsize=None)
def minAdm(M):
    M=tuple(M)
    if len(M)<=1: return 0
    if len(M)==2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t)+minAdm(redChain(t,M)) for t in range(min(M[0],M[1])+1))
WMAX=7
shells=0; fail_m=0; fail_M1j=0; ex=[]
for arity in (4,5):
    for M in product(range(1,WMAX+1),repeat=arity):
        M0,M1,Mlast=M[0],M[1],M[-1]; mM=minAdm(M)
        for t in range(1,min(M0,M1)+1):
            r=min(M0-t,M1-t)
            for j in range(0,r):
                u=t+j; a=M0-u; b=M1-u
                m_frame=min(M1,Mlast)-j
                m_shell=M1-j        # = b+t; the shell's actual #{SVs>=ε}
                shells+=1
                if mM > a*b + u*m_frame: fail_m+=1
                if mM > a*b + u*m_shell:
                    fail_M1j+=1
                    if len(ex)<10: ex.append((M,t,j,u,a,b,m_shell,mM,a*b+u*m_shell))
print(f"interior shells: {shells}")
print(f"  FAIL with frame-m threshold um (Codex m=min(M1,Mlast)-j): {fail_m}")
print(f"  FAIL with shell-(M1-j) threshold u(M1-j)=u(b+t): {fail_M1j}")
if fail_M1j==0:
    print("  => route alpha SAVED IF leaf-1 keeps the shell-domain + threshold u(M1-j)/2 (G's own top-(M1-j) frame). minAdm(M)<=ab+u(M1-j) holds for ALL interior shells.")
else:
    print(f"  => {fail_M1j} shells FAIL even u(M1-j) => genuinely need route-beta (det(GG^T) to IH). Examples (M,t,j,u,a,b,M1-j,minAdm,ab+u(M1-j)):")
    for e in ex: print("    ",e)
# sanity: M1-j == b+t ?
print("check M1-j == b+t: ", all((M[1]-j)==( (M[1]-(t+j)) + t) for M in [(3,4,5,6)] for t in [1,2] for j in [0,1]))
