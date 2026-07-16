from functools import lru_cache
import sys
sys.setrecursionlimit(10000)

@lru_cache(maxsize=None)
def minAdmRec(M):
    L=len(M)
    if L==1: return 0
    if L==2: return M[0]*M[1]
    best=None
    for t in range(0,min(M[0],M[1])+1):
        red=(t,)+M[2:]
        v=(M[0]-t)*(M[1]-t)+minAdmRec(red)
        best=v if best is None else min(best,v)
    return best

def deepTailMin(M): return min(M[2:])

def binding_cuts(M):
    minv=minAdmRec(M); cuts=[]
    for t in range(0,min(M[0],M[1])+1):
        red=(t,)+M[2:]
        if (M[0]-t)*(M[1]-t)+minAdmRec(red)==minv: cuts.append(t)
    return minv,cuts

edge_b2=[]; deepcorank=[]; viol=[]
W=7
for M0 in range(1,W):
 for M1 in range(1,W):
  for M2 in range(1,W):
   for M3 in range(1,W):
    M=(M0,M1,M2,M3); rho=deepTailMin(M); minv,cuts=binding_cuts(M)
    for t in cuts:
        a=M0-t; b=M1-t
        if a<1 or b<1: continue                 # nondegenerate binding cut
        if a+b>rho+1: viol.append((M,t,a,b,rho)) # should be EMPTY (banked bound)
        if a+b>=rho+2: deepcorank.append((M,t,a,b,rho))
        if a+b==rho+1 and b>=2: edge_b2.append((M,t,a,b,rho))
print("nondeg binding cuts with a+b > deepTailMin+1 (banked-bound violation, expect 0):", len(viol))
print("nondeg binding cuts, DEEP-CORANK a+b>=deepTailMin+2 (expect 0):", len(deepcorank))
print("nondeg binding argmin STRICT-EDGE (a+b=deepTailMin+1) with b>=2:", len(edge_b2))
for x in edge_b2[:15]: print("   M=%s t=%d a=%d b=%d rho=%d"%x)
# also count b=1 strict-edge for contrast
edge_b1=[]
for M0 in range(1,W):
 for M1 in range(1,W):
  for M2 in range(1,W):
   for M3 in range(1,W):
    M=(M0,M1,M2,M3); rho=deepTailMin(M); _,cuts=binding_cuts(M)
    for t in cuts:
        a=M0-t;b=M1-t
        if a>=1 and b>=1 and a+b==rho+1 and b==1: edge_b1.append((M,t,a,b,rho))
print("nondeg binding argmin STRICT-EDGE with b=1:", len(edge_b1))

print("\n=== REFINED: require t>=1 (genuine surviving pivot) ===")
edge_b2_t1=[]; edge_b2_t1_big=[]
W2=8
for M0 in range(1,W2):
 for M1 in range(1,W2):
  for M2 in range(1,W2):
   for M3 in range(1,W2):
    M=(M0,M1,M2,M3); rho=deepTailMin(M); _,cuts=binding_cuts(M)
    for t in cuts:
        a=M0-t;b=M1-t
        if t>=1 and a>=1 and b>=2 and a+b==rho+1:
            edge_b2_t1.append((M,t,a,b,rho))
            if M0>=3 and M1>=3: edge_b2_t1_big.append((M,t,a,b,rho))
print("t>=1 nondeg binding argmin, b>=2 strict-edge (a+b=deepTailMin+1):", len(edge_b2_t1))
for x in edge_b2_t1[:15]: print("   M=%s t=%d a=%d b=%d rho=%d"%x)
print("... of those with M0>=3 AND M1>=3:", len(edge_b2_t1_big))
for x in edge_b2_t1_big[:10]: print("   M=%s t=%d a=%d b=%d rho=%d"%x)
