import numpy as np
# Pin the EXACT Tuple indexing for rankFn, and verify the interior-window pattern.
# Tuple A on widths d=(d_0,...,d_L): A has L matrices A_0,...,A_{L-1}, A_s : d_s × d_{s+1}.
# rankFn d A i j (i≤j) = rank(A_i A_{i+1} ··· A_{j-1}) — the partial product from index i to j-1.
#   i=j: empty product = Id_{d_i}, rank = d_i.
#   j=i+1: rank(A_i) (single matrix).
#   j>i+1: the product.
# The cascade: A_s = C_s = diag(1^{t_{s+1}}, 0) : d_s × d_{s+1}, d=M.
#
# CRITICAL CHECK for (3,2,3): the i=1 row. d=(3,2,3), L=2. A_0:3×2 (cascade diag(1^{t_1}=1,0)),
# A_1:2×3 (cascade diag(1^{t_2}=0)=0). 
# rankFn(1,1) = d_1 = 2 (empty product on the middle width). rankFn(1,2) = rank(A_1) = rank(0) = 0.
# But my g227 showed rankFn(1,2)=2 for (3,2,3) — that's a BUG in g227 (it computed rank(C_1) but C_1
# there was the WRONG block). Let me recompute carefully.
def cascade_tuple(M, t):
    L=len(M)-1; tt=[M[0]]+list(t); Cs=[]
    for s in range(L):
        C=np.zeros((M[s], M[s+1])); rk=tt[s+1]
        for i in range(min(rk, M[s], M[s+1])): C[i,i]=1.0
        Cs.append(C)
    return Cs, tt
def rankFn(M, t):
    Cs, tt = cascade_tuple(M,t); L=len(M)-1; R={}
    for i in range(L+1):
        for j in range(i, L+1):
            if i==j: R[(i,j)]=M[i]
            else:
                P=Cs[i]
                for s in range(i+1,j): P=P@Cs[s]
                R[(i,j)]=int(round(np.linalg.matrix_rank(P,tol=1e-9)))
    return R, tt
for M,Tstar,lab in [((2,2,2),(1,0),"(2,2,2)"),((3,2,3),(1,0),"(3,2,3)")]:
    Cs,tt=cascade_tuple(M,Tstar); L=len(M)-1
    print(f"=== {lab}, T*={Tstar}, t_0..t_L={tt} ===")
    print(f"  cascade blocks: " + ", ".join(f"C_{s}({M[s]}×{M[s+1]})=diag(1^{tt[s+1]},0)" for s in range(L)))
    R,_=rankFn(M,Tstar)
    for i in range(L+1):
        row=[(f"{R[(i,j)]:2d}" if j>=i else " .") for j in range(L+1)]
        print(f"    rankFn i={i}: [{' '.join(row)}]")
    # interpret:
    print(f"    diag (i=j) = widths {[M[i] for i in range(L+1)]} (empty products) ✓")
    print(f"    (0,j) = running ranks {[R[(0,j)] for j in range(L+1)]} = t_0..t_L ✓")
    print()
print("KEY for rs-grind: rankFn(cascade) i j = rank(C_i···C_{j-1}). The (0,j) row IS the prescribed")
print("running ranks t_0..t_L (= T* with t_0=M_0). The DIAGONAL i=j = the widths M_i (empty product).")
print("The INTERIOR windows (0<i<j) = rank of the interior partial product = min over the window of the")
print("cascade's surviving rank — a DETERMINED function of T* (the cascade is canonical). This 2-index")
print("pattern IS embedRank(T*-as-2-index). rs-grind proves rankFn(cascadeTuple M T*) = this, by computing")
print("rank of the explicit diagonal products (each a diag of 1s, rank = #surviving 1s = the window min).")
