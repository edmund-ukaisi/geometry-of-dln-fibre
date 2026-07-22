from itertools import product
def runMin(M,j): return min(M[i] for i in range(j+2))
def admBound(M,j): return min(M[0],M[1]) if j==0 else M[j+1]
def admissible(M,T):
    L=len(T)
    if any(T[j]>admBound(M,j) for j in range(L)): return False
    for i in range(L):
        for j in range(i,L):
            if T[j]>T[i]: return False
    if L>=1 and T[L-1]!=0: return False
    return True

# Check: for every admissible T, is T_j <= runMin M j for all j?
violations=0; total=0; ex=[]
for L in range(1,5):
    for M in product(range(6),repeat=L+1):
        for T in product(range(6),repeat=L):
            if not admissible(M,T): continue
            total+=1
            for j in range(L):
                if T[j]>runMin(M,j):
                    violations+=1
                    if len(ex)<10: ex.append((M,T,j,T[j],runMin(M,j)))
                    break
print(f"admissible T with some T_j > runMin: {violations}/{total}")
for e in ex: print("  ",e)

# So admTight == Adm.  Now the REAL Tier-3 question: does #(Mval-minimisers over Adm) == a(l-a)+1 ?
# We can't compute (l,a) from M generically here, but check the COUNT of minimisers on the DLN-relevant M.
# Instead just report: is the runMin filter vacuous? (answer: yes, from above)
