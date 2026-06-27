import sympy as sp
# Does the identity-corner deepest point ALWAYS give triangular unit pivots? Test a richer case:
# (4,4,4) r=2: A1,A2 each 4x4 rank 2, identity-corner. B = rank-2 corner. Bigger regular block.
def check(M, r, label):
    M1,M2,M3=M; n1=M1*M2; n2=M2*M3
    a=sp.symbols(f'a0:{n1}',real=True); b=sp.symbols(f'b0:{n2}',real=True)
    W1=sp.Matrix(M1,M2,a); W2=sp.Matrix(M2,M3,b)
    # deepest: v1 = rank-r identity corner (I_r in top-left), v2 likewise
    v1=sp.zeros(M1,M2); v2=sp.zeros(M2,M3)
    for i in range(r): v1[i,i]=1; v2[i,i]=1
    B=v1*v2
    P=sp.expand((v1+W1)*(v2+W2))
    gens=[sp.expand((P-B)[i,j]) for i in range(M1) for j in range(M3)]
    allv=list(a)+list(b)
    nReg=-r**2+r*(M1+M3)
    # For each regular generator, find its unit-pivot variable; check they're DISTINCT (triangular).
    reg=[]
    for idx,g in enumerate(gens):
        coeffs={vv:sp.diff(g,vv).subs({x:0 for x in allv}) for vv in allv}
        lin_vars=[vv for vv,c in coeffs.items() if c!=0]
        if lin_vars:
            # pick a unit-pivot var (coeff ±1)
            piv=[vv for vv in lin_vars if abs(coeffs[vv])==1]
            reg.append((idx, piv[0] if piv else None))
    nreg_count=len(reg)
    # check the chosen pivots are distinct (a valid triangular elimination order exists):
    pivots=[p for _,p in reg if p is not None]
    distinct = len(set(pivots))==len(pivots) and all(p is not None for _,p in reg)
    print(f"{label}: M={M} r={r}: #regular gens={nreg_count}, nReg formula={nReg}",
          "✓" if nreg_count==nReg else "✗",
          f"| every reg gen has a unit pivot & pivots DISTINCT (triangularizable): {distinct}")

check((4,4,4),2,"(4,4,4) r=2")
check((3,3,3),1,"(3,3,3) r=1")
check((4,3,2),1,"(4,3,2) r=1")
check((4,3,2),2,"(4,3,2) r=2")
print()
print("If pivots are DISTINCT in every case => a triangular elimination order ALWAYS exists at the")
print("deepest point => explicit unit-pivot route, NO constant-rank. The identity corner gives each")
print("regular generator (i,j) (i<r or j<r) a private perturbation entry with a ±1 coeff.")
