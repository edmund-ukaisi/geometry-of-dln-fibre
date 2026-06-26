import sympy as sp
# (2,2,2,2) r=1, L=3. Chain C1 C2 C3, each 2x2. deepest = each layer rank-1 identity corner.
# B = prod of the deepest layers (rank 1). Check the regular/core split is unit-pivot at the deepest pt.
w = sp.symbols('w0:12', real=True)
v1=sp.Matrix([[1,0],[0,0]]); v2=sp.Matrix([[1,0],[0,0]]); v3=sp.Matrix([[1,0],[0,0]])
B=v1*v2*v3  # rank 1 = [[1,0],[0,0]]
C1=v1+sp.Matrix([[w[0],w[1]],[w[2],w[3]]]); C2=v2+sp.Matrix([[w[4],w[5]],[w[6],w[7]]]); C3=v3+sp.Matrix([[w[8],w[9]],[w[10],w[11]]])
P=sp.expand(C1*C2*C3)
gens=[sp.expand((P-B)[i,j]) for i in range(2) for j in range(2)]
allv=list(w)
J=sp.Matrix([[sp.diff(g,vv).subs({x:0 for x in allv}) for vv in allv] for g in gens])
rk=J.rank()
# nReg for (2,2,2,2) r=1: -r^2 + r(H1+HL+1) = -1 + 1*(2+2) = 3
nReg = -1 + 1*(2+2)
print(f"=== (2,2,2,2) r=1, L=3, deepest (each layer rank-1 corner) ===")
print(f"  generators: 4, Jacobian rank = {rk}, nReg formula = {nReg}", "✓" if rk==nReg else "✗")
reg=[]; core=[]
for idx,g in enumerate(gens):
    lin=sum(sp.diff(g,vv).subs({x:0 for x in allv})*vv for vv in allv)
    (reg if lin!=0 else core).append((idx,sp.expand(lin)))
print(f"  regular (unit-pivot lin): {len(reg)}, core (no lin): {len(core)}")
for idx,lin in reg: print(f"    g{idx} lin = {lin}")
unit_pivots=all(any(abs(sp.diff(gens[idx],vv).subs({x:0 for x in allv}))==1 for vv in allv) for idx,_ in reg)
print(f"  every regular generator has UNIT pivot: {unit_pivots}")
print()
print("=== VERDICT (L2 deepest-point split, #125) ===")
print("At the deepest point, the regular block (dim nReg) splits off via UNIT-PIVOT generators (each a")
print("variable with ±1 coeff from the identity corner); the residual core generators have no linear part.")
print("=> EXPLICIT triangular unit-pivot elimination (the #122 route), NO constant-rank theorem needed.")
print("The deepest point is even CLEANER than arbitrary v (#122): it IS the canonical block-normal form,")
print("so no gauge is needed first — the identity corners are already in place (deepestPoint_exists).")
