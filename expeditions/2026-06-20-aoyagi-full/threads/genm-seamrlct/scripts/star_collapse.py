import sympy as sp
# 4-layer, verify: removing middle Morse directions (A3=0, A2A1A0=0) => leading form is a STAR (bipartite),
# not a triangle.  Use 2x2 layers. A3=0; pick A2,A1,A0 rank-1 with A2A1A0=0 and pairwise products nonzero.
# A0=E00 (rank1), A1=E00 (rank1): A1A0=E00 (!=0). A2=E11 (rank1): A2A1A0=E11 E00=0. A2A1=E11 E00=0 (edge(3,0) coeff=0).
# Hmm want A2A1!=0 for edge(3,0). Try A2=E01: A2A1A0=E01 E00 E00=E01 E00 = 0? E01 E00 = row0col1 * row0col0 = 0.
# Let me pick to keep some edges. A0=E00,A1=E00 -> A1A0=E00. A2=E10 -> A2A1=E10 E00=E10(!=0), A2A1A0=E10 E00 E00=E10 E00=0? E10 E00=row1col0*row0col0=E10. Then *A0=E00: E10 E00=E10. !=0. bad.
E=lambda i,j:sp.Matrix([[1 if (r,c)==(i,j) else 0 for c in range(2)] for r in range(2)])
A3=sp.zeros(2,2); A0=E(0,0); A1=E(0,0); A2=E(1,1)
print("A2A1A0=",(A2*A1*A0).tolist()," A1A0=",(A1*A0).tolist()," A2A1=",(A2*A1).tolist())
bases=[A0,A1,A2,A3]
Zb=A3*A2*A1*A0
print("Z base =",Zb.tolist())
syms=[];pert=[]
for i in range(4):
    s=sp.symbols(f'p{i}_0:4'); syms+=list(s); pert.append(sp.Matrix(2,2,s))
Ls=[bases[i]+pert[i] for i in range(4)]
Z=sp.expand(Ls[3]*Ls[2]*Ls[1]*Ls[0])
loss=sp.expand(sum(z**2 for z in Z))
poly=sp.Poly(loss,*syms); md=min(sum(m) for m in poly.monoms())
lead=sum(cf*sp.prod([v**k for v,k in zip(syms,m)]) for m,cf in poly.terms() if sum(m)==md)
print("min-deg=",md)
# which layer-perturbation pairs appear (by which p{i}_ block each var belongs to)
def layer_of(varname): return int(str(varname)[1])
pairs=set()
lp=sp.Poly(lead,*syms)
for m,cf in lp.terms():
    layers=sorted(set(layer_of(syms[i]) for i in range(len(m)) if m[i]>0))
    pairs.add(tuple(layers))
print("layer-index supports in leading form:",sorted(pairs))
print("=> if all contain layer 3 (star center) -> bipartite/star; a triangle would be {0,1},{1,2},{0,2} w/o 3")
