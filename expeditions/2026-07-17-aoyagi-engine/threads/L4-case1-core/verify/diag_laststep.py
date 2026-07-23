import sympy as sp, sys, os
sys.path.insert(0, os.path.abspath('.'))
from capstone_adjudication import dims_coords, oracle_edges, coreGen, Phi_p, wmu
from capstone_locus_core import couplingCoords, couplingClear
from capstone_kill_invariant import escaped, state_of

# Question: at the last clear (node6 for (2,3,3,3)), is foldResid node6's escaped(2)-coeff EQUAL to
# foldResid node5's escaped(2)-coeff (recoord writes col-a, not escaped col)? And does foldResid node5's
# escaped(2)-coeff vanish under couplingClear(node6) [more-cleared] but NOT couplingClear(node5)?
d=(2,3,3,3)
N,u = dims_coords(d); coords=set(u.keys()); edges,meta = oracle_edges(d)
br=[e for e in edges if e[0]!="terminal"]
# node5 = br[:5], node6 = br[:6]
def raw_foldResid(path):
    return [sp.expand(f) for f in coreGen(Phi_p(u, d, path, True), d)]
r5 = raw_foldResid(br[:5]); r6 = raw_foldResid(br[:6])
S6,c6 = state_of(d,br,6); esc = escaped(d, S6+1)   # escaped(2)
cc5 = couplingCoords(d, br[:5], coords); cc6 = couplingCoords(d, br[:6], coords)
z5 = {u[k]:0 for k in cc5}; z6 = {u[k]:0 for k in cc6}
print(f"escaped(S6+1={S6+1}) = {sorted(esc)}")
print(f"cc5\\cc6 new couplings at last clear: {sorted(cc6-cc5)}")
for m in esc:
    for j in range(min(len(r5),len(r6))):
        c5 = sp.expand(r5[j].coeff(u[m],1)); c6 = sp.expand(r6[j].coeff(u[m],1))
        if c5==0 and c6==0: continue
        eq = sp.expand(c5-c6)==0
        v5at6 = sp.expand(c5.subs(z6))==0   # node5-coeff killed by node6-clear?
        v5at5 = sp.expand(c5.subs(z5))==0   # node5-coeff killed by node5-clear?
        v6at6 = sp.expand(c6.subs(z6))==0
        print(f" slot{j} u_{m}: c5==c6? {eq}  c5|_cc6=0? {v5at6}  c5|_cc5=0? {v5at5}  c6|_cc6=0? {v6at6}")
