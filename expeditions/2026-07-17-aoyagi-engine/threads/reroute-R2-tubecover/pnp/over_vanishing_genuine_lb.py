#!/usr/bin/env python3
"""
(ii) GENUINE (not toric-upper-bound) lower bound rlct >= 4 for the over-vanishing born-native leaves.

IMPORTANT correction to the naive read: the toric LP computes rlct of the MONOMIAL ideal <all
monomials of all g_k>, which CONTAINS <g_k>, so toric-LP >= true rlct -- it is an UPPER bound.  For
the SURVIVOR leaves it is exact (survivor => normal crossings => both bounds meet); for the
OVER-VANISHING leaves we need a GENUINE lower bound.  The elder's single_le_sum with ONE pure-monomial
M is a genuine lower bound but INSUFFICIENT (loss >= (vm.M)^2 lands on a jac-0 coord -> threshold 1/2).

THE GENUINE MECHANISM (the right refinement of the elder's nested single_le_sum):
    loss o g_c = vm^2 * sum_k vf_k^2  >=  vm^2 * sum_{k in S} vf_k^2
where S = a subset of residual factors whose DIFFERENTIALS at 0 are r INDEPENDENT coordinate
directions, all on jac-exponent-0 coords disjoint from supp(vm).  By the implicit function theorem a
jac-det-1 change of coords (unipotent, within the jac-0 coords) turns {vf_k : k in S} into r
coordinates z_1..z_r, so
    loss >= vm^2 * (z_1^2 + ... + z_r^2),   vm in disjoint (jac>0) coords, z_i jac-0.
Since vm and z live in disjoint variable blocks with product structure,
    rlct(loss) >= min( threshold(vm^2), r/2 ),   threshold(vm^2) = min_{t in supp vm} (kappa_t+1)/(2 vm_t).
This is a GENUINE lower bound (monotonicity of rlct under >= + product-of-disjoint-blocks).  If
r >= 8 AND threshold(vm^2) >= 4 for every over-vanishing leaf, then rlct >= 4 -- CITE-FREE, elementary.

r = rank of the linear parts (Jacobian at 0) of the vf_k restricted to jac-0 coordinates.
"""
import sympy as sp, numpy as np
from fractions import Fraction as Fr
exec(open('true_rlct_bornnative_all288.py').read().split('if __name__')[0])
def g_leaf_map(p1,p2,p3):
    def F(w):
        w=bb(C2,p3)(w); w=bb(C1,p2)(w); w=permP(w); w=shearH(w); w=bb(C0,p1)(w); return w
    return F
def whole_conj(i,j,p2,p3): return conj(g_leaf_map(20,p2,p3), make_sigma(i,j))(list(u))
def show(exp): return '*'.join(f'u{t}^{exp[t]}' for t in range(21) if exp[t]>0) or '1'

def genuine_lb(w):
    P=A1(w)*A0(w); gens=[sp.expand(P[a,b]) for a in range(4) for b in range(3)]
    gg=None
    for g in gens:
        if g==0: continue
        pp=sp.Poly(g,*u); e=[min(m[t] for m in pp.monoms()) for t in range(21)]
        gg=e if gg is None else [min(a,b) for a,b in zip(gg,e)]
    vm=[int(x) for x in gg]; vmx=sp.prod([u[t]**vm[t] for t in range(21)])
    vfs=[sp.expand(sp.cancel(g/vmx)) for g in gens]
    # jac
    J=sp.Matrix(21,21, lambda a,b: sp.diff(w[a],u[b])); dp=sp.Poly(sp.expand(J.det()),*u)
    kappa=[int(min(m[t] for m in dp.monoms())) for t in range(21)]
    # threshold(vm^2)
    supp=[t for t in range(21) if vm[t]>0]
    thr_vm = min(Fr(kappa[t]+1, 2*vm[t]) for t in supp) if supp else Fr(10**9)
    # linear parts of vf_k restricted to jac-0 coords
    free=[t for t in range(21) if kappa[t]==0]
    Jlin=[]
    for vf in vfs:
        if vf==0: continue
        row=[sp.Poly(vf,*u).coeff_monomial(u[t]) for t in free]  # coeff of the degree-1 monomial u_t
        Jlin.append(row)
    Mlin=sp.Matrix(Jlin) if Jlin else sp.zeros(1,len(free))
    r=Mlin.rank()
    # also confirm the pinned coords are jac-0 (they are, by construction of 'free') and disjoint from vm
    disjoint = all(kappa[t]==0 for t in free) and all(vm[t]==0 for t in free)
    lb=min(thr_vm, Fr(r,2))
    return dict(vm=vm, kappa=kappa, thr_vm=thr_vm, r=r, lb=lb, disjoint=disjoint)

if __name__=='__main__':
    OV=[(p2,p3) for p2 in [1,5,6,7] for p3 in [1,5,6,7]]
    print("="*98)
    print("(ii) GENUINE lower bound rlct >= min(threshold(vm^2), r/2) for the 16 over-vanishing types (p1=20)")
    print("="*98)
    ok_all=True; mins=[]
    for (p2,p3) in OV:
        d=genuine_lb(g_leaf_map(20,p2,p3)(list(u)))
        ok = d['lb']>=4 and d['disjoint']
        ok_all = ok_all and ok
        mins.append(d['lb'])
        print(f"  leaf(20,{p2},{p3}): vm={show(d['vm']):<16} threshold(vm^2)={str(d['thr_vm']):>5} "
              f"reg-seq r={d['r']:2d}  r/2={str(Fr(d['r'],2)):>4}  =>  rlct >= min = {str(d['lb']):>4} "
              f"(={float(d['lb']):.2f})  [{'>=4 OK' if ok else '<4 !!!'}]")
    print("\n-- NATIVE check: genuine LB on ACTUAL whole-conjugate g_c (dominant p1=5) --")
    for (p2,p3) in [(1,1),(5,5),(6,7)]:
        d=genuine_lb(whole_conj(2,1,p2,p3))
        print(f"  g_c(dom5;canon {p2},{p3}): vm={show(d['vm']):<16} thr(vm^2)={str(d['thr_vm']):>5} "
              f"r={d['r']:2d} => rlct>=min={str(d['lb'])} [{'>=4 OK' if d['lb']>=4 else '<4'}]")
    print("\n"+"="*98)
    if ok_all:
        print(f"VERDICT (ii) GENUINE: every over-vanishing leaf-type has r>=8 regular-sequence coords (jac-0,")
        print(f"   disjoint from vm) AND threshold(vm^2)>=4, so rlct >= min(threshold(vm^2), r/2) >= 4.")
        print(f"   min genuine lower bound over all 16 types = {min(mins)} (={float(min(mins)):.2f}).")
        print(f"   This is CITE-FREE + elementary (single_le_sum on a REGULAR SEQUENCE, not one monomial;")
        print(f"   product-of-disjoint-blocks rlct).  Corrects the single-M mechanism (was threshold 1/2).")
    else:
        print("VERDICT (ii): some leaf FAILS the genuine bound -- investigate (potential RED).")
    print("="*98)
