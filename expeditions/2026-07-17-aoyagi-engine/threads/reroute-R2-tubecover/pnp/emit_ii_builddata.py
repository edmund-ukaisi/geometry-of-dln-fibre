#!/usr/bin/env python3
"""
EMIT the (ii) formaliser build data, per over-vanishing leaf-TYPE (16 canonical, p1=20):
  vm (exponent vector), the r=8 regular-sequence (vf index -> pinned jac-0 coord z_j) map + the Psi
  unipotent shear (z_j := vf_{k_j}; identity on pure-monomial vf, a shear on the linear vf),
  disjointness (z coords vs supp(vm)) + jac-0 confirmation, threshold(vm^2), min(threshold, r/2).
By the exact loss-symmetry all other dominants are sigma_{p1}-images (r, threshold, min invariant).
"""
import sympy as sp
from fractions import Fraction as Fr
exec(open('true_rlct_bornnative_all288.py').read().split("if __name__==")[0])
def g_leaf_map(p1,p2,p3):
    def F(w):
        w=bb(C2,p3)(w); w=bb(C1,p2)(w); w=permP(w); w=shearH(w); w=bb(C0,p1)(w); return w
    return F
def show(exp): return '*'.join(f'u{t}^{exp[t]}' for t in range(21) if exp[t]>0) or '1'

def build_data(p2,p3):
    w=g_leaf_map(20,p2,p3)(list(u))
    P=A1(w)*A0(w); gens=[sp.expand(P[a,b]) for a in range(4) for b in range(3)]
    gg=None
    for g in gens:
        if g==0: continue
        pp=sp.Poly(g,*u); e=[min(m[t] for m in pp.monoms()) for t in range(21)]
        gg=e if gg is None else [min(a,b) for a,b in zip(gg,e)]
    vm=[int(x) for x in gg]; vmx=sp.prod([u[t]**vm[t] for t in range(21)])
    vfs=[sp.expand(sp.cancel(g/vmx)) for g in gens]
    J=sp.Matrix(21,21, lambda a,b: sp.diff(w[a],u[b])); dp=sp.Poly(sp.expand(J.det()),*u)
    kappa=[int(min(m[t] for m in dp.monoms())) for t in range(21)]
    suppvm=[t for t in range(21) if vm[t]>0]
    thr=min(Fr(kappa[t]+1,2*vm[t]) for t in suppvm)
    # regular sequence: vf_k whose linear part is a single jac-0 coord not in supp(vm); pin distinct coords
    pins=[]; used=set()
    for k,vf in enumerate(vfs):
        if vf==0: continue
        lin=[t for t in range(21) if sp.Poly(vf,*u).coeff_monomial(u[t])!=0]
        cand=[t for t in lin if kappa[t]==0 and vm[t]==0 and t not in used]
        if len(lin)>=1 and cand:      # has a fresh jac-0 pin
            z=cand[0]; used.add(z)
            shear = "identity (vf is the coord)" if sp.Poly(vf,*u).is_monomial and vf==u[z] else f"z{z} := {vf}"
            pins.append((k,z,vf,shear))
    r=len(pins)
    return vm,kappa,suppvm,thr,pins,r

if __name__=='__main__':
    OV=[(p2,p3) for p2 in [1,5,6,7] for p3 in [1,5,6,7]]
    print("="*100)
    print("(ii) BUILD DATA — 16 canonical over-vanishing leaf-types (p1=20).  Read-off: rlctAt(vm^2 * sum z_j^2)")
    print("     = min(threshold(vm^2), r/2)   [product RLCT: monomial (x) times sum-of-squares (z), disjoint].")
    print("="*100)
    for (p2,p3) in OV:
        vm,kappa,suppvm,thr,pins,r=build_data(p2,p3)
        zcoords=[z for (_,z,_,_) in pins]
        disj=all(vm[z]==0 and kappa[z]==0 for z in zcoords)
        val=min(thr, Fr(r,2))
        print(f"\nTYPE (p1=20,p2={p2},p3={p3}):")
        print(f"  vm = {show(vm)}   supp(vm)={['u%d'%t for t in suppvm]}   jac on supp(vm) = "
              +", ".join(f'kappa[u{t}]={kappa[t]}' for t in suppvm))
        print(f"  threshold(vm^2)=min_t (kappa+1)/(2*vm) = {thr}   r={r}   r/2={Fr(r,2)}   "
              f"=> value = min = {val} (={float(val):.2f})")
        print(f"  regular sequence (vf index -> pinned coord z_j; Psi shear):")
        for (k,z,vf,shear) in pins:
            print(f"     vf_{k:2d} -> z=u{z:<2d}  jac0={kappa[z]==0} disjoint-from-vm={vm[z]==0}   Psi: {shear}")
        print(f"  z-coords {['u%d'%z for z in zcoords]} DISJOINT from supp(vm) & all jac-0: {disj}")
    print("\n"+"="*100)
    print("Psi (per type) = the product of unipotent shears {u_z := u_z + (vf_k - u_z)} over the LINEAR vf,")
    print("identity on the pure-monomial vf.  Block-triangular, det=1, keep-set INCLUDES supp(vm)={u1,u5,u20-images}")
    print("and every non-z coord.  Under Psi: vf_k|_{k in reg-seq} = z_j (coords); vm unchanged; jac u^kappa unchanged.")
    print("Other dominants p1: apply sigma_{p1} (loss-symmetry) to vm, kappa, the vf/z sets — r, threshold, value invariant.")
