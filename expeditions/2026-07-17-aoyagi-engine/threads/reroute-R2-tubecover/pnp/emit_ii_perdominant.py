#!/usr/bin/env python3
"""
(ii) formaliser asks:
 (1) per-dominant Psi/vm/z for all 9 dominants (p1 in {0..7,20}) x 16 over-vanishing (p2,p3)-types,
     AND verify the sigma_{p1}-transport is EXACT (so they may apply sigma uniformly instead).
 (2) all 12 residual factors vf_k per type (incl. the 4 dropped non-reg-seq), for the canonical p1=20.

Ground truth = computed DIRECTLY from the actual whole-conjugate chart g_c = conj(g_leaf(20,p2,p3), sigma_{p1}).
"""
import sympy as sp
from fractions import Fraction as Fr
exec(open('true_rlct_bornnative_all288.py').read().split("if __name__==")[0])
def g_leaf_map(p1,p2,p3):
    def F(w):
        w=bb(C2,p3)(w); w=bb(C1,p2)(w); w=permP(w); w=shearH(w); w=bb(C0,p1)(w); return w
    return F
def whole_conj(i,j,p2,p3): return conj(g_leaf_map(20,p2,p3), make_sigma(i,j))(list(u))
def show(exp): return '*'.join(f'u{t}^{exp[t]}' for t in range(21) if exp[t]>0) or '1'

def factor(w):
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
    pins=[]; used=set()
    for k,vf in enumerate(vfs):
        if vf==0: continue
        lin=[t for t in range(21) if sp.Poly(vf,*u).coeff_monomial(u[t])!=0]
        cand=[t for t in lin if kappa[t]==0 and vm[t]==0 and t not in used]
        if cand:
            z=cand[0]; used.add(z); pins.append((k,z,vf))
    return vm,kappa,thr,vfs,pins

OV=[(p2,p3) for p2 in [1,5,6,7] for p3 in [1,5,6,7]]
DOM=[(0,0,20),(0,1,2),(0,2,3),(1,0,0),(1,1,4),(1,2,6),(2,0,1),(2,1,5),(2,2,7)]  # (i,j,p1)

if __name__=='__main__':
    import sys
    # ---- (2) canonical 12 vf_k explicit (ask 2) ----
    print("="*100); print("(2) CANONICAL (p1=20) — all 12 residual factors vf_k per type: coreGen_k o g = vm * vf_k")
    print("="*100)
    canon={}
    for (p2,p3) in OV:
        vm,kappa,thr,vfs,pins=factor(g_leaf_map(20,p2,p3)(list(u)))
        canon[(p2,p3)]=(vm,kappa,thr,[tuple(sp.Poly(vf,*u).monoms()) if vf!=0 else () for vf in vfs],pins)
        regidx=[k for (k,z,vf) in pins]
        print(f"\nTYPE(20,{p2},{p3}) vm={show(vm)}  reg-seq k={regidx} (8)  drop k={[k for k in range(12) if k not in regidx]}")
        for k,vf in enumerate(vfs):
            tag='REG->z u%d'%[z for (kk,z,_) in pins if kk==k][0] if k in regidx else 'drop'
            print(f"   vf_{k:2d} = {vf}    [{tag}]")
        sys.stdout.flush()

    # ---- (1) per-dominant table + sigma-transport verification ----
    print("\n"+"="*100)
    print("(1) PER-DOMINANT (9 dominants x 16 types) — DIRECT from whole_conj; + sigma_{p1}-transport check")
    print("="*100)
    transport_ok=True
    for (i,j,p1) in DOM:
        sig=make_sigma(i,j)
        # generator-column permutation tau induced by sigma (coreGen index perm); detect empirically below
        print(f"\n--- dominant p1={p1} (i={i},j={j});  sigma_{p1} nontrivial index map: "
              f"{ {k:sig(k) for k in range(21) if sig(k)!=k} } ---")
        for (p2,p3) in OV:
            vm,kappa,thr,vfmon,pins=factor(whole_conj(i,j,p2,p3))
            regidx=[k for (k,z,vf) in pins]; zc=[z for (k,z,vf) in pins]
            val=min(thr,Fr(len(pins),2))
            # transport check: vm(dom) should equal sigma-permuted canonical vm; z should be sigma(canonical z)
            cvm,ckappa,cthr,cvfmon,cpins=canon[(p2,p3)]
            vm_t=[0]*21
            for t in range(21): vm_t[sig(t)]=cvm[t]
            zc_t=sorted(sig(z) for (k,z,vf) in cpins)
            ok = (vm==vm_t) and (sorted(zc)==zc_t) and (thr==cthr) and val>=4
            transport_ok = transport_ok and ok
            print(f"   ({p1},{p2},{p3}): vm={show(vm):<18} z={sorted(zc)} thr={str(thr):>4} val={val} "
                  f"[sigma-transport EXACT: {ok}]")
        sys.stdout.flush()
    print("\n"+"="*100)
    print(f"sigma_{{p1}}-transport EXACT for all 9x16: {transport_ok}")
    print("=> the formaliser may EITHER read the explicit per-dominant table above, OR formalise the")
    print("   canonical 16 (p1=20) once and apply sigma_{p1} (a pure coord permutation) uniformly:")
    print("   vm_dom = sigma_{p1}(vm_canon); z_dom = sigma_{p1}(z_canon); threshold & value invariant.")
    print("   (Both give identical ground truth; explicit table is zero-bookkeeping, sigma is 1 relabel.)")
