#!/usr/bin/env python3
"""
(ii) NESTED-SURVIVOR verification for the OVER-VANISHING born-native leaves (elder-ruled mechanism).

The over-vanishing leaves (empty single-entry survivor) are REQUIRED in the value cover (restrict-to-
clean-144 DEAD; feeder DEAD). Their threshold >=4 must be established via the nested mechanism:

    loss o g_c = vm^2 * sum_k vf_k^2   (vm = over-vanishing loss-GCD monomial; vf_k = residual factors)
If SOME residual factor vf_k IS A PURE MONOMIAL M, then sum_k vf_k^2 >= M^2 (all summands >=0), so
    loss o g_c >= (vm * M)^2,
a NORMAL-CROSSINGS lower bound with effective (higher) survivor monomial ek0 = vm*M.  Since loss
vanishes SLOWER than (vm*M)^2, rlct(loss) >= rlct((vm*M)^2) = min_{t: ek0_t>0} (kappa_t+1)/(2*ek0_t)
=: threshold_nested.  If threshold_nested >= 4 for every over-vanishing leaf, the (ii) mechanism gates
the build.  If some leaf has NO pure-monomial residual factor -> FLAG #172-recurse (sum vf^2 needs its
own resolution / {R=0} recursion, to be witness-cleared / bounded).

By the exact loss-symmetry (F10b), the 144 over-vanishing whole-conjugate leaves collapse onto the 16
canonical (p1=20) over-vanishing leaf-types (p2 in {1,5,6,7} x p3 in {1,5,6,7}); vm, M, ek0, threshold
all transport by sigma.  We compute on the canonical reps AND verify nativeness on actual conjugates.
"""
import sympy as sp, numpy as np
from fractions import Fraction as Fr
from scipy.optimize import linprog
exec(open('true_rlct_bornnative_all288.py').read().split('if __name__')[0])

def g_leaf_map(p1,p2,p3):
    def F(w):
        w=bb(C2,p3)(w); w=bb(C1,p2)(w); w=permP(w); w=shearH(w); w=bb(C0,p1)(w); return w
    return F
def whole_conj(i,j,p2,p3): return conj(g_leaf_map(20,p2,p3), make_sigma(i,j))(list(u))

def gens_of(w):
    P=A1(w)*A0(w); return [sp.expand(P[a,b]) for a in range(4) for b in range(3)]
def jac_kappa(w):
    J=sp.Matrix(21,21, lambda a,b: sp.diff(w[a],u[b])); dp=sp.Poly(sp.expand(J.det()),*u)
    return [int(min(m[t] for m in dp.monoms())) for t in range(21)]
def true_rlct(w,kappa):
    ms=set()
    for g in gens_of(w):
        if g==0: continue
        for m in sp.Poly(g,*u).monoms(): ms.add(tuple(int(x) for x in m))
    ms=sorted(ms)
    res=linprog(np.array(kappa,float)+1.0,A_ub=-np.array(ms,float),b_ub=-np.ones(len(ms)),bounds=[(0,None)]*21,method='highs')
    return Fr(res.fun).limit_denominator(10**6)/2

def nested(w):
    """Return dict: vm(exp vector), residual factors summary, pure-monomial M candidates,
       best nested ek0 + threshold (exact Fraction), and whether a pure-monomial M exists."""
    gens=gens_of(w)
    gg=None
    for g in gens:
        if g==0: continue
        pp=sp.Poly(g,*u); e=[min(m[t] for m in pp.monoms()) for t in range(21)]
        gg=e if gg is None else [min(a,b) for a,b in zip(gg,e)]
    vm=[int(x) for x in gg]; vmexpr=sp.prod([u[t]**vm[t] for t in range(21)])
    vfs=[sp.expand(sp.cancel(g/vmexpr)) for g in gens]
    kappa=jac_kappa(w)
    # pure-monomial residual factors that vanish at 0 (the nested survivors)
    cands=[]
    for k,vf in enumerate(vfs):
        if vf==0: continue
        pf=sp.Poly(vf,*u)
        if len(pf.terms())==1:                      # single monomial (times a constant)
            Mexp=list(pf.monoms()[0])
            if any(x>0 for x in Mexp):              # vanishes at 0 (a genuine nested survivor)
                ek0=[vm[t]+int(Mexp[t]) for t in range(21)]
                supp=[t for t in range(21) if ek0[t]>0]
                thr=min(Fr(kappa[t]+1,2*ek0[t]) for t in supp)
                cands.append((k,Mexp,ek0,thr))
    best=max(cands,key=lambda c:c[3]) if cands else None
    return dict(vm=vm,kappa=kappa,ncands=len(cands),best=best,vfs=vfs)

def show_mono(exp):
    return "*".join(f"u{t}^{exp[t]}" for t in range(21) if exp[t]>0) or "1"

if __name__=='__main__':
    OV=[(p2,p3) for p2 in [1,5,6,7] for p3 in [1,5,6,7]]
    print("="*96)
    print("(ii) NESTED-SURVIVOR verification: 16 canonical over-vanishing leaf-types (p1=20)")
    print("="*96)
    flags172=[]; rows=[]
    for (p2,p3) in OV:
        w=g_leaf_map(20,p2,p3)(list(u))
        nd=nested(w); tr=true_rlct(w,nd['kappa'])
        vm=nd['vm']
        if nd['best'] is None:
            flags172.append((p2,p3))
            print(f"\n leaf(20,{p2},{p3}): vm={show_mono(vm)}  true_rlct={tr}")
            print(f"    NO pure-monomial residual factor -> FLAG #172-recurse (sum vf^2 needs own resolution)")
            continue
        k,Mexp,ek0,thr=nd['best']
        ok = thr>=4
        rows.append((p2,p3,tr,thr,ok))
        print(f"\n leaf(20,{p2},{p3}): vm={show_mono(vm)}   #pure-mono nested survivors={nd['ncands']}")
        print(f"    best nested M = {show_mono(Mexp)} (residual factor idx {k})")
        print(f"    higher ek0 = vm*M = {show_mono(ek0)}")
        print(f"    threshold_nested = min_t (kappa+1)/(2*ek0) = {thr} (={float(thr):.3f})   true_rlct={tr}   "
              f"[{'>=4 OK' if ok else '<4  <<< nested insufficient'}]"
              + ("  (TIGHT: nested==true)" if thr==tr else "  (nested < true: valid lower bd)"))
    print("\n"+"="*96)
    # native check on actual conjugates: verify nested M transports natively for a sample dominant
    print("NATIVE check: nested survivor on ACTUAL whole-conjugate g_c (dominant p1=5, i=2,j=1):")
    sig=make_sigma(2,1)
    for (p2,p3) in [(1,1),(1,5),(5,5)]:
        w=whole_conj(2,1,p2,p3); nd=nested(w); tr=true_rlct(w,nd['kappa'])
        if nd['best']:
            k,Mexp,ek0,thr=nd['best']
            print(f"   g_c(dom5; canon p2={p2},p3={p3}): nested M={show_mono(Mexp)} ek0={show_mono(ek0)} "
                  f"threshold={thr} true_rlct={tr} [{'>=4 OK' if thr>=4 else '<4'}]")
        else:
            print(f"   g_c(dom5; canon p2={p2},p3={p3}): NO pure-mono M -> #172")
    print("\n"+"="*96)
    if flags172:
        print(f"#172-FLAGGED leaf-types (no pure-monomial nested survivor): {flags172}")
    if rows and all(r[4] for r in rows) and not flags172:
        print("VERDICT (ii): EVERY over-vanishing leaf-type has a pure-monomial nested survivor with")
        print("              threshold_nested >= 4.  The nested mechanism GATES the (ii) build.")
        mn=min(r[3] for r in rows)
        print(f"              min threshold_nested over all 16 types = {mn} (={float(mn):.3f}).")
    elif not flags172:
        print("VERDICT (ii): some nested thresholds < 4 (single-M insufficient) -- see rows above.")
    print("="*96)
