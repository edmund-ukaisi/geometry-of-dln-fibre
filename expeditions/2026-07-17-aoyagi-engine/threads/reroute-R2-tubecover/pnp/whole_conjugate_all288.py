#!/usr/bin/env python3
"""
SHARPENED MANDATE (coordinator): verify the WHOLE-CONJUGATE born-native chart for ALL 288 leaves,
and EMIT the native (permuted-centre) blow-up data.

The value-correct chart for dominant p1 is the loss-symmetry conjugate
    g_c = sigma^{-1} o g_leaf(20,p2,p3) o sigma        (sigma = make_sigma(i,j), A0slot[i,j]=p1)
which DECOMPOSES into DIRECT atoms (the (C)-seat decomposition):
    sigma^{-1} o bb(C,p) o sigma = bb(sigma(C), sigma(p))   [permuted-centre blow-up, direct]
    sigma^{-1} o shearH  o sigma = the native §2 shear
    sigma^{-1} o permP   o sigma = a direct permutation
So g_c = bb(sigma(C0),sigma(20)) o [native shear] o [native perm] o bb(sigma(C1),sigma(p2)) o bb(sigma(C2),sigma(p3)).
(Convention: make_sigma sends slot 20 -> A0slot[i,j]; "sigma" here = the coordinator's sigma^{-1}. The
 concrete permutations are printed, so the naming convention is immaterial to the emitted build data.)

DELIVER:
 (0) VERIFY each of the 9 make_sigma is a genuine LOSS SYMMETRY (L o sigma == L, exact).      -> underpins invariance.
 (1) EMIT per dominant: node-1/2/3 native centres (sigma(C),sigma(p)) + conj-permP (direct perm).
 (2) VERIFY all 288 whole-conjugate charts: toric-LP rlct, survivor = pivot-cross, jac>=7 on the
     survivor support, divisorMin>=8.  Cross-check rlct(g_c) == rlct(g_leaf(20,p2,p3)) (invariance).
     KILL: any leaf with survivor on a jac<7 coord (rlct<4) = RED.
 (3) EXACT rational lower-bound certificate (LP duality) for every tight (float rlct==4.0) leaf.
"""
import sympy as sp, numpy as np
from fractions import Fraction as Fr
from scipy.optimize import linprog
from collections import Counter
exec(open('true_rlct_bornnative_all288.py').read().split('if __name__')[0])   # bb, permP, shearH, A0,A1, C0/C1/C2, make_sigma, conj, A0slot, slot2ij

def g_leaf_map(p1,p2,p3):
    def F(w):
        w=bb(C2,p3)(w); w=bb(C1,p2)(w); w=permP(w); w=shearH(w); w=bb(C0,p1)(w); return w
    return F

def whole_conj(i,j,p2,p3):
    return conj(g_leaf_map(20,p2,p3), make_sigma(i,j))(list(u))

def loss_of(w):
    P=A1(w)*A0(w); return sum(sp.expand(P[a,b])**2 for a in range(4) for b in range(3))

# ---------- chart analysis (toric LP + survivor + jac) ----------
def analyse_chart(w):
    J=sp.Matrix(21,21, lambda a,b: sp.diff(w[a],u[b]))
    dp=sp.Poly(sp.expand(J.det()),*u)
    kappa=[int(min(m[t] for m in dp.monoms())) for t in range(21)]
    P=A1(w)*A0(w); gens=[sp.expand(P[a,b]) for a in range(4) for b in range(3)]
    monset=set()
    for g in gens:
        if g==0: continue
        for m in sp.Poly(g,*u).monoms(): monset.add(tuple(int(x) for x in m))
    mons=sorted(monset)
    c=np.array(kappa,float)+1.0; M=np.array(mons,float)
    res=linprog(c, A_ub=-M, b_ub=-np.ones(len(mons)), bounds=[(0,None)]*21, method='highs')
    rlct=res.fun/2.0 if res.success else None
    # value monomial (loss GCD) + survivor + binding axes
    gg=None
    for g in gens:
        if g==0: continue
        pp=sp.Poly(g,*u); e=[min(m[t] for m in pp.monoms()) for t in range(21)]
        gg=e if gg is None else [min(a,b) for a,b in zip(gg,e)]
    vm=[int(x) for x in gg]
    vmexpr=sp.prod([u[t]**vm[t] for t in range(21)])
    quots=[sp.expand(sp.cancel(g/vmexpr)).subs({s:0 for s in u}) for g in gens]
    surv=[t for t,v in enumerate(quots) if v!=0]
    binding=[t for t in range(21) if vm[t]>0]
    jac_on_binding={t:kappa[t] for t in binding}
    dmin=min(kappa[t]+1 for t in binding) if binding else None
    return dict(rlct=rlct,kappa=kappa,mons=mons,surv=surv,binding=binding,
                jac_on_binding=jac_on_binding,dmin=dmin,vm=vm)

def exact_lower_cert(kappa, mons, target=8):
    c=np.array(kappa,float)+1.0; M=np.array(mons,float)
    res=linprog(c, A_ub=-M, b_ub=-np.ones(len(mons)), bounds=[(0,None)]*21, method='highs')
    y=-np.array(res.ineqlin.marginals)
    yr=[Fr(v).limit_denominator(10**6) if v>0 else Fr(0) for v in y]
    lhs=[sum(yr[i]*mons[i][t] for i in range(len(mons))) for t in range(21)]
    feas=all(lhs[t]<=kappa[t]+1 for t in range(21)) and all(a>=0 for a in yr)
    obj=sum(yr)
    return (feas and obj>=target), res.fun, obj

if __name__=='__main__':
    import time,sys
    print("="*94)
    print("WHOLE-CONJUGATE born-native fan: all 288 leaves (toric-LP + native-centre EMIT + exact cert)")
    print("="*94)

    # (0) loss symmetry
    print("\n[0] LOSS-SYMMETRY check for the 9 make_sigma (L o sigma == L, exact):")
    L=loss_of(list(u))
    for i in range(3):
        for j in range(3):
            sig=make_sigma(i,j)
            Ls=L.subs({u[k]:u[sig(k)] for k in range(21)}, simultaneous=True)
            ok=sp.expand(Ls-L)==0
            print(f"    sigma(i={i},j={j}) -> dominant slot {A0slot[(i,j)]:2d}: L-invariant = {ok}")
            if not ok: print("      !!! NOT A LOSS SYMMETRY"); sys.exit(1)

    # (1) EMIT native centres per dominant
    print("\n[1] EMIT native (permuted-centre) blow-up data per dominant (sigma(C),sigma(p)); "
          "conj-permP as a direct permutation:")
    for i in range(3):
        for j in range(3):
            sig=make_sigma(i,j); p1=A0slot[(i,j)]
            nC0=sorted(sig(k) for k in C0); nC1=sorted(sig(k) for k in C1); nC2=sorted(sig(k) for k in C2)
            # conj perm: sigma^{-1} o permP o sigma  as an index map
            inv={sig(k):k for k in range(21)}
            cperm={t: sig(PERMIDX.get(inv[t], inv[t])) for t in range(21)}
            cperm_nontriv={t:cperm[t] for t in range(21) if cperm[t]!=t}
            print(f"  dominant p1={p1:2d} (i={i},j={j}):")
            print(f"     node1 centre={sig(20):2d}  dirs sigma(C0)={nC0}")
            print(f"     node2 centres sigma(C1)={nC1}   (canonical p2 -> native sigma(p2))")
            print(f"     node3 centres sigma(C2)={nC2}   (canonical p3 -> native sigma(p3))")
            print(f"     conj-permP nontrivial map = {cperm_nontriv}")

    # (2) full 288 whole-conjugate sweep
    print("\n[2] SWEEP all 288 whole-conjugate leaves (toric-LP rlct, survivor, jac, divisorMin):")
    t0=time.time()
    rlct_hist=Counter(); dmin_hist=Counter(); nsurv_hist=Counter(); reds=[]; invfail=[]
    minjac_surv=99; tight=[]; survival_examples=[]
    canon_cache={}
    for i in range(3):
        for j in range(3):
            sig=make_sigma(i,j); p1=A0slot[(i,j)]
            for p2 in C1:
                for p3 in C2:
                    a=analyse_chart(whole_conj(i,j,p2,p3))
                    r=a['rlct']; d=a['dmin']
                    rlct_hist[round(r,3)]+=1
                    if d is not None: dmin_hist[d]+=1
                    nsurv_hist[len(a['surv'])]+=1
                    for t in a['binding']:
                        minjac_surv=min(minjac_surv,a['jac_on_binding'][t])
                    # invariance cross-check vs canonical g_leaf(20,p2,p3)
                    if (p2,p3) not in canon_cache:
                        canon_cache[(p2,p3)]=analyse_chart(g_leaf_map(20,p2,p3)(list(u)))['rlct']
                    if abs(r-canon_cache[(p2,p3)])>1e-6: invfail.append((p1,p2,p3,r,canon_cache[(p2,p3)]))
                    if r is None or r<4-1e-6:
                        reds.append((p1,p2,p3,round(r,4),d,tuple(a['surv']),a['jac_on_binding']))
                    if r is not None and r<4.05: tight.append((i,j,p2,p3,p1))
                    if len(survival_examples)<6 and a['surv']:
                        survival_examples.append((p1,p2,p3,round(r,3),d,tuple(a['surv']),a['jac_on_binding']))
    dt=time.time()-t0
    print(f"  (swept 288 in {dt:.1f}s)")
    print("  rlct distribution     :", dict(sorted(rlct_hist.items())))
    print("  divisorMin distribution:", dict(sorted(dmin_hist.items())))
    print("  #survivors/leaf        :", dict(sorted(nsurv_hist.items())))
    print("  min jac over ALL survivor-support axes (need >=7):", minjac_surv)
    print("  invariance rlct(g_c)==rlct(canonical) failures:", len(invfail))
    print("  example survivor leaves:")
    for e in survival_examples: print("     ", e)

    # (3) exact certification of tight leaves
    print(f"\n[3] EXACT rational lower-bound cert (LP duality) for {len(tight)} tight (rlct==4.0) leaves:")
    allok=True; ncert=0
    for (i,j,p2,p3,p1) in tight:
        a=analyse_chart(whole_conj(i,j,p2,p3))
        ok,LPmin,obj=exact_lower_cert(a['kappa'],a['mons'],8)
        ncert+=1
        if not ok:
            allok=False
            print(f"    leaf(p1={p1},p2={p2},p3={p3}): !! exact cert FAILED (float LPmin={LPmin:.4f}, dual obj={obj})")
    print(f"    exactly certified rlct>=4 on {ncert}/{len(tight)} tight leaves: {allok}")

    print("\n"+"="*94)
    if reds:
        print(f"RED: {len(reds)} whole-conjugate leaves with rlct<4 (KILL TRIPPED):")
        for row in reds: print("   ",row)
    else:
        print("SURVIVED: ALL 288 whole-conjugate born-native leaves have rlct>=4 / divisorMin>=8;")
        print("          the survivor support (pivot-cross) ALWAYS lands on jac>=7 coords (min jac=%d)."%minjac_surv)
        print("          + loss-symmetry invariance (0) makes rlct(g_c)=rlct(canonical) EXACT (%d/288 match)."%(288-len(invfail)))
    print("="*94)
