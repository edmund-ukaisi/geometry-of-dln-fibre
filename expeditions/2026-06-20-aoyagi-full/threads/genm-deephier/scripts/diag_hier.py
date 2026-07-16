import numpy as np
from deephier_lp import analyze4, binding_cut, Ck_hier_LP, minAdm

# non-square single deep matrix examples, print all strata
for M in [(5,5,6,3),(6,6,7,4),(5,5,3,6),(7,7,8,5),(6,6,3,3),(8,8,9,4)]:
    tstar,r=binding_cut(M)
    for j in range(1,r):
        u=tstar+j; a=M[0]-u;b=M[1]-u
        if a<1 or b<1: continue
        info=analyze4(M,u)
        print(f"M={M} u={u} a={a} b={b} rho={info['rho']} n={info['n']} M2={info['M2']} exc={info['exc']} minAdm={info['minAdm']} 2T1q={info['target']} urho={info['urho']}")
        for (k,s,kap,Cs,Ch,Chl) in info['recs']:
            flag=" TIGHT" if Ch==info['target'] else (" UNDER!!" if Ch<info['target'] else "")
            print(f"    k={k} rankZ={s} kappa={kap} C_single={Cs} C_hier={Ch} lossonly={Chl}{flag}")
        print()
