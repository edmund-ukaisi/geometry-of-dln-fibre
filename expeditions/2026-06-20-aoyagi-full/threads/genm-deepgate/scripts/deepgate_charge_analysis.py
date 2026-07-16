"""
Where does the binding (worst) deep stratum sit relative to d = rho-b (the charge threshold)?
And how much slack does the charge-biting full-collapse stratum have?
This isolates whether the det charge EVER determines finiteness.
"""
import itertools
from deepgate_scan import CR, minAdm, binding_cut, analyze

def survey(arity, Wmax):
    nwidths=arity+1
    worstk_gt_d = 0            # binding stratum is a charge-biting one
    total=0
    min_fullcollapse_slack = None
    fc_argmin = None
    min_G_over_target = None   # smallest ratio (min_k G(k)) - target considering charge strata only
    charge_binding_cases = []
    for M in itertools.product(*([range(1,Wmax+1)]*nwidths)):
        tstar,r=binding_cut(M)
        for j in range(1,r):
            u=tstar+j; a=M[0]-u; b=M[1]-u
            if a<1 or b<1: continue
            info=analyze(M,u); total+=1
            d=info['d']; rho=info['rho']; target=info['target']
            # full collapse k=rho
            fc = info['recs'][-1]   # (k=rho, s=0, kappa, G, C*)
            fc_slack = fc[4]-target
            if min_fullcollapse_slack is None or fc_slack<min_fullcollapse_slack:
                min_fullcollapse_slack=fc_slack; fc_argmin=(M,u,info)
            # is the binding stratum charge-biting?
            if info['worst_k']>d:
                worstk_gt_d+=1
                charge_binding_cases.append((M,u,info))
            # smallest G(k) (uncapped) among charge strata minus target
            for (k,s,kap,G,Cs) in info['recs']:
                if k>d:
                    gap = G - target
                    if min_G_over_target is None or gap<min_G_over_target:
                        min_G_over_target=gap
    return dict(total=total, worstk_gt_d=worstk_gt_d, min_fc_slack=min_fullcollapse_slack,
                fc_argmin=fc_argmin, min_G_charge_over_target=min_G_over_target,
                charge_binding=charge_binding_cases)

if __name__=="__main__":
    for arity,Wmax in [(4,10),(5,7),(6,5)]:
        S=survey(arity,Wmax)
        print(f"=== arity {arity} widths 1..{Wmax}: {S['total']} cuts ===")
        print(f"  binding stratum is charge-biting (worst_k>d): {S['worstk_gt_d']}")
        print(f"  min full-collapse (k=rho) slack over target: {S['min_fc_slack']}")
        M,u,info=S['fc_argmin']
        print(f"    at M={M} u={u} a={info['a']} b={info['b']} rho={info['rho']} d={info['d']} "
              f"minAdm={info['minAdm']} target={info['target']}; full-collapse C*={info['recs'][-1][4]}")
        print(f"  min over CHARGE strata (k>d) of  G(k)-target (uncapped): {S['min_G_charge_over_target']}")
        if S['charge_binding']:
            print("  --- cases where a charge-biting stratum BINDS ---")
            for (M,u,info) in S['charge_binding'][:8]:
                kb=info['worst_k']; rec=info['recs'][kb-1]
                print(f"     M={M} u={u} a={info['a']} b={info['b']} rho={info['rho']} d={info['d']} "
                      f"target={info['target']} worst_k={kb} C*={info['worst']} (kappa={rec[2]},G={rec[3]})")
