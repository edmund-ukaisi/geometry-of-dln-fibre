import sympy as sp
from adv_dln import nReg, jacobian_rank_at_deepest, product

def ambient(H):
    return sum(H[s]*H[s+1] for s in range(len(H)-1))

def aligned_base(H, r):
    L=len(H)-1
    out=[]
    for k in range(L):
        M=sp.zeros(H[k],H[k+1])
        for i in range(min(r,H[k],H[k+1])): M[i,i]=1
        out.append(M)
    return out

print("="*72)
print("TEST of g203 SHARPENED claim: flat dim (= ambient - nReg) ?= r^2*(L-1)  [pure gauge]")
print("   and cross-check with EXACT rank(J): is flat = ambient - rank(J) really = r^2(L-1)?")
print("="*72)
print(f"{'H':<22}{'r':>3}{'L':>3}{'amb':>5}{'nReg':>6}{'amb-nReg':>9}{'r^2(L-1)':>10}{'rankJ':>7}{'amb-rankJ':>10}  verdict")
configs = [
    # pp2's g203 validation set (all interior widths = r):
    ((3,1,3),1),((2,1,2),1),((3,1,1,3),1),((2,2),2),((3,1,1),1),((2,1,3),1),
    # MY adversarial: interior widths > r (partial degeneracy), the untested class:
    ((4,2,3,2,4),2),((3,2,3),2),((4,2,4),2),((5,3,2,4),2),((3,1,2,1,3),1),
    ((2,3,3),2),((3,3,2),2),((3,4,1,4,3),1),((2,5,2),2),((3,2,5),2),
    ((4,3,1,3,4),1),((2,3,4),2),((4,3,2),2),
]
breaks_g203=[]
breaks_main=[]
for H,r in configs:
    L=len(H)-1; amb=ambient(H); nr=nReg(H,r)
    base=aligned_base(H,r)
    rk,nv,J,mats=jacobian_rank_at_deepest(H,base)
    flat_def = amb-nr
    gauge = r*r*(L-1)
    flat_actual = amb-rk
    g203_ok = (flat_def==gauge) and (flat_actual==gauge)
    main_ok = (rk==nr)
    verdict = "ok" if (g203_ok and main_ok) else ("MAIN-BREAK" if not main_ok else "g203-BREAK")
    if not main_ok: breaks_main.append((H,r,rk,nr))
    if not g203_ok and main_ok: breaks_g203.append((H,r,flat_actual,gauge))
    print(f"{str(H):<22}{r:>3}{L:>3}{amb:>5}{nr:>6}{flat_def:>9}{gauge:>10}{rk:>7}{flat_actual:>10}  {verdict}")
print()
print(f"MAIN-mandate breaks (rank(J) != nReg): {breaks_main if breaks_main else 'NONE'}")
print(f"g203 sharpened-claim breaks (flat != r^2(L-1)): {breaks_g203 if breaks_g203 else 'NONE'}")
