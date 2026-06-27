"""Reproduce the cobuild REFUTATION of cert-104b's n_raw = M(last) claim.

cert-104b claim:  minAdm(M) == min( M0*M1 ,  M(last) + minAdm(child) )
  where child = schurStateRed M = (M0-1, M1-1, M2, M3, ...)   [pivots drop by 1, tail fixed]
  and  mk = M0*M1   (layer-0 matrix dimension),  n_raw = M(last) (cert claim),  R = minAdm(child).
  V8 (codim-doubled, x2 of the rlct identity):  min{mk, n_raw + R} == minAdm.
"""
from itertools import product
from minadm import min_adm, argmin_adm

def child(M):
    M = list(M)
    M[0] -= 1
    M[1] -= 1
    return tuple(M)

def v8_formula(M):
    L = len(M) - 1
    mk = M[0] * M[1]
    nlast = M[-1]               # M(Fin.last L) = output width
    ch = child(M)
    # child valid? widths must be >=0; minAdm needs L>=1 chain with all widths.
    R = min_adm(ch)
    return min(mk, nlast + R), mk, nlast, R, ch

if __name__ == "__main__":
    fails = []
    total = 0
    undershoots = []
    for L in range(1, 5):           # L = number of layers; chain has L+1 widths
        for widths in product(range(1, 5), repeat=L+1):
            M = tuple(widths)
            # child needs M0>=1, M1>=1 (pivots drop by 1). If M0==0 or M1==0 skip (no pivot).
            if M[0] < 1 or M[1] < 1:
                continue
            total += 1
            ma = min_adm(M)
            f, mk, nlast, R, ch = v8_formula(M)
            if f != ma:
                fails.append((M, ma, f, mk, nlast, R, ch))
                if f < ma:
                    undershoots.append((M, ma, f))
    print(f"checked {total} nodes; {len(fails)} fail; {len(undershoots)} undershoot (unsound)")
    print("\nsample fails:")
    for row in fails[:15]:
        M, ma, f, mk, nlast, R, ch = row
        tag = "UNDERSHOOT" if f < ma else "over"
        print(f"  M={M} minAdm={ma}  formula min({mk},{nlast}+{R})={f}  [{tag}] child={ch}")
    print("\nthe two cited witnesses:")
    for M in [(2,1),(3,3,3,3)]:
        if M[0]>=1 and M[1]>=1:
            ma=min_adm(M); f,mk,nlast,R,ch=v8_formula(M)
            print(f"  M={M} minAdm={ma} formula min({mk},{nlast}+{R})={f}")
