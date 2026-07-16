"""
couplerad_reducedreach.py -- does the reduced lost-block bilinear (u, p, k) reach its floor
minAdm(u,p,k) by (i) the banked SQUARE SchurCore, (ii) fibre-peel alone, or (iii) genuinely need the
NON-square corank step?  De-risks the ★5 gap with the wall-review's reach model.

Reach model (from r1upper-wall-review.md / iterfibre-route-cert.md, EXACT):
  * best_iterfibre(chain) = max over terminal-factor choice of min(clean-peel rows/cols, terminal Morse):
      for the 2-layer chain (u,p,k):  = 1/2 * max( min(k, u*p), min(u, p*k) ).       [exponent-preserving]
  * square-SchurCore reach: frobSq(Delta.S), Delta r x r SQUARE -> minAdm(r,r,p'); for (u,p,k) this fires
      directly iff u==p (then reach = minAdm(u,u,k)) or k==p (transpose, reach = minAdm(u,p,p) via E square).
  * the CURRENT closed set = chains whose (1/2)minAdm is reached by best_iterfibre OR the square-SchurCore.
The reduced lost bilinear at cell k is (u, p, k) with p = k+exc (exc=|M2-n|).  Its floor is minAdm(u,p,k).
We ask, over the ARISING (u,p,k): is minAdm(u,p,k) reached by best_iterfibre? by square-SchurCore? neither?
"""
from fractions import Fraction as Fr
from functools import lru_cache
import itertools

@lru_cache(maxsize=None)
def minAdm(M):
    M = tuple(M)
    if len(M) == 2:
        return M[0]*M[1]
    m0,m1 = M[0],M[1]; rest = M[2:]
    return min((m0-t)*(m1-t)+minAdm((t,)+rest) for t in range(0, min(m0,m1)+1))

def binding_cut(M):
    m0,m1 = M[0],M[1]; rest = M[2:]
    best=None; targ=None
    for t in range(0, min(m0,m1)+1):
        v=(m0-t)*(m1-t)+minAdm((t,)+rest)
        if best is None or v<best: best=v; targ=t
    return targ, min(m0-targ, m1-targ)

def best_iterfibre_2layer(u,p,k):
    """(1/2)*max(min(k,u*p), min(u,p*k))  -- exponent-preserving fibre reach (codim units: *2)."""
    return max(min(k, u*p), min(u, p*k))   # in CODIM units (already *2 of the /2 threshold)

def square_schur_reach(u,p,k):
    """codim reached if a square factor exists: u==p -> minAdm(u,u,k); k==p (E square) -> minAdm(u,p,p)."""
    r = None
    if u==p: r = minAdm((u,u,k))
    if k==p:
        v = minAdm((u,p,p))
        r = v if r is None else max(r,v)
    return r

print("="*104)
print("Reduced lost-block bilinear (u,p,k), p=k+exc: floor=minAdm(u,p,k); reach by fibre / square-SchurCore")
print("="*104)
print(f"{'M':>16} {'u':>2} {'k':>2} {'exc':>3} {'(u,p,k)':>10} {'floor':>5} {'fibre':>5} {'sqSchur':>7} "
      f"{'fibre>=floor':>11} {'sq>=floor':>9} {'either':>6}")
need_new = []
arity4 = list(itertools.product(range(2,8), repeat=4))
for M in arity4:
    tstar,r = binding_cut(M)
    rho=min(M[2:]); n=M[-1]; M2=M[2]; exc=abs(M2-n)
    for j in range(1,r+1):
        u=tstar+j; a=M[0]-u; b=M[1]-u
        if a<1 or b<1 or a+b>rho-1: continue
        for k in range(1,rho+1):
            p=k+exc
            floor = minAdm((u,p,k))
            fib = best_iterfibre_2layer(u,p,k)
            sq  = square_schur_reach(u,p,k)
            fib_ok = fib>=floor
            sq_ok  = (sq is not None) and sq>=floor
            either = fib_ok or sq_ok
            if not either:
                need_new.append((M,u,k,exc,(u,p,k),floor,fib,sq))
# print a representative sample + the arising-chain summary
seen=set()
for M in [(4,4,4,4),(3,4,5,4),(5,5,5,5),(3,3,4,4),(4,5,6,5)]:
    tstar,r=binding_cut(M); rho=min(M[2:]); n=M[-1]; M2=M[2]; exc=abs(M2-n)
    for j in range(1,r+1):
        u=tstar+j; a=M[0]-u; b=M[1]-u
        if a<1 or b<1 or a+b>rho-1: continue
        for k in range(1,rho+1):
            p=k+exc; floor=minAdm((u,p,k)); fib=best_iterfibre_2layer(u,p,k); sq=square_schur_reach(u,p,k)
            print(f"{str(M):>16} {u:>2} {k:>2} {exc:>3} {str((u,p,k)):>10} {floor:>5} {fib:>5} "
                  f"{str(sq):>7} {str(fib>=floor):>11} {str(sq is not None and sq>=floor):>9} "
                  f"{str((fib>=floor) or (sq is not None and sq>=floor)):>6}")

print("\n" + "="*104)
print(f"SCAN arity-4 widths 2..7: reduced (u,p,k) NOT reached by fibre OR square-SchurCore: {len(need_new)}")
if need_new:
    print("  -> these NEED the general non-square corank step (or a smarter composition). Sample:")
    for w in need_new[:25]:
        M,u,k,exc,chn,floor,fib,sq = w
        print(f"    M={M} u={u} k={k} exc={exc} (u,p,k)={chn} floor={floor} fibre={fib} sqSchur={sq}")
else:
    print("  -> EVERY arising reduced bilinear is reached by fibre OR square-SchurCore (banked-closable).")
