#!/usr/bin/env python3
import sympy as sp, random
def gen(tag,m,n): return sp.Matrix(m,n, lambda i,j: sp.Symbol(f'{tag}{i}_{j}', real=True))
def beta(C,piv):
    pi,pj=piv; u=C[pi,pj]; m,n=C.shape
    return sp.Matrix(m,n, lambda i,j: u if (i,j)==piv else u*C[i,j])
def alpha_int(C,cl):
    m,n=C.shape; C=C.as_mutable()
    for i in range(cl+1,m):
        for j in range(cl+1,n):
            C[i,j]=C[i,j]-C[i,cl]*C[cl,j]
    return C
def process(C,ncl,use_alpha=True):
    C=C.as_mutable()
    for c in range(ncl):
        if use_alpha: C=alpha_int(C,c)
        C=beta(C,(c,c))
    return sp.expand(C)
def wmin(M,n): return min(M[:n+1])
def nonzero(expr):
    """polynomial nonzero? evaluate at a random exact-rational point (nonzero at one point => nonzero)."""
    e=sp.expand(expr)
    if e==0: return False
    syms=list(e.free_symbols)
    random.seed(1)
    for _ in range(3):
        sub={s: sp.Rational(random.randint(1,7), random.randint(1,5)) for s in syms}
        if sp.nsimplify(e.subs(sub))!=0: return True
    return e!=0

R=lambda b:("NONZERO" if b else "0")
print("="*78, flush=True)
print("(2,2,2): PURE live-column test, row J=0 (no cleared-cols, no dropped-cols)", flush=True)
print("="*78, flush=True)
M=[2,2,2]
C0=process(gen('a0',2,2),wmin(M,1)); C1=process(gen('a1',2,2),wmin(M,2))
print("  clearing step prodPrefix=C0; row0 = [",sp.factor(C0[0,0]),",",sp.factor(C0[0,1]),"]",flush=True)
print("   live-col (0,1) @ clearing step:", R(nonzero(C0[0,1])), flush=True)
prod=sp.expand(C0*C1)
print("   live-col (0,1) @ LEAF (C0*C1):", R(nonzero(prod[0,1])), flush=True)
C0b=process(gen('a0',2,2),wmin(M,1),use_alpha=False)
print("   (a) pre-alpha pure-beta (0,1):", R(nonzero(C0b[0,1])), "-> not structurally 0", flush=True)
print("  => (2,2,2) live-col = (d): not cleared by alpha / blow-up / drop(none) / bmon.", flush=True)

print("\n"+"="*78, flush=True)
print("(4,3,4): row J=1, all three column types (cleared 0 / live 2 / dropped 3)", flush=True)
print("="*78, flush=True)
M=[4,3,4]; print("  running-min widths",[wmin(M,n) for n in range(3)],"(runmin=3, full M(L)=4)",flush=True)
C0=process(gen('a0',4,3),wmin(M,1)); C1=process(gen('a1',3,4),wmin(M,2))
print("  clearing step prodPrefix=C0(4x3): cleared-col(1,0)=",R(nonzero(C0[1,0])),"[needs Lg]  live-col(1,2)=",R(nonzero(C0[1,2])),"[needs Rg]",flush=True)
prod=sp.expand(C0*C1)
for lbl,j in [("cleared(1,0)",0),("live(1,2)",2),("dropped(1,3)",3)]:
    print(f"  LEAF {lbl}:", R(nonzero(prod[1,j])), flush=True)
row3=any(nonzero(prod[3,j]) for j in range(4))
print("  dropped-ROW: row3 has a NONZERO entry?", row3, "(InvVal3 dropped-clause needs row3==0 => FAILS)", flush=True)
# numeric rank
random.seed(2); syms=list(prod.free_symbols)
sub={s: sp.Rational(random.randint(1,9),random.randint(1,4)) for s in syms}
rk=sp.Matrix(4,4,lambda i,j: prod[i,j].subs(sub)).rank()
print(f"  rank(prod)={rk} (inner dim 3) => row 3 is a linear combo of rows 0-2, NOT a zero row", flush=True)
print("\nVERDICT: live-col=(d); cleared-col=(d, needs Lg); dropped col/row NOT zeroed under interior-alpha", flush=True)
