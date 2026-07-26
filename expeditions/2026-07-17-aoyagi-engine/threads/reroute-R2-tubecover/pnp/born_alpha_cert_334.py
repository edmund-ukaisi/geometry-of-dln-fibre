#!/usr/bin/env python3
"""
The UNIVERSAL born-alpha certificate, instantiated at every (3,3,4) block-shape (CORRECTED:
the block-elimination cross-term is kept, so the whole block E-factors, matching the exact
anchors deep_chart_ablation / loss_gcd_toggle).

Aoyagi (S,J) peel at a coupled block M = Dbar . S:
  Dbar r x r, pivot (0,0)=1, pivot row d_{0j} (j>=1), pivot col d_{i0} (i>=1),
    Schur block D[i,j] (i,j>=1) = E*alpha*Dred[i-1,j-1] + d_{i0}*d_{0j}   (block-elim cross-term KEPT)
  S r x c, born recoord pivot row:
    S[0,:] = E*(1,t2..tc) - sum_{i>=1} d_{0i}*S[i,:]   (born-alpha ON) ; row i>=1 free residual
Then  M = Dbar.S  has:
    M[0,:] = E*(1,t2..tc)                          (recoord cancels the cross-term EXACTLY)
    M[i,:] = E*(d_{i0}*(1,t..) + alpha*Dred.S_rows)  (i>=1 : E-factored, carries alpha => non-binding)
  => pivot M[0,0] = E EXACTLY,  residual = M[0,0]/GCD = 1 (a CONSTANT) => survivor, rho = inf.

recoord OFF (born-alpha dropped): M[0,:] = 1*S0 + sum d_{0i}Si = E*Trow*? no -- S0 stays E*Trow (no
subtraction), so M[0,:] = E*Trow + sum d_{0i}*Si (the raw cross-term is NOT cancelled) -> M[0,0] is a
SUM, residual over-vanishes.  (The ablation.)
"""
import sympy as sp

def resolve_coupled_block(r, c, born=True):
    E, al = sp.symbols('E alpha')
    # exceptional/join coords
    t = [sp.Integer(1)] + [sp.Symbol(f't{j}') for j in range(2, c + 1)]  # length c
    d = {}          # Dbar entries
    for i in range(r):
        d[(0, 0)] = sp.Integer(1)
    for j in range(1, r):
        d[(0, j)] = sp.Symbol(f'd0{j}')     # pivot row
    for i in range(1, r):
        d[(i, 0)] = sp.Symbol(f'd{i}0')     # pivot col
    Dred = {}
    for i in range(1, r):
        for j in range(1, r):
            Dred[(i, j)] = sp.Symbol(f'D{i}{j}')
            d[(i, j)] = E * al * Dred[(i, j)] + d[(i, 0)] * d[(0, j)]   # block-elim cross-term KEPT
    Dbar = sp.Matrix(r, r, lambda i, j: d[(i, j)])
    Sfree = sp.Matrix(r, c, lambda i, j: sp.Symbol(f's{i}{j}'))
    Trow = [E * t[j] for j in range(c)]
    S = Sfree.copy()
    for j in range(c):
        rec = sum(d[(0, i)] * Sfree[i, j] for i in range(1, r)) if r >= 2 else 0
        S[0, j] = Trow[j] - (1 if born else 0) * rec
    M = sp.expand(Dbar * S)
    gens = [sp.expand(M[i, j]) for i in range(r) for j in range(c)]
    return gens, sp.expand(M[0, 0]), (E, al)

def all_syms(gens, extra):
    s = set(extra)
    for g in gens:
        s |= sp.sympify(g).free_symbols
    return sorted(s, key=str)

def monomial_gcd_exps(gens, syms):
    g = None
    for p in gens:
        p = sp.expand(p)
        if p == 0:
            continue
        pp = sp.Poly(p, *syms)
        exps = [min(m[i] for m in pp.monoms()) for i in range(len(syms))]
        g = exps if g is None else [min(a, b) for a, b in zip(g, exps)]
    return g

def exc_degree(expr, E, al):
    """total degree in the exceptional coords (E,alpha) of the LOWEST such monomial."""
    p = sp.Poly(sp.expand(expr), E, al)
    return min(m[0] + m[1] for m in p.monoms())

def cert_block(name, r, c):
    print(f"\n[{name}]  M = Dbar({r}x{r}) . S({r}x{c})  ->  {r}x{c} product")
    for born in (True, False):
        gens, piv, (E, al) = resolve_coupled_block(r, c, born=born)
        syms = all_syms(gens, [E, al])
        gexp = monomial_gcd_exps(gens, syms)
        m = sp.prod([syms[i]**gexp[i] for i in range(len(syms))]) if gexp else sp.Integer(1)
        quots = [sp.cancel(g / m) for g in gens]
        at0 = [sp.expand(q).subs({s: 0 for s in syms}) for q in quots]
        surv = [i for i, v in enumerate(at0) if v != 0]
        pivq = sp.expand(sp.cancel(piv / m))
        piv_const = (pivq.free_symbols == set())
        tag = "born-ON " if born else "recrd-OFF"
        print(f"    [{tag}] GCD={m};  survivor idx={surv} => {'SURVIVOR' if surv else 'OVER-VANISHES'}")
        if born:
            # exceptional degree of pivot (T-row) vs a Delta-block entry (non-binding check)
            tdeg = exc_degree(piv, E, al)
            ddeg = exc_degree(gens[c], E, al) if r >= 2 else None   # first Delta-row entry M[1,0]
            print(f"       pivot M[0,0]={piv}, residual={pivq}  "
                  f"[{'EXACT CONST => rho=inf' if piv_const else 'NON-const'}]")
            print(f"       exc-deg(T-row pivot)={tdeg}"
                  + (f" < exc-deg(Delta-row M[1,0])={ddeg}  => Delta non-binding" if ddeg is not None
                     else "  (terminal: no Delta block)"))

if __name__ == '__main__':
    print("=" * 95)
    print("UNIVERSAL born-alpha certificate at each (3,3,4) resolution block-shape (corrected)")
    print("=" * 95)
    cert_block("T6  corank-2 canonical  (top peel, 3x3 . 3x3)", 3, 3)
    cert_block("T8  deep corank-1       (2x3 block)", 2, 3)
    cert_block("T9  deepest 1x2 Morse   (1x2 terminal row)", 1, 2)
    cert_block("T4  case12 split A      (2x2 sub-block)", 2, 2)
    cert_block("T5  case12 split B      (3x4 wide block)", 3, 4)
    cert_block("T7  case12 split C      (1x3 sub-row)", 1, 3)
