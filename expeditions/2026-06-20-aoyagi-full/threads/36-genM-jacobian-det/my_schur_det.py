#!/usr/bin/env python3
"""
DECORRELATED independent check of the per-factor Schur-frame det law.

CLAIM (cert): the local Schur map  S : (X, K, N, E) -> [[K, K N],[X K, X K N + E]]
where K: t x t (FULL t^2 free entries), X: r x t, N: t x c, E: r x c
is a polynomial map from R^{t^2 + r t + t c + r c} to the (t+r) x (t+c) = (t+r)(t+c) output entries.
Count: inputs = t^2 + rt + tc + rc = (t+r)(t+c) = outputs. SQUARE. Good (it's a full chart of the
(t+r)x(t+c) matrix space, parametrized through the rank/Schur factorization).

The Jacobian det of S w.r.t. (X,K,N,E) should be (det K)^(r+c)  [up to sign].

We test this for a grid of (t,r,c) by symbolic Jacobian det + factoring.
This is INDEPENDENT of Codex's chained construction -- it tests the single-block atomic law.
"""
import sympy as sp

def schur_det(t, r, c):
    K = sp.Matrix(t, t, lambda i,j: sp.Symbol(f'k{i}{j}', real=True))
    X = sp.Matrix(r, t, lambda i,j: sp.Symbol(f'x{i}{j}', real=True)) if r>0 else sp.zeros(0,t)
    N = sp.Matrix(t, c, lambda i,j: sp.Symbol(f'n{i}{j}', real=True)) if c>0 else sp.zeros(t,0)
    E = sp.Matrix(r, c, lambda i,j: sp.Symbol(f'e{i}{j}', real=True)) if (r>0 and c>0) else sp.zeros(r,c)
    top = sp.Matrix.hstack(K, K*N)                 # t x (t+c)
    bot = sp.Matrix.hstack(X*K, X*K*N + E)         # r x (t+c)
    A = sp.Matrix.vstack(top, bot)                 # (t+r) x (t+c)
    outs = [A[i,j] for i in range(t+r) for j in range(t+c)]
    ins  = list(K) + list(X) + list(N) + list(E)
    assert len(outs) == len(ins), (len(outs), len(ins), (t,r,c))
    J = sp.Matrix(len(outs), len(ins), lambda a,b: sp.diff(outs[a], ins[b]))
    d = sp.factor(sp.expand(J.det()))
    detK = sp.factor(K.det())
    target = detK**(r+c)
    ratio = sp.simplify(d / target) if target != 0 else None
    ok = ratio in (1,-1,sp.Integer(1),sp.Integer(-1))
    return (t,r,c), d, target, ratio, ok

for (t,r,c) in [(1,1,1),(2,1,1),(1,2,1),(1,1,2),(2,1,2),(2,2,1),(1,2,2),(2,2,2),(3,1,1)]:
    key, d, tgt, ratio, ok = schur_det(t,r,c)
    print(f"(t,r,c)={key}: detJ = (detK)^({r+c}) ? ratio={ratio}  PASS={ok}")
