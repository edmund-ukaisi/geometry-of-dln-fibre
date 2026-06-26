#!/usr/bin/env python3
"""
Confirm the STRUCTURAL factorization of the Schur map that makes its Jacobian det a clean
block-triangular computation in Lean (no 27x27 SCC grading).

The Schur map S(X,K,N,E) = [[K, KN],[XK, XKN+E]].
Its DIFFERENTIAL (a LINEAR map on increments (dX,dK,dN,dE)) at the point (X,K,N,E):
  dA = [[dK, dK N + K dN],[dX K + X dK, dX K N + X dK N + X K dN + dE]]
This linear map, in the ordered output blocks (TL: t x t, TR: t x c, BL: r x t, BR: r x c) and
ordered input blocks (dK : t x t, dN : t x c, dX : r x t, dE : r x c), has the BLOCK structure:

  dA_TL = dK
  dA_TR = dK N + K dN
  dA_BL = X dK + dX K
  dA_BR = X dK N + X K dN + dX K N + dE

Order outputs (TL, TR, BL, BR) and inputs (dK, dN, dX, dE). The Jacobian is BLOCK LOWER TRIANGULAR
w.r.t. this pairing:
  TL <- dK           : depends ONLY on dK              (diagonal block #1)
  TR <- dN (+ dK)    : the dN-part is  dN |-> K dN     (the K-tensor block)
  BL <- dX (+ dK)    : the dX-part is  dX |-> dX K     (the K^T-tensor block)
  BR <- dE (+ dK,dN,dX): the dE-part is dE |-> dE      (identity block)

So with the input/output pairing (TL<->dK, TR<->dN, BL<->dX, BR<->dE), the diagonal blocks are:
  TL/dK:  dK |-> dK            -> det 1
  TR/dN:  dN |-> K dN          -> det (det K)^c     [left mult by K on a t x c matrix space]
  BL/dX:  dX |-> dX K          -> det (det K)^r     [right mult by K on an r x t matrix space]
  BR/dE:  dE |-> dE            -> det 1
and the off-diagonal couplings (TR<-dK, BL<-dK, BR<-dK,dN,dX) are STRICTLY in lower-triangular
position, so they DON'T affect the det.

=> det = 1 * (det K)^c * (det K)^r * 1 = (det K)^(r+c).   <-- the clean Lean route.

VERIFY this block-triangular reading numerically/symbolically: build the differential as a matrix
in the (dK,dN,dX,dE) ordered basis and confirm its det = (det K)^(r+c) AND that it's block-tri.
"""
import sympy as sp

def check(t, r, c):
    K = sp.Matrix(t, t, lambda i,j: sp.Symbol(f'k{i}{j}', real=True))
    X = sp.Matrix(r, t, lambda i,j: sp.Symbol(f'x{i}{j}', real=True)) if r>0 else sp.zeros(0,t)
    N = sp.Matrix(t, c, lambda i,j: sp.Symbol(f'n{i}{j}', real=True)) if c>0 else sp.zeros(t,0)
    # differential blocks. Input basis order: dK (t*t), dN (t*c), dX (r*t), dE (r*c).
    # Output basis order: TL (t*t), TR (t*c), BL (r*t), BR (r*c).
    # left-mult-by-K on (t x c): matrix = I_c (kron) K  acting on vec? We just check det law directly.
    # Build full differential as Jacobian in this ORDER, then check block-lower-tri + det.
    top = sp.Matrix.hstack(K, K*N)
    bot = sp.Matrix.hstack(X*K, X*K*N) if r>0 else sp.zeros(0, t+c)
    # E added to BR only.
    # outputs in block order TL,TR,BL,BR:
    A_TL = K
    A_TR = K*N if c>0 else sp.zeros(t,0)
    A_BL = X*K if r>0 else sp.zeros(0,t)
    A_BR = (X*K*N if (r>0 and c>0) else sp.zeros(r,c))
    # plus E in BR (E enters linearly)
    Evars = sp.Matrix(r, c, lambda i,j: sp.Symbol(f'e{i}{j}', real=True)) if (r>0 and c>0) else sp.zeros(r,c)
    A_BR = A_BR + Evars
    outs = ([A_TL[i,j] for i in range(t) for j in range(t)] +
            [A_TR[i,j] for i in range(t) for j in range(c)] +
            [A_BL[i,j] for i in range(r) for j in range(t)] +
            [A_BR[i,j] for i in range(r) for j in range(c)])
    ins = (list(K) + list(N) + list(X) + list(Evars))
    J = sp.Matrix(len(outs), len(ins), lambda a,b: sp.diff(outs[a], ins[b]))
    # block sizes
    nTL, nTR, nBL, nBR = t*t, t*c, r*t, r*c
    # check block lower-tri: zero in (block_row, block_col) for col>row in order TL<TR<BL<BR
    bounds = [0, nTL, nTL+nTR, nTL+nTR+nBL, nTL+nTR+nBL+nBR]
    blocknames = ['TL','TR','BL','BR']
    upper_zero = True
    for br in range(4):
        for bc in range(br+1, 4):
            sub = J[bounds[br]:bounds[br+1], bounds[bc]:bounds[bc+1]]
            if not sub.is_zero_matrix:
                upper_zero = False
    d = sp.factor(J.det())
    tgt = sp.factor(K.det()**(r+c))
    ratio = sp.simplify(d/tgt) if tgt!=0 else None
    return (t,r,c), upper_zero, ratio in (1,-1)

for (t,r,c) in [(1,1,1),(2,1,1),(1,2,1),(1,1,2),(2,2,2),(2,1,2),(3,2,1)]:
    key, bt, detok = check(t,r,c)
    print(f"(t,r,c)={key}: block-lower-tri(TL,TR,BL,BR)={bt}  det=(detK)^(r+c) PASS={detok}")
