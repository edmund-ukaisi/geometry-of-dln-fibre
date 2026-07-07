import sympy as sp

# L=2, r=1, all core blocks 1x1 (H=[2,2,2], m_s = H_s - r = 1). Scalars.
# Honest reindexed decode layers (blocks), with boundary structure:
#   layer 0 (boundary): deepBlkY_0 = 0, deepBlkT_0 = 0
#   layer 1 (=L-1 boundary): deepBlkZ_1 = 0, deepBlkT_1 = 0
# raw core slot decode: t0, t1  (= decode(q).core_s, the raw core = honest (2,2) at boundary)
# gauge reads: X_s, Y_s, Z_s
# deepest constants: a0=deepBlkA_0, a1=deepBlkA_1, z0=deepBlkZ_0, y1=deepBlkY_1

X0,Y0,Z0,X1,Y1,Z1 = sp.symbols('X0 Y0 Z0 X1 Y1 Z1')
a0,a1,z0d,y1d = sp.symbols('a0 a1 z0d y1d')   # deepBlk constants
t0,t1 = sp.symbols('t0 t1')                    # raw core-slot decode

# Honest reindexed decode layers Chat_s = fromBlocks(A,Y,Z,T) with deepBlk + read
# layer0: A=a0+X0, Yblk=0+Y0=Y0, Zblk=z0d+Z0, T=deepBlkT_0(=0)+t0 = t0
Ah0 = a0+X0; Yh0 = Y0;        Zh0 = z0d+Z0; Th0 = t0
# layer1: A=a1+X1, Yblk=y1d+Y1, Zblk=0+Z1=Z1, T=0+t1=t1
Ah1 = a1+X1; Yh1 = y1d+Y1;    Zh1 = Z1;      Th1 = t1

def frb(A,Y,Z,T):  # 2x2 fromBlocks (all scalar)
    return sp.Matrix([[A,Y],[Z,T]])

Chat0 = frb(Ah0,Yh0,Zh0,Th0)
Chat1 = frb(Ah1,Yh1,Zh1,Th1)
P = Chat0*Chat1        # honest product = reindex(prod decode)

def schur(M):  # blockSchur of 2x2 scalar: T - Z*A^-1*Y
    return M[1,1] - M[1,0]*M[0,0]**(-1)*M[0,1]

ScoreSchur = sp.simplify(schur(P))

# honest per-layer Schur cores
S0c = schur(Chat0); S1c = schur(Chat1)
# honest coupling K̂_1 = Z1 * (P11)^-1 * (Chat0)_12  ; K̂_0 = 0
Khat1 = Zh1 * P[0,0]**(-1) * Chat0[0,1]
coreProd_honest = sp.simplify(S0c*(1-Khat1)*S1c)
print("schur_product_ldu_rec check (coreProd == ScoreSchur):",
      sp.simplify(coreProd_honest - ScoreSchur) == 0)

# NAIVE per-layer cores (what deepestCoreAbsorb produces): S_s^naive = t_s - Z_s (1+X_s)^-1 Y_s
S0n = t0 - Z0*(1+X0)**(-1)*Y0
S1n = t1 - Z1*(1+X1)**(-1)*Y1

# huntwist LHS with honest coupling: prod(s -> (1-K_s) S_s^naive) = S0n*(1-Khat1)*S1n
huntwist_honestK = sp.simplify(S0n*(1-Khat1)*S1n)
print("huntwist(honest K, naive cores) == ScoreSchur:",
      sp.simplify(huntwist_honestK - ScoreSchur) == 0)

# naive chain coupling: build C^naive_s = fromBlocks(1+X_s, Y_s, Z_s, t_s); Kcoup on that
Cn0 = frb(1+X0, Y0, Z0, t0); Cn1 = frb(1+X1, Y1, Z1, t1)
Pn = Cn0*Cn1
Kn1 = Cn1[1,0]*Pn[0,0]**(-1)*Cn0[0,1]     # Z1*(Pn11)^-1*Y0
coreProd_naive = sp.simplify(schur(Cn0)*(1-Kn1)*schur(Cn1))
print("naive chain: blockSchur(prod C^naive) == ScoreSchur:",
      sp.simplify(schur(Pn) - ScoreSchur) == 0)

# numeric discriminator (random rational)
import random
subs = {X0:sp.Rational(1,3),Y0:sp.Rational(2,5),Z0:sp.Rational(-1,4),
        X1:sp.Rational(1,7),Y1:sp.Rational(3,5),Z1:sp.Rational(-2,3),
        a0:3,a1:2,z0d:sp.Rational(1,2),y1d:sp.Rational(-1,3),
        t0:sp.Rational(1,5),t1:sp.Rational(2,7)}
print("--- numeric ---")
print("ScoreSchur        =", float(ScoreSchur.subs(subs)))
print("huntwist honest K =", float(huntwist_honestK.subs(subs)))
print("naive chain Schur =", float(sp.simplify(schur(Pn)).subs(subs)))
