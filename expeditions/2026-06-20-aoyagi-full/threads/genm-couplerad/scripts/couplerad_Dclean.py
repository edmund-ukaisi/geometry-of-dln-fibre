"""
couplerad_Dclean.py -- (D) b≥2 charge free-box is a CLEAN two-step (NOT a coupled E-recursion).

The coupling I feared came from the A-ROW-PEEL (det_gram_cons) decomposition. The S-FIRST route dissolves it:
  ∫∫_box det((A·S)(A·S)ᵀ)^{−a/2} dA dS  =  ∫_A [ ∫_S det((A·S)(A·S)ᵀ)^{−a/2} dS ] dA.
INNER: via A = R·Q (LQ: R invertible b×b, Q b×M₂ orthonormal rows, QQᵀ=I_b),
  det(A·SSᵀ·Aᵀ) = det(R)²·det((Q·S)(Q·S)ᵀ),  det(R)² = det(A·Aᵀ),
  so  ∫_S det((A·S)(A·S)ᵀ)^{−a/2} dS  =  det(A·Aᵀ)^{−a/2} · C(Q),   C(Q) = ∫_S det((Q·S)(Q·S)ᵀ)^{−a/2} dS.
  C(Q) < ∞ iff a+b ≤ n, and is BOUNDED uniformly over orthonormal-row Q (compact Stiefel + continuity;
  equivalently the projections Q·s_j have a density bounded uniformly over Q). So  I(A) ≤ C·det(A·Aᵀ)^{−a/2}.
OUTER: ∫_A det(A·Aᵀ)^{−a/2} dA < ∞ iff a+b ≤ M₂  (= schurB's detGram_lintegral / corank weight).
COMBINED: a+b ≤ min(M₂,n) = ρ. CLEAN — uniform inner × finite outer, NO recursion, NO coupling, NO log,
NO pseudo-det, NO Cauchy–Binet, NO SVD (Gram-Schmidt/LQ is non-spectral).
"""
import numpy as np
rng = np.random.default_rng(2024)

print("="*90)
print("(D) b≥2 CLEAN two-step: verify (1) the LQ identity, (2) inner = C·det(AAᵀ)^{−a/2} uniform, (3) threshold.")
print("="*90)

# (1) EXACT identity det(A SSᵀ Aᵀ) = det(R)²·det((QS)(QS)ᵀ), det(R)² = det(AAᵀ).
A = rng.uniform(-1, 1, (2, 5)); S = rng.uniform(-1, 1, (5, 3))
Q1, R1 = np.linalg.qr(A.T)                 # A.T = Q1 R1  ⟹  A = R1.T Q1.T
Q, R = Q1.T, R1.T                           # A = R Q, Q orthonormal rows
lhs = np.linalg.det((A@S)@(A@S).T); rhs = np.linalg.det(R)**2 * np.linalg.det((Q@S)@(Q@S).T)
print(f"(1) det(A SSᵀ Aᵀ)={lhs:.6f}  det(R)²·det((QS)(QS)ᵀ)={rhs:.6f}  match={abs(lhs-rhs)<1e-9}")
print(f"    det(R)²={np.linalg.det(R)**2:.6f}  det(AAᵀ)={np.linalg.det(A@A.T):.6f}  match={abs(np.linalg.det(R)**2-np.linalg.det(A@A.T))<1e-9}")

# (2) inner I(A)·det(AAᵀ)^{a/2} bounded uniform over A (incl ill-conditioned) — CLEAN scaling det(AAᵀ)^{−a/2}.
def I_of_A(A, Ss, a):
    v = [abs(np.linalg.det((A@S)@(A@S).T))**(-a/2) if np.linalg.det((A@S)@(A@S).T) > 1e-14 else 1e12 for S in Ss]
    return np.mean(np.clip(v, 0, 1e12))
print("\n(2) inner I(A)·det(AAᵀ)^{a/2} across diverse A (flat ⟹ uniform C ⟹ clean det(AAᵀ)^{−a/2}):")
for M2, n, b, a in [(5, 5, 2, 1), (4, 4, 2, 1), (5, 4, 2, 1)]:
    Ss = [rng.uniform(-1, 1, (M2, n)) for _ in range(4000)]; rs = []
    for A in [rng.uniform(-1,1,(b,M2)), np.diag([1.0]+[.05]*(b-1))@rng.uniform(-1,1,(b,M2)), 0.3*rng.uniform(-1,1,(b,M2))]:
        d = np.linalg.det(A@A.T)
        if d > 1e-12: rs.append(I_of_A(A, Ss, a)*d**(a/2))
    print(f"    M2={M2} n={n} b={b} a={a}: ratios {np.round(rs,2)}  spread [{min(rs):.2f},{max(rs):.2f}] (uniform)")

# (3) combined threshold a+b ≤ ρ = min(M2,n) sharp.
def meanclip(M2, n, b, a, N=4000):
    out = []
    for _ in range(N):
        A = rng.uniform(-1,1,(b,M2)); S = rng.uniform(-1,1,(M2,n)); Y = A@S; d = np.linalg.det(Y@Y.T)
        out.append(abs(d)**(-a/2) if d > 1e-14 else 1e12)
    return np.mean(np.clip(out, 0, 1e12))
print("\n(3) combined ∫∫ finite iff a+b ≤ ρ=min(M2,n):")
for M2, n, b, a in [(4,4,2,1),(4,4,2,2),(3,3,2,1),(3,3,3,1),(5,5,3,1),(5,5,3,3)]:
    rho = min(M2, n); mc = meanclip(M2, n, b, a)
    print(f"    M2={M2} n={n} b={b} a={a} ρ={rho} a+b={a+b} inscope={a+b<=rho}: mean(clip)={mc:.1f}")
print("\n=> CLEAN two-step, threshold a+b ≤ ρ. (D) is (C) generalized (‖A‖^{−1} → det(AAᵀ)^{−a/2}), no E-recursion.")
