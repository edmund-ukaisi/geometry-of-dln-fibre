#!/usr/bin/env python3
# =============================================================================
# WITNESS W2 — CODIM-UNDERSHOOT FAMILY  (executable kill-condition, exact)
# =============================================================================
# DISCRIMINATOR (prodcorank-cert.md §2; princ-answer.md Q2):
#   The TRUE minimal codimension of the product-corank locus V_m = {rank(P*Z)<=n-m}
#   is C_m = m^2 - floor(m^2/4), which UNDERSHOOTS the naive single-factor-drop
#   codimension m^2 by exactly floor(m^2/4). That gap equals a*c = dim coker(d mu)
#   on the balanced component — the exact non-submersiveness of matrix
#   multiplication. So m^2 (transverse) and C_m (true codim) are DIFFERENT numbers
#   whenever m >= 2.
#
# ENGINE KILL-CONDITION GUARDED:
#   The engine must not conflate the two codim accountings on the balanced
#   (min-corank >= 2) component:
#     - the FREE-block / submersive discrepancy is m^2 (valid only where the
#       pullback is transverse, i.e. min-corank <= 1);
#     - the VARIETY codim is C_m < m^2.
#   Any native step that charges m^2 as the discrepancy at a NON-transverse
#   (min-corank >= 2) cut, or that uses C_m as if the joint center split off a
#   free reduced chain, is unsound. This witness exhibits the exact gap that
#   separates them, member by member.
#
# EXACT INSTRUMENTS:
#   - exact integer minimisation of the Schubert codim a^2 + c^2 + e(c-a+e);
#   - closed forms C_m and the gap floor(m^2/4), checked to agree;
#   - EXACT (sympy, over QQ) rank of the normal-space / coker map at explicit
#     RATIONAL balanced points  (NOT float numpy ranks — a float rank at a
#     tolerance is not the exact rank).
#
# FAMILY: headline n = 4,5,6,7 (per the cert); robustness sweep n = 2..8.
#
# EXPECTED RESULT (see w2_codim_undershoot_family.out for the verbatim run):
#   - true codim(n,m) = C_m for every (n,m); minimiser (a,c,e) ~ balanced.
#   - gap = m^2 - C_m = floor(m^2/4) = a*c, for every m.
#   - EXACT normal-map rank at n=4,m=2 balanced point = 3 = C_2 (not 4).
#   - EXACT coker(d mu) dim at n=4,m=4 balanced point = 4 = floor(16/4) = 4^2 - C_4.
# =============================================================================

import sympy as sp

def hdr(s): print("\n" + "="*70 + "\n" + s + "\n" + "="*70)
def Ck(k): return k*k - (k*k)//4

# ---- exact Schubert minimisation of the product-corank codim ----------------
def true_codim(n, k):
    """Minimal codim of {rank(P*Z) <= n-k}, exact integer search over balanced
    components (a,c,e): rank P drops a, rank Z drops c, dim(im Z cap ker P)=e,
    giving rank(P*Z) = (n-c)-e <= n-k.  codim = a^2 + c^2 + e(c-a+e)."""
    best, barg = None, None
    for a in range(0, n+1):
        for c in range(0, n+1):
            e = max(0, k - c)          # minimal alignment to reach corank k
            if e > a or e > n - c:     # Schubert feasibility of dim(U cap V) >= e
                continue
            if (n - c) - e < 0:
                continue
            codim = a*a + c*c + e*(c - a + e)
            if best is None or codim < best:
                best, barg = codim, (a, c, e)
    return best, barg

hdr("E1: true product-corank codim  vs  naive m^2  vs  C_m  (exact integer)")
print("family: headline n=4..7, robustness n=2..8")
all_match = True
gap_match = True
for n in range(2, 9):
    tag = "  <== HEADLINE" if 4 <= n <= 7 else ""
    print(f"\n n={n}:{tag}")
    for m in range(1, n+1):
        tc, (a, c, e) = true_codim(n, m)
        gap = m*m - tc
        ok = (tc == Ck(m))
        gok = (gap == (m*m)//4 == a*c)
        all_match &= ok
        gap_match &= gok
        print(f"   m={m}: true codim={tc:>3}  naive m^2={m*m:>3}  C_m={Ck(m):>3}  "
              f"UNDERSHOOT gap = m^2 - C_m = {gap:>2} = floor(m^2/4)={(m*m)//4} = a*c={a*c}  "
              f"(a,c,e)={(a,c,e)}  match={ok and gok}")
print("\nE1 VERDICT  true codim == C_m for all (n,m):", all_match)
print("E1 VERDICT  gap == floor(m^2/4) == a*c for all (n,m):", gap_match)

# ---- exact normal-map rank at an explicit RATIONAL balanced point (n=4,m=2) --
# Point on the balanced component a=c=e=1: rank P=3 (ker=<e1>), rank Z=3
# (im Z=<e1,e2,e3>, so e1 in im Z cap ker P), rank(P*Z)=2=n-m.
hdr("E2: EXACT normal-map rank at n=4, m=2 balanced point (expect 3 = C_2, not 4)")
Q = sp.Rational
# P: col1 = 0 (e1 in ker), remaining 3 columns generic-rational, rank 3.
P = sp.Matrix([
    [0,  2,  1,  3],
    [0,  1,  4,  1],
    [0,  5,  1,  2],
    [0, -1,  3,  1],
])
# Z: row4 = 0 (im Z subset <e1,e2,e3>), top 3x4 block rank 3.
Z = sp.Matrix([
    [ 2, -1,  1,  3],
    [ 1,  2,  4,  1],
    [-1,  1,  2,  5],
    [ 0,  0,  0,  0],
])
PZ = P * Z
print("rank P =", P.rank(), " rank Z =", Z.rank(), " rank(P*Z) =", PZ.rank(),
      " (target rank n-m = 2)")
assert P.rank() == 3 and Z.rank() == 3 and PZ.rank() == 2, "point off the balanced component"
# coker(P*Z) = left nullspace (nullspace of transpose); ker(P*Z) = right nullspace.
Ucok = PZ.T.nullspace()            # list of 2 exact basis vectors (4x1)
Vker = PZ.nullspace()              # list of 2 exact basis vectors (4x1)
Ucok = sp.Matrix.hstack(*Ucok)     # 4 x 2
Vker = sp.Matrix.hstack(*Vker)     # 4 x 2
# normal map (dP,dZ) -> Ucok^T (dP*Z + P*dZ) Vker  in the 4-dim space Mat(2,2).
rows = []
for i in range(4):
    for j in range(4):
        dP = sp.zeros(4, 4); dP[i, j] = 1
        rows.append(list((Ucok.T * (dP * Z) * Vker)))
for i in range(4):
    for j in range(4):
        dZ = sp.zeros(4, 4); dZ[i, j] = 1
        rows.append(list((Ucok.T * (P * dZ) * Vker)))
Jn = sp.Matrix(rows)               # 32 x 4, exact rational
local_codim = Jn.rank()            # EXACT rank over QQ
print("EXACT rank of normal-space map (= local codim of V_2 at this point):", local_codim)
print("naive transverse codim would be (n-r)^2 = 2^2 = 4; C_2 =", Ck(2))
E2 = (local_codim == 3 == Ck(2))
print("E2 VERDICT  exact local codim = 3 = C_2 (undershoots naive 4):", E2)

# ---- exact coker(d mu) dim at n=4, m=4 balanced point (expect 4) ------------
# Both factors corank 2, im Z subset ker P (alignment e=2): P*Z = 0.
hdr("E3: EXACT coker(d mu) dim at n=4, m=4 balanced point (expect a*c=4)")
# ker P = im P = <e1,e2>: rank-2 map onto <e1,e2> from <e3,e4>.
P4 = sp.Matrix([
    [0, 0,  1,  2],
    [0, 0,  3,  1],
    [0, 0,  0,  0],
    [0, 0,  0,  0],
])
# im Z = <e1,e2> (subset ker P): rows 3,4 zero, top 2x4 rank 2.
Z4 = sp.Matrix([
    [ 2, 1, -1,  1],
    [ 1, 3,  2,  1],
    [ 0, 0,  0,  0],
    [ 0, 0,  0,  0],
])
PZ4 = P4 * Z4
print("rank P =", P4.rank(), " rank Z =", Z4.rank(), " rank(P*Z) =", PZ4.rank(),
      " (im Z subset ker P => P*Z = 0)")
assert P4.rank() == 2 and Z4.rank() == 2 and PZ4.is_zero_matrix
# image of d mu : (dP,dZ) -> dP*Z + P*dZ  inside Mat(4,4) = 16-dim
rows = []
for i in range(4):
    for j in range(4):
        dP = sp.zeros(4, 4); dP[i, j] = 1
        rows.append(list(dP * Z4))
for i in range(4):
    for j in range(4):
        dZ = sp.zeros(4, 4); dZ[i, j] = 1
        rows.append(list(P4 * dZ))
M = sp.Matrix(rows)                # 32 x 16, exact
img_rank = M.rank()
coker_dim = 16 - img_rank
print("EXACT dim image(d mu) =", img_rank, " ; coker dim =", coker_dim)
print("expected a*c = 2*2 = 4 = floor(16/4) = 4^2 - C_4 =", 16 - Ck(4))
E3 = (coker_dim == 4 == 16 - Ck(4))
print("E3 VERDICT  exact coker(d mu) dim = 4 = 4^2 - C_4:", E3)

# ---- overall ---------------------------------------------------------------
hdr("W2 OVERALL")
ok = all_match and gap_match and E2 and E3
print("E1 (codim=C_m, gap=floor(m^2/4)=a*c):", all_match and gap_match)
print("E2 (exact normal-map rank = 3 = C_2):", E2)
print("E3 (exact coker(d mu) dim = 4 = 4^2-C_4):", E3)
print("W2 PASS:", ok)
assert ok, "W2 FAILED — a load-bearing exhibit did not reproduce"
print("\n[W2] the balanced product-corank codim C_m undershoots naive m^2 by "
      "exactly floor(m^2/4) = coker(d mu). m^2 and C_m are distinct for m>=2.")

# =============================================================================
# CHECKED-IN OUTPUT: see w2_codim_undershoot_family.out . Key lines:
#   E1 VERDICT  true codim == C_m for all (n,m): True
#   E1 VERDICT  gap == floor(m^2/4) == a*c for all (n,m): True
#   E2 VERDICT  exact local codim = 3 = C_2 (undershoots naive 4): True
#   E3 VERDICT  exact coker(d mu) dim = 4 = 4^2 - C_4: True
#   W2 PASS: True
# =============================================================================
