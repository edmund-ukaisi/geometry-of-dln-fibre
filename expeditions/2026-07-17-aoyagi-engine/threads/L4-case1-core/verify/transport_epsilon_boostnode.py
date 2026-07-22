"""
pnp-transport STAGE 1: termwise ε-decomposition of the case11 boost-node residual.

Ground truth anchor: the boost-node parent residual (2,2,2,2), validated by the banked
`case11_boostready_crosscheck.py` / codex boost-readiness-2222-answer:

    R_p = H . [[1, beta],[0, s]] ,   H = Z B ,   s = u12   (the reused-pivot birth coord)

- Z = C^(3) (layer-3, deeper factor), B = recoordinatised layer-2 block.
- boost CENTER  C = {s} ∪ {layer-2 col-0 block} = {s, b00, b10}   (the LEDGER boost center = ed.center)
- geometric SUPPORT (carried invariant `supportAt`) = full layer-2 block = {b00,b01,b10,b11}
  PLUS the pivot s.  (support ⊋ center: the col-1 coords {b01,b11} are support∖center.)

The boostReady obligation (`realBranch_boostReady_case11`, Case1Wire.lean:386, currently sorry):
    parent residual is Deg1SupportedOn the SMALL center C, even though carried only on the LARGE support.

This script:
  (1) reproduces R_p, re-confirms A1/A2/A3 (Deg1-on-center + u_pivot divisibility) [re-ground],
  (2) TERMWISE ε-decomposition: for each entry, each monomial, read ε(s) = exponent of the pivot s;
      confirm the MECHANISM: every monomial that reads a support-only coord (b01/b11 in col-1) has ε(s)>=1,
      i.e. the (support∖center) coords appear ONLY multiplied by the pivot. THIS is boostReady.
  (3) exhibit the re-grouping: R_p = sum_{i in C} c'_i * u_i  with c'_i center-free  (Deg1SupportedOn C).
"""
import sympy as sp

# --- symbols ---------------------------------------------------------------
s = sp.symbols('u12')                 # the reused-pivot birth coordinate (= divisor u_{1,2})
beta = sp.symbols('beta')             # pending Schur shear tail (pivot-row tail of the boost block)
b00,b01,b10,b11 = sp.symbols('b00 b01 b10 b11')   # recoordinatised layer-2 block (col0={b00,b10}, col1={b01,b11})
z00,z01,z10,z11 = sp.symbols('z00 z01 z10 z11')   # layer-3 deeper factor C^(3)

B = sp.Matrix([[b00,b01],[b10,b11]])
Z = sp.Matrix([[z00,z01],[z10,z11]])
H = sp.expand(Z*B)                    # H = Z B

center = [s, b00, b10]                # ed.center  (boost center)
support = [b00, b01, b10, b11]        # supportAt   (full layer-2 block)
support_only = [b01, b11]             # support \ center  (col-1)
allvars = (s,beta,b00,b01,b10,b11,z00,z01,z10,z11)

# --- (1) R_p and A1/A2/A3 ---------------------------------------------------
Rp = sp.expand(H * sp.Matrix([[1,beta],[0,s]]))
entries = list(Rp)

def deg_in(f, xs):
    return max([sum(m) for m in sp.Poly(sp.expand(f), *xs).monoms()], default=0)

# A1: vanish when the center -> 0
A1 = all(sp.expand(f).subs({x:0 for x in center}, simultaneous=True) == 0 for f in entries)
# A2: total degree <= 1 in the center coords
A2 = all(deg_in(f, center) <= 1 for f in entries)
# A3: after the boost blow-up (center coords c |-> s*c), each entry is exactly divisible by s
pulled = [sp.expand(f.subs({b00:s*b00, b10:s*b10}, simultaneous=True)) for f in entries]
A3 = all(sp.expand(g.subs(s,0)) == 0 and sp.cancel(g/s).is_polynomial(*allvars) for g in pulled)
print("A1 (vanish at center=0) :", A1)
print("A2 (deg<=1 in center)   :", A2)
print("A3 (s | entry after boost blow-up):", A3)
assert (A1,A2,A3) == (True,True,True), "boost-node residual not boost-ready!"

# --- (2) TERMWISE epsilon-decomposition ------------------------------------
# For each entry, expand into monomials; for each monomial read eps(s) = power of s,
# and record which support-only coords (b01/b11) it reads.
print("\n--- termwise eps(pivot s) per entry ---")
mechanism_ok = True
for idx, f in enumerate(entries):
    P = sp.Poly(sp.expand(f), *allvars)
    sidx = P.gens.index(s)
    b01i, b11i = P.gens.index(b01), P.gens.index(b11)
    print(f"entry {idx}: {sp.expand(f)}")
    for mono, coeff in P.terms():
        eps_s = mono[sidx]
        reads_support_only = (mono[b01i] > 0) or (mono[b11i] > 0)
        tag = "  <-- reads support-only (col1)" if reads_support_only else ""
        print(f"    mono {mono}  coeff {coeff}   eps(s)={eps_s}{tag}")
        # MECHANISM: any monomial reading a support-only coord must carry eps(s)>=1
        if reads_support_only and eps_s < 1:
            mechanism_ok = False
print("\nMECHANISM (every support-only monomial carries eps(s)>=1):", mechanism_ok)
assert mechanism_ok, "boostReady mechanism FAILS: a col-1 coord appears without a pivot factor"

# --- (3) explicit Deg1SupportedOn(center) re-grouping ----------------------
# Show R_p[j] = sum_{i in center} c'_i * u_i with each c'_i center-free.
print("\n--- explicit Deg1SupportedOn(center={s,b00,b10}) re-grouping ---")
regroup_ok = True
for idx, f in enumerate(entries):
    fe = sp.expand(f)
    # coefficient of each center coord, then check the remainder vanishes
    c_b00 = sp.expand(fe.coeff(b00,1).subs({b00:0,b10:0,s:0}))   # part linear in b00, center-free
    c_b10 = sp.expand(fe.coeff(b10,1).subs({b00:0,b10:0,s:0}))
    c_s   = sp.expand(fe.coeff(s,1).subs({b00:0,b10:0,s:0}))
    recon = sp.expand(c_b00*b00 + c_b10*b10 + c_s*s)
    ok = sp.expand(fe - recon) == 0
    # center-free check
    cf = all(sp.expand(sp.diff(cc, v))==0 for cc in (c_b00,c_b10,c_s) for v in center)
    print(f"entry {idx}: c_s = {c_s} ;  c_b00 = {c_b00} ;  c_b10 = {c_b10} ;  exact={ok}, center-free={cf}")
    regroup_ok = regroup_ok and ok and cf
print("\nRE-GROUPING (Deg1SupportedOn center holds, coeffs center-free):", regroup_ok)
assert regroup_ok
print("\nNOTE: c_s = h01 = z00*b01 + z01*b11  ABSORBS the col-1 coords into the PIVOT term.")
print("      This is the 'untouched terms carry u_pivot in their coefficient' mechanism, exactly.")
print("\nSTAGE 1 PASS")
