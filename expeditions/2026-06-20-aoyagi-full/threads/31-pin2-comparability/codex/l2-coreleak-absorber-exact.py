#!/usr/bin/env python3
"""
EXACT-ALGEBRA adjudication of the L2 derivative-leg atom (thread 31, aoyagi-full).

Two sharp truth-values:

  Q1 (core-leak / OBSTRUCTION): Is D(schurCorrectionConj)(0) != 0 genuinely?  I.e. when
      coreAbsorb.symm shears the core slot by the *conjugated* per-layer Schur correction
      whose Y/Z reads are nonzero away from the origin, does the conjugated shift have a
      nonzero derivative at the origin?  [genm-l2conj: "value-0 -> PIN-0 transfers, mechanical";
      genm-l2thread: "the leak is real, value-0 is insufficient for PIN-1".]

  Q2 (absorber atom / WITNESS): Is  d/d(core) deepestEFull (0) = 0  ?  I.e. in the reg-residual
      blocks (P00-1, P01, P10) of  P = reindex(prod(framedParamsPivot q))  at L=2, is every term
      that carries a core coordinate  T_s  multiplied by a factor vanishing at the origin
      (so the partial wrt every core coord is 0 at q=0)?

Structure transcribed from the Lean defs (DeepestFramedProduct/Pivot, DeepestGaugeConstruction):

  framedLayer s P Q X Y Z T = corM + P * reindex(fromBlocks X Y Z T) * Q,   corM = fromBlocks I 0 0 0
  framedParamsPivot q  layer s :
     non-last : framedParams  (X_s,Y_s,Z_s read off (reg,spec); T_s = core read)
     last     : same shape, pivot column split (same block algebra)
  deepestEFull q = reg-residual (P00-I, P01, P10) of reindex(prod over s of framedLayer_s)

We test at L=2 with the SMALLEST non-degenerate widths that keep all four blocks alive:
  r = 1 (pivot rank), H0 = H1 = H2 = 2  (so each corank H_s - r = 1).
This is the realizability minimum where Z_0, Y_1 are genuinely present.
The frames P_s, Q_s are the deepest-point gauge frames; we test BOTH:
   (a) P_s = Q_s = I  (the bare additive chart, the "W=I" baseline)
   (b) the block-triangular endpoint frames hPtri/hQtri (P0 block-lower, Q1 block-upper),
       which is what the actual bundle supplies.
Everything is exact symbolic (sympy), so the partial derivatives at 0 are exact rationals.
"""

import sympy as sp

def fromBlocks(A, B, C, D):
    """[[A,B],[C,D]] with A r x r, etc. -- mirrors Matrix.fromBlocks (rThresholdSplit order)."""
    return sp.Matrix(sp.BlockMatrix([[A, B], [C, D]]))

def reg_residual(P, r):
    """(P00 - I, P01, P10) as a flat list of entries -- mirrors deepestEFull's (toBlocks11-1, 12, 21)."""
    P11 = P[0:r, 0:r] - sp.eye(r)
    P12 = P[0:r, r:]
    P21 = P[r:, 0:r]
    return list(P11) + list(P12) + list(P21)

def build_L2(r, m0, m1, m2, frames="I"):
    """
    Returns (residual_entries, core_syms, gauge_syms).
    Widths: H0 = r+m0, H1 = r+m1, H2 = r+m2 ; corank m_s.
    Layer 0 maps Fin H0 -> Fin H1 (castSucc=H0, succ=H1).
    Layer 1 maps Fin H1 -> Fin H2.
    """
    # --- gauge + core symbols per layer ---
    def blk(name, rows, cols):
        return sp.Matrix(rows, cols, lambda i, j: sp.Symbol(f"{name}_{i}_{j}"))
    # layer 0: X0 (rxr), Y0 (r x m1), Z0 (m0 x r), T0 (m0 x m1)
    X0 = blk("X0", r, r); Y0 = blk("Y0", r, m1); Z0 = blk("Z0", m0, r); T0 = blk("T0", m0, m1)
    # layer 1: X1 (rxr), Y1 (r x m2), Z1 (m1 x r), T1 (m1 x m2)
    X1 = blk("X1", r, r); Y1 = blk("Y1", r, m2); Z1 = blk("Z1", m1, r); T1 = blk("T1", m1, m2)

    core_syms = list(T0) + list(T1)
    gauge_syms = list(X0)+list(Y0)+list(Z0) + list(X1)+list(Y1)+list(Z1)

    corM0 = fromBlocks(sp.eye(r), sp.zeros(r, m1), sp.zeros(m0, r), sp.zeros(m0, m1))
    corM1 = fromBlocks(sp.eye(r), sp.zeros(r, m2), sp.zeros(m1, r), sp.zeros(m1, m2))

    dev0 = fromBlocks(X0, Y0, Z0, T0)   # H0 x H1
    dev1 = fromBlocks(X1, Y1, Z1, T1)   # H1 x H2

    if frames == "I":
        P0 = sp.eye(r+m0); Q0 = sp.eye(r+m1); P1 = sp.eye(r+m1); Q1 = sp.eye(r+m2)
    elif frames == "tri":
        # block-triangular endpoint frames the bundle supplies:
        #  P0 block-LOWER (hPtri: toBlocks12 = 0): [[A,0],[C,D]]
        #  Q1 block-UPPER (hQtri: toBlocks21 = 0): [[A,B],[0,D]]
        #  interior boundary frames (Q0, P1) generic invertible (use I here; they are the
        #  deepest-frame which at the boundary is identity by hQf0/hPfL -- see hinterface).
        a = blk("PA0", r, r); c = blk("PC0", m0, r); d = blk("PD0", m0, m0)
        P0 = fromBlocks(a, sp.zeros(r, m0), c, d)
        e = blk("QA1", r, r); b = blk("QB1", r, m2); f = blk("QD1", m2, m2)
        Q1 = fromBlocks(e, b, sp.zeros(m2, r), f)
        Q0 = sp.eye(r+m1); P1 = sp.eye(r+m1)
        gauge_syms += list(a)+list(c)+list(d)+list(e)+list(b)+list(f)
    else:
        raise ValueError(frames)

    FL0 = corM0 + P0 * dev0 * Q0
    FL1 = corM1 + P1 * dev1 * Q1
    P = FL0 * FL1     # the product prod(framedLayer); reindex is identity here (already block-split order)

    resid = reg_residual(P, r)
    return resid, core_syms, gauge_syms, (X0,Y0,Z0,T0,X1,Y1,Z1,T1)

def at_origin(expr_list, all_syms):
    sub = {s: 0 for s in all_syms}
    return [sp.expand(e).subs(sub) for e in expr_list]

def partials_at_origin_wrt(expr_list, target_syms, all_syms):
    """Return dict: for each residual entry index, the list of (sym, dval at 0) that are nonzero."""
    sub0 = {s: 0 for s in all_syms}
    out = []
    for idx, e in enumerate(expr_list):
        ee = sp.expand(e)
        nz = []
        for t in target_syms:
            d = sp.diff(ee, t).subs(sub0)
            if d != 0:
                nz.append((t, d))
        out.append((idx, nz))
    return out

def lowest_degree_in_targets(expr, target_syms):
    """Minimum total degree (in target_syms) of any monomial in expr. Tells degree-1 vs degree-2."""
    poly = sp.Poly(sp.expand(expr), *target_syms) if target_syms else None
    if poly is None:
        return None
    degs = []
    for monom, coeff in poly.terms():
        if coeff != 0:
            degs.append(sum(monom))
    return min(degs) if degs else None  # None means expr has NO target_syms at all (deg infinity)

print("="*78)
print("L = 2, r = 1, H = (2,2,2)  (corank 1 each); EXACT symbolic")
print("="*78)

for frames in ["I", "tri"]:
    print(f"\n----- frames = {frames} -----")
    resid, core_syms, gauge_syms, blocks = build_L2(1, 1, 1, 1, frames=frames)
    all_syms = core_syms + gauge_syms

    # base check: residual = 0 at origin (deepest point sits at residual 0)
    base = at_origin(resid, all_syms)
    print("residual at origin (should be all 0):", base)

    # ---- Q2: d/d(core) of EACH residual entry at origin ----
    print("\n[Q2] core partials of deepestEFull at the origin:")
    core_part = partials_at_origin_wrt(resid, core_syms, all_syms)
    any_core_deg1 = False
    for idx, nz in core_part:
        if nz:
            any_core_deg1 = True
            print(f"   residual[{idx}] has NONZERO core partial at 0: {nz}")
    if not any_core_deg1:
        print("   ALL core partials are 0 at the origin  ==>  d/d(core) deepestEFull(0) = 0  (atom TRUE)")

    # degree audit: lowest degree of each core sym's appearance per residual entry
    print("\n[Q2 degree audit] for each residual entry, lowest total-degree of monomials")
    print("   containing AT LEAST ONE core coord (None = entry has no core coord at all):")
    for idx, e in enumerate(resid):
        ee = sp.expand(e)
        # keep only monomials that contain >=1 core symbol
        poly = sp.Poly(ee, *all_syms)
        min_deg_with_core = None
        for monom, coeff in poly.terms():
            if coeff == 0:
                continue
            core_deg = sum(monom[all_syms.index(c)] for c in core_syms)
            if core_deg >= 1:
                tot = sum(monom)
                if min_deg_with_core is None or tot < min_deg_with_core:
                    min_deg_with_core = tot
        print(f"   residual[{idx}]: min total-degree of a core-carrying monomial = {min_deg_with_core}")

print("\n" + "="*78)
print("Q1 separate model: the CONJUGATED shift's derivative at 0")
print("="*78)
print("""
schurCorrection_s(p) = -Z_s(p) * (1 + X_s(p))^-1 * Y_s(p)   (reads p = (reg,spec) gauge slot)
coreAbsorb.symm shears core by  -shift = -schurCutoffShift  near 0.
Q1 asks: D(schurCorrection_s)(0) =? 0   (as a map of the gauge slot p).
Since Y_s, Z_s are LINEAR coordinate reads (read*_s), Y_s(0)=Z_s(0)=0 but
D Y_s(0), D Z_s(0) are the (nonzero) linear reads themselves, and (1+X)^-1 -> I.
""")
# Model one layer's schurCorrection as a function of a scalar deformation t along each read,
# exact: -Z (1+X)^-1 Y with Z=Z(t), Y=Y(t) linear, X=X(t) linear, all 0 at t=0.
t = sp.Symbol("t")
# r=1, m=1 scalars: X=x*t, Y=y*t, Z=z*t  (the linear reads)
x, y, z = sp.symbols("x y z")
X = sp.Matrix([[x*t]]); Y = sp.Matrix([[y*t]]); Z = sp.Matrix([[z*t]])
corr = -Z * (sp.eye(1) + X).inv() * Y      # = -(z t)(1+x t)^-1 (y t)
corr = sp.expand(sp.series(corr[0,0], t, 0, 3).removeO())
print("schurCorrection (one layer, scalar) as a series in t:", corr)
print("   d/dt at t=0 :", sp.diff(corr, t).subs(t,0), "   (the VALUE-derivative of the correction)")
print("   leading order:", "t^2  ==> D(correction)(0) = 0  (the correction itself is degree-2!)")

print("\n" + "="*78)
print("EXTRACT: the exact degree-2 core-leak monomials (the brief's Y0.T1, T0.Z1)")
print("="*78)
resid, core_syms, gauge_syms, blocks = build_L2(1, 1, 1, 1, frames="I")
(X0,Y0,Z0,T0,X1,Y1,Z1,T1) = blocks
all_syms = core_syms + gauge_syms
labels = ["P00-1 (reg 1,1)", "P01 (reg 1,2)", "P10 (reg 2,1)"]
for idx, e in enumerate(resid):
    ee = sp.expand(e)
    poly = sp.Poly(ee, *all_syms)
    core_terms = []
    for monom, coeff in poly.terms():
        core_deg = sum(monom[all_syms.index(c)] for c in core_syms)
        if core_deg >= 1:
            mon = sp.prod([all_syms[i]**monom[i] for i in range(len(all_syms)) if monom[i] > 0])
            core_terms.append(coeff*mon)
    print(f"\nresidual[{idx}] = {labels[idx]}:")
    print(f"   FULL = {ee}")
    print(f"   core-carrying monomials: {core_terms if core_terms else 'NONE (no core coord)'}")

# ============================================================================
# VERDICT (pen-and-paper, genm-assemble, 2026-06-28) -- exact algebra + #print axioms
# ============================================================================
# Q1 (core-leak derivative):  The bare shift schurCorrection = (-Z)(1+X)^-1 Y is BILINEAR
#     in (Z,Y), both vanishing at 0, so D(schurShift)(0) = 0 GENUINELY (scalar series = -t^2 yz).
#     This is ALREADY PROVED in Lean: hasStrictFDerivAt_schurCutoffShift_zero (axiom-clean).
#     genm-l2thread's "D(readY) is the nonzero linear read => term nonzero" argument is WRONG:
#     it forgets the term is multiplied by Z(0)=0 (Leibniz: D(ZY)(0) = Z(0)DY + (DZ)Y(0) = 0).
#     The deepest-point's RAW deepBlkZ_0 != 0 is a DIFFERENT object (the deepestPoint matrices),
#     NOT the gauge-slot read Z_0(p) that feeds the shift (which is 0 at the origin).
#     ==> genm-l2conj is RIGHT that the shift's derivative VALUE is 0; but its inference
#         "value-0 => PIN-0 transfers => mechanical" is the WRONG REASON. The real reason
#         the leg closes is the block-triangular invertibility below (G need not vanish).
#
# Q2 (absorber atom  d/d(core) deepestEFull(0) = 0):  TRUE (exact, both I and tri frames).
#     Core coords enter the reg residual ONLY at degree 2: T1*Y0 (in P01), T0*Z1 (in P10) --
#     EXACTLY the brief's named leaks Y0.T1, T0.Z1 -- each * an origin-vanishing gauge factor.
#     BUT: this atom is NOT NEEDED for the hTilde invertibility. regStraightenTotalCLM2 D_E
#     = [[F, G],[0, I]] is invertible iff F (reg->reg block) is, INDEPENDENT of G = d/d(core).
#     (det = F; inverse [[1/F, -G/F],[0,I]].)  Lean: regStraightenTotalCLM2_equiv_of_regBlock_isUnit.
#
# BOTTOM LINE: In the genm-assemble worktree the entire derivative leg is ALREADY sorry-free
#     and axiom-clean (hasStrictFDerivAt_schurCutoffShift_zero, _coreShearHomeo_symm_zero,
#     deepestEFull_deriv, regStraightenTotalCLM2_equiv_of_regBlock_isUnit). The "remaining gap"
#     sorry the brief cites (GaugeConstruction:215-221) is from a STALE/parallel worktree copy;
#     this worktree's hTilde (DeepestL2Wiring.lean:222-274) composes the proved facts. No new
#     geometry is owed for this leg. (Q2 atom is a TRUE bonus fact, not on the critical path.)

# ============================================================================
# Q1 RE-CHECK (controller objection: is the Z-factor full-layer deepBlkZ+readZ?)
# ============================================================================
# CONTROLLER'S MECHANISM (modeled in /tmp/q1_conj_check.py, internally consistent):
#   IF shift's Z = Zhat = deepBlkZ0 + readZ0  with deepBlkZ0 != 0, deepBlkY0 = 0, THEN
#   value(0) = -deepBlkZ0*deepBlkY0 = 0 (OK basepoint) BUT D(.)(0) = -deepBlkZ0*D(readY) != 0.
#   So genm-l2thread's blocker WOULD be real -- FOR THAT OBJECT.
#
# BUT the live def's Z-factor is the BARE deviation read `readZ` (DeepestSchurShift.lean:135-139),
# NOT deepBlkZ+readZ. There is NO `deepBlk` addend / `schurCorrectionConj` anywhere in any worktree
# (grep: 0 hits). Three independent confirmations the bare reading is correct:
#   (1) SOURCE: schurCorrection p s = -(readZ p s)*(1+readX p s)^-1*(readY p s); readZ/Y are the
#       frame-conjugated DEVIATION reads (DeepestSplitConcrete: readX/Y/Z(split w) = deviation block
#       of (w - w_deepest)), living in the r+(.-r) split where the deepest layer = fromBlocks 1 0 0 0.
#       The controller's "deepBlkZ0 = toBlocks21 != 0" is the RAW deepestPoint matrix in the STANDARD
#       basis -- a DIFFERENT split. In the framed split deepBlkZ0 = 0, and readZ carries all the Z.
#   (2) CODEX (xhigh, decorrelated): A/B/C/D all confirm; verdict "D(schurCorrection)(0)=0, bare-read".
#   (3) PROOF-CONSISTENCY: `coreAbsorb 0 = 0` (DeepestGaugeChart structure field, PROVED via
#       coreShearHomeo_basepoint + schurCutoffShift_zero) AND `D(coreShearHomeo.symm)(0)=id`
#       (hasStrictFDerivAt_coreShearHomeo_symm_zero, PROVED axiom-clean, needs D(shift)(0)=0).
#       Under the conjugated reading the latter would be FALSE -- a proved axiom-clean theorem cannot
#       rest on a false hypothesis chain. So the reads ARE bare. QED.
#
# FINAL Q1 VERDICT (unchanged, now triple-locked): D(shift)(0) = 0. genm-l2conj right on the value;
# genm-l2thread's blocker applies only to a non-existent conjugated object. The leg is closed.
