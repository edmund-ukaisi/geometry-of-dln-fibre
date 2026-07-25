# B1 escape-cone probe (#170) — WITNESS: B1 DISSOLVES (detail-at-scale artifact)

**Seat:** reroute-R2-tubecover (same pen-and-paper, decorrelated). Exact algebra (sympy over ℚ) +
own Codex xhigh (`codex/b1-{prompt,answer}.md`, EXIT 0) — CONVERGED by an independent route, and Codex
CORRECTED one of my sub-computations (see Q1). NO Lean. Scripts: `probe4_b1_escape.py` (+ the numpy
d.o.s. guide inline). This is the LAST open caveat from the tube probe (#169); the two compose.

## NET VERDICT: B1 DISSOLVES. The sector-count escape cone is a DETAIL-AT-SCALE artifact of the
FIXED-shear atlas, NOT a monument-adjacent hole. The lower bound `rlct ≥ ½·minAdm` SURVIVES the
non-coverage. Destination stays **(A) fully-cite-free reachable / (B) P-with-small-cite**; (C) OFF.

The escape cone DOES meet the fibre {loss=0} (so it is NOT dismissable by naive loss-regularity), BUT
its local RLCT equals the bound EXACTLY — so the uncovered region contributes AT the threshold, never
below it. And the atlas CAN be made to cover it (permutation-closed / pivot-adapted normalization).

---

## THE ESCAPE CONE (sector-count #144/#145, concrete)
Original DLN coords x₀..x₂₀ = matrix entries (0–8 = C¹ 3×3, 9–20 = C² 3×4), loss = ‖C¹·C²‖²_F,
minAdm(3,3,4)=8, bound `rlct ≥ 4`. Valid (normal-crossings) charts pivot on V={0,1,2,3,20}; the
W={4,5,6,7} (shear-written C¹ entries) charts are non-normal-crossings UNDER A FIXED shear. Valid
images ⊆ {max_W ≤ C·max_V}, so the **escape cone E = {max_W > C·max_V}** (positive-measure,
scale-invariant, meets every ball) is covered by NO valid chart. Witness x = t·e₄.

## Q1 — the escape cone MEETS the fibre; local RLCT there = the BOUND (Codex CORRECTED me)
- x = t·e₄ (only C¹ entry #4 = t, C²=0): loss = ‖C¹·0‖² = 0. So **E ∩ {loss=0} ≠ ∅** — it is NOT
  loss-regular; naive "droppable because bounded away from the fibre" FAILS. [FACT]
- **Local RLCT at t·e₄ = 4 = ½·minAdm — I initially mis-computed this as 2.** My "loss ≈ t²‖C²-row‖²
  ⇒ rlct 2" was the RLCT of the SLICE with C¹ FROZEN at tE₄. The FULL 21-dim local RLCT (Codex,
  verified): with a=C¹-pivot≠0, Gaussian elim gives loss ≍ ‖ũ‖² + ‖S·V‖², S = D − c·a⁻¹·r (the 2×2
  Schur complement of C¹), V the 2×4 lower block of C². ‖ũ‖² (ũ∈ℝ⁴) → 4/2 = 2; **‖S·V‖² is itself a
  smaller DLN loss (S 2×2, V 2×4) with rlct = ½·minAdm(2,2,4) = ½·4 = 2** (verified). Total 2+2 = **4**.
  So the escape cone's deepest point contributes EXACTLY the bound, not below it. [PROVEN, decorrelated]
- STRUCTURE: the escape-cone singularity is SELF-SIMILAR — a smaller DLN product (2,2,4) via the Schur
  complement. This is why it lands exactly at ½·minAdm (the recursion value), never below.

## Q2/Q3 — E is a finite union of permuted-VALID sectors ⇒ rlct(loss|E) = ½·minAdm (PROVEN)
The Frobenius loss is PERMUTATION-invariant: ‖P·C¹·Q · Q⁻¹·C²·S‖ = ‖C¹·C²‖ for permutation matrices
(verified exact: row-swap of C¹ AND inner-index swap (C¹Q, Q⁻¹C²) both leave loss unchanged). Row/col
permutations act transitively on C¹'s 9 entries.
- **Codex refinement (sharper than my first pass):** NO single permutation sends all of E into one
  valid cone (row-degree pattern (2,2) on W vs (3,1,1) on its complement forces one W-axis to stay a
  W-axis). Instead E = ⋃_{w∈W} E_w (partition by which W-coord is max), and for each w a permutation
  φ_w sends E_w into a valid dominance sector: φ_w(E_w) ⊆ {max_W ≤ C·max_V}.
- Then rlct(loss|E_w) = rlct(loss|φ_w(E_w)) [isometry] ≥ rlct(loss|valid region) ≥ ½·minAdm [subset
  monotonicity rlct(f|A) ≥ rlct(f|B) for A⊆B; valid charts read ≥ ½·minAdm]. Finite-union min ⇒
  **rlct(loss|E) ≥ ½·minAdm**; and ≤ ½·minAdm since E ⊇ nbhds of small t·e₄ (local rlct = 4). So
  **rlct(loss|E) = ½·minAdm exactly.** [PROVEN]

## Q4 — the lower bound SURVIVES the non-coverage (PROVEN)
vol{loss<ε} = vol{loss<ε, covered} + vol{loss<ε, E} (nonneg, no cancellation of leading poles) ⇒
rlct(loss) = min(rlct(covered), rlct(E)). Both = ½·minAdm. So non-coverage by the fixed-shear atlas is
a **proof-completeness defect, not a counterexample** to `rlct ≥ ½·minAdm`. [PROVEN]

## Q5 — DETAIL-AT-SCALE, dissolved by a permutation-closed (pivot-adapted) atlas (PROVEN + 1 inference)
- Coordinate permutations have Jacobian ±1, preserve the Frobenius loss AND monomial Jacobians / normal
  crossings. So a W-pivot chart defined by TRANSPORTING a valid V-pivot chart through the loss-isometry
  φ_w is normal-crossings and reads the same ratio. The permutation-closed atlas covers E with valid
  charts. [PROVEN abstractly]
- CORROBORATING (my probe4, exact): the "128 invalid charts" are a COMPOSITION-ORDER artifact —
  SHEAR-OUTERMOST reordering (blow-up on un-sheared coords, shear applied last as a global unipotent
  bijection) makes det Dg a coordinate MONOMIAL for ALL pivots (verified p=0,4,5: fixed-shear gives
  non-monomial for 4,5; shear-outermost gives monomial). So the Jacobian obstruction is order-dependent
  and removable. [FACT, Jacobian-level]
- THE ONE INFERENCE (Codex + me): that a specific rewritten "adaptive-shear" formula (or the
  shear-outermost order) exactly realizes the transported chart AND still monomialises the IDEAL (not
  just the Jacobian) — the ideal-monomialisation-in-the-new-order should be checked in the build. The
  permutation-transport argument is airtight abstractly; the concrete formula is build labour.

## FIRMEST / MOST-LIKELY-TO-BREAK / GENERALITY
- **FIRMEST [PROVEN, decorrelated]:** B1 does not break `rlct ≥ ½·minAdm`. The escape cone meets the
  fibre but its local RLCT = ½·minAdm EXACTLY (self-similar Schur-complement DLN sub-loss); rlct(loss|E)
  = ½·minAdm; the bound = min(covered, E) = ½·minAdm survives whether or not the fixed atlas covers E.
- **MOST LIKELY TO BREAK IT (scoped, detail-at-scale):**
  1. The **permutation-closed / pivot-adapted-normalization atlas** must be built (fixed-shear leaves E
     uncovered; the transported chart's concrete adaptive-shear formula must monomialise the IDEAL in
     the new order — Jacobian-monomial is verified, ideal-level is the build check). This is the SAME
     R2 spec correction as the tube probe (fan the normalization WITH the pivot).
  2. If the atlas proof insists on literal coverage AND the build ships a fixed shear, B1 is a real
     (but fixable) proof-completeness gap — not a math obstruction.
- **GENERALITY:** the mechanism is (i) permutation-invariance of the Frobenius loss (UNIVERSAL, all
  instances) + (ii) the escape-cone singularity being a self-similar smaller DLN loss contributing
  ½·minAdm (structural). Verified exact at (3,3,4) where the escape cone was FOUND; the (3,3,3,2,2)
  mechanism is identical (permutation-invariance is instance-independent). Instance-verified +
  structural inference for full generality.

## COMPOSES WITH THE TUBE PROBE (#169) — one unified R2 spec
Both B2 (the {unit≈0} tube) and B1 (the escape cone) DISSOLVE, and BOTH need the SAME fix: a
**permutation-closed atlas that fans the normalization/shear WITH the pivot** (not a fixed
normalization). Fixed-normalization covers 0% of the tube (B2) and leaves the escape cone (B1). This is
the sector-count's route (a)/(A), now rigorously priced as detail-at-scale. #145's ~2% is fully
reconciled at depth: (B2) tube = within-chart via 1/R + survivor-entry fan; (B1) escape cone =
permutation-closed atlas; the deep stratum {R=0}/{loss deeper} = the self-similar recursion.

## CLOSE
B1 GREEN: WITNESS, detail-at-scale. The destination is now fully de-risked for the lower bound —
(A)/(B) reachable, (C) off. The residual is ALL detail-at-scale build labour, precisely named: the
permutation-closed (pivot-adapted-normalization) atlas [B1+B2 unified] + the recursion-on-{R=0}
terminating with no divisor ratio < ½·minAdm [the tube probe's #172 caveat]. No monument. NEXT: this
was the last probe (per heartbeat "no more probes after these") — the build (R2) can start on the
unified survivor-entry / permutation-closed fan spec.

---

## ADDENDUM — R>0 sandwich in the escape charts (#170 refinement, controller Q): SANDWICH SUFFICES
(exact, `probe5_sandwich_escape.py`). The R>0-corrected framing: the lower bound needs only the
POINTWISE SANDWICH `loss = monomial²·R` with `R(0)≠0`, NOT the full ideal identity. Does the
pivot-adapted escape chart give it?

**VERDICT: YES for the correctly-constructed (loss-isometric / matched) escape charts — the fix needs
ONLY the sandwich; ideal-monomialisation is STRONGER than the lower bound requires.** With a sharp,
flagged nuance about WHICH charts are fan members.

- **Matched escape chart (inner-permutation image, a loss-isometry): sandwich holds, R(0)=1.** The
  full-swap chart (pivot on C3[0,1] AND C4[1,0] — the matched inner permutation) gives
  Ye[0,0] = c′·p′ + 1, Re(0) = 1 — IDENTICAL sandwich structure to canonical. [FACT, exact]
- **The sandwich holds IFF the chart monomial is a MATCHED product term of X[0,0].**
  X[0,0] = C3[0,0]·C4[0,0] + C3[0,1]·C4[1,0] (two terms = the two matched/diagonal pairings). A chart
  whose monomial is one of these two → X[0,0]/mono = 1 + (small) → R(0)=1. A MISMATCHED monomial
  (C3[0,1]·C4[0,0] or C3[0,0]·C4[1,0]) → X[0,0]/mono = a SUM OF TWO RATIOS → R(0)=0, sandwich FAILS.
  [FACT, exact — the controller's flagged failure mode, found]
- **The mismatched pairings are NOT fan members — they are the RECURSION's domain, not a hole.** A
  mismatched sector {C3[0,1] dom & C4[0,0] dom} is exactly where X[0,0] is a SUM of two COMPARABLE
  monomials with NO dominant term — so it is not monomialised by any single-term chart; it needs a
  DEEPER blow-up to separate the two terms (and it contains the {X[0,0]=0} cancellation sub-locus).
  This is the SAME detail-at-scale recursion already identified (the tube/{R=0} deep stratum), not a
  new obstruction. The matched charts cover the dominant-monomial sectors (sandwich); the
  comparable-monomial sectors recurse.

**R2 SPEC SHARPENING (unifies the two probes' spec):** the fan must fan by the **loss-isometry orbit**
— the MATCHED inner-permutation pairings (each chart's monomial = a product term of the survivor) —
NOT arbitrary independent pivot choices. Three failure/success modes now pinned:
  - radial-pivot-only (keep one survivor entry): covers 0% of the tube [tube probe]. ✗
  - mismatched-independent pivots: R(0)=0, no kept survivor [this probe]. ✗ (not a fan member; recurse)
  - matched-consistent (loss-isometry orbit): R(0)=1, sandwich holds. ✓ — THE fan.
In the FULL (unweighted) DLN loss the matched structure is the loss-symmetry group (verified
permutation-invariance, probe4); the residual's δ-weighting distinguishes the survivor row but the
matched pairings are still exactly the two product terms of each survivor entry.

**NET:** the escape-cone (and tube) fix needs only the R>0 SANDWICH — the "ideal-level build check" I
listed is STRONGER than the lower bound requires, which SIMPLIFIES the R2 spec. The only residual is
the recursion (comparable-monomial / {R=0} deep strata), already named as detail-at-scale (#172). No
ideal-monomialisation needed for the lower bound; no monument.

### Tie-in: the matched escape chart has det-monomial AND the sandwich TOGETHER (probe6, exact)
The matched/pivot-adapted (shear-outermost) escape chart — blow-up on the off-diagonal pivot pair
(C3[0,1]=A, C4[1,0]=B) with the normalization adapted so the '1' sits at the pivot slot — has:
- **det Dg = −A⁵·B³** — a coordinate MONOMIAL (the two blow-up radials); IDENTICAL exponents to the
  canonical chart's (w⁵ for C3's 6 coords, y³ for C4's 4 coords).
- **loss = (A·B)²·R, R(0) = 1** (kept survivor X[0,0]/(AB) = c′p′ + 1 → 1) — the SANDWICH.
So the escape chart reads the SAME divisor ratios (A: (5+1)/2 = 3, B: (3+1)/2 = 2, min = 2 = ½·minAdm)
as canonical → contributes EXACTLY the bound. It is a complete valid sandwich chart. The B1 fix needs
ONLY the sandwich; the shear-outermost / pivot-adapted (matched) order supplies both det-monomial and
R(0)≠0. (The shear is a unipotent bijection fixing 0 with D(shear)(0)=I, so applied last it cannot
destroy R(0) — a value-at-0 of the kept survivor — it only re-monomialises the Jacobian.) [FACT, exact]
