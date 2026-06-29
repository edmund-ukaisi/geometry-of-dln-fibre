# det_comp 2nd-M #eval findings (spec-validate-FIRST) — the per-PIECE decomposition is the open question

Branch genm-interior @cd5696c3. Per the gate (A): re-spec det_comp + run the 2nd-M #eval UP FRONT, validate
the per-piece dets are UNIFORM across M BEFORE any Lean build. Using the VALIDATED chain builder
(families.py build/flatten, from genm-budget's radial-sep work). Findings (honest):

## WHAT THE #eval CONFIRMED
- (3,3,3,3) GLOBAL det via the validated chain builder: `−x0^5·x1^4·x4^2·x12^3` — u-SEPARATES as a single
  front power 5 = minAdm−1, the rest a clean monomial. Reproduces the known answer ✓. (And genm-budget's
  families.py ALREADY validated this global u-separation across L=4/L=5 multi-t≥2 families — the GLOBAL det
  = u^{minAdm−1}·monomial is validated ACROSS M.)

## WHAT THE #eval REVEALED (the genuine open question for det_comp)
- The NAIVE per-LAYER square partition (layer-k outputs vs layer-k-owned coords) is NON-SQUARE: layer-1's
  9 outputs vs 11 "owned" coords; layers 0,2 have 9 outputs vs 0 owned. CAUSE: A_k reads boundary {k,k+1}
  (the PROVEN b-0 nearest-neighbor locality), so the coords do NOT partition per-layer-square. The
  per-piece DECOMPOSITION is NOT a simple layer partition.
- (2,3,2) [2nd M, smaller K-cores]: my naive block allocation OVER-COUNTS coords (13 vs flatDim 12) — a
  faithful SQUARE chart at an arbitrary 2nd M needs the EXACT per-M coord budget (which coords free vs
  fixed/identity) — itself the delicate per-M bookkeeping, NOT trivial to hand-balance correctly.

## HONEST ASSESSMENT (do NOT over-claim — the binding lesson)
- The GLOBAL det uniformity (u^{minAdm−1}·monomial ∀M) is VALIDATED (3333 + genm-budget families). The
  leafH exponent vector is the per-coordinate powers of that monomial. 2b-i-C/D (interiorDet_of_factored)
  ALREADY consumes this abstractly (given the map equality + det bookkeeping).
- The det_comp PER-PIECE factorization (DFrame_M = ∏ triangular pieces, each a uniform local det) is NOT
  YET validated as uniform — and the #eval shows the naive per-layer partition FAILS (the right piece
  decomposition is subtle, NOT layer-square). The pieces must be the TRIANGULAR FRAME factors (radial,
  per-boundary Schur/LDU), NOT a layer partition — and getting that decomposition right (so DFrame_M = ∏
  pieces with uniform per-piece dets) is the genuine open sub-spec.
- RISK FLAG: the per-piece decomposition may itself need per-M structure (the same M-dependence one level
  down). The #eval did NOT confirm a uniform per-piece formula — it confirmed the GLOBAL det (already known)
  and revealed the naive partition fails.

## RECOMMENDATION (honest, not over-claiming)
The 2nd-M #eval VALIDATES the global det uniformity but does NOT yet validate a uniform PER-PIECE
det_comp factorization (the naive layer-partition fails; the correct triangular-piece decomposition + its
M-uniformity is unestablished). Before committing det_comp as the build route, the genuine open piece is:
WHAT is the correct per-piece (triangular frame factor) decomposition of DFrame_M, and is it M-uniform?
This is a design-depth question — recommend a focused pen-and-paper `witness` (the design-space seat) to
EXHIBIT the per-piece factorization DFrame_M = ∏ pieces at the (3,3,3,3) anchor + validate it M-uniform
on a 2nd M (with the correctly-balanced square chart), BEFORE the Lean build. If the per-piece
factorization is ALSO M-dependent/intractable → (B) roadmap+operator. The det_comp route is PLAUSIBLE
(Codex-preferred, the global det is uniform) but its per-piece form is NOT yet validated — I will not
claim it tractable on the global-det evidence alone (the layer-compatible-e lesson).
