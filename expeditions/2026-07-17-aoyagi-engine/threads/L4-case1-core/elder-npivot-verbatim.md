# Elder verbatim — the faithful `N_p` object + the coupled re-bake spec (RATIFIED)

**Status:** pnp-transport's `npivot-certificate.md` RATIFIED (elder). Object-level spec for arch-C's
coupled re-bake round. worked.tex-anchored (443–457 clear + deeper recoord; 609–627 block blow-up).
The elder rules the OBJECT; arch-C renders the Lean + re-gates. Where a signature is given it is
load-bearing (name = content); where a "principle" is given, arch-C designs the exact clause.

## 1. `N_p` — the object (the def to render)

Per edge at state `s=(S,J)`, chart pivot `p = (a,b) ∈ canonCenterOf s` (flat coord decoding to layer
`S`, row `a`, col `b`), the faithful step map is `stepMap = blockBlowupMap(center, p) ∘ N_p`, with:

- `blockBlowupMap(center, p)` — UNCHANGED (spectator-free; pivot `p` → exceptional `u`, other center
  entries `d_ij → u·w_ij`, spectators pass).
- **`N_p` = pivot-centered Schur reduction (unipotent) + deeper recoordinatization**, two components:
  1. **In-layer Schur at `p`** (layer `S`): `Q₁` clears the pivot COLUMN `b` (row-op:
     `Q₁ = I − ∑_{i≠a}(w_{ib}/w_{ab}) e_i e_a^T`), `Q₂` clears the pivot ROW `a` (col-op:
     `Q₂ = I − ∑_{j≠b}(w_{aj}/w_{ab}) e_b e_j^T`); in the chart `w_{ab}=1`. Result:
     pivot→1, pivot row/col→0, Schur residual `w_ij − w_ib·w_aj` off the pivot cross. **Both unipotent
     (det 1)** — verified all pivots, 2×2/3×3/4×4/2×3 (elder `/tmp/npivot_verify.py`; pnp `npivot_monomialise.py`).
  2. **Deeper recoord** (layer `S+1`): `A_{S+1} → A_{S+1}·Q₁⁻¹`, `Q₁⁻¹ = I + ∑_{i≠a}(w_{ib}) e_i e_a^T`
     (right column-mix; a linear map on layer-(S+1) coords with coefficients `{1, w_{ib}}` from layer `S`).
     This IS Aoyagi's `A'^{(S+1)} = Q_2'^{-1}A^{(S+1)}` (worked.tex:445) read in the Lean product order
     `mult = A_{N-1}···A_0` — transpose-dual (her left-by-col-op-inverse ↔ Lean right-by-row-op-inverse;
     the product order is reversed, so left-neighbor↔right-neighbor and row-op↔col-op — VERIFIED elder).
- **The fan.** `N_p` is a FAMILY parametrized by `p ∈ canonCenterOf`. CORNER pivots (`a=cleared ∨ b=cleared`)
  reduce to `canonShearOf`'s in-layer cross-term `−u_γ·u_β` PLUS the deeper recoord; STRICT-INTERIOR pivots
  (`a,b>cleared`) are the pivot-SHIFTED Schur. `canonShearOf` was the corner instance WITH the recoord dropped.

## 2. Re-authored shear-pin family (the principles; arch-C designs the clauses)

The current family encodes an UNFAITHFUL layer-locality (shear reads+writes only layer `S`). The faithful
shear reads layer `S` (the pivot's row/col) and WRITES layer `S` (interior Schur) AND layer `S+1` (the
deeper recoord). Re-author:

- **`canonShearOf` → `canonNormalizationOf d s p`** — pivot-PARAMETRIC (gains the pivot argument `p`), and
  its displacement now has TWO supports: (i) layer-`S` strict interior (the Schur `−w_ib·w_aj`, pivot-shifted
  to `p`), (ii) layer-`S+1` (the recoord `+w_{ib}·(col-mix)`). The `p`-independence of the OLD def is retired
  (L1⊥L3 was the unfaithful call; L1/L3 COUPLED).
- **`canonShearOf_support` / `CanonicalSchurStep` → the two-support predicate.** No longer "supported on
  layer-`S` interior only." New: the displacement at flat coord `k` is nonzero only if EITHER (i) `k` is
  layer `S`, strict interior relative to `p` (row,col on the pivot side), OR (ii) `k` is layer `S+1` in the
  recoord image (the `Q₁⁻¹` column-mix). Both components explicit; still NEVER writes a bare pivot corner as
  a spectator. This is the write-side content the boost-readiness derivation now consumes.
- **`ShearWithinCarveRaw` clause-(I)** — currently "shear VANISHES on layers ≥ supportLayer(child)=S+1".
  This FORBADE the faithful shear and must be REPLACED: the shear writes layer `S+1` EXACTLY via the
  specified recoord `·Q₁⁻¹` (not arbitrarily). Clause-(I) becomes a POSITIVE pin: "on layer `S+1` the
  displacement equals the `Q₁⁻¹` deeper recoord; on layers > `S+1` it vanishes." (Clauses II/III — pivot-row
  and cleared-pivot — carry as re-parented to the pivot-shifted `p`; arch-C reconciles with `PivotPreservation`.)
- **L1 value-pin** — `IsRealBranch` pins `shearφ = canonShearOf` → `shearφ = canonNormalizationOf d s p`
  (the pivot-parametric N_p at the chart pivot). Re-bake of L1's value-pin.

## 3. The fan pin (IsRealBranch; pnp-fan's cover fix, coupled to the shear)

- Replace the single-pivot pin `(∀ piv, canonPivotOf … = some piv → piv = pivot)` with the MEMBERSHIP pin
  `pivot ∈ canonCenterOf s` — the pivot is a FREE choice within the value-pinned center (pnp-fan cover fix,
  SOUND with a bijective shear for the COVER).
- COUPLED to §2: the chart's shear is `canonNormalizationOf … pivot` — the SAME `pivot`. So each fan chart
  carries `(pivot, pivot-fixing N_p)` as a PAIR. This is what makes every covering chart also monomialise
  (the value leaves) — the coupling pnp-fan proved necessary.

## 4. `foldResid` strict transform (the δ=1 branch gains the recoord)

`foldResid`'s δ=1 arm currently substitutes `blockBlowupCoordQuot pivot ∘ edgeShearRaw(canonShearOf)`. The
faithful arm substitutes `blockBlowupCoordQuot pivot ∘ edgeShearRaw(canonNormalizationOf … pivot)` — i.e.
the deeper recoord is now IN the substitution (the piece that supplies the δ=1 ε-increment, cert §7). The
δ=0 arm and the region machinery are unchanged in shape.

## 5. What is PRESERVED (do not re-open) + the decisive check

- **b-chain / `M_{s,k}`: PRESERVED** (the faithful-vs-composite decider). `N_p` is det-1, so it adds
  NOTHING to the `blockBlowupMap` Jacobian `u^{|center|−1} = u^{M'−1}`; `|canonCenterOf| = M'`
  (`(M(S)−J)(M^{(S+1)}−J)`, worked.tex:626) on every case-2 step of all three witnesses. So Aoyagi's
  exponents + the banked Object-B↔D bridge (`min M_{s,k} = minAdm = cCodim`) are UNCHANGED. **The composite
  fallback is NOT forced.** (Elder-verified det-1 + monomialisation at every pivot through corank-3;
  banked thread-27 Codex on the (3,3,4) coupled peel b-vector + exponent 8.)
- Gap-B homogeneity (`coreGen_/foldResid_layerHomogeneous` over layerCoords): STABLE — the recoord is
  per-layer-(S+1)-linear (§1.2), and `PerLayerDeg1From fromLayer=S+1` excludes the shallower added degree.
  seat-L3T2's atoms survive with the generic `comp_of_linear` step.
- UNTOUCHED: `blockBlowupMap`, Objects A/C/D/E, the Object-B↔D bridge, bLedger/a′, payoff isolation.

## 6. Residuals / cautions for the render
- The `canonNormalizationOf` positive value depends on the pivot's chart (`w_{ab}=1` normalization); the
  `apply_interior`-style value lemma re-authors pivot-parametrically.
- The corank-3 stress (4×4) is elder-verified (all pivots det-1 + monomialise). pnp-transport's offered
  `g-coupled-33322-separated` would be additional coverage; NOT required (the mechanism is corank-blind —
  Gaussian elimination on a nonzero exceptional pivot — verified through corank-3).
- Sequence: this re-bake is the prerequisite beneath boostReady/ChainNF transport+boundary; the Gap-B
  atoms (canonFlatten pin) + hparent rider + cover salvage (b) can proceed in parallel per prior rulings.
