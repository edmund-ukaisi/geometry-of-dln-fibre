# Re-architecture blueprint — the matrix-ideal Schur-clearing route (L3/L4/L5 swap)

**Status: DESIGN DELIVERABLE (reversible half). Nothing executes** — no render, no seat move, no charter
edit landing, no retirement — **until the operator's explicit go.** Controller gates this statement-delta
before any render. Elder-authored (blueprint); controller commits. Gates green: math cert
(`corank2-cert/certificate.md` + `cert_334_corank2.py`, controller re-ran exit 0), the corank-2 Lean
prototype (controller fidelity-read: non-vacuous, RegionRepresents elementary, RED absent, ~5-cycle bounded
tax), and the elder RE-ARCHITECT ruling (compass "THE PIVOTAL FORK — RESOLVED").

The swap is LOCALIZED: replace L3/L4/L5's `FoldStepInvAt` coordinate-substitution proof of the per-chart
ideal-identity certificate with the paper's per-step unimodular Schur-clearing proof of the SAME certificate.
The `Chart`/`Resolution` framework and the value engine are UNCHANGED.

---

## §1 THE NEW L3/L4/L5 SPEC (statement-delta — the load-bearing piece)

**Design principle (the whole point): state FOR THE OBJECT, not a coordinate-support predicate.** The
carried datum is the IDEAL IDENTITY `⟨(∏C)∘g⟩ = ⟨diag b⟩` (both ways, polynomial cofactors) — Aoyagi's own
Cases-1&2 / Lemma-2 object — never a degree-1 support set. Worked template: `corank2-cert/certificate.md`
items [QP]/[D]/[I⇒]/[I⇐]; Lean shape: `Corank2Proto.lean` (branch -PROTO).

### N1 `chartStep_idealIdentity` — the per-step unimodular Schur-clearing (SUPERSEDES L4 `case1_preserves_stepInv` @ MonumentAtlas:1513 AND L3 `case2_preserves_stepInv` @ :1473)
Signature shape (per a real-branch chart step `p → p.extend ed`, on the fixed ambient):
```
theorem chartStep_idealIdentity (d) (e) (p : TreePath d) (ed : TreeEdge d p)
    (hbranch : (p.extend ed).IsRealBranch e) :
  ∃ (Q₁ Q₂ : Matrix … ℝ),   -- unipotent, POLYNOMIAL entries + polynomial inverses (det = 1)
    (Q₁ * A_step * Q₂ = Matrix.fromBlocks 1 0 0 Δ) ∧          -- [QP]: pivot ≡ 1, coupling in the residual Δ
    ⟨entries (A_step)⟩ = ⟨entries (Matrix.fromBlocks 1 0 0 Δ)⟩ -- [I⇒]/[I⇐]: both-ways, cofactors = Q₁/Q₁⁻¹ entries
```
- Content = the cert's [QP]+[I⇒]+[I⇐]: `Q₁·A·Q₂ = diag(1,Δ)`, `Δ = C₂₂ − C₂₁·C₁₂` (the coupled Schur
  complement); forward `A = Q₁⁻¹·peeled` and backward `peeled = Q₁·A` give `⟨A⟩=⟨peeled⟩` with EXPLICIT
  POLYNOMIAL cofactors (the `Q₁`/`Q₁⁻¹` entries). The cross-term `F₃F₂ ∈ ⟨F₂,F₃⟩` drops in one line
  (product of generators). **NO divide-by-pivot, NO degree-1 tracking, NO support predicate.**
- **corank≥2 is the SAME statement** — clearing J pivots one at a time, each an identical
  ideal-preserving step; the coupling accumulates in `Δ`. There is NO special corank≥2 lemma (the WALL's
  reason to exist evaporates).
- ONE unified case: case11/case12/case2 are the SAME per-step Schur-clearing (the four-case split was a
  coordinate-substitution artifact). The controller's `chartStep_idealIdentity` may keep a thin case-guard
  only where the block geometry (which rows/cols) genuinely differs; the IDEAL-IDENTITY proof is uniform.

### N2 `leafChart_idealIdentity` — the path-fold (SUPERSEDES L5 `leaf_stepInv_of_path` @ MonumentAtlas:1753)
Path induction folding N1 along the tree: `⟨(∏C)∘gmap⟩ = ⟨diag b⟩` at each leaf, with the accumulated
divisibility chain `b₁|b₂|…|b_M` ([D]: `b = (E, E·α·v, …)`) and the join Jacobian `|det Dg| = monomial·unit`
(unit nonvanishing on the nbhd — [D]'s `unit(0)=1`). Output = the per-chart `PrincipalInv` (the CURRENT L5
output), so the KEPT downstream (L1 → the two `RegionRepresents` → `Chart`) is unchanged.
- The recursion is a clean fold of identical ideal-preserving steps (N1); the residual matrix `Δ`/`D_next`
  shrinks per layer ([ML]) — the ONLY measured cost (see §4).

### The supersession is EXACT at the interface
N2 produces the SAME per-chart `PrincipalInv` that `leaf_stepInv_of_path` produces. So `L1`
(`principalInv_regionRepresents`) → `hideal_fwd`/`hideal_bwd` → `Chart` (LeafChartWire:183-184) →
`exists_atlasRealizesExponents` are UNTOUCHED. The swap is invisible above the per-chart certificate.

---

## §2 SHARED / KEPT (explicit — the swap does NOT touch these)
- The `Chart`/`Resolution` framework (`ProductResolution.lean`): `hideal_fwd`/`hideal_bwd`
  (= `GermRepresents`/`RegionRepresents` both ways, coeffs continuous on nbhd), `hjac`, the cover fields.
- The value engine: Object A (`IdealInvariance.rlctAt_sumSqFam_eq_of_germ_eq`, LANDED) → Object B CoV
  (`two_mul_rlctAt_eq_divisorMin`, route-independent — consumes any `Resolution`) → Object C
  (`MonomialRLCT`, LANDED) → Object D (`divisorMin_eq_cCodim`, LANDED). Ideal-level, sorry-free.
- `buildTree` + `FoldProduced`/`FoldRealizes` provenance; L1 (`principalInv_regionRepresents`); L6
  (`leafPath_chartGeometry`); L7 (`leafPath_compactCover` — the full-fan cover + σ-transport, elder L7
  ruling stands); L8 (`leafPath_realizesExponents`).
- The destination/definition-of-done: `via_engine`'s payoff (§9.4/F7). UNCHANGED — this is an
  adapt-the-ladder re-scope of the CONSTRUCTION only, not the objective.

---

## §3 RETIRE (explicit list — QUARANTINE TARGETS, NO ACTION until operator-go; mark SUPERSEDED not REFUTED)
The following are the divide-by-pivot / coordinate-support-tracking apparatus, obviated by N1/N2:
`FoldStepInvAt`; `case1_preserves_stepInv` (THE WALL); `case2_preserves_stepInv`; `leaf_stepInv_of_path`;
`couplingClear`/`couplingCoords`; `sourceClearedResid` + the KILL (`sourceClearedResid_ignoresEscapedBelow`);
the #95 row-phantom machinery; the #98 growth-arm descent; degree-1 exactness (`Deg1SupportedOn`/`Slot`);
`CanonicalPivots`; the cap frontier (`sourceClearedResid_capped`, CapDescent).
- **SUPERSEDED, not REFUTED (binding on the retirement commit):** the coordinate invariant was TRUE where
  it held; it is the ENCODING that was the drift. Retirement banners say "superseded by the matrix-ideal
  Schur-clearing route (N1/N2); a construction the paper's route obviates," NOT "false." This keeps the
  record honest about why ~260 commits of real (if mis-encoded) work is set aside.
- The #82/#84/#85/#87/#95/#9.x arc (couplingCoords keying, canonical-pin, phantoms, the pivot-pin) all
  retire WITH `FoldStepInvAt` — they were adjudications WITHIN the superseded encoding. The compass F-forks
  and §9 rulings stay as HISTORY (marked superseded-with-the-encoding), not deleted.

---

## §4 THE ONE MEASURED RISK — the [ML] cast-tax (prototype-measured, not asserted)
The load-bearing products (`peeled = diag(1,Δ)·(Q₂⁻¹·C₂)`, `D_next·C^(S+1)`) are `Matrix.mul` on blocks whose
widths CHANGE per (S,J) (dependent-dim / opaque-width). Mitigation (baked into the cert contract): keep `g`
fixed-ambient; carry ONLY the residual block as the dependent-dim matrix; use fully-applied
`Matrix.mul_assoc` terms (the `mul_three_reassoc` idiom), not `rw`/`simp`. The corank-2 prototype MEASURED
this as a ~5-cycle bounded tax (controller fidelity-read: RED absent, RegionRepresents elementary). This is
the ONLY open cost; the math is settled. If the full-`d` path-fold reveals the cast-tax scales badly, the
"lighter IN LEAN" claim reopens — but the prototype + Object-A-is-the-interface make a clean render expected.

---

## §5 PROPOSED charter/compass reframe (DRAFT — inside this doc; NOT edited into charter.md until operator-go)
- **charter §1 Object B:** replace "the blow-up MONOMIALISES ⟨∏C⟩=⟨diag(b)⟩ via the coordinate fold" framing
  with "the per-step unimodular Schur-clearing (Cases 1&2 / Lemma 2) maintains the IDEAL IDENTITY
  ⟨A⟩=⟨diag(1,Δ)⟩ with polynomial cofactors; the coupling lives in the residual matrix; corank≥2 is the
  same step iterated. The exceptional monomials accumulate into diag(b) at the terminal chart." The coupled
  corank≥2 stays NOT-OPTIONAL, but is now the SAME step, not a special object.
- **charter §3 (standing math-warnings):** RETIRE the geometric-substitution-drift warnings (the divide-by-
  pivot / degree-1 / support-tracking class) — mark them "superseded: the encoding they guarded is retired."
  ADD one warning: "the ideal identity is stated FOR THE OBJECT (⟨A⟩=⟨diag⟩, polynomial cofactors); never
  re-introduce a coordinate-support predicate — that was the drift." KEEP the `canonCenterOf`-full-block
  tripwire only as HISTORY (its object retires).
- **compass:** "THE PIVOTAL FORK — RESOLVED" is recorded; add the objects-A-E frame note (the value engine
  is done; the sole construction = N1/N2). The F1/F2 forks are VINDICATED (the ideal-level route they
  adopted is now the implementation, not just the fork).

---

## §6 Render order (for after operator-go — NOT part of this design deliverable)
1. Controller gates this statement-delta (N1/N2 signatures + supersession map).
2. Render N1 (`chartStep_idealIdentity`) on the fixed ambient, corank-2 first (the prototype is the seed),
   then general block geometry. 3. Render N2 (`leafChart_idealIdentity`) path-fold. 4. Re-point L5's output
   consumer (L1/LeafChartWire) — invisible if N2's output = `PrincipalInv`. 5. Retire §3 (banners +
   quarantine). 6. Charter/compass reframe (§5). 7. Full-build green + `#print axioms` on `via_engine`.

---

## §7 Carried render-gate obligations (blueprint GATED/approved 2026-07-24; both flags green)
Controller approved the statement-delta; both flagged points green (uniform-N1 as design direction;
SUPERSEDED-not-REFUTED binding). Two obligations carried to the render (de-risking in progress):
1. **N1-uniformity merge-confirm (render-time tripwire).** The case-distinctions are (a) divide-by-pivot
   behavior (substitution artifact — gone) + (b) tree-structure bookkeeping (which pivot; S-increment
   merge/rollover vs J-increment fresh), which lives in N2's FOLD = buildTree provenance (KEPT), NOT in a
   different N1. So N1 is uniform. OBLIGATION: confirm N2's fold correctly sequences the uniform N1 across a
   case11-MERGE/rollover + the terminal (⟨diag b⟩→⟨b₁⟩ principal) on a concrete multi-layer witness —
   pnp-ideal's multilayer.py extended to merge/rollover+terminal (decorrelated, exact, reversible). If the
   merge genuinely differs at the IDEAL level, N1 keeps a thin merge-vs-fresh guard; expected uniform.
2. **Interface output-type match (render refinement).** N1/N2's output type must EXACTLY match what L1
   (`principalInv_regionRepresents`) consumes — the current `PrincipalInv` fields — so the supersession is
   interface-invisible (L1→hideal→Chart untouched). The prototype produced `RegionRepresents` directly; the
   blueprint routes through `PrincipalInv` (the conservative, L1-keeping choice). Verify the `PrincipalInv`
   type/fields match at render (a mismatch = re-point L1's consumer, still local).
Both are RENDER-time (post-operator-go) checks; neither blocks the design. Execution held for operator-go.
