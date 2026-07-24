# Build brief — the geometric atlas (the SOLE residual of the close-out)

**Status: build-prep. The Lean build fires ONLY on the operator's explicit go.** This brief consolidates
the scattered L6/L7 render (`theory/aoyagi-2023-reproduction/ideal-route-full-render.md` §§ L6/L7/obligations
+ SEAM-CHECK + SCOPE CALIBRATION) into one executable spec.

## The one thing to close

`DLNFibre.DLN.Aoyagi.LearningCoefficient.exists_coreResolution:311` — a single `sorry` supplying

    hgeo : ∃ res : Resolution F (0 : Fin D → ℝ), AtlasRealizesExponents d res

instantiated at `D = flatDim d`, `F = coreGen d e`, for the REDUCED core widths `d : Fin (N+1) → ℕ`
(monotone, positive; post-Theorem-3). **Everything else is sorry-free + clean-three, and the payoff cone is
cite-free** (`{propext, sorryAx, Classical.choice, Quot.sound}` — no Aoyagi/Watanabe axiom). Closing :311 ⟹
the charter's cite-free learning-coefficient goal.

## Verified context (do NOT rebuild these — they are DONE, `#print axioms` clean-three)

- **Spine:** L-A (Schur block-elim, any corank), L-B (`b`-chain maintenance), Theorem 4 — rendered + matches source.
- **Combinatorial value (BOTH bounds):** `Engine.o5_core_realized` (∃ leaf, `divExp = minAdm d` = `hattain`),
  `tStar_realized` (Clearable ⟹ realized), `clearable_of_minimizer`, and `minAdm_le_terminalExponents`
  (`hlb`) — all clean-three. Cross-checked by the thread-12 battery (B1–B6: reachable = Clearable; minimizer
  ⟹ realized; strand is chooser-independent).
- **Adapter wiring:** `RecursionAdapter.hlb_hattain_of_atlasRealizesExponents` (sorry-free) turns
  `AtlasRealizesExponents d res` into `hlb ∧ hattain` against `qipMin d`. The seam binds on the SAME
  `buildTree d (conOracle d) conRoot` o5 produces its leaf in (verified: adapter :96-97).

## The target: `AtlasRealizesExponents d res` (RecursionAdapter:55)

A match of ℕ-valued exponent VALUE-supports (NOT a structural chart↔leaf correspondence):
- **`hmem`:** `∀ chart c, ∀ binding axis a, (jac a + 1) ∈ terminalExponents (buildTree d (conOracle d) conRoot)`.
- **`hrealize`:** `∀ leaf l, ∀ k, l.divExp k = minAdm d → ∃ chart c, ∃ axis a, (jac a + 1) = l.divExp k`.

Both follow once each chart's binding-axis exponents ARE the tree's terminal divisor exponents `M_{s,k} =
Mval(t)` (Object C, general-`L`, done). So the geometric charts must carry those exponents.

## What the build must inhabit — a real `Resolution res`

Per chart `c` (a `Chart` record, `Core/Aoyagi/ProductResolution.lean`):
- `g_c` — analytic map; `hg_analytic`. **[L6]** `g_c = ∘_j (β_j ∘ σ_j)` along the buildTree branch: `β_j` the
  blow-up chart maps, `σ_j` the `Q`-induced ambient relabels (unipotent-polynomial, one 1×1 pivot per step).
- `hg_inj` / `hexcep_null` — a.e.-injectivity off the (null) exceptional. **[L6]** `β_j` injective off its
  exceptional divisor; `σ_j` a bijection.
- `hjac` — DOM-WIDE `|det Dg_c| = jacWeight jac_c · unit`, `unit` nonvanishing on ALL of `nbhd`. **[L6,
  rendered EXACT]** `det Dσ_j ≡ 1` exactly (unipotent `Q`, block-triangular `[[I,0],[∂c'/∂u, Q⁻¹]]`);
  `det Dβ_j` = exact blow-up monomial; composite = exact monomial, so `unit ≡ 1` identically (germ-only trap
  structurally void).
- `hideal` — `⟨F∘g_c⟩ = ⟨diag b⟩` (rides L-A/L-B, the verified spine).
- `bexp`/`jac`/`k₀` — the exponent ledgers; `jac a + 1 = M_{s,k} = Mval(t)` on binding axes (the value-match).

Atlas-level:
- `hcover` — measure-zero cover `volume(U \ ⋃_c g_c'' dom_c) = 0`, `dom_c` compact. **[L7 — THE UN-PROBED
  PIECE]** Reduce to the kept `-L7cover` engine `LeafCoverTiling` (646bcdcdb, sorry-free on-branch;
  box-inflation fan) via two obligations:
  - **obligation-1 (per-edge box-containment):** `closedBall 0 R ⊆ σ_edge '' closedBall 0 (f R)`, `f = r +
    C·r²`, `C ~ widths`. One-pivot-per-step ⟹ each shear is degree-2 PER-EDGE (composite degree grows but
    the engine iterates per-edge; `f^[depth]` finite at finite depth).
  - **obligation-2 (fan-completeness):** the `m` affine charts of each blow-up's `ℙ^{m-1}` cover it + Cases
    exhaustive (KC-2) + pnp-fan transfer.

## rev-render's audit gates (the eventual decorrelated L6/L7 audit will attack exactly here)

1. Does the **L6** construction inhabit ALL `Chart` fields — esp. dom-wide `hjac` — for the COUPLED leaves,
   general-`d`?
2. Does **L7's `hcover`** hold for the COUPLED fan at corank≥2 (obligation-1 per-edge box-containment
   composed general-`d` + obligation-2 fan-completeness)? **This is the piece the audits left genuinely
   UN-PROBED at corank≥2 — the highest residual risk.**

## Reuse

- `-L7cover` `LeafCoverTiling` (646bcdcdb) — the abstract box-inflation cover engine; sorry-free on-branch;
  merge into trunk during the build.
- `-PROTO` `Corank2Proto.lean` (05c35eb8a) — the corank-2 cast-tax Lean shape (reference).
- The salvaged Engine (`o5_core_realized` &c.) — for the exponent (`M_{s,k} = Mval`) side of the value-match.
- Cast discipline: keep ideal-level (germ family, `finCongr`-only casts, never `Matrix.mul`).

## Scope honesty (do NOT understate)

The residual SIZE = **value-match (shrunk by the ℕ-value-match bonus) + real charts (L6, rendered exact) +
real cover (L7 coupled `hcover`, UN-PROBED at corank≥2)**. The bonus lightens only the COMBINATORIAL
matching; the GEOMETRIC burden (charts + cover) is unchanged. This is the genuine standard-geometry build,
with L7's coupled `hcover` the un-probed, highest-risk part — NOT "small."

## First build unit (go/no-go, when the operator authorizes)

The corank-2 ideal-level chart (using `-PROTO`'s shape): build ONE coupled leaf's `Chart` (g + dom-wide
`hjac` = monomial·1) at corank-2, then its `hcover` contribution via the `-L7cover` engine. If the dom-wide
`hjac` and the per-edge box-containment inhabit cleanly at corank-2, the general-`d` build is the same step
iterated; if `hcover` at corank-2 fights, that is the un-probed risk materialising — STOP + report.

## CORANK-2 FIRST UNIT — RESULT: MECHANISM GO (builder geo-atlas-c2 + rev-render audit, 2026-07-24)

`Corank2GeoAtlas.lean` (origin/expedition/aoyagi-engine-geo-c2, 1c4e33f71). Builder reports GO, clean-three;
rev-render decorrelated audit (+ Codex) CONFIRMS the two mechanisms are GENUINE but scopes it precisely:

- **The two hardest geometric MECHANISMS are de-risked (genuine, general sorry-free primitives):**
  `coShear_covers` (coupled per-edge box-containment, `closedBall r ⊆ coShear '' closedBall (r+r²)`, the
  genuine 4-term rank-1 Schur shear on Fin 8) and `coG_hjac` (dom-wide `|jacDet| = u_p^{|S|-1}·1`, unit ≡ 1
  identically). Built on `PathAtoms` (`jacDet_blockShear = 1`, general φ), `BlockBlowup`
  (`jacDet_blockBlowupMap`), `LeafCoverTiling` (`covers_subset`) — all sorry-free + general in `Fin D`/φ/S/p.
  **This retires the "un-probed at corank≥2" hcover flag for the MECHANISMS.**
- **C=1 (not corank·widths) is correct but rank-1 is LOAD-BEARING:** rests on (a) source/target separation
  (φ reads {0..3}, writes {4..7} ⟹ inverse exactly quadratic), (b) rank-1 (ONE product per corrected
  coord), (c) norm (holds in sup AND ℓ²). A rank-`q` step gives `r + q·r²` — so C=1 REQUIRES genuine
  one-pivot-per-step at every node.
- **NOT general-`d` — MECHANISM GO only (the builder's "stand-in" caveat is load-bearing).** `covers_coTree`
  proves `Covers f coTree 1` for ONE hardcoded depth-2 tree reusing the SAME shear/center at both levels.
  It does NOT establish `∀d, Covers f (buildTree d) 1`. The general-`d` hcover assembly (= the actual
  `exists_atlasRealizesExponents` build) still needs: (1) a parameterized local-cover lemma for every block
  size + pivot type; (2) the real `buildTree d` ↔ `FanTree` node correspondence; (3) instantiation with
  VARYING shears / shrinking blocks / actual centers; (4) fan-completeness over the real centers (no omitted
  strata); (5) radius bookkeeping where recentering alters constants; (6) engine-leaf ↔ atlas-chart. It is
  bounded-buildable (general primitives + the same argument), NOT a new monument — but it is NOT done.
- **NEW sub-point to NAIL for general-`d` — CENTERS.** The stand-in is origin-centered. At a NONZERO center
  the Schur update gains LINEAR terms (`a·δbᵀ + δa·bᵀ + δa·δbᵀ`) → center-dependent constants that can break
  the clean `r+r²` recurrence. Safe IFF every blow-up+shear is at its CHART origin (each blow-up at the chart
  origin ⟹ the residual is origin-expanded ⟹ safe). Controller read: Aoyagi's construction IS chart-origin
  centered (each blow-up is at the vanishing locus = the chart origin; the box-inflation fan covers by
  radius inflation, not recentering) — so likely SAFE, but the origin-centered stand-in gives NO evidence;
  CONFIRM in the general-`d` build that no fan chart needs a nonzero center.

**Net:** corank-2 GO = the two hardest MECHANISMS proven genuine on general primitives (a real de-risk of the
prior highest-risk flag). The general-`d` hcover ASSEMBLY (items 1–6 + CENTERS) + `hideal` + the
Resolution/AtlasRealizesExponents wiring remain — the actual `exists_coreResolution:311` build. Do NOT round
"corank-2 GO" up to "L7 done". Controller `#print axioms` gate on the module pending (confirm §6
`#assert_banked_clean_batch` GREEN, not stale-olean).
