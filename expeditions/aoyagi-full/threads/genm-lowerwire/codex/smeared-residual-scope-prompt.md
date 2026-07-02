<task>
Lean 4 / Mathlib formalisation scope assessment (NOT a code task). I need you to classify a residual as
BOUNDED (a mechanical/finite build with a clear route) vs WALLED (needs genuinely new math/design), and
name the precise remaining gap, from the facts below. Do not write code.

SETTING. An RLCT lower-bound "achiever box-divergence" for deep linear networks, over width vectors
`M : Fin (L+1) → ℕ`, dispatched by a spine over a trichotomy: INTERIOR / BOUNDARY-CLEAN / BOUNDARY-SMEARED.
I just wired the INTERIOR branch at general L (the `0 < deepRank` sub-stratum) from a landed general-L
LIVE-leaf chart atom. The question is the SMEARED branch's general-L status.

WHAT IS BANKED (sorry-free, verified by reading the files):
- The SMEARED assembly is fully M-agnostic: `routeMCore_box_diverges_of_smearedChart` derives box-divergence
  from a `SmearedAchieverChart M` bundle (any L), and `hSmeared_of_smearedChart` reduces the spine's
  `hSmeared` slot ∀M to "construct one chart-builder `BoundarySmeared M → SmearedAchieverChart M`".
- The chart factors `φ = ψ ∘ R`: `ψ` a measure-preserving rational shear ∘ reshape (`shearMBody`, proven
  measure-preserving + measurable embedding at GENERIC width `N`), `R` a polynomial radial blow-up (the sole
  Jacobian carrier `|det D| = |u p|^h`). The `SmearedChartData` per-ε bundle needs: field-A containment, the
  radial fderiv/injOn/det, the PEELED RATE `routeMCore M (ψ(R(insertNth p z y))) = z²·Uy y`, and `Uy > 0`.
- At L=2 the SMEARED branch is CLOSED OUTRIGHT: `smeared_deepRank_eq_M0` proves the L=2 smeared regime is
  ALWAYS the SQUARE stratum (`deepRank M = M 0`, `r+s = M 1`, `s>0`), and `smearedChart_of_square` builds a
  total `BoundarySmeared M → SmearedAchieverChart M` on it (`M : Fin 3 → ℕ`), fed by the fully-unconditional
  square box-divergence `routeMCore_smearedL2_square_uncond`.
- The DECODE + rate machinery (`RouteMSmearedDecodeL2`, `RouteMSmearedSquareL2`, `RouteMSmearedChartL2`,
  `RouteMSmearedChartOpaque`) is all pinned to `Fin 3` (L=2), "the L=2 slice of the general smeared result",
  generalizing the worked `(2,3,1)` to opaque L=2 widths.
- `scalarGram_cancel_of_rankOneColumns` is banked (general linear algebra): for a rank-one-columns front
  product `P`, the scalar-Gram routing `Λ₀` satisfies `P₁·Λ₀ = P₂` off the pole — the docstring says this is
  the generic version of the per-M cancellation the flat-coordinate ∀M smeared rate will consume,
  "specialized to `P = frontProd M` via the front-bottleneck rank-one fact (a SEPARATE, still-to-build
  bridge)".

WHAT IS NOT BUILT (verified by grep over the whole codebase):
- `frontProd M` (the general-L front product feeding the shear) is NOT defined — only named in prose.
- `RectVarahChain` (the general-L rectangular chain wiring) does NOT appear anywhere.
- There is NO general-L `smearedChart_of_square` / `SmearedAchieverChart`-builder; only the `Fin 3` one.
- The general-L smeared chart does NOT reuse the general-L chain substrate the INTERIOR work uses
  (`RouteMGenChain`/`Cgen`/`Agen`/the staircase-conjugated det) — no such import in any smeared file.

MY DRAFT ASSESSMENT (challenge it): the general-L SMEARED residual is WALLED-leaning-BOUNDED. The
assembly + the measure-preserving shear + the scalar-Gram cancellation are width-generic (BOUNDED substrate),
but the specific general-L PEELED RATE needs (a) a `frontProd M` definition, (b) the front-bottleneck
rank-one bridge `frontProd M has rank-one columns` to invoke `scalarGram_cancel_of_rankOneColumns`, and (c)
the general-L decode of `routeMCore M (ψ(R ·))` into `z²·Uy` — currently only at L=2. The L=2 SQUARE collapse
(`smeared_deepRank_eq_M0`) does NOT hold at L≥3 (there the smeared regime need not be square), so the L=2
closer is not liftable; a genuine general-L rate build is required. That is DESIGN-then-build, not a
mechanical tide.

QUESTIONS:
1. Is my WALLED-leaning-BOUNDED classification right, or is it cleanly BOUNDED (a finite mechanical build)
   or cleanly WALLED (new math)? Give the single most load-bearing reason.
2. Does the general-L INTERIOR chain substrate (Cgen/Agen staircase-conjugated det) plausibly make the
   smeared `frontProd M` + rate REACHABLE (shared substrate), or is the smeared rate a fundamentally
   different construction (rational shear + rank-one Gram, not the interior staircase)? 
3. Name the PRECISE remaining gap in one sentence, in the form the controller commissions next.
</task>

<output_contract>
3 numbered sections. Section 1: one-word class (BOUNDED / WALLED / BOUNDED-WITH-DESIGN) + <=5 lines.
Section 2: verdict (SHARED-SUBSTRATE / DIFFERENT-CONSTRUCTION / UNCERTAIN) + <=5 lines. Section 3: a single
sentence naming the gap. Flag inference vs. fact.
</output_contract>

<grounding_rules>
You do not have the repo; reason only from the facts I gave. Mark anything you infer beyond them as an
assumption. If you cannot classify without a fact I did not give, say which fact.
</grounding_rules>
