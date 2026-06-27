<task>
I am formalising (Lean 4 + Mathlib) the per-node RLCT (real log-canonical threshold) MIN fact for deep
linear networks, generalizing a (2,2,2) construction to general matrix shapes. I have hit a precise
architectural question and need a decorrelated soundness judgement.

SETUP. Fix a 2-layer DLN node: A is m×k (the deepest pivot layer), B is k×n. The "true loss" at the
deepest (all-zero) point is F(A,B) = ‖A·B‖²_Frobenius, a polynomial on the flat ambient
ℝ^N, N = mk + kn. We want rlctAtOn F at the origin.

The RLCT here is the "weighted threshold":
  weightedThreshold G ρ {w*} := sSup { c' ≥ 0 : |G|^{−c'}·ρ is locally integrable on some open Ω ∋ w* }.
rlctAtOn F w* = weightedThreshold F (ρ≡1) {w*}.

THE PROVED TRANSPORT LEMMA I HAVE (call it TRANSPORT_AUX). For a self-map π : M → M of a
finite-dimensional real normed space M with additive-Haar volume, with a null measurable set E s.t.
  - π is proper,
  - π is injective off E (InjOn π Eᶜ),
  - π is differentiable off E with derivative Dπ (HasFDerivAt off E),
  - π is SURJECTIVE (Function.Surjective π),
  - volume (π '' E) = 0   (Luzin-N),
THEN  weightedThreshold F φ {w*} = weightedThreshold (F∘π) (fun m ↦ φ(π m)·|det Dπ m|) (π⁻¹{w*}).

THE PROVED OUTER PRODUCT-MIN LEMMA I HAVE. For G(y₀,z) = y₀²·K(z) on ℝ × Z, with weight |y₀|^e
(e = mk−1) on the y₀-factor only and K ≠ 0 a.e.:
  weightedThreshold (y₀²·K(z)) (|y₀|^e) {(0,0)} = min( (e+1)/2 , rlctAtOn K 0 ).
(So with e=mk−1 the y₀-side is mk/2.)

THE PLAN (from a pen-and-paper cert). Define the single-pivot blow-up
  φ₁ : (y₀, u, v, W, B) ↦ (A, B),   A = y₀·Â,   Â = [[1, uᵀ],[v, W]]  (Â top-left entry = 1),
so F∘φ₁ = y₀²·core, core = ‖Â·B‖², and |det Dφ₁| = |y₀|^{mk−1}. Then:
  rlctAtOn F 0 = weightedThreshold F 1 {0}
              =[TRANSPORT_AUX, π=φ₁] weightedThreshold (F∘φ₁) (|det Dφ₁|) (φ₁⁻¹{0})
              = weightedThreshold (y₀²·core) (|y₀|^{mk−1}) {0}
              =[OUTER PRODUCT-MIN] min( mk/2 , rlctAtOn core 0 ).
Then an inner squeeze gives rlctAtOn core 0 = n/2 + rlctOf(child).

THE OBSTRUCTION I FOUND. The single-pivot blow-up φ₁ is NOT SURJECTIVE as a self-map of ℝ^N.
Its image of the A-block is {A : A₀₀ ≠ 0} ∪ {A = 0} (set y₀=A₀₀, Â=A/A₀₀ when A₀₀≠0; y₀=0 ⟹ A=0).
It MISSES {A : A₀₀ = 0, A ≠ 0}, a positive-measure set. So TRANSPORT_AUX's `Function.Surjective π`
hypothesis FAILS. (The standard fix is an argmax cover: one pivot chart per matrix entry (i,j) covering
{A ≠ 0}, glued by a cover lemma; Mathlib has no bundled argmax-cover.)

THE QUESTIONS (rank-ordered, give the single cheapest sound route):

1. Is there a SOUND way to get rlctAtOn F 0 = min(mk/2, rlctAtOn core 0) using a SINGLE chart (not a
   full cover), given the non-surjectivity? Specifically: the RLCT is a LOCAL quantity at the origin.
   The blow-up image {A₀₀≠0}∪{A=0} — does it contain a neighborhood-germ adequate for the threshold?
   NO: the missing set {A₀₀=0,A≠0} accumulates at the origin (e.g. A = (0,0;t,0)→0). So a single
   pivot chart genuinely cannot see the loss germ on the missing stratum. Confirm or refute that a
   single chart is INSUFFICIENT and a cover is mathematically required for the EQUALITY (both ≤ and ≥).

2. Granting a cover is needed: for the MIN fact specifically, do we actually need the full equality, or
   does the structure of `weightedThreshold` give the cover-min "for free"? I.e., is there a lemma shape
   "weightedThreshold over a finite cover = min/inf over charts of the per-chart weighted thresholds"
   analogous to the g5_flat_cover lintegral-additivity, that would let me compute rlctAtOn F 0 as
   min over the mk pivot charts of (per-chart weighted threshold)? Each pivot-(i,j) chart gives the
   SAME min(mk/2, rlctAtOn core 0) by symmetry (row/col permutation), so the cover-min collapses to one
   value. Is "RLCT = inf over a finite cover of per-piece thresholds" SOUND in general, and what is the
   minimal Lean lemma (integrability on a union ⟺ integrability on each piece)?

3. Alternatively: can I AVOID surjectivity by transporting only the ≤ direction (which TRANSPORT_AUX's
   sibling `weightedThreshold_le_transport` gives WITHOUT surjectivity), and getting ≥ by a separate
   argument? The ≤ direction gives rlctAtOn F 0 ≤ min(mk/2, rlctAtOn core 0). For ≥, is there a clean
   lower-bound route (e.g. the loss F restricted to the chart image, or a sub-integrability)? Is the
   one-sided route enough to ESTABLISH the MIN equality, or only a bound?

4. If the honest answer is "the general MIN-fact equality requires the argmax cover machinery (mk
   charts + a cover-additivity lemma + the tie-set null argument), which is substantially more than the
   single proved transport lemma", say so plainly and estimate the Lean surface (which Mathlib pieces:
   the g5_flat_cover is available; what's the gap to a weightedThreshold-cover-min lemma). I need to
   know whether to (a) build the cover, or (b) report this as the genuine remaining geometric long pole
   and hand back the precise sub-obstruction.
</task>

<output_contract>
Four numbered sections matching Q1-Q4. For each: a crisp verdict (SOUND / UNSOUND / INSUFFICIENT) +
the one-line reason. Then a final "ROUTE" section: the single cheapest mathematically-sound path to the
MIN-fact equality, and whether it is single-chart or requires a cover. Be concrete about the minimal
lemma needed. Under 600 words.
</output_contract>

<grounding_rules>
Distinguish what is a theorem (provable) from what is a heuristic. If you claim a single-chart route
works, give the precise reason the non-surjectivity does not break the EQUALITY (both directions). If
you cannot, say the cover is required. Flag any step that is inference vs. established measure theory.
</grounding_rules>
