<task>
Lean 4 + Mathlib formalisation. I am building the BOUNDARY-SMEARED rational achiever chart φ_sm into the
EXISTING `NodeAchieverChart M` structure (option (a), least-disruptive). The controller's plan was: the
ONLY pole-affected field is `cov`, dischargeable via a split (c-o-v on s\N0 + image-null of φ_sm''(s∩N0)).
While building the validate-small M=(1,2,1), I found a SECOND pole-affected field that may break option (a).
I need a sharp yes/no on whether option (a) survives, or whether the assembly/structure must change.

THE STRUCTURE (cannot change for one instance; `routeMCore_box_diverges_of_nodeChart` consumes it):
  structure NodeAchieverChart (M) where
    phi : (Fin N → ℝ) → (Fin N → ℝ)
    p   : Fin N                       -- binding pivot axis (the z-axis)
    leafH : Fin N → ℕ                 -- Jacobian exponents
    Ufun : (Fin N → ℝ) → ℝ
    leaf_integrand : ∀ (c : ℝ) (u : Fin N → ℝ),     -- NOTE: ∀ u, POINTWISE
        (∏ j, |u j|^{leafH j}) * |routeMCore M (phi u)|^{-c}
          = monomialIntegrand N (nodeLeafK N p) leafH c u * (Ufun u)^{-c}
    cov : ∀ V, MeasurableSet V → ∀ g,
        ∫⁻ x in phi '' (V\{x|x p=0}), g x
          = ∫⁻ u in V\{x|x p=0}, ofReal(∏|u j|^{leafH j}) * g (phi u)
    -- (+ Ubound, Umeas, image_subset, hpos, leafH_pivot)

The M-agnostic assembly `routeMCore_box_diverges_of_nodeChart` uses `leaf_integrand` via
`setLIntegral_congr_fun hPmeas (fun u _ => ... rw [W.leaf_integrand])` — i.e. it rewrites the integrand
POINTWISE on ALL of the box P = [0,δ]^N. monomialIntegrand here encodes the loss base |u_p|²: the
leaf_integrand identity is effectively asserting `|routeMCore M (phi u)| = |u_p|² · Ufun u`^... i.e.
the RATE `F∘φ = u_p² · U` POINTWISE on all u.

THE SMEARED CHART (M=(1,2,1), validated): coords (a,b,z,sb), φ_sm = paramsEquivFlat ∘ chartParams where
A⁰=[a,b], A¹=[z − (b/a)·sb ; sb]. Pivot p = z-axis. Rate: F∘φ = ‖A⁰A¹‖² = (a·z − b·sb + b·sb)² = a²z²
= z²·U with U = a². BUT in Lean, division-by-zero is 0, so at the pole N0 = {a=0}: (b/a)=b·0⁻¹=0, so
A¹ top = z, and A⁰A¹ = 0·z + b·sb = b·sb ≠ 0. So F∘φ(a=0) = (b·sb)², while z²·U = z²·a² = 0. The rate
F∘φ = z²·U holds ONLY off N0={a=0}.

So `leaf_integrand` (∀u) FAILS at N0: LHS |z|⁰·|(b·sb)²|^{-c} vs RHS monomialIntegrand·(a²)^{-c} =
|z|⁰·|z²|^{-c}·0^{-c} (0^{-c}=0 for c>0) — mismatch. I verified there is NO extension of φ_sm at a=0
making F∘φ = z²a²: at a=0, A⁰A¹ = b·(A¹ bottom) and A¹ bottom = sb is a FREE diffeo coord, so it cannot
be forced to 0 without destroying the diffeo.

THE QUESTIONS:
1. Confirm: the rational φ_sm CANNOT satisfy the EXISTING `leaf_integrand` field (∀u, pointwise),
   because the rate F∘φ=z²U holds only off the null N0={a=0} and no diffeo-preserving extension fixes
   it at a=0. YES/NO + the precise reason if I'm wrong.
2. Given (1), option (a) as framed ("only cov is pole-affected, fits the existing structure verbatim")
   is INCOMPLETE — `leaf_integrand` is also pole-affected. Rank the fixes by Lean cost / disruption:
   (i) WEAKEN leaf_integrand to an a.e. statement (`∀ᵐ u`) AND change the assembly's
       `setLIntegral_congr_fun` to an a.e. `setLIntegral_congr` dropping the null {a=0} (= editing the
       banked M-agnostic core `routeMCore_box_diverges_of_nodeChart` + the structure field type);
   (ii) keep the structure, but have the SMEARED instance's `leaf_integrand` field carry a DIFFERENT
        Ufun that makes the identity hold ∀u (is there a Ufun' with |F∘φ|=|u_p|²·Ufun' pointwise? F∘φ
        is a genuine function of u — set Ufun'(u) := |F∘φ(u)|/|u_p|² where u_p≠0, else anything; but
        then Ufun' is NOT z-free / not the polynomial a², and Ubound's a.e.-positivity + boundedness
        must still hold — assess whether Ufun' := |routeMCore(phi u)|/(u_p)² (off {u_p=0}) is a legal
        Ufun: bounded on the box? a.e.-positive? measurable? It equals a² off N0, so a.e. it IS a²);
   (iii) a NEW structure NodeAchieverChartAE with a.e. leaf_integrand + a.e./split cov + a matching
        a.e. assembly (most disruptive, but the cleanest home for ALL rational charts).
3. Assess (ii) precisely: define `Ufun_sm u := |routeMCore M121 (phi121sm u)| / (u 2)²` (the z-axis is
   u 2). Off {z=0} this is a genuine function; off N0 it equals a²; on N0 (but z≠0) it equals
   (b·sb)²/z². Does this make `leaf_integrand` hold ∀u with {z=0} the only excluded set (which IS the
   removed pivot locus)? I.e. is leaf_integrand really only needed off {u_p=0}? RE-READ: the assembly
   rewrites on ALL of P=[0,δ]^N (including u_p=0 points). But at u_p=z=0, monomialIntegrand has
   |z|²^{-c}=0^{-c}=⊤·... actually |u_p|^{leafH}=|z|⁰=1 and the loss base |z|²^{-c}; hmm. Does the
   leaf_integrand identity AT z=0 hold trivially (both sides blow up / are defined via rpow conventions)?
   If leaf_integrand at u_p=0 holds for ANY Ufun (because both sides degenerate identically), then
   option (ii) with Ufun_sm = |F∘φ|/z² (which = a² a.e., is bounded a.e.-positive measurable) might
   satisfy leaf_integrand ∀u WITHOUT touching the assembly. Assess whether F∘φ = z²·Ufun_sm holds ∀u
   BY DEFINITION of Ufun_sm (it does, off z=0, by construction; at z=0 both sides are 0 since F∘φ(z=0)
   = ‖a·0... ‖, wait F∘φ at z=0: A⁰A¹ = a·(0 − (b/a)sb)+b·sb = -b·sb+b·sb = 0 off N0, = b·sb on N0).
   Carefully determine F∘φ at z=0 and whether Ufun_sm := F∘φ/z² gives a CLEAN ∀u identity F∘φ=z²·Ufun_sm
   (z²·(F∘φ/z²) = F∘φ for z≠0; at z=0 both 0?). Does this dodge the whole problem at the cost of Ufun
   being a ratio (still measurable, bounded a.e., positive a.e.)?
</task>

<output_contract>
Answer Q1 (yes/no + reason), Q2 (rank the 3 fixes, pick cheapest sound), Q3 (the Ufun_sm=F∘φ/z² dodge:
does it make leaf_integrand hold ∀u without touching the assembly? yes/no + the precise blocking fact
if no — especially whether Ufun_sm is a legal Ufun: bounded-on-box, a.e.-positive, measurable). End with
"VERDICT:" — either "option (a) survives via <fix>, no assembly change" or "GAP: assembly/structure must
change because <reason>". Flag inference vs Mathlib-fact. ≤ 8 sentences per question.
</output_contract>

<grounding_rules>
Be precise about rpow conventions at 0 in ℝ≥0∞/ℝ (x^{-c} for x=0, c>0). Distinguish Mathlib facts from
inference. The load-bearing uncertainty is Q3: whether Ufun_sm := |routeMCore(phi u)|/(u_p)² is a legal
NodeAchieverChart.Ufun (a.e.-positive + bounded-on-box + measurable) AND makes leaf_integrand hold ∀u.
