<task>
Lean 4 + Mathlib v4.29 plumbing. I have a C¹ self-map `f : M → M` of a finite-dim real normed space
(`M`, `[NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M] [CompleteSpace M]`), with
`f wstar = wstar` and `HasFDerivAt f (f' : M →L[ℝ] M) wstar` where `f' : M ≃L[ℝ] M` is a
continuous-linear-equiv (invertible derivative at the fixed point). The implicit-function-theorem
gives me `h := hf.toOpenPartialHomeomorph f hf' (one_ne_zero) : OpenPartialHomeomorph M M` with
`h = f` on its source, `h.open_source`, `wstar ∈ h.source`, `h.symm` continuous, and (via
`to_localInverse`) `h.symm` is `ContDiffAt ℝ 1` at `f wstar = wstar`.

I must FEED a downstream lemma that requires a SINGLE open set `V` with `wstar ∈ V` and:
  (hmaps)     ∀ w ∈ V, f w ∈ V            -- f maps V into V
  (hsymmmaps) ∀ w ∈ V, h.symm w ∈ V       -- the local inverse maps V into V
  (hleft)     ∀ w ∈ V, h.symm (f w) = w   -- inverse on V
  (hright)    ∀ w ∈ V, f (h.symm w) = w   -- inverse on V
  (hπcont)    ContinuousOn f V
  (hsymmcont) ContinuousOn h.symm V
  (hderiv)    ∀ w ∈ V, HasFDerivAt f (fderiv ℝ f w) w
  (hderivsymm)∀ w ∈ V, HasFDerivAt h.symm (fderiv ℝ h.symm w) w

i.e. a BI-INVARIANT open neighbourhood of the fixed point on which f and its local inverse are
mutually inverse C¹ maps. The OpenPartialHomeomorph gives source S (open ∋ wstar, f=h on S, h.symm∘h=id
on S) and target T (open ∋ wstar since f wstar=wstar, h∘h.symm=id on T), but a fixed nbhd is NOT
forward-invariant in general (a diffeo at a fixed point can push points of S out of S).

QUESTION: what is the cleanest Mathlib v4.29 construction of such a bi-invariant V, and the proofs of
the 8 properties? Two candidate strategies:

STRATEGY A (intersection/shrink): V := S ∩ T ∩ f⁻¹'(S ∩ T) ∩ h.symm⁻¹'(S ∩ T) (or an iterated
version). Does this give hmaps/hsymmmaps? (For w ∈ V: f w ∈ S∩T by the f⁻¹ clause, but is f w ∈ f⁻¹'(S∩T),
i.e. f(f w) ∈ S∩T? Not obviously — needs a second preimage clause, and it may not terminate.) Is there
a fixed finite intersection that closes, or does this genuinely fail to be invariant?

STRATEGY B (don't need true invariance — restrict the downstream to a smaller working set): The
downstream lemma's forward leg actually only integrates over `s = V ∩ f⁻¹'(Ω ∩ V)` for an arbitrary
open Ω ∋ wstar, and uses `hleft` for InjOn on `s ⊆ V` and `f '' s ⊆ Ω`. So maybe `hmaps` (full
forward-invariance of V) is NOT actually load-bearing and can be supplied vacuously/weakly. Is there a
choice of V (e.g. V = S, with hmaps PROVED only where needed, or hmaps replaced by a weaker
consequence) that satisfies the literal signature above? Specifically: can `hmaps : ∀ w ∈ V, f w ∈ V`
hold with V = S ∩ h.symm '' S or V = S ∩ T or similar, given f=h on S and h: S→T bijectively?

GROUND TRUTH to check: h : S ≃ T (homeomorphism), h = f on S, h.symm = inverse on T. If I take
V := S ∩ T, is f(V) ⊆ V? f(V) = h(S ∩ T) ⊆ h(S) = T; but ⊆ S? Not necessarily. So V=S∩T fails hmaps.
What is the RIGHT V? I suspect V := S ∩ T ∩ h⁻¹'(S ∩ T) ∩ h.symm⁻¹'(S ∩ T) and then hmaps holds
because for w ∈ V, w ∈ h⁻¹'(S∩T) means h w = f w ∈ S∩T, AND we need f w ∈ the preimage clauses too —
which is the non-terminating worry. Adjudicate whether a FIXED intersection suffices for the literal
8 properties, or whether the downstream lemma should be re-stated to not require global hmaps.
</task>

<output_contract>
1. VERDICT: does a FIXED finite-intersection V satisfy all 8 properties (give the exact V), OR is full
   forward-invariance unobtainable from a fixed nbhd (so the downstream signature is too strong and
   should drop/weaken hmaps)? One line.
2. If a V works: the exact `V := …` and a 1-2 line proof sketch for EACH of hmaps, hsymmmaps, hleft,
   hright (the C¹/cont/deriv ones are routine — focus on the four invariance/inverse ones).
3. If no fixed V works: state precisely what weaker hypothesis the downstream lemma actually needs
   (e.g. only hleft on V + hsymmmaps, with hmaps droppable), citing that the forward leg restricts to
   V ∩ f⁻¹'(Ω∩V).
4. The Mathlib v4.29 lemma names for: OpenPartialHomeomorph source/target open + mem, h = f on source,
   h.symm∘h = id on source (left_inv), h∘h.symm = id on target (right_inv), maps_to.
</output_contract>

<grounding_rules>
Distinguish PROVABLE set-algebra (V ⊆ S etc.) from CONJECTURE about invariance. If you claim a fixed V
is bi-invariant, give the explicit membership chase for hmaps (the hard one). If it can't close, say so
and give the weaker-hypothesis fix. Use real Mathlib v4.29 names (OpenPartialHomeomorph API:
.open_source, .open_target, .map_source, .map_target, .left_inv, .right_inv, .left_inv', etc.) — flag
any name you are unsure exists in v4.29.
</grounding_rules>
