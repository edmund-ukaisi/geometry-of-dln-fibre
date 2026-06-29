<task>
I am refactoring a Lean 4 / Mathlib formalisation. Context: the paper Lehalleur–Rimányi
"Geometry of the fibers of the multiplication map of deep linear networks". The payoff is
rlct(square-Frobenius loss of an N-layer linear network with target B) = ½·codim(mult⁻¹(B)),
i.e. the real-log-canonical threshold equals half the geometric codimension of the multiplication
fibre. This is Aoyagi's analytic theorem (Aoyagi Thm 1 / LR Thm 8.6); not in Mathlib.

CURRENT STATE (the monolith I must refactor):
A structure `RlctInterface d K ι` carries an OPAQUE map `rlct : (Tuple ℝ d → ℝ) → ℝ` and a SINGLE
cited field:
  cited_aoyagi_dln : ∀ (B : Matrix … ℝ) (r : ℕ), 0 < N → B.rank = r → r ≤ min d →
    rlct (lossDLN d B) = ((codimRepCanonical (fibre (k:=K) d (B.map ι))).toNat : ℝ) / 2
Here:
 - `lossDLN d B A = Tr((mult d A − B)ᵀ (mult d A − B))` is a REAL loss on `Tuple ℝ d`
   (d : Fin (N+1) → ℕ);
 - `codimRepCanonical (Z)` = Ideal.height of the vanishing ideal of the canonical entry-flattening
   of Z, an ℕ∞-valued GEOMETRIC codimension; it is defined over ANY field `k` (parametric), but the
   DLN payoff instantiates it over an ALGEBRAICALLY CLOSED, CHAR 0 field `K` (e.g. ℂ), with `ι : ℝ →+* K`;
 - `fibre d B = {A | mult d A = B}`.
So the single field FUSES (a) the analytic equality rlct = ½·codim_ℝ over ℝ, with (b) a real↔complex
codimension passage codim_ℝ(real fibre) = codimRepCanonical(fibre over K). The brief calls (b) the
hidden "transfer T", and wants it EXPOSED, not buried.

THE REQUESTED REFACTOR (the brief):
Replace the one fused field with a THIN cited interface carrying three GENERAL analytic theorems as
named fields (each true for all functions, cited to source), NOT the DLN-specific equality:
  C1: rlct(∑_{i<c} xᵢ²) = c/2   (Watanabe; smooth nondegenerate-quadratic block value)
  C2: rlct(∑ fᵢ²) ≤ ½·codim_ℝ(common zero set)   (Watanabe universal upper bound)
  C3: a monomial-extraction / resolution LOWER bound: given a normal-crossing log-principalisation
      datum of the loss IDEAL with divisor data (kⱼ,hⱼ), rlct ≥ ⨅ⱼ (hⱼ+1)/(2kⱼ)  (log-canonical /
      Varchenko); of the IDEAL, not the set (the set-only form is false).
PLUS expose T as either a PROVED lemma or an explicit carried field `transfer_real_complex`. Then
re-derive `cited_aoyagi_dln` as a DERIVED theorem from {C1,C2,C3,T} with the upper-bound and
lower-bound matching steps (R2/R3) entering as EXPLICIT named hypotheses for now (they land in a
later wave). All downstream theorems must keep compiling. Gates: green, sorry-free, axiom-clean
`#print axioms = [propext, Classical.choice, Quot.sound]` — NO new global `axiom` (cited content is
STRUCTURE FIELDS, exactly like the current monolith).

THE SURPRISE I DISCOVERED (the brief's recon was stale): there is ALREADY a large, serious, parallel
analytic RLCT formalisation in the same library, namespace `DLNFibre.DLN.RLCT.*`, DISCONNECTED from
the monolith:
 - a genuine `rlctAt H F wstar : ℝ≥0∞` (Aoyagi Def 1, the integral-sup form
   sSup{c : |F|^{−c} locally integrable near wstar}), over a real Lebesgue MeasureSpace on
   `Params H` (H : Fin (L+1) → ℕ, REVERSED index convention vs `d`: H 0 = output, H last = input);
   loss `dlnLoss H B A = ∑ᵢⱼ ((prod A − B)ᵢⱼ)²` (explicit sum-of-squares, not trace-form);
 - PROVED: `rlctAt_mono`, `weightedThreshold_transport` (Jacobian change-of-vars), `rlct_unit_invariant`,
   `rlct_germ_local`, `rlct_additive_smooth_block` (`λ(∑xᵢ² + G²) = n/2 + λ(G²)` — essentially C1);
 - a SINGLE cited `axiom monomial_rlct` (the bare weighted-monomial threshold = ⨅ axisRatio +
   pole-order), from which `monomialThreshold_ge_of_mult` (the C3 lower-bound mechanism) is PROVED;
 - `block_elimination` (L1, Schur normal form), `aoyagiLambda`, `aoyagiTheta` defined; a headline
   `aoyagi_learning_coefficient` being ASSEMBLED but still carrying several `sorry`s + the axiom.
This `RLCT/*` effort is IN-PROGRESS (many sorries; not axiom-clean), and it uses DIFFERENT TYPES from
the monolith: `Params H` vs `Tuple ℝ d`, sum-of-squares vs trace loss, reversed width indexing.

KEY GEOMETRY FACT for T: each top-dimensional minimising orbit-closure component of the fibre is the
orbit of `realizerD m` (m a minimising Kostant partition), and `realizerD` is built from
combinatorial 0/1 interval-direct-sum data — so its entries are literally 0/1, RATIONAL, hence REAL.
`codimRepCanonical` is parametric in the field; over ℝ it is the height of the same vanishing ideal
with ℝ coefficients.

QUESTIONS (rank by importance, be concrete and Lean-aware):

1. SEAM CHOICE. Given the parallel real `rlctAt` already exists (but in-progress, different types),
   should the thin interface (a) stay SELF-CONTAINED with an opaque `rlct` map + opaque cited C1/C2/C3
   fields (decoupled from RLCT/*, fastest, what the brief asks), or (b) be TYPED AGAINST the real
   `rlctAt`/`dlnLoss`/`Params` so C1/C2/C3 become statements about the genuine object (closes the gap
   to the real definition, but forces reconciling Params↔Tuple + sum-of-squares↔trace + index reversal
   NOW)? Which is the right bedrock move for ONE tide, given the controller will later want the opaque
   `rlct` replaced by the real `rlctAt`? What is the minimal seam that does NOT have to be re-buried later?

2. THE TRANSFER T. Is `codim_ℝ(real fibre) = codimRepCanonical(fibre over alg-closed K)` honestly
   PROVABLE in Lean from the `realizerD`-rationality fact above, within one tide, or does it need
   genuine new real-algebraic-geometry (e.g. real points Zariski-dense in each top component ⟹ real
   dimension = complex dimension, requiring a real-Nullstellensatz / dimension-theory bridge Mathlib
   may lack)? If it needs that depth, confirm it should be an EXPLICIT carried field
   `transfer_real_complex` (clearly "to be proved in rung T"), and give the cleanest honest STATEMENT
   of that field. Critically: note that the monolith's RHS uses `codimRepCanonical … over K` — so to
   even STATE a factored T I need a `codim_ℝ` object (codimRepCanonical instantiated at ℝ). Is
   introducing `codimRepCanonical (k:=ℝ) (fibre (k:=ℝ) d B)` and asserting it equals the K-version the
   right intermediate, or is there a subtlety (e.g. ℝ not alg-closed ⟹ the ℝ-height can DIFFER from
   the geometric codim, the real locus can have lower dimension than the complex variety)? This last
   point worries me: over ℝ the vanishing ideal / height need NOT equal the complex codimension in
   general. Is the factorization `rlct = ½·codim_ℝ` ∘ `codim_ℝ = codim_K` even the right factorization,
   or is the honest intermediate something else (e.g. the REAL-DIMENSION of the real fibre, or the
   complex codim directly with T absorbing the real↔complex in one step)?

3. C2/C3 SHAPES. For the thin interface to be USABLE to re-derive the equality, C2 (upper) and C3
   (lower) must bracket ½·codim. Give the cleanest Lean-stateable shapes for C2 and C3 such that
   composing them yields `rlct(loss) = ½·codim` GIVEN explicit R2/R3 "matching" hypotheses (the upper
   bound's codim_ℝ matches the geometric codim; the lower bound's ⨅(hⱼ+1)/(2kⱼ) equals ½·codim for the
   DLN resolution). What EXACTLY should R2 and R3 be as named hypotheses so that the cited boundary is
   honestly {C1,C2,C3,T} + {R2,R3 holes} and nothing is smuggled?

4. NAME=CONTENT TRAP. Where is the subtle overclaim risk in this refactor (a field whose NAME asserts
   more than its statement, or T re-buried)? Flag any place the proposed structure would let an
   `rlct_…` theorem secretly assume C3 for an unexhibited resolution.
</task>

<output_contract>
Five sections, in order:
  (1) SEAM — recommend (a) or (b), one paragraph why, + the minimal non-re-buried seam.
  (2) TRANSFER T — provable-in-one-tide? yes/no + the obstruction precisely; the honest STATEMENT of
      the factorization (address the ℝ-not-alg-closed subtlety in Q2 head-on: is codim_ℝ = codim_K the
      right intermediate or is it false/needs a different object?).
  (3) C2/C3/R2/R3 — the cleanest Lean-stateable field/hypothesis shapes (pseudo-Lean is fine).
  (4) NAME=CONTENT — the 1–3 specific overclaim risks to avoid.
  (5) VERDICT — one-line: proceed with which seam + T as proved-or-field.
Be terse. Pseudo-Lean over prose where a statement shape is the answer.
</output_contract>

<grounding_rules>
Distinguish what you can DERIVE mathematically (state as fact) from what you INFER about the Lean
codebase you cannot see (flag as inference). If a claim depends on a Mathlib lemma you are unsure
exists at v4.29, say so explicitly. Do not invent Mathlib lemma names as if confirmed.
</grounding_rules>
