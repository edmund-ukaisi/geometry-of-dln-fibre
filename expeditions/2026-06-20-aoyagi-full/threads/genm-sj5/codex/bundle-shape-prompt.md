<task>
Adjudicate the correct SHAPE of a base-case invariant clause in a Lean formalisation of an
RLCT (real-log-canonical-threshold) finiteness proof for deep linear networks. This is a math
design question; I want your independent structural analysis, not code.

## Architecture (verified from the Lean source)

We prove `∀ chain M, RouteMBoxThresholdFinite M` (a box integral is finite below a threshold
½·minAdm(M)) by a DECORATED DESCENT on chain arity:

- A chain is `M : Fin (n+1) → ℕ` (n+1 nodes; n matrices A_0…A_{n-1}, A_s of size M_s × M_{s+1};
  the map is the product A_0·A_1···; the loss at the most singular fibre is frobSq(product)).
- A `SJDecoration D` on M carries: an exceptional-coordinate count `d`, a generator carrier, an
  accumulated jacobian-exponent vector `jac : Fin d → ℕ`, a deeper parameter space `Z : Type`
  with `ctx : Z → (spectator × (active → ℝ))` and a domain `dom ⊆ Z`.
- The decorated loss is `decLoss D u z = Σ_i ( ∏_ℓ |u_ℓ|^{supp i ℓ} · res_i(z) )²`, a sum over
  generators i, each a product of exceptional-coordinate monomials (exponents `supp i ℓ`) times a
  LINEAR residual `res_i(z)` in the active variables. Write `k_ℓ = min_i supp i ℓ` (the shared
  divisor exponent) and `commonDivisor(u) = ∏_ℓ |u_ℓ|^{k_ℓ}`.
- The finiteness predicate: `DecoratedBoxThresholdFinite D` := for all c' < ½·minAdm(M),
  `∫_{z∈dom} ∫_{u∈[0,1]^d} (∏_ℓ|u_ℓ|^{jac_ℓ})·decLoss(u,z)^{−c'} < ∞`.
- The DESCENT (strong induction on arity n): STEP at arity n takes a decoration D on M, PEELS the
  front pair of nodes (collapsing (M_0,M_1) to a single rank-t node, KEEPING the deeper tail
  M_2…M_n), which INCREASES d by 1 and DECREASES arity by 1, producing a decoration D' on the
  shorter chain; it invokes the induction hypothesis `adm D' → finite D'`, then transfers
  finiteness back. BASE at arity 1 (a width-2 chain M=(M_0,M_1), a single matrix): `adm D →
  finite D`.
- `adm D := genuineCarrier D ∧ (a=0 ∨ b=0 ∨ FaithfulSJAt D)` where a,b are front-block corank
  widths. `adm` is the loop INVARIANT: it must (i) hold for the trivial (d=0) starting decoration,
  (ii) be PRESERVED by every peel (so it holds at ALL intermediate arities along the descent), and
  (iii) at the width-2 base imply finiteness. `FaithfulSJAt` is the clause under design.
- `genuineCarrier D` pins `D.Z ≃ᵐ Params M` (the honest full parameter tuple of THIS chain M) with
  the residuals reading off the product entries `prod M (e z)`. At a width-2 chain, `Params M` is a
  SINGLE M_0×M_1 matrix, and `minAdm((M_0,M_1)) = M_0·M_1`.

## The consuming base lemma (fixed, banked)

`corankLeaf_rpow_lt_top`: for a FIXED matrix `Z : Fin n → Fin Dcol` with `Z·Zᵀ − c·I ≽ 0` (PSD),
`c>0`, and `0 < a·n`, the FREE-BLOCK integral `∫_{Γ ∈ matBox a n T} frobSq(Γ·Z)^{−c'} dΓ < ∞`
for every `c' < (a·n)/2`. (Proof: Rayleigh `frobSq(Γ·Z) ≥ c·frobSq(Γ)`, then the free-Γ Morse.)
Note Z is a FIXED matrix here; Γ is the integration variable.

## The clause that FAILED (Lean-verified dead-end)

The current `FaithfulSJAt` d≥1 branch requires a single dehomogenised generator i₀ with
`∃ c>0, ∀ z∈dom, c ≤ |res_{i₀}(z)|` (the i₀ residual bounded below by a positive constant), aiming
for the lower bound `decLoss ≥ commonDivisor(u)²·res_{i₀}(z)² ≥ commonDivisor²·c²` (so finiteness
comes from the u-monomial charge alone). A fresh formaliser reports this is not consumable and a
naive `∃ (Z:matrix)(c>0), Z·Zᵀ≽c·I` clause is vacuous. A draft replacement bundles the γ with a
structural leaf identity `decLoss = commonDivisor(u)²·frobSq(Γ·Z)` (Γ a free block over a box via a
measure iso dom≅matBox, Z a matrix, Z·Zᵀ≽c·I, and dim Γ exposed).

## Facts you should use
- `res_i(z)` is LINEAR (no constant term) in the active variables, which at width-2 ARE the entries
  of the free M_0×M_1 matrix. A nonzero linear form on a box containing 0 is not bounded below by a
  positive constant.
- The peel keeps the deeper tail M_2…M_n; the "deeper product" Z_tail = A_2·A_3···A_{n-1} at an
  intermediate arity is a FUNCTION of the deeper parameters (varies over dom) and DROPS RANK on a
  sublocus. At the width-2 base there is NO deeper tail (a single matrix), so any deeper product is
  the empty product = identity.

<questions>
Answer each independently and structurally; do not assume my preferred answer.
1. Is `∃ (Z : matrix) (c>0), Z·Zᵀ≽c·I` — with Z existentially free and unconnected to decLoss — a
   genuine constraint on the decoration D, or vacuous? Why.
2. `corankLeaf` needs Z a FIXED matrix. The invariant must hold at INTERMEDIATE arities where the
   only natural candidate for Z (the deeper tail product) VARIES over dom and drops rank on a
   sublocus. So: in the bundled leaf identity `decLoss = commonDivisor²·frobSq(Γ·Z)`, should Z be
   (i) a single fixed matrix, (ii) a z-dependent matrix Z(z) with a sector condition
   `∀z∈dom, Z(z)Z(z)ᵀ≽c·I`, or (iii) something else? What makes the invariant simultaneously
   FAITHFUL at intermediate arities AND consumable by the fixed-Z corankLeaf at the base?
3. Should `dim Γ = minAdm M` be a CARRIED clause of the invariant, or DERIVED at the width-2 base?
   Consider whether `dim(front free block) = minAdm M` can hold at arity > 2 given minAdm satisfies
   a back-peel recursion minAdm M = (front charge) + minAdm(deeper tail).
4. FAITHFULNESS of the identity `decLoss = commonDivisor(u)²·frobSq(Γ·Z)` with a u-INDEPENDENT
   residual block: the per-generator supports `supp i ℓ` DIFFER across generators (this anisotropy
   is the whole reason a per-generator carrier is used, not a scalar weight). After factoring
   commonDivisor(u), does the residual generally stay u-independent (a clean frobSq of a free
   block), or do leftover monomials `∏_ℓ|u_ℓ|^{supp i ℓ − k_ℓ}` remain per generator? Under what
   scoping (e.g. a corner blow-up sector |u_1|≤|u_0|, or a fully-uniform-support terminal) does the
   clean frobSq form actually hold?
5. Net: give the minimal faithful shape of the d≥1 clause (as a list of the data + propositions it
   must bundle), flagging any piece that is width-2-specific (derive at base) vs genuinely invariant
   (carry). Flag any over-specification.
</questions>
</task>

<output_contract>
Five numbered answers matching the questions, each 3-8 sentences. Then a final section
"MINIMAL FAITHFUL SHAPE" listing the bundle as data + props with each tagged [CARRY] or
[DERIVE-AT-BASE] or [DROP]. Distinguish clearly what you assert as FACT (forced by the setup) from
what is a JUDGEMENT/recommendation. Be concrete about the Z fixed-vs-varying question — that is the
crux.
</output_contract>

<grounding_rules>
Ground every claim in the architecture facts above. If a claim depends on a fact not given, say
which fact you are assuming. Do not invent Lean API. The RLCT/Morse fact you may use: for a free
matrix block Γ of dimension N over a box, `∫ frobSq(Γ)^{−c'} < ∞ ⟺ c' < N/2`.
</grounding_rules>
