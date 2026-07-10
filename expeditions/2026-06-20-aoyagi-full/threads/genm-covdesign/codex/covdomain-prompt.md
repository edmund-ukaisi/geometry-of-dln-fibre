<task>
I am formalising (Lean 4 + Mathlib, real Lebesgue `∫⁻`) one finiteness lemma from Aoyagi's RLCT
computation for deep linear networks. I need an INDEPENDENT design for a BOUNDED-domain, mechanisable
route. Please derive it from scratch; do not defer to any "standard" claim without giving the explicit
estimate.

SETUP (exact objects).
- A chain of tail matrix factors. `P = A_1 · A_2 · ... · A_{L-1}` is the product of `L-1` real matrix
  factors, `A_i` of size `m_i × m_{i+1}`. `P` is `m_1 × m_L`. Each `A_i` ranges over the unit box
  `[-1,1]^{m_i × m_{i+1}}` (call the whole tuple `A'`, ranging over the product box `B'`).
- A leading factor `A_0` of size `m_0 × m_1`, ranging over its unit box `[-1,1]^{m_0 × m_1}`.
- `frobSq(X) = ‖X‖_F^2 = Σ entries²`.
- Fix an integer corank `q ≥ 0`, and fix a `q×q` sub-minor selection `(ρ,κ)` (q rows of `P`, q cols
  of `P`). The CHART is `U = { A' ∈ B' : the q×q submatrix P[ρ,κ] is invertible }` (an open,
  full-dimensional subset of the box).

THE INTEGRAL I need finite:
    J = ∫_{A' ∈ U}  ∫_{A_0 ∈ box}  frobSq(A_0 · P)^{-c'}  dA_0  dA'
for a real exponent `c'` with `0 ≤ c' < (1/2)·minAdm(M)`, where `minAdm(M)` is a known positive integer
(Aoyagi's "smallest admissible codimension" of the chain M = (m_0,...,m_L)). You may treat `minAdm` as
a black-box positive integer with ONE usable inequality (the front-peel charge bound):
    minAdm(M)  ≤  m_0·q  +  minAdm(redTail),
where `redTail = (m_1 - q, m_2 - q, ..., m_L - q)` is the "reduced chain" (all tail widths dropped by q).

INDUCTION HYPOTHESIS available (this is the ONLY handle on the tail's singularity):
    (IH)  For every exponent `s < (1/2)·minAdm(redTail)`,
          ∫_{Y ∈ box(redTail)} frobSq( Y_1·Y_2·...·Y_{L-1} )^{-s} dY  <  ∞,
    where `Y_i` ranges over the unit box `[-1,1]^{(m_i - q)×(m_{i+1}-q)}` and the product
    `Y_1···Y_{L-1}` is the REDUCED-chain product (an `(m_1-q)×(m_L-q)` matrix). NOTE: the IH is a
    BOUNDED-box statement (Y in the UNIT box). It is NOT known over unbounded Y.

BANKED TOOLS I can call (Lean lemmas, use freely):
  (T1) Uniform radial Morse-residual bound. For a Morse block `R ∈ ℝ^d`, any radius `T>0`, any fixed
       `w>0`, and any `c' > d/2`:
           ∫_{[-T,T]^d} (‖R‖² + w)^{-c'} dR  ≤  Cresid(d,c') · w^{-(c' - d/2)},
       with `Cresid` a finite constant INDEPENDENT of T (it is the whole-space integral ∫_{ℝ^d}
       (‖R‖²+w)^{-c'} = Cresid·w^{-(c'-d/2)}, finite because c'>d/2). This bound is uniform in the box
       radius T.
  (T2) Polar/spherical blow-up: ∫_{ℝ^N} h = ∫_{sphere} ∫_{r∈(0,∞)} r^{N-1} h(r·ω) dr dω  (measure form,
       exact).
  (T3) Measure-preserving block shears (Jacobian 1): the map (x, D) ↦ (x, D - K·x) preserves Lebesgue
       measure for any measurable matrix-valued K(x). Also the per-factor unit-triangular shear
       [[I,0],[-K_i,I]] · A_i · [[I,0],[K_{i+1},I]]  is block-upper-triangular with pivot
       α_i = A_i^{TL} + A_i^{TR}·K_{i+1} on the chart, and the corank block is the Schur complement.
  (T4) rank(P) = q + rank(Schur complement of the pivot). On the chart, rank P ≥ q.

THE SUBTLETY (this is where naive routes die — confirm you see it, then route AROUND it).
The natural move is a change of variables threading the per-factor Schur complements to turn P into a
block-upper normal form, so that the tail singularity becomes the reduced-chain product and the IH
applies. But the shear coefficients `K_i = γ_i·α_i^{-1}` involve the INVERSE of the pivot block. The
pivot is invertible on the open chart but its determinant is NOT bounded away from 0 on the chart, so
this change of variables maps the BOUNDED chart `U` to an UNBOUNDED region in the reduced (Schur)
coordinates. Hence:
   - You CANNOT just apply the IH (which is a unit-BOX statement).
   - You CANNOT bound the reduced integral by the whole reduced space (that integral DIVERGES for small
     exponents: the reduced product has degree 2(L-1) so the radial tail ∫^∞ r^{flatDim-1-2(L-1)s} dr
     diverges when 2(L-1)s < flatDim, i.e. for small s).
   - A naive countable cover {|det pivot| ≥ 1/n} is unsafe (overlapping pieces, the per-piece bound
     grows without a summable envelope).

<output_contract>
Give me ONE concrete bounded-domain route (or a rigorous impossibility argument) with:
1. The exact sequence of coordinate moves / dominations, in the ORIGINAL bounded (A_0, A') coordinates
   as much as possible, naming which of (T1)-(T4) and (IH) each step consumes.
2. The exact exponent bookkeeping: show the final exponent fed to the IH is `< (1/2)·minAdm(redTail)`,
   using the charge bound `minAdm ≤ m_0 q + minAdm(redTail)`.
3. If your route needs a finite cover, state the cover explicitly and PROVE (a) it is finite and
   measurable, (b) each piece is finite with a bound that SUMS. Address head-on: near the deepest
   sub-stratum {rank P drops below q or the largest minor → 0} the pivot minor → 0 — does your cover
   still give a uniform bound there, or does that sub-locus need separate treatment?
4. Explicitly handle the A_0 (Morse) block AND the reduced (tail) block separately, since (T1) makes
   the A_0 block's unboundedness free but the tail block is the hard part.
5. If NO bounded route exists (a genuine wall), say so and give the obstruction precisely.
</output_contract>

<grounding_rules>
- Exact estimates only; give the explicit inequality at each domination step (no "clearly integrable").
- Distinguish what you PROVE from what you CONJECTURE. Flag any step you are unsure of.
- Prefer the native radial-blow-up tool (T2) over leaving a bounded domain, if that is what works.
- Do NOT assume the loss splits cleanly as ‖Morse‖² + ‖reduced‖² — verify the split (there may be
  cross terms / pivot factors), and if there are, show your route survives them.
</grounding_rules>
