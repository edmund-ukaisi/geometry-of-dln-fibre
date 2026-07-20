# Decorrelated review: Aoyagi 2023 DLN §5 mechanism + two mint-path pricing

You are a decorrelated second opinion for a math-formalisation recon. I read
Aoyagi's "Consideration on the learning efficiency of multiple-layered neural
networks with linear units" (2023 preprint, 31pp) end-to-end. I want you to
RED-TEAM my reading of the core construction and my pricing of two formalisation
paths. Do NOT agree by default — hunt for where I have mis-stated the mechanism
or mis-priced a path. You do not have the PDF; reason from the summary + your
knowledge of resolution-of-singularities / RLCT (real log-canonical threshold)
theory in Watanabe's singular learning theory.

## Setup (what the paper computes)
- Model: deep linear net Y = (∏_{s=1}^L A^(s)) X + noise. Learning coefficient
  (RLCT) λ = the LCT of the ideal ⟨∏A^(s) − ∏A*^(s)⟩ at the true param, where
  LCT λ_{w*}(J) := sup{c : ∫_U (∑F_i²)^{−c} φ dw < ∞} for J=⟨F_i⟩ (real field, k=1).
  λ = largest pole of the zeta ∫(∑F²)^{z}. θ = its order (multiplicity).
- Endgame (Theorem 2): closed form λ = [−r²+r(H^(1)+H^(L+1))]/2 + a(ℓ−a)/(4ℓ)
  − ℓ(ℓ−1)/4·M̃² + ½∑_{i<j}M^(Si)M^(Sj), θ = a(ℓ−a)+1, with M^(s)=H^(s)−r the
  coranks, and (M, ℓ, a) a Def-3 combinatorial datum.

## My reading of the SINGLE mathematical idea of §5 (the proof)
1. **Regular peel (Theorem 3, via Lemma 2 Schur/unipotent normal form).**
   Unipotent (regular) changes of coords P1,P2 block-diagonalize the product:
   P1(∏A^(s))P2 = [C_1, 0; 0, ∏C^(s)], C_1 an r×r regular block. The ideal
   ⟨∏A−diag(E_r,0)⟩ splits into r²+r(M^(1)+M^(L+1)) FREE regular coordinate
   directions (contributing the closed-form [−r²+r(H^(1)+H^(L+1))]/2 to λ) PLUS
   the pure corank product ideal ⟨∏_{s=1}^L C^(s)⟩ with C^(s) of size M^(s)×M^(s+1).
   So λ = regular-const + λ_O⟨∏C^(s)⟩.
2. **Deepest point (Theorem 4, cited [22]).** For homogeneous generators, the
   LCT at the origin (all C^(s)=0) dominates (≤) any shifted point, so it suffices
   to compute λ at the origin of the corank product variety.
3. **Recursive monomialization (the heart).** ONE uniform idea: iterated blow-ups
   along submanifolds, monomializing the product ideal ⟨∏C^(s)⟩ into a diagonal of
   monomials. A double induction on (S = layer index 0..L+1, J = # cleared pivots).
   Invariant at (S,J): ⟨∏C^(s)⟩ = ⟨ diag(b_1..b_{M(S)}) · [E_J 0; 0 D_J] · ∏_{s>S}C^(s) ⟩,
   with b_i monomials in the exceptional coords u_{s,k} (b_i = ∏_{t̃_{s,k}=i−1} u · b_{i−1}),
   D_J a residual matrix of un-cleared variables, and a MONOMIAL Jacobian
   ∏du_{s,k}^{M_{s,k}−1}. The "Cases" 1(1)/1(2)/2 are the CHARTS of one blow-up event:
   - 1(1): factor a divisor u across an equal-run of b's (merge into run, decrement
     pending count, exponent bump M' = M + J₁·(M^(S+1)−J)); does not advance J.
   - 1(2): the pivot-creation chart — corner entry becomes a unit, unipotent row/col
     ops clear one pivot (E_J→E_{J+1}, D_J→D_{J+1}), advance J by 1.
   - 2: uniform-run/layer step — factor u across the WHOLE residual block (exponent
     (M(S)−J)(M^(S+1)−J)), clear pivots one at a time; J increases by ONE per Case-2
     step; when J exceeds min(M(S),M^(S+1)) advance layer S→S+1 folding in C^(S+1).
   Terminates at S=L+1 with ⟨∏C^(s)⟩ = ⟨diag(b_1..b_{M(L+1)})⟩ (fully monomial).
4. **λ read-off (Hironaka change-of-vars).** Each resolution chart yields a candidate
   λ = ½·min{M_{s,k} : t̃_{s,k}=0}, with M_{s,k} a quadratic in corank differences
   M_{s,k} = (M^(1)−t^(1))(M^(2)−t^(1)) + ∑_{j=2}^L (t^(j−1)−t^(j))(M^(j+1)−t^(j)),
   t=(t^(1),..,t^(L)) a per-chart weakly-decreasing exponent vector. Global λ = min
   over charts of the candidate; solved in closed form by Lemma 3 (a discrete
   quadratic minimization / QIP over how corank mass distributes across levels;
   min A(b) = a·ℓ(ℓ−a) at b=a or a−1). θ = a(ℓ−a)+1 counts the achieving charts
   (Lemmas 4,5 + explicit chart constructions Eqs (1)-(5)).

QUESTION 1: Is "iterated blow-ups monomializing the product-of-matrices ideal along
the layer filtration; the cases are charts of one blow-up event; λ reads off as
min over charts of ½·min_{t̃=0} of a quadratic Jacobian-exponent, solved by a
discrete quadratic program" a FAITHFUL one-sentence characterization? What is the
load-bearing thing I might be getting wrong (e.g. does the min-over-charts really
compute the LCT — could there be a chart giving a SMALLER ratio that the case
enumeration misses; is the resolution genuinely a resolution i.e. proper+iso off
exceptional; does the ½ and the "+1" in Hironaka's (h_j+1)/(2k_j) get absorbed
correctly into M_{s,k}?).

## The two formalisation paths (we already have a Lean "engine")
Our engine already banks, sorry-free: the QIP (minAdm M = min_{T∈Adm} Mval(T),
Mval = Aoyagi's M_{s,k}, Adm = weakly-decreasing cone with block bounds), and
aoyagiLambda H r = [−r²+r(H^(1)+H^(L+1))]/2 + ½·minAdm(coranks) — matching
Theorem 2's λ in min-form (build-time #eval checks reproduce ground truth). The
open holes are: (a) monomialization_terminates (build the resolution tree), and
(b) region_glue (the per-chart integration → box-integral finiteness).

- **hbox** (engine's sole output) = ∀M, ∀c'<minAdm(M)/2, ∫_box (∑F²)^{−c'} < ⊤.
  This is the FINITENESS / one direction: λ ≥ ½·minAdm.
- **Path A (default):** engine → hbox → adapter → learning-coefficient assembly.
  The EQUALITY λ = ½·minAdm needs the OTHER direction (divergence at c' ≥ ½·minAdm,
  the attaining chart), which we currently either (i) delegate to a banked upstream
  achiever or (ii) supply by a CITED axiom `cited_aoyagi_dln` (rlct = ½·codim).
- **Path B (native λ theorem):** transcribe Aoyagi's λ theorem in full including
  BOTH directions of the Hironaka read-off, producing the exact equality natively
  and DELETING `cited_aoyagi_dln`.

My pricing claim: Path B ⊇ Path A in analytic content — it needs everything Path A
needs (the §5 monomialization + finiteness direction) PLUS: (B1) a monomial-integral
DIVERGENCE lemma (∫u^{h−2k c'}du = ∞ for c' ≥ (h+1)/(2k) — mirror of the banked
finiteness atoms, mechanical/medium), (B2) the ≥-direction of the change-of-variables
(lower-bound the downstairs integral by the pushforward of the diverging chart —
needs ONE chart, no cover, but needs the chart map to be a diffeo onto its image
with the divergence surviving), and (B3) knowing WHICH chart attains (already have
`liveAttainment`: minAdm ∈ terminalExponents of a nonempty-srcBox leaf). It SKIPS
essentially nothing structural (both share §5); the box-threshold framing is not
extra either way.

QUESTION 2: Is my claim "Path B strictly dominates Path A in content, so the marginal
cost of Path B over Path A is just B1+B2+B3, and B2 is the genuinely new hard piece"
correct? Or is there a way Path B is CHEAPER (skips the coverage/exhaustiveness proof
that Path A's finiteness direction needs, because divergence needs only one chart)?
i.e. could the EQUALITY be reachable by a lower-bound + a SEPARATE cheaper upper bound
(e.g. Watanabe's universal rlct ≤ ½·codim already banked) so that the expensive
coverage theorem is only needed for one side? Which side genuinely needs coverage?

QUESTION 3: The hardest NAMED object. For Path B, is the hardest new object (a) the
coverage/no-smaller-ratio theorem (that the enumerated charts give the TRUE min, not
just an upper bound), or (b) the two-sided change-of-variables/proper-birational
transport, or (c) something else? Aoyagi's paper does NOT prove coverage as a theorem
— she asserts "by a blow-up process". Is the coverage the irreducible new proof
obligation regardless of path, or can the divergence-side (lower bound) avoid it?

Answer Q1, Q2, Q3 crisply. Flag any place my mechanism reading is WRONG. Be terse.
