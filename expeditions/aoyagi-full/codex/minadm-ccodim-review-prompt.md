<task>
Independent soundness/fidelity review of a Lean 4 formalisation of a headline math identity.

CLAIM (the paper's central codimension identity, Lehalleur–Rimányi 2024 "Geometry of the fibers of
the multiplication map of deep linear networks"):

    (minAdm M : ℤ) = cCodim M 0        for all M : Fin (L+1) → ℕ with 1 ≤ L

where
- minAdm M = ((Adm M).inf' Mval).toNat  is Aoyagi's admissible-cone minimum of the candidate value
    Mval M T = ∑_{j : Fin L} (tPrev j − T_j)(M_{j+1} − T_j),   tPrev j = (M_0 if j=0 else T_{j-1});
  Adm M = admissible cone: T weakly-decreasing, T_{L-1}=0, T_j ≤ admBound(j) (=min(M_0,M_1) at j=0, else M_{j+1}).
- cCodim M 0 = min over Kostant partitions m of codimForm(extendℤ m), the LR Cor 3.5 Ext-pairing quadratic form
    codimForm N f = ∑_{1≤i≤u≤j≤v≤N} f(i-1)(j-1) * f(u)(v).

I am auditing the proof for soundness and fidelity. I need an INDEPENDENT check of two design points where
a "green but subtly wrong" proof could hide. Reason from the math; do not assume my framing is correct.

=== POINT A: THE ROUTE DEVIATION ===

The proof does NOT build a bijection Adm M ↔ {all Kostant partitions}. Instead it uses:
  (1) a value-preserving bijection Adm M ↔ qipFeasible M = {e : Fin L → ℕ | ∑ e = M_0}
      via  eOfT M T c = ρ_c − ρ_{c+1}   (ρ = expSurvivor: ρ_0=M_0, ρ_{k+1}=T_k),
      inverse  tOfE M e c = M_0 − ∑_{j≤c} e_j,  with  Mval M T = Gqip M (eOfT M T)
      where Gqip d e = ∑_{1≤j≤i≤N} e_i (e_j + d_j − d_{j-1})  is the QIP objective;
  (2) then  min_e Gqip = qipMin = cCodim  via a SEPARATELY-banked equality  cCodim_eq_qipMin
      (proved as le_antisymm of an easy substitution direction cCodim ≤ qipMin, and a HARD converse
       cCodim ≥ qipMin that shows every cCodim-minimiser is "horizontal-lace" (HL), hence in the image
       of the substitution e ↦ mOfE d e).

The justification for NOT using the literal Adm ↔ Kostant bijection: the forward image of e ↦ mOfE d e
is ONLY the horizontal-lace (boundary-supported) Kostant partitions — a PROPER subset (e.g. for (2,2,2):
3 of the 6 Kostant partitions). So the substitution is not surjective onto all Kostant partitions, and a
direct bijection Adm ↔ Kostant does not exist; the non-surjectivity is instead absorbed by the hard
converse (the global cCodim-minimiser is itself HL).

QUESTIONS:
- Is this route logically sound as a proof of minAdm = cCodim, GIVEN the banked cCodim_eq_qipMin? In
  particular: does routing the minimum through qipFeasible (= HL partitions only) rather than all Kostant
  partitions LOSE anything, or is it fully repaired by cCodim_eq_qipMin (min over ALL Kostant = min over HL)?
- Is the "literal route fails / image is only boundary-supported" reasoning correct? Could there be a
  monotone M where the min over the HL image STRICTLY exceeds the min over all Kostant partitions — which
  would make qipMin > cCodim and BREAK the route? (I believe cCodim_eq_qipMin's hard converse rules this
  out by showing the global minimiser is HL — sanity check that this is the right thing to require.)

=== POINT B: THE CRUX — diffRank read-agreement (an off-by-one hiding place) ===

Mval = codimForm(diffRank(cascadeRank M T))  is a signed ring identity (all M,T, NO admissibility), where
  cascadeRank M T a b = ρ_b + (M_a − ρ_a)  on the box 0≤a,b≤L (else 0), and
  diffRank r a b = r a b − r(a-1)b − r a(b+1) + r(a-1)(b+1)  (mixed 2nd difference).
diffRank(cascadeRank) is boundary-supported:
  - TOP ROW:    diffRank .. 0 b   = ρ_b − ρ_{b+1}        (for 0≤b, b+1≤L)
  - RIGHT COL:  diffRank .. a L   = q_a − q_{a-1}        (q_x = M_x − ρ_x; for 1≤a≤L)
  - INTERIOR (1≤a≤L, 0≤b≤L-1):  = 0.

The bridge to Gqip uses codimForm_mOfE: codimForm(extendℤ(mOfE M e)) = Gqip M e, where mOfE's nonzero
entries are
  - LOW COLUMN:  mOfE(0, b) = e_b            (b < N)
  - TOP ROW:     mOfE(a, last) = e_{a-1} + (d_a − d_{a-1})    (a ≥ 1)

The proof shows diffRank(cascadeRank M T) agrees with extendℤ(mOfE M (eOfT M T)) on the two families of
reads codimForm makes (first factor f(i-1)(j-1) for 1≤i≤j≤L; second factor f(u)(v) for 1≤u≤v≤L):

  FIRST-FACTOR agreement (diffRank_first_eq): at i=1 the read (0, j-1) is diffRank top row = ρ_{j-1}−ρ_j;
    mOfE side = e_{j-1} = (eOfT)_{j-1} = ρ_{j-1}−ρ_j. For i≥2 both sides are 0 (interior / mOfE off).
  SECOND-FACTOR agreement (diffRank_second_eq): at v=L the read (u, L) is diffRank right col = q_u−q_{u-1};
    mOfE side = e_{u-1} + (M_u − M_{u-1}) = (ρ_{u-1}−ρ_u) + (M_u − M_{u-1}). For v<L both sides are 0.

QUESTIONS:
- Verify the algebra q_u − q_{u-1} = (ρ_{u-1} − ρ_u) + (M_u − M_{u-1}) with q_x = M_x − ρ_x. Is it an exact
  identity, or is there a sign / index (off-by-one) error?
- Verify the FIRST-factor read is the TOP ROW (index-0 row / low column of mOfE = the "e" part) and the
  SECOND-factor read is the RIGHT COLUMN (last column / top row of mOfE = the "e + d-diff" part), i.e. the
  orientation "first↔e, second↔e+ddiff" is correct and not swapped. codimForm reads f(i-1)(j-1) with the
  SECOND index j-1 ≤ L-1 (never L) and f(u)(v) with FIRST index u ≥ 1 (never 0). Do these ranges force
  exactly i=1 (first factor nonzero only on row 0) and v=L (second factor nonzero only on column last)?
- The second-factor agreement uses Monotone M (to cast d_u − d_{u-1} : ℕ honestly as a ℤ difference in
  mOfE's top-row entry). Is monotonicity GENUINELY required there, and is it harmless that the first-factor
  agreement does NOT need it?
- Does the boundary support (top row = ρ-difference, right col = q-difference, interior = 0) plus these two
  agreements FULLY determine codimForm(diffRank) = codimForm(extendℤ mOfE)? Any read codimForm makes that is
  NOT covered by the two families 1≤i≤j≤L and 1≤u≤v≤L (e.g. the corner (0, L))?
</task>

<output_contract>
Two sections, POINT A and POINT B. For each: a VERDICT line (SOUND / BROKEN / UNDERSPECIFIED), then
terse justification. If BROKEN, give the specific failing case (concrete M or index) and the minimal fix.
Do the q-difference algebra explicitly. Be adversarial: try to find a counterexample before concluding sound.
</output_contract>

<grounding_rules>
Distinguish what you VERIFIED by direct computation (mark [computed]) from what you INFER from my framing
(mark [inferred]). If a claim depends on a banked lemma whose internals you cannot see (cCodim_eq_qipMin,
codimForm_mOfE), say so explicitly and state what you are ASSUMING about it. Do not rubber-stamp.
</grounding_rules>
