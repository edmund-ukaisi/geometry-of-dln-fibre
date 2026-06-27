<task>
Lean 4 + Mathlib v4.29. Pick the lightest encoding to get a NAMED MvPolynomial for an a.e.-positivity proof.

GOAL: prove `∀ᵐ x : Fin N → ℝ, 0 < achieverUfun x` where `achieverUfun x = VvalGen (x p) M t (decoder x) hle`,
`VvalGen = ∑_{i,j} (HrGen i j)²`, `HrGen = reindex (Hmat 0)`, and `Hmat 0 : Matrix (Fin (Twid 0)) (Fin (Wwid n)) ℝ`
is the telescope quotient of an abstract `Chain n u` (over ℝ): `Hmat s = B_s · Hmat(s+1) + E_s · suffix(s+1)`,
`Hmat n = R`, `suffix s = A_s·…·A_{n-1}`, `suffix n = 1`. The `Chain`'s blocks (`A`,`B`,`E`,`R`) come from a
decoder `genBlkFlatStruct ... x` whose entries are each a SINGLE flat coordinate `x i` (read linearly via a
fixed `Equiv.symm`), plus the radial `u = x p`. So `achieverUfun` is a polynomial map in `x`.

The banked nullity tool is `MvPolynomial.ae_eval_ne_zero (p) (hp : p ≠ 0) : ∀ᵐ x, eval x p ≠ 0`. It needs a
NAMED `p : MvPolynomial (Fin N) ℝ` with `eval x p = achieverUfun x` and `p ≠ 0`.

CONSTRAINTS:
- The abstract `Chain`/`suffix`/`Hmat`/`chain_telescope` engine is `ℝ`-PINNED and consumed by ~14 banked
  files; ring-generalizing it to `CommRing R` is too heavy/risky.
- `Matrix.map_mul` (`(A*B).map f = A.map f * B.map f` for ring hom f), `RingHom.mapMatrix`, and
  `MvPolynomial.eval f : MvPolynomial σ R →+* R` (a RingHom) are available. `Matrix.map` commutes with `+`,
  `*`, scalar mul under a ring hom; `(1).map f = 1`, `(0).map f = 0`.
- `Hmat`/`suffix` are `noncomputable def`s by downward recursion on remaining length `d`, with `_succ`/`_last`
  unfold lemmas (`Hmat_succ`, `Hmat_last`, `suffix_succ`, `suffix_last`).

CANDIDATE ROUTES:
(R1) PARALLEL POLY CHAIN: build a standalone `Chain`-like recursion over `MvPolynomial (Fin N) ℝ` mirroring
     `suffixAux`/`HmatAux` (reading `X i`/`X p` for the blocks), define `UPolyGen := ∑ (PolyHmat_0 i j)²`,
     prove `eval x (PolyHmat_0 i j) = HrGen i j` by induction on the recursion using `Hmat_succ`/`suffix_succ`
     + `eval` ring-hom pushing. Cost: re-mirror the recursion + one naturality induction.
(R2) MATRIX-MAP NATURALITY ON THE EXISTING ℝ CHAIN: observe that the ℝ `Hmat 0` for the decoder `decoder x`
     equals `(Hmat^P 0).map (eval x)` where `Hmat^P` is the SAME `Hmat` def but instantiated at a
     POLYNOMIAL decoder `decoderP : GenBlk` over... — but `GenBlk`/`Chain` are ℝ-typed, so I cannot
     instantiate them over MvPolynomial without generalizing. Does `Matrix.map`/`RingHom.mapMatrix` give any
     way to AVOID a polynomial-typed chain, e.g. by exhibiting the ℝ `Hmat 0 (decoder x)` as `eval x ∘ (a
     fixed polynomial matrix)` WITHOUT a polynomial chain? I suspect NOT (the chain is ℝ-typed end to end),
     confirm.
(R3) ONE-ENTRY ONLY: I only need `VvalGen ≥ (Hmat_0 i0 j0)²` for ONE entry, with that entry a nonzero
     polynomial. Does reducing to one entry meaningfully lighten R1 (a scalar recursion `PolyHentry` instead
     of a full matrix `PolyHmat`)? Over opaque widths, is a scalar-valued downward recursion carrying just
     `Hmat_s i0 (j0)`-th... no — `Hmat_s = B_s·Hmat(s+1)+…` couples ALL rows, so a single entry of `Hmat_0`
     depends on a full row of `Hmat_1`, etc. So a scalar recursion does NOT close; I'd still need the full
     `PolyHmat` row/matrix. Confirm R3 does NOT lighten R1.

QUESTIONS:
Q1. Confirm R2 is a dead end (no MvPolynomial without a polynomial-typed chain) and R3 does not lighten R1
    (single entry needs the full matrix recursion). One paragraph each.
Q2. For R1 (the route): the cleanest Lean SHAPE. Do I define a NEW structure `PolyChain` (mirroring `Chain`
    over `MvPolynomial (Fin N) ℝ`) and re-derive `PolyHmat`/`PolySuffix` + the ONE naturality lemma
    `eval x (PolyHmat c0 0 _ i j) = (ℝ-Hmat (cR x) 0 _) i j` (by `d`-induction, `Hmat_succ`/`suffix_succ` on
    both sides, `map_add`/`map_mul`/`Matrix.map_mul` pushing `eval`)? OR is there a way to reuse the EXISTING
    `Chain` def at type `MvPolynomial (Fin N) ℝ` by making JUST `Chain`/`suffixAux`/`HmatAux`/their `_succ`
    lemmas `{R : CommRing}`-generic (a SCOPED generalization of ONLY `RouteMAchieverTelescope.lean`, NOT the
    14 consumers — the consumers keep using it at `R = ℝ`, which still typechecks since the def becomes more
    general)? Assess: does generalizing ONLY `Chain`/`suffix`/`Hmat`/`chain_telescope` to `CommRing` break
    the 14 consumers, or do they keep working at `R = ℝ` (the generalization is conservative — every ℝ-use is
    a special case)? This scoped generalization seems strictly better than a duplicate `PolyChain` IF the
    consumers don't break. Rank: scoped-generalize-Chain vs duplicate-PolyChain.
Q3. The naturality lemma's hardest step: `eval x` (a RingHom ℝ-coeff... wait, `eval x : MvPolynomial (Fin N) ℝ
    →+* ℝ`) pushed through `Matrix.map`. Is `(A * B).map (eval x) = A.map (eval x) * B.map (eval x)` exactly
    `Matrix.map_mul`? And `(u • A).map f = f u • A.map f` — what's the lemma name (or is it `Matrix.map_smul`
    composed with the scalar)? And the base `suffix_last`/`Hmat_last`: `(1 : Matrix).map f = 1` is
    `Matrix.map_one` (needs `f 0 = 0`, `f 1 = 1`) — confirm the exact v4.29 names.

OUTPUT CONTRACT:
- Q1: confirm R2 dead / R3 no-lighten, ≤ 4 sentences each.
- Q2: the RANKED decision (scoped-generalize-Chain vs duplicate-PolyChain) with the conservativity
    assessment (do the 14 consumers break?), + the chosen route's lemma skeleton (signatures), ≤ 12 sentences.
- Q3: the exact v4.29 lemma names for map_mul / map_smul / map_one / map_zero under a RingHom, ≤ 6 sentences.
- End: ONE recommended route + the single biggest risk, ≤ 4 sentences. Flag INFERENCE vs known API.
</task>
