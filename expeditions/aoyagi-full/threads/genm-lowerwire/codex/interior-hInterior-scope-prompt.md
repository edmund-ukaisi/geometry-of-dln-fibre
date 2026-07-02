<task>
Lean 4 / Mathlib formalisation soundness check. I am wiring a general-L "interior box-divergence" atom
into an achiever-dispatch spine for an RLCT (real log canonical threshold) computation of deep linear
networks. I need you to adjudicate ONE fidelity/soundness question and confirm the honest scope of a
lemma I am about to build.

CONTEXT — the definitions (all over `M : Fin (L + 1) → ℕ`, a width vector):

- `tach M : Fin (L+1) → ℕ` is a chosen "achiever descent path" (a `Classical.choose` argmin), with
  `tach 0 = M 0`.
- `Text M (tach M) : ℕ → ℕ`, with `Text M t 0 = M 0` and `Text M t (j+1) = t ⟨j,_⟩` (in range).
- `Wext M : ℕ → ℕ`, with `Wext M k = M k` (in range).
- `deepRank M := Text M (tach M) L`  (the compressed rank flowing into the deepest/leaf factor).
- `deepRows M := Wext M (L-1) = M (L-1)`.
- `InteriorDrop M : Prop :=`
    `0 < Wext M L ∧ ∃ p, 1 ≤ p ∧ p < L ∧ Text M (tach M) (p+1) < Text M (tach M) p ∧`
      `(∀ b, p ≤ b → b < L → Text M (tach M) (b+1) < Wext M b)`.

THE ATOM I WAS GIVEN (sorry-free, general L): `routeMCore_box_diverges_interiorLiveGen`, with hypotheses
  `ha : StructAdm M (tach M)`   (discharged unconditionally by `structAdm_tach M hL`, needs `hL : 0 < L`)
  `hL : 0 < L`
  `h0r : 0 < Text M (tach M) L`   (= `0 < deepRank M`)
  `h0c : 0 < Wext M L`
  `hpos : 1 ≤ minAdm M`
  `hInt : InteriorDrop M`
  plus `c'`, `hc' : ½·minAdm ≤ c'`, `ε`, `hε : 0 < ε`,
  conclusion: `∫⁻_{cubeBox N ε} |routeMCore M|^{-c'} = ⊤` (call it `BoxDiverges M c' ε`).

THE SPINE OBLIGATION I must discharge (general L): `hInterior : ∀ _ : 2 ≤ L, InteriorDrop M → BoxDiverges M c' ε`.
The spine also has in scope: `hpos : 1 ≤ minAdm M`, `hMpos : ∀ s, 0 < M s`, `hc'`, `hε`.

WHAT I OBSERVED in the L=2 (Fin 3) code (verified by reading the files):
- The L=2 interior branch does NOT feed the LIVE atom directly. It CASES on `Text M (tach M) 2 = 0`:
  * `deepRank = 0`: uses a SEPARATE atom `routeMCore_box_diverges_eDeepRank0` (a pure E-block radial chart).
  * `0 < deepRank`: uses the LIVE-leaf atom.
- `interiorDrop_L2_iff` proves: `InteriorDrop M ↔ (0 < M 2 ∧ deepRank M < M 0 ∧ deepRank M < M 1)`.
  This places NO positive lower bound on `deepRank M`. Example `(2,2,1)` with `tStar = ![0,0]` has
  `deepRank = 0` yet `InteriorDrop` holds.
- The `deepRank = 0` handler (`eDeepRank0*`) is entirely pinned to `Fin (2+1)` — there is NO general-L
  `deepRank = 0` atom. Only the LIVE (`0 < deepRank`) atom is lifted to general L.

MY QUESTIONS:

1. Is it TRUE that `InteriorDrop M` does NOT imply `0 < Text M (tach M) L` (= `0 < deepRank M`) in
   general? I claim it does not (the L=2 characterization + the `(2,2,1)` example show `deepRank = 0` is
   compatible with `InteriorDrop`). Confirm or refute. If there is a subtle reason `deepRank` must be
   positive under `InteriorDrop` at general L that the L=2 picture hides, name it.

2. Given (1), the given general-L LIVE atom can discharge `hInterior` ONLY on the sub-stratum
   `0 < deepRank M`. To discharge `hInterior` for ALL `InteriorDrop M` at general L, one additionally
   needs a general-L `deepRank = 0` atom, which does not exist (only L=2). Is my conclusion correct that
   the FULL general-L `hInterior` is therefore WALLED at the `deepRank = 0` sub-stratum for L ≥ 3, and
   the honest deliverable is a lemma discharging only the `0 < deepRank` interior sub-stratum
   (carrying `h0r : 0 < deepRank M` as an explicit hypothesis, since it is NOT derivable from
   `InteriorDrop`)?

3. Sanity-check the thin bridge for the `0 < deepRank` lemma: from `2 ≤ L` I get `hL := 0 < L` and
   `ha := structAdm_tach M hL`; `h0c := hInt.1` (the first conjunct `0 < Wext M L`); `h0r` explicit;
   then apply the atom. Is `h0c := hInt.1` sound (`InteriorDrop`'s first conjunct IS `0 < Wext M L`)? Any
   trap in taking `ha` unconditionally from `structAdm_tach`?
</task>

<output_contract>
Answer in 3 numbered sections matching my 3 questions. For each: a one-word verdict
(CONFIRM / REFUTE / UNCERTAIN) then <= 6 lines of reasoning. Flag explicitly anything you are
INFERRING vs what follows directly from the definitions I gave you. End with a single line:
SCOPE = <the honest lemma statement you recommend I build>.
</output_contract>

<grounding_rules>
You do not have the repo. Reason ONLY from the definitions and observations I gave you. If a claim
needs a fact I did not state (e.g. a monotonicity of `tach`), say so explicitly and mark it as an
assumption, do not assert it as fact.
</grounding_rules>
