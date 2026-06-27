<task>
I am formalising in Lean 4 + Mathlib the rate-side fields of an "achiever chart" bundle for
deep-linear-network RLCT lower bounds, parametric over an arbitrary width vector
M : Fin (L+1) → ℕ and a descent path t : Fin (L+1) → ℕ. I need a strategy check on the ONE
hard piece before I commit ~400 LoC.

THE ENGINE (all banked, sorry-free):
- `GenBlk M t` is a structure with 5 matrix-block fields over OPAQUE dependent widths
  `Text M t k` / `Wext M k`: `Bmat k`, `Nblk k`, `Wblk k`, `Rmat k`, `Rfin k`.
- `chainOfMt u M t B hle : FactoredChain L u` builds a chain whose abstract `toChain` has:
  `A k = chainA(Nblk k)(Wblk k)(C(k+1))`, `C k = Bmat k · chainQ(Nblk k) + u•Rmat k` (interior),
  `C L = u • Rfin L` (leaf), kept part `B k = Bmat k`, error `E k = Rmat k · A k`.
- The telescope keystone (banked): `C 0 · suffix 0 = u • Hmat 0`, where
  `Hmat s = B_s · Hmat(s+1) + E_s · suffix(s+1)`, `Hmat L = Rfin L`,
  `suffix s = A_s · A_{s+1} · ... · A_{L-1}`, `suffix L = 1`.
- Given identity boundary `hC0 : C 0 = 1`, the RATE is FREE:
  `routeMCore M (phiGen u M t B hle) = u² · VvalGen u M t B hle`, where
  `VvalGen = ‖HrGen‖²` (sum of squares of entries of `Hmat 0`, reindexed).
- An EXISTING structured decoder `genBlkFlatStruct M t ha x : GenBlk M t` reads free coords from
  disjoint flat slots, with `Bmat 0 = reindex 1`, `Rmat 0 = 0` (so `hC0` holds), interior
  `Bmat(k+1) = bmatStack [K; X·K]`, `Rmat(k+1) = rmatPad(E into bottom-right)`, BUT `Rfin = fun _ => 0`
  (a DEAD leaf — known bug "D1"). The genuine x-dependent chart `phiFlatStructV M t ha hN x`
  and its rate `routeMCore = (x p)²·VvalGen(...genBlkFlatStruct...x...)` are banked.

THE GOAL: fill `NodeAchieverChart.Ubound` (need `Ufun > 0` a.e. on a box + bounded) and `Umeas`.
Set `Ufun x := VvalGen (x p) M t (DECODER x) hle`. `VvalGen ≥ 0` (sum of squares) and measurability
(polynomial) are easy. The HARD field is a.e.-positivity: I need `VvalGen ≢ 0` as a function of x,
i.e. there EXISTS a witness point w with `VvalGen(...w...) > 0`, hence the zero-set is Lebesgue-null
(via `MvPolynomial.ae_eval_ne_zero`, the route the (2,2,2) anchor used with an explicit polynomial).

THE PROBLEM: with the DEAD leaf `Rfin = 0`, `Hmat L = 0`. At the natural all-1-diagonal/all-0-angular
witness, `Hmat 0` telescopes to 0 (every `E_s` carries `Rmat·A`; the leaf is 0). So I must use a LIVE
leaf. The certificate says build `B_det M` = `genBlkFlatStruct` EXCEPT `Rfin L` is LIVE with a fixed-1
pivot at `Rfin_L(0,0) = 1`. At the witness point w = {all kept-diagonal Bmat_k(0,0)=1, all
Nblk/Wblk/angular E = 0, pivot=1}, the claim is `Hmat_0(0,0)|_w = (∏_k Bmat_k(0,0)) · 1 = 1 ≠ 0`,
because the coupling terms `E_k·suffix` vanish (Rmat=0 except pivot) and the telescope reduces to the
all-kept path `B_{L-1}·...·B_0 · Rfin_L`.

MY QUESTIONS (rank by what is cheapest/most-robust to formalise over OPAQUE dependent widths):

Q1. Is there a way to AVOID the full opaque `Hmat_0(0,0)|_w = 1` telescoping? Specifically: instead of
    a single witness point in (Fin N → ℝ), can I pick a SPECIAL value of the decoder `B : GenBlk M t`
    DIRECTLY (not via the flat reader), e.g. `Bmat k = 1`-ish, `Nblk=Wblk=Rmat=0`,
    `Rfin L = single (0,0) 1`, and prove `VvalGen u M t B_witness hle > 0` for that EXPLICIT B and some u?
    Then non-vacuity of `VvalGen ≢ 0 as a function of x` follows IF the flat decoder's image hits B_witness.
    But the a.e.-positivity I actually need is about `x ↦ VvalGen(...DECODER x...)`. Does proving
    `∃ B, VvalGen u M t B hle > 0` even help, or must the witness be a genuine flat x that the decoder maps
    to a B with `Hmat_0 ≠ 0`? (The MvPolynomial route needs the witness to be a point in the x-space.)

Q2. To get `Hmat_0(0,0)|_w = ∏_k Bmat_k(0,0)`: the cleanest induction. `Hmat` recurses downward on
    remaining length `d = L − s`. At w, `E_k = Rmat_k · A_k = 0` for interior k (Rmat=0), so
    `Hmat_s = B_s · Hmat(s+1)` (the `E_s·suffix` term drops), down to `Hmat_L = Rfin_L`. So
    `Hmat_0 = Bmat_0 · Bmat_1 · ... · Bmat_{L-1} · Rfin_L` at w. Then I need the (0,0) entry of this
    product over opaque widths = ∏ Bmat_k(0,0) · Rfin_L(0,0). Is it cleaner to (a) prove
    `Hmat_s|_w = (Bmat_s · ... · Bmat_{L-1}) · Rfin_L` as a MATRIX identity by downward induction (using
    `Hmat_succ` + `E_s = 0`), then evaluate the (0,0) entry; or (b) carry the scalar `Hmat_s(0,0)|_w`
    directly through the induction? Over opaque dependent widths, which avoids the dependent-Fin cast hell?
    What is the minimal structural condition on Bmat_k at w to make the (0,0)-entry telescope clean
    WITHOUT computing the whole product (e.g. Bmat_k maps the 0-th basis col to 1·(0-th basis col) + ...)?

Q3. ALTERNATIVE that sidesteps Hmat entirely: `VvalGen = ‖Hmat_0‖²` and `prod M (chartParams) = u • Hmat_0`
    (reindexed). So `VvalGen = ‖prod / u‖²`. Could I instead prove a.e.-positivity of `Ufun` via the
    EXPLICIT product `prod M (chartParamsGen ...)` at the witness — bypassing `Hmat`? For opaque
    L, is `prod = layer_0 · ... · layer_{L-1}` and its (0,0) entry any easier than `Hmat_0(0,0)`?
    They are both length-L products over opaque widths — confirm they are the same difficulty.

Q4. The witness as an MvPolynomial point: the (2,2,2) route built `UPoly : MvPolynomial (Fin N) ℝ` with
    `eval x UPoly = Uval x`, showed `UPoly ≠ 0` via a single eval, then `ae_eval_ne_zero`. For ∀M,
    `VvalGen(...DECODER x...)` as a function of x IS a polynomial in x. But proving it equals
    `eval x` of a CONCRETE MvPolynomial over opaque N is itself hard. Is there a Mathlib route to
    "f is a polynomial/analytic map and f(w) ≠ 0 for some w ⟹ {f = 0} null" WITHOUT constructing the
    MvPolynomial explicitly — e.g. `AnalyticOn` + the identity theorem? Rank the available Mathlib v4.29
    lemmas for "nonzero polynomial/analytic-map zero set is null" that do NOT require me to name the
    polynomial. If there is none, say so and confirm the explicit-MvPolynomial route is required.

OUTPUT CONTRACT:
- Answer Q1–Q4 in order, each ≤ 8 sentences.
- For Q2, give the SINGLE cleanest induction shape (matrix-identity vs scalar-carry) with the minimal
  structural lemma on Bmat_k at w, as a Lean-shaped sketch (lemma statements, not full proofs).
- End with: the ONE recommended path (which Q's route), and the single biggest cast/dependent-width risk
  in it, in ≤ 5 sentences.
- Flag explicitly where you are INFERRING Mathlib API vs stating known v4.29 lemmas.
</task>
