# worked.tex uplift vs source PDF (image pass) — task #63 part 1

**Charge:** the amended task #63 pairs the coverage audit (part 2, `paper-coverage-audit.md`) with a
"worked.tex UPLIFT vs source PDF (as images)". This is part 1: a fresh page-image cross-check of the
reproduction `theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex` against the canonical source
`paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf`
(31 pp., the SSRN preprint), with the uplift edits found.

**Scope covered this pass.** The prior owed-math audit (`verify-owed-math-audit.md`) image-verified the
"mountain" (pp.14–22), the arithmetic (pp.24–26), and p.8 (Def 3) — but **skipped the front matter**
(Def 1 / Lemma 1 / Def 2 / the monomial rule / Thm 1 / Lemma 2 / Thm 3, pp.1–13). This pass reads the
**entire paper pp.1–31** as images and cross-checks each load-bearing statement against worked.tex. The
front matter (pp.5–14) is now image-verified for the first time; the tail (pp.23, 25–31) independently
corroborates the prior pass.

## Findings

**ONE genuine defect (reproduction-side; the Lean object is unaffected):**

- **Lemma 1 inequality direction is flipped.** worked.tex line 166 states, for `G₁,…,G_m ∈ J = ⟨F₁,…,F_n⟩`,
  `rlct(∑G²) ≥ rlct(∑F²)`. The **source (Aoyagi Lemma 1, p.5) states `≤`**, and `≤` is the correct
  direction: `G ∈ J` gives the pointwise domination `∑G² ≤ c·∑F²` near `w*` (Cauchy–Schwarz on
  `G_i = ∑ a_{ij}F_j`), so `(∑G²)^{-α} ≥ c^{-α}(∑F²)^{-α}`, so the `G`-integral is harder to converge, so
  the threshold `rlct(∑G²) ≤ rlct(∑F²)`. Concrete check: `F = x`, `J = ⟨x⟩`, `G = x² ∈ J` ⟹
  `rlct(x⁴) = 1/4 ≤ rlct(x²) = 1/2`, and `x⁴ ≤ x²` near 0. The flip also **contradicts worked.tex's own
  fnote** (line 174), which correctly derives the domination `∑G² ≤ c∑F²`. **The Lean object is correct**
  (`Core.Aoyagi.IdealInvariance.rlctAt_sumSqFam_le_of_germRepresents` proves the `≤` direction; the
  equality usage — "same ideal ⟹ same rlct" — is symmetric and so was never corrupted). This is a
  statement-line typo in the reference doc, found because p.5 was outside the prior image pass.

**Everything else is faithful** (image-confirmed this pass):

- **Def 1** (p.5): `λ = sup{c : ∫|F|^{-kc}φ < ∞}`, `k=1` real / `k=2` complex; largest zeta pole; order;
  φ-independence when `φ(w*) ≠ 0`; ideal → sum of squares. Matches worked.tex `def:rlct`.
- **Def 2** (p.5): `‖C‖`, `⟨C⟩`. Matches.
- **Monomial rule** (p.6): `λ = min_U min_j (h_j+1)/(2k_j)`, `θ = max_u Card{…}`. Matches the boxed rule
  (denominator `2k_j`, the squared-loss convention). Matches.
- **Theorem 1 / RRR** (pp.6–7): the M-set four-case (`{1,2,3}` if `M^(s) < ½∑M`; `{1,2}/{1,3}/{2,3}` on
  the `≥`-dominance branches), `ℓ, M̃, M, a`, the λ formula, `θ = a(ℓ−a)+1`. Matches `thm:rrr` + `def:Mset-L2`.
- **Def 3 / general L** (p.8): the three conditions incl. the printed `≤` in condition (iii). Matches
  `def:Mset` — and worked.tex's **(T-D)** flag (printed `≤` a suspected typo for `≥`) is a faithful,
  appropriately-hedged transcription.
- **Theorem 2** (p.9): all three rewrite forms + `θ = a(ℓ−a)+1` + the equal-width example. Matches
  `thm:main`; the **(T-A)** flag (form-B middle term is `(M + (a−ℓ)/ℓ)²`, `M` not divided by `ℓ`) is
  confirmed correct against the image.
- **Lemma 2 / block elimination** (pp.10–11): `Q₁AQ₂ = diag(A₁, C₄)`, `Q₁,Q₂` unipotent, `rank C₄ = r₁−r`.
  Matches `lem:blockelim` (the lemma the monument's `canonNormalizationOf` shears realize).
- **Theorem 3 / product reduction** (pp.11–13): `P₁(∏A)P₂ = diag(C₁, ∏C^(s))`; the regular-part identity
  `λ⟨∏A − ∏A*⟩ = (−r²+r(H¹+H^{L+1}))/2 + λ⟨∏C⟩` (image: `r²+r(H¹+H^{L+1}−2r) = −r²+r(H¹+H^{L+1})`, checked).
  Matches `thm:prodreduce`.
- **Theorem 4 / deepest point** (p.14): `λ_{(0,…,0,w*)}⟨F⟩ ≤ λ_{(w*)}⟨F⟩` for homogeneous `F` + the
  φ-domination hypothesis. Matches `thm:deepest` (prior pass; re-confirmed).
- **p.23** (the `M_{s,k}` completion-of-squares), **p.24** (Lemma 3, the `A(b)/ℓ²` balance, min `= aℓ(ℓ−a)`;
  worked.tex's **(N-1)** "not a typo" holds), **pp.25–26** (Lemmas 4–5, `H̃_j/H̃'_j`, the `T̃/T̃'` extremal
  vectors, `θ = a(ℓ−a)+1`, the `t_{s,k}` local-coordinate construction eqs (1)–(5)), **pp.27–31**
  (Conclusions + references): corroborate the prior pass; no new defect. Reference cross-check: `[22]` =
  Aoyagi Entropy 15(9) 2013 (= the other source PDF, the Thm-4 method); `[12]` = Aoyagi–Watanabe 2005 (Thm 1);
  `[30,31,32]` = the Lemma 1 sources; `[15]` = Hironaka. All consistent with worked.tex's citations.

## Uplift edits (frozen; for the controller to apply + commit to worked.tex)

**EDIT 1 — fix the Lemma 1 direction (worked.tex line 166).**
- OLD: `$\rlct_{w^\ast}(G_1^2+\cdots+G_m^2)\ge\rlct_{w^\ast}(F_1^2+\cdots+F_n^2)$.`
- NEW: `$\rlct_{w^\ast}(G_1^2+\cdots+G_m^2)\le\rlct_{w^\ast}(F_1^2+\cdots+F_n^2)$.`
- (single change: `\ge` → `\le`; aligns with source Lemma 1 p.5, worked.tex's own fnote, and the Lean
  `rlctAt_sumSqFam_le_of_germRepresents`.)

**EDIT 2 — add a ledger entry** in the §6 collected-typos/underspec enumerate (a reproduction-side
correction, distinct from the paper's own typos T-A…T-F):
> `(R-1)` **Lemma 1 direction — reproduction typo, corrected 2026-07-23 (front-matter image pass).** The
> reproduction printed `rlct(∑G²) ≥ rlct(∑F²)` for `G ∈ J`; the source (Aoyagi Lemma 1, p.5) and the
> correct direction are `≤` (pointwise `∑G² ≤ c∑F²` ⟹ the more-singular `G`-side has the smaller
> threshold; e.g. `rlct(x⁴)=¼ ≤ rlct(x²)=½`). The Lean object was already correct
> (`rlctAt_sumSqFam_le`); only the reproduction statement line was flipped.

**EDIT 3 — header status note** (optional hygiene): extend the 2026-07-21 elder-annotation block to record
that the **front matter (pp.5–14) is now image-verified (2026-07-23)** — Def 1 / Lemma 1 (corrected) / Def 2 /
monomial rule / Thm 1 / Def 3 / Thm 2 / Lemma 2 / Thm 3 / Thm 4 — closing the last image-unverified
load-bearing region; the full paper pp.1–31 is now image-cross-checked.

## Net

The reproduction is faithful to the source across the full paper, with **one corrected defect** (Lemma 1
direction). The image-verification class is now closed for the entire paper (pp.1–31), not just the
mountain + arithmetic. No load-bearing claim in worked.tex diverges from the source after EDIT 1.
