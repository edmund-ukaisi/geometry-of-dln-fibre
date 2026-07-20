# Review — P1-R5 `TopDimMinPrimes` count-transport extraction (CRUX)

**Reviewer:** independent decorrelated audit (read-only, no full build — controller re-gated at 3819).
**Target:** commit `9b66a95f` on `expedition/foundation-lift-p1`; modules
`lean/DLNFibre/Core/MinimalPrime/{Localization,Polynomial,Radical,Bridge,TopDimensional}.lean`.
**Method:** own reading of the four modules + the deleted sources via `git diff -M` across the rename +
the helper lemmas in `Core/Dimension/Localization` + the DLN discharge in `TopDimMinPrimesW1W2`;
a decorrelated Codex `xhigh` consult on the `hper`-shape / DVR-at-uniformizer question
(`codex/hper-shape-{prompt,answer}.md`).

## Overall verdict: PASS — clear-to-PR (no blocking findings)

The crux `hper` is honestly per-prime, not weakened, not silently discharged; the four transport
headlines are faithful re-homes (statements byte-identical across the rename, confirmed by diff); the
assembly is coherent. One **non-blocking** docstring-accuracy note (item 3c) and one preserved Codex
interpretive caveat (the `ncard`-of-infinite convention, item 1, not a defect of these rungs).

---

## (1) The per-prime `hper` shape — **PASS**

`topDimMinPrimes_ncard_away_eq` (Localization.lean:218–224) carries
```
hper : ∀ p ∈ TopDimMinPrimes A,
  ringKrullDim (Localization.Away (Ideal.Quotient.mk p f)) = ringKrullDim (A ⧸ p)
```
**Confirmed genuinely per-prime, NOT weakened, NOT discharged**, on direct read:

- It is universally quantified over each `p ∈ TopDimMinPrimes A`, with the localizing element the image
  `Ideal.Quotient.mk p f` of `f` **in that specific quotient** `A ⧸ p`, equated to `ringKrullDim (A ⧸ p)`.
- It is a **separate argument** from the global `hdim : ringKrullDim S = ringKrullDim A`. Both appear as
  independent explicit hypotheses on `topDimMinPrimes_ncard_away_eq`, `bijOn_comap_topDimMinPrimes_away`,
  and `map_mem_topDimMinPrimes_of_avoid`.
- `hper` is consumed in **exactly one** place — `map_mem_topDimMinPrimes_of_avoid` (Localization.lean:182–189),
  the `map`-direction top-dimensionality, via
  `rw [ringKrullDim_quotient_map_localizationAway_eq f S p, hper p hp, hp.2, hdim]`. The
  `comap`-direction (`comap_mem_topDimMinPrimes_of_away`) deliberately does **not** use `hper` — it runs a
  squeeze `dim A = dim S = dim(S⧸P) = dim(Away(mk p f)) ≤ dim(A⧸p) ≤ dim A` needing only the always-true
  `ringKrullDim_localization_le`. This asymmetry is correct: the `≤`-half is free; only the `map`-side
  no-drop (`≥`) needs the per-prime input.

**Diff evidence (faithful re-home):** `git diff 9b66a95f^ 9b66a95f -M` on the Localization module shows the
`+`/`−` hunks touch **only** docstrings and the `namespace`/`open` lines — never a `theorem … :` signature
line or a proof body. `hper`'s text does not appear in any `+`/`−` proof-relevant hunk. So it is
**byte-identical** to the source `TopDimMinPrimesLocalization` (84% rename similarity; the delta is prose +
ns surgery).

**Math reason it must stay per-prime (decorrelated, convergent):** my own reading plus the Codex `xhigh`
consult independently produced the same counterexample to the folding `hdim ∧ havoid ⟹ hper`:

> `A = R × B` with `R = k[t]₍ₜ₎` (a DVR, uniformizer `t`), `B = k[u]`, and `f = (t, 1)`.
> Minimal primes `p = (0)×B`, `q = R×(0)` are **both** top-dimensional (`dim(A⧸p)=dim R=1`,
> `dim(A⧸q)=dim B=1`, `dim A = 1`). `havoid` holds (`f∉p`, `f∉q`). Global `hdim` holds:
> `A[1/f] ≅ k(t) × B`, `dim = max(0,1) = 1 = dim A`. **Yet** for the top prime `p`,
> `(A⧸p)[1/f̄] ≅ R[1/t] ≅ k(t)` has dim 0 ≠ 1 = dim(A⧸p) — so `hper` **fails** while `hdim ∧ havoid` hold.

This is the precise sharpening of the memory note `per-prime-nodrop-localization.md`: a *bare* DVR does not
witness the gap (it fails `hdim`), so the witness genuinely needs the product-of-two-components shape, with
the dimension-preserving component masking the dropping one in the global max. Were `hper` replaced by a
global form or dropped in favour of `hdim+havoid`, the lemma would be **over-strong / unsound** on `A=R×B`.
It isn't. **Name = content confirmed.**

## (2) Transport soundness + faithful re-home of the four headlines — **PASS**

All four headline statements match their names/docstrings and are faithful re-homes (diff-confirmed: only
docstring/namespace/`open` changes, plus two re-homed defs and one rename):

- **`topDimMinPrimes_ncard_away_eq`** (Localization) — see (1). Hypotheses minimal: `hdim` (separately
  necessary in full generality — Codex Q2: derivable from `hper+havoid` only when `TopDimMinPrimes A ≠ ∅`,
  which the lemma does not assume, so keeping it is correct), `havoid`, per-prime `hper`. `[CommRing A]`
  only; no Noetherian needed — correct, the mechanism is `IsLocalization.minimalPrimes_map` +
  `BijOn.ncard_eq`, both unconditional.
- **`topDimMinPrimes_mvPolynomial_ncard_eq`** (Polynomial.lean:206–208) — `[IsNoetherianRing A] [Finite ι]`.
  Both hypotheses are load-bearing: `Finite ι` for the `card ι` dimension shift
  (`MvPolynomial.ringKrullDim_of_isNoetherianRing`), Noetherian for the same. Statement = name.
- **`topDimMinPrimes_quotient_radical_ncard_eq`** (Radical.lean:121–125) — `(J : Ideal R)`, no extra
  hypotheses, via `radical_minimalPrimes` + `zeroLocus_radical`. Minimal. Statement = name.
- **`ringKrullDim_quotient_eq_iff_height_eq`** (Bridge.lean:100–111) — `[Field k] [Finite σ]`,
  `(hIne : I ≠ ⊤)`, `(hp : p ∈ I.minimalPrimes)`. A genuine biconditional (characterization over assertion).
  Hypotheses minimal: `hIne` needed (else `R⧸I` trivial), the catenary needs the field + finite-σ.

Two re-homed auxiliaries verified byte-faithful against their pre-commit sources:
- `ringKrullDim_doubleQuot_eq` (Radical.lean:53–63) — proof byte-identical to the deleted
  `TopComponentsTopDim` version (only `{R}[CommRing R]` inlined to the file `variable`); general
  `[CommRing R]`, any `I`, any prime `P` of `R⧸I`. No DLN coupling. Correct re-home.
- `isPrime_map_mvPolynomial_C` (Polynomial.lean:48–53) — statement + proof identical to the deleted
  `SchurSideNoDrop.isPrime_map_C_of_isPrime`; only renamed. **Clash claim verified true** (was a grep-path
  artefact on first pass): Mathlib has `Ideal.isPrime_map_C_of_isPrime` as an `instance` in
  `RingTheory/Polynomial/Basic.lean:596`, the **univariate** `R[X]` version in the `Ideal` namespace — so
  the unchanged name in ns `Ideal` would genuinely clash. Rename to the multivariate name is justified and
  `name = content`.

## (3) P1-assembly coherence — **PASS-with-one-non-blocking-note**

- **Namespace:** all six `MinimalPrime/` modules in ns `Ideal` (the two extra `namespace`-grep hits are
  docstring prose). Mirrors `Mathlib.RingTheory.Ideal.MinimalPrime` → upstream move is a file-move.
- **Clash gate:** each headline + the two re-homed/renamed decls has exactly one definition; no Mathlib or
  sibling collision (`rg` clean).
- **No overclaim:** no `@[stacks]`, `@[simp]`, `@[instance]`, or `@[reducible]` attributes in any of the six
  modules — no attribute overstatement. No `sorry`/`axiom`/`native_decide`/`#exit`.
- **Factoring:** clean. `Localization`→`Dimension.Localization` (R2/R3 ≤-half + fg no-drop),
  `Bridge`→`Dimension.Codimension` (#14 catenary), `Polynomial`/`Radical`→Mathlib + `TopDimensional`. All
  four transport modules import **only** clean `Core` + Mathlib — **zero** `DLNFibre.DLN` imports
  (`Core→DLN` arrow respected). Aggregator imports the four after `TopDimensional`; the four deleted
  sources are gone.
- **DLN keystone discharge (the per-prime flag):** `TopDimMinPrimesW1W2.topDimMinPrimes_ncard_away_eq_of_fgDomain`
  (W1W2.lean:72–84) discharges `hper` **per-prime** — it passes the keystone `(fun p hp ↦ ?_)` (a per-prime
  lambda) and closes each instance with R3's `ringKrullDim_localizationAway_eq_of_fg_domain (k:=k) (A⧸p)
  (mk p f) hgne`, after establishing `A⧸p` is an f.g. `k`-domain and `mk p f ≠ 0` (from `havoid`). This is
  exactly the once-per-top-prime discharge the priorities flag required — and the math reason it works
  generically (each `A⧸p` finite-type over `k`) is precisely what a general DVR lacks, sidestepping the
  Codex counterexample. The wrapper's own `hdim` input is correctly labelled "global"; only `hper` is
  per-prime. Downstream `TopDimMinPrimesW0` and `TopComponentsTopDim` consume the extracted
  `quotTopDimSet`/`ringKrullDim_doubleQuot_eq`/`ringKrullDim_quotient_eq_iff_height_eq` via selective
  `open Ideal (…)`; `TopComponentsTopDim` additionally imports `RadicalCatenary` (it is itself DLN-coupled,
  so in-scope) — matches the statement card's flagged re-pointing surprise.

**Non-blocking note (3c):** the count transport lemmas use `Set.BijOn.ncard_eq`, which is unconditional
(true for infinite sets too — both sides 0). So the rungs are **sound regardless of finiteness**; Codex's
flagged `ncard`-of-infinite = 0 convention is **not** a soundness issue for these lemmas. Non-vacuity (the
count is a genuine finite `cTheta`) is established downstream (`ncard_topDimMinPrimes_sigma_eq_cTheta_dminus`,
DLN), outside this rung's scope. Preserved as an interpretive caveat, not a defect.

---

### Decorrelation note
The Codex `xhigh` consult independently reproduced the `A = R×B` counterexample to the `hper` folding
(convergent with my own reading), confirmed `hper` per-prime **necessary: YES** and `hdim` separately
**necessary: YES** in full generality (NO if top-set nonempty), and judged the `hper` shape correct-and-
minimal-for-the-use. Its points (3 shape-is-slightly-broader-than-bare-use, 4 ncard-convention) are
preserved here as inference/interpretive notes, not promoted to defects. Artefacts:
`codex/hper-shape-prompt.md`, `codex/hper-shape-answer.md`.
