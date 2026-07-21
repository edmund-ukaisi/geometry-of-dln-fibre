# Statement card — Object E / P6 combinatorial half, Tier 1 (banded-interval combinatorics)

Seat: seat-E (lean-formaliser). Branch `expedition/aoyagi-engine-E`. Module
`lean/DLNFibre/Core/Aoyagi/OrderCount.lean`. Elder three-tier split (journal 2026-07-21): this is
**Tier 1** — the abstract `(ℓ, a)` banded-interval combinatorics, `Core`-pure (Mathlib-only leaf).
θ-name / certified selector objects / tree-ledger are Tiers 2–3 (not here).

---

> **Claim (fidelity anchor).** The per-`j` interval cardinality `#{H : H̃_j ≤ H ≤ H̃'_j}` of Aoyagi
> p.26 equals `min(j, a, ℓ−a, ℓ−j) + 1`, i.e. the closed `min`-form agrees with the paper's printed
> three-range piecewise cardinality (for `a ≤ ℓ`, `j ≤ ℓ`).
>
> - **Lean:** `DLNFibre.Core.Aoyagi.OrderCount.perJCard_eq_paper`
>   (`lean/DLNFibre/Core/Aoyagi/OrderCount.lean` @ `46f12b577`)
> - **Gloss.** `perJCard ℓ a j = perJCardPaper ℓ a j`, where `perJCard = min(min j a)(min(ℓ−a)(ℓ−j)) + 1`
>   and `perJCardPaper` is the verbatim p.26 piecewise: `j+1` for `j ≤ min{a,ℓ−a}`; `min{a,ℓ−a}+1`
>   for `min{a,ℓ−a} < j ≤ max{a,ℓ−a}`; `min{a,ℓ−a}+1+max{a,ℓ−a}−j` for `max{a,ℓ−a} < j ≤ ℓ`.
> - **Proved.** The two forms are equal on `a ≤ ℓ`, `j ≤ ℓ` (`split_ifs <;> omega`). Axiom-clean.
> - **Assumed.** `a ≤ ℓ`, `j ≤ ℓ` (the paper's index range).
> - **Cited.** none.
> - **Deferred.** none.
> - **Status.** sorry-free.

> **Claim (band-area core).** The sum of the band widths is `a(ℓ−a)`:
> `∑_{j=0}^{ℓ} min(j, a, ℓ−a, ℓ−j) = a(ℓ−a)` (for `a ≤ ℓ`). Width-independent — the shared
> partial-sum term `∑_{l=1}^{j+1} M^{(S_l)}` and the integer `M = M*` cancel in `H̃'_j − H̃_j`.
>
> - **Lean:** `DLNFibre.Core.Aoyagi.OrderCount.bandWidth_sum`
>   (`lean/DLNFibre/Core/Aoyagi/OrderCount.lean` @ `46f12b577`)
> - **Gloss.** `∑ j ∈ Finset.range (ℓ+1), bandWidth ℓ a j = a * (ℓ − a)`, `bandWidth` the `min`-of-four.
> - **Proved.** Unconditional on `a ≤ ℓ`. Proof: double-count `bandWidth = #{i∈[1,m] : i≤j ∧ i≤ℓ−j}`
>   with `m = min(a, ℓ−a)`, `Finset.sum_comm`, inner count `#{j : i≤j≤ℓ−i} = ℓ+1−2i`, and the helper
>   `sum_Icc_linear : ∑_{i=1}^{m}(ℓ+1−2i) = m(ℓ−m)` (`2m ≤ ℓ`). Axiom-clean.
> - **Assumed.** `a ≤ ℓ`.
> - **Cited.** none.
> - **Deferred.** none.
> - **Status.** sorry-free.

> **Claim (Tier-1 headline).** The banded-interval count is `a(ℓ−a)+1`:
> `bandCount ℓ a = a(ℓ−a)+1` (for `a ≤ ℓ`), where `bandCount = (band area) + 1` (the `+1` is the
> single terminal branch, the Case-1(2) `J`-increment).
>
> - **Lean:** `DLNFibre.Core.Aoyagi.OrderCount.bandCount_eq`
>   (`lean/DLNFibre/Core/Aoyagi/OrderCount.lean` @ `46f12b577`)
> - **Gloss.** `bandCount ℓ a = a * (ℓ − a) + 1`.
> - **Proved.** Unconditional on `a ≤ ℓ` (immediate from `bandWidth_sum`). Kill-set by `decide` on the
>   DEFINITION: `bandCount 2 2 = 1`, `2 1 = 2`, `3 2 = 3`, `4 2 = 5`; edges `1 0 = 1`, `1 1 = 1`,
>   `5 0 = 1`, `5 5 = 1`. Axiom-clean.
> - **Assumed.** `a ≤ ℓ`.
> - **Cited.** none.
> - **Deferred.** **(named, NOT asserted anywhere in the module):** (i) that `bandCount` equals the
>   true count of RLCT-attaining binding branch-vectors — Aoyagi Lemma 5's loose two-sided argument
>   (union upper bound + Case-1(2) + explicit construction); this is task #39's pen-and-paper
>   adjudication (the exact count-object), and Tier 2/3's binding. (ii) that this count equals the
>   analytic zeta-pole multiplicity `ρ` — needs meromorphic continuation Mathlib lacks (monument-class).
> - **Status.** sorry-free; framing awaiting elder ratification (does the deferred-seam framing satisfy K4?).

---

## Fidelity findings (seat-E, numerics-verified; sent to team-lead/elder at SPECIFY)

- The per-`j` three-range cardinality = `min(j,a,ℓ−a,ℓ−j)+1` exactly (checked vs the p.25–26 images).
- **`a(ℓ−a)+1` is NOT a clean single band cardinality.** The raw per-`j` sum `∑(bandWidth+1)`
  OVERCOUNTS (`ℓ=4,a=2 → 7 ≠ 5`); the union `|⋃_j [H̃_j,H̃'_j]|+1` is width-DEPENDENT (`{4,6,7,8}` at
  `ℓ=4,a=2`). Only the band-**area** `∑ bandWidth = a(ℓ−a)` is intrinsic. So Lemma 4's envelope+increment
  (sufficient) is met by all `C(ℓ,a)` step-arrangements (≠ `a(ℓ−a)+1`). Consistent with
  `verify-repro-s4s5.md` (which does not certify a clean single-count).
- The terminal equality `H̃_ℓ = H̃'_ℓ = 0` needs Def-3 consistency (`P, M*, a` relations) — NOT pure
  `(ℓ,a)`; so the explicit envelopes (which use the width/`M*` data) belong at **Tier 2**, and the
  width-independence theorem `H̃'_j − H̃_j = bandWidth ℓ a j` is the Tier-1↔Tier-2 bridge (built when
  Tier 2 exists).

## Cross-checks (ground truth)

- Selector values (Def-3 `(ℓ,a)` bound at Tier 2): `(2,2,2)→(2,2)→1`, `(2,1,2)→(2,1)→2`,
  `(2,2,2,2)→(3,2)→3`, ThetaOrderDistinction `(4,2)→5`.
- Tree-ρ ground truth (thread-37 traversal, for Tier-2/3): `(2,2,2)→1`, `(3,3,4)→1` [minAdm=8],
  `(2,2,3,2)→1`, `(2,2,2,2)→3`. `ρ = max-over-leaves per-leaf min-achiever count = distinct
  min-achieving binding profiles`; naive Adm-minimiser count DIVERGES at 6 instances (`[3,3,1,1]`:
  naive 2 vs true 1) — the object task #39 pins.
