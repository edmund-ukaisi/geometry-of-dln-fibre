# Red-team certificate: Aoyagi (2023) Definition 3 — the `≤` defect + the geometric `Mval_min` fix

Seat: `pen-and-paper`. All arithmetic is **exact integer / `Fraction`** (Python `fractions`), no floats.
Decorrelated `local-codex-consult` (gpt-5.x, xhigh) run twice as independent search.

**SOURCE OF TRUTH = the page images** `theory/aoyagi-2023-reproduction/pages/p*.png`, read visually.
The pdf→text extraction (`aoyagi-2023-extracted-text.txt`) **garbles a load-bearing inequality
direction** and was the cause of the original (now-superseded) "ambiguity" reading.

Pages verified visually: Def 3 (p08), Theorem 2 (p09), the L=2 / Theorem-1 case definition (p07).

## Definitions, as read from the images (authoritative)

**Definition 3 (p08).** Reduced widths `M^(s)=H^(s)−r`, `s=1..L+1`. Select
`calM = {M^(S_1),…,M^(S_{ℓ+1})}` (sub-multiset), `S = Σ_{k=1}^{ℓ+1} M^(S_k)`, such that
- (i)  `M^(S_j) < M^(s)`            for `M^(s) ∉ calM`  (selected strictly below excluded);
- (ii) `S > ℓ·M^(s)`                for `M^(s) ∈ calM`;
- (iii) **`S ≤ (ℓ−1)·M^(s)`**        for `M^(s) ∉ calM`.

Then `M* = ⌈S/ℓ⌉`, `a = S − (M*−1)ℓ`.

> **CORRECTION to the prior cert and the worked `.tex`.** Both used (iii) as `S ≥ (ℓ−1)M^(s)`.
> The image shows **`≤`** unambiguously (high-res crop `/tmp/p08_def3_crop.png`). This flips the
> entire analysis. The earlier "multiple-valid-`calM` ambiguity" was a *phantom of the bad `≥`
> extraction*; the real defect is different and is shown below.

**Theorem 2 (p09).** `λ = (−r²+r(H^(1)+H^(L+1)))/2 + a(ℓ−a)/(4ℓ) − (ℓ(ℓ−1)/4)(S/ℓ)² + ½Σ_{i<j}M^(S_i)M^(S_j)`,
`θ = a(ℓ−a)+1`. Verified term-by-term against the image; my `thm2_core` (the expression minus the
prefactor) is correct.

**L=2 / Theorem 1 case definition (p07), total & unambiguous.** With three widths,
`calM = {1,2,3}` if every `M^(s) < ½ΣM`; else `{1,2}` if `M^(3) ≥ M^(1)+M^(2)`; `{1,3}` if
`M^(2) ≥ M^(1)+M^(3)`; `{2,3}` if `M^(1) ≥ M^(2)+M^(3)`. (Drop the *large* excluded width.)

Census ranges (exact enumeration): L=2 (w 1..6/8), L=3 (w 1..5), L=4 (w 1..4).

---

## THE DEFECT (Check 1, corrected): condition (iii) `≤` contradicts the paper's own L=2 case

**(A) With the true `≤`, Definition 3 is EMPTY on the majority of width vectors** and **unambiguous
where nonempty.**

| census | no valid `calM` | multiple `calM` | truly ambiguous |
|---|---|---|---|
| L=2 (216) | **105** | 0 | 0 |
| L=3 (625) | **476** | 0 | 0 |
| L=4 (1024) | **860** | 0 | 0 |

So the prior cert's "ambiguity / multiple `calM`" finding is **withdrawn** — it was entirely an
artifact of the `≥` mis-extraction. The true `≤` pins a unique set (when one exists); the genuine
defect is non-totality.

**(B) The `≤` is inconsistent with the paper's verified L=2 special case.** The L=2 definition (p07,
total, ground truth) selects `calM={1,2}` exactly when `M^(3) ≥ M^(1)+M^(2)` — dropping a *large*
excluded width. But general Def-3 (iii) at `ℓ=1` demands `S ≤ (ℓ−1)M^(s) = 0`, **impossible** for
positive widths. So general Def-3 with `≤` rejects the very set the paper's own L=2 case selects.

Witness `M=[1,1,3]`: L2 case gives `calM={1,1}`, `ℓ=1` (correct RLCT). General Def-3 (iii) needs
`1+1 ≤ 0` — false. General Def-3 is **empty** here. Confirmed: on the 216 L=2 vectors, general Def-3
(`≤`) is empty on 105, all of which the L=2 case handles correctly.

**(C) Neither raw direction is a complete repair** (decorrelated Codex agrees, independently):
- `≤` (printed): over-tight → empty on the majority, contradicts L=2.
- `≥` (the mis-extraction): at `ℓ=1` becomes `S ≥ 0`, always true → restores L=2 consistency
  (general-`≥` max-ℓ reproduces the L=2 case exactly, **0 mismatches over 512 vectors, never empty**),
  but `≥` is *loose*: it admits spurious low-ℓ active sets, so `ℓ` is not pinned (the phantom
  ambiguity of the prior cert).

Mechanism: the inequalities are an active-set / balancing characterization; the boundary direction and
strictness are transcription-fragile. The correct selection is "the `ℓ+1` smallest reduced widths for
the `ℓ` that balances the partition" — which the inequalities try, and fail, to pin.

## Check 2 — `Mval_min` totality: PASS (structural)

`Mval(t) = (M^(1)−t_1)(M^(2)−t_1) + Σ_{j=2}^{L}(t_{j−1}−t_j)(M^(j+1)−t_j)`; admissible `t` weakly
decreasing, `0 ≤ t_s ≤ min(M^(1),…,M^(s+1))`, **`t_L=0`**. `Mval_min = min_t Mval(t)`.

The all-zeros profile is always admissible, `Mval(0,…,0) = M^(1)·M^(2)`, lattice finite & nonempty ⇒
min attained, `Mval_min ≤ M^(1)·M^(2) < ∞` on **every** width vector — including all
empty-Def-3 vectors. `t_L=0` is load-bearing (without it the min is trivially 0). Codex confirms
`t_L=0` is forced by the resolution's terminal zero fiber (`H_ℓ=0`).

## Check 3 — Agreement `½·Mval_min` = the correct RLCT: PASS, and it FIXES the defect

- Where general Def-3 (`≤`) is nonempty, `½·Mval_min` = its closed form exactly (0 disagreements:
  L=2 111/111, L=3 149/149, L=4 164/164).
- **Crucially, on ALL 216 L=2 vectors — including the 105 where `≤`-Def-3 is empty —
  `½·Mval_min` equals the paper's own total L=2 ground-truth RLCT (0 mismatches).** This is the
  load-bearing certificate: the geometric primitive gives the right answer *precisely where Definition
  3 fails*.
- The L=2 fixed definition agrees with `½·Mval_min` on all 216/216.

## Check 4 — Clean internal form: PASS

`Mval_min = ½(Σ_{i=1}^{ℓ} q_i² − Σ_{k=1}^{ℓ+1} m_k²)`, `m` = `ℓ+1` smallest reduced widths, `q` the
balanced `ℓ`-split of `P=Σ m_k`, `ℓ+1` the balancing size. 0 failures across the censuses and sampled
L=5,6. (Equality is `Mval_min == clean_form`, i.e. `2·rlct_core == clean_form`.)

## BONUS — `Mval_min` is permutation-invariant

`Mval(t)` is not manifestly symmetric (it singles out `M^(1),M^(2)`), yet `Mval_min` is identical on
every ordering of a width multiset — 0 violations across L=2,3,4. Matches the paper's headline
permutation invariance; licenses sorting in the Lean `aoyagiLambda`.

---

## Bottom line for the typo ledger + Lean `aoyagiLambda`

- **TYPO (genuine paper defect, not extraction): Definition 3 condition (iii) `S ≤ (ℓ−1)M^(s)`.**
  As printed it is empty on the majority of inputs and contradicts the paper's own (correct, total)
  L=2 special case. Reversing to `≥` restores L=2 consistency but is then ambiguous in `ℓ`. The
  inequalities are a fragile active-set characterization; **neither direction is a clean primitive.**
- **Fix (sound, certified): take `rlct_core := ½·Mval_min` as primitive.** It is total,
  permutation-invariant, equals the paper's L=2 ground truth on every vector (incl. all empty-Def-3
  ones), equals the general closed form wherever Def-3 is nonempty, and equals the clean form. Def-3
  becomes a derived consequence on its (defective) valid locus. `t_L=0` must be in the Lean lattice.
- **For Lean:** define `aoyagiLambda = prefactor + ½·Mval_min` (or the `lambdaCore` clean form);
  do **not** transcribe Definition 3's inequalities as the definition.

### Caveats (next to the claim)

- Agreement (Check 3) and the clean form (Check 4) are verified by **exact enumeration over finite
  censuses** (L≤6, bounded widths), and against the paper's *total* L=2 ground truth for all L=2. The
  general-`L` agreement is the geometric theorem (`codim S(t)=Mval` / resolution) the expedition still
  owes; it is not proven here. Totality (Check 2) and the L=2 contradiction (Check 1B) **are**
  structural/derived, not census-bound.
- That `≤` is a *typo* for `≥` (vs a deeper mis-statement) is an **inference** from L=2 consistency
  (Codex concurs); the paper's text as printed is `≤`. The "smallest-set at the balancing `ℓ`" reading
  is inferred authorial intent, confirmed on every census case.
- Permutation invariance of `Mval_min` is **empirically certified** over the censuses; no proof here.

### Provenance

Image crops: `/tmp/p08_def3_crop.png`, `/tmp/p08_full_def3.png`, `/tmp/p09_thm2.png`, p07 read inline.
Scripts (exact-arithmetic, reproducible): `/tmp/aoyagi_correct.py`, `/tmp/reconcile_L2.py`,
`/tmp/final_reconcile.py`, `/tmp/totality.py`, `/tmp/perm.py`. Codex artefacts:
`/tmp/codex_consult/def3-le-{prompt,answer}.md` (corrected reading), `…/def3-{prompt,answer}.md`
(initial, superseded `≥` reading).
