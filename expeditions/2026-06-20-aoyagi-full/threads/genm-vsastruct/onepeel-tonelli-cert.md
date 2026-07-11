# genm-vsastruct — the (3,3,3,4) ONE-PEEL Tonelli finiteness (DecoratedPeelStep body)

**Seat:** pen-and-paper (design + obstruction). **Date:** 2026-07-11. **NO Lean.** **Charge:** nail the
(3,3,3,4) one-peel decorated finiteness = the fixed-A₂ corner slice integrated over the deep data; does the
JOINT integral close at 7/2, and is the A₂-rank-drop rescued by codim or a binding deeper stratum?
**Exact algebra:** `/tmp/onepeel_tonelli.py` (slice divergence rate + A₂-codim rescue, MC-confirmed).
**Decorrelated:** `codex/tonelli-{prompt,answer}.md` (gpt-5.6, xhigh; my lean withheld — it CONFIRMED the
rescue thresholds and sharpened the correlation + the endpoint). Companions: `corner334`/`t4-merge-derisk`
(the sector slice `sjSlice_corner_two_block_lt_top`), `dps-instance-cert` (the fixed-slice +∞ where a unit
vanishes).

---

## ONE-LINE VERDICT

**The (3,3,3,4) one-peel joint integral CLOSES at `c' < 7/2` (strict). The A₂-integration RESCUES the
fixed-slice rank-drop divergence by codimension compensation — every rank-drop tube is NON-binding
(`{U₁=0}`→`c'<4`, `{U₀=0}`→`c'<11/2`, `{A₂=0}`→`c'<6`, all `> 7/2`), with no hidden mixed/rank-2 threshold
(Codex correlation check). The binding `7/2` is the SECTOR corner slice ITSELF (`sjSlice_corner_two_block`);
literally at `c'=7/2` the slice diverges `∫r^{−1}` (the strict `<` is honest). So NO separate deeper (S,J)
peel is analytically required for the A₂-rank-drop — the complement is closed by a codim-rescue norm-power
(Morse) integral `∫‖v̄A₂‖^{−s}dA₂ < ∞ ⟺ s < codim`, banked-adjacent. This SIMPLIFIES (refines) the earlier
"explicit deeper-stratum" framing: the complement is a Morse rescue, not a recursion. BUILDABLE from
`{sector slice + Tonelli over A₂ + the codim-rescue}`.**

---

## 1. The Tonelli assembly — closes at 7/2 (strict); A₂-integration rescues the rank-drop

The one-peel integral is `∫_{deep data} S(U₀,U₁; c') dμ`, `S` the fixed-A₂ corner slice
`∫∫_{[0,1]²} u₀³u₁² (u₀²U₀+u₁²U₁)^{−c'} du₀du₁`, deep data `(A₂ 3×4, v̄,w₁,w₂ unit 3-vectors, δ,a_piv)`,
`U₁ = a_piv²‖v̄A₂‖²`, `U₀ = ‖w₁A₂‖²+δ²‖w₂A₂‖²`.

**The slice per-point (sector `U₀,U₁>0`):** finite ⟺ `c' < (h₀+h₁+2)/2 = (3+2+2)/2 = 7/2`
(`sjSlice_corner_two_block_lt_top`, banked). **At `c'=7/2` it DIVERGES** (`∫r^{−1}`, endpoint) — so the
one-peel threshold is STRICT `c'<7/2`, and the endpoint divergence is the GENERIC slice, not a rank-drop.
[FACT — banked + Codex.]

**The slice DIVERGES as a unit → 0** (exact, MC-confirmed `onepeel_tonelli.py`: exponents 1.20, 1.70 at
`c'=3.2`):
`S ≍ U₁^{−(c'−2)}` as `U₁→0` (the `u₀`-only corner, threshold `(3+1)/2=2`); `S ≍ U₀^{−(c'−3/2)}` as
`U₀→0` (the `u₁`-only corner, threshold `(2+1)/2=3/2`). [FACT.]

**The A₂-integration RESCUES each rank-drop tube** (codim compensation; `∫U_k^{−(div)}·U_k^{d_k/2−1}dU_k`):

| tube | zero-locus | codim `d` | slice div. | rescue threshold `c' <` |
|---|---|---|---|---|
| `{U₁=0}` | `{v̄A₂=0}`, `v̄A₂∈ℝ⁴` | **4** (MC: density ≈`U₁^{1.92}`) | `U₁^{−(c'−2)}` | `2 + d/2 = 4` |
| `{U₀=0}` | `{w₁A₂=w₂A₂=0}`, `∈ℝ⁸` | **8** | `U₀^{−(c'−3/2)}` | `3/2 + d/2 = 11/2` |
| `{A₂=0}` | `‖A₂‖²→0`, `∈ℝ^{12}` | **12** | `‖A₂‖^{−2c'}` | `d/2 = 6` |

All rescue thresholds `> 7/2` ⟹ **every rank-drop tube is NON-binding**; the binding `7/2` is the sector
slice. [FACT — exact + MC; Codex-confirmed term-for-term.] Equivalently (Morse–Bott form): in the normal
coords `z = v̄A₂ ∈ ℝ⁴` the singularity is `‖z‖^{−s}`, `s = 2(c'−2)`, and `∫_{‖z‖<ε}‖z‖^{−s}dz < ∞ ⟺ s<4 ⟺
c'<4`.

## 2. The correlation is BENIGN — no hidden mixed / rank-2 threshold (Codex refinement)

My initial "both units vanish on the rank-drop locus" was imprecise. Sharpened [FACT — Codex]:
`{U₁=0} = {v̄A₂=0}` has generic rank 2 (leftker `= ℝv̄`); `{U₀=0} = {W ⊆ ker A₂ᵀ}` with `dim W=2` **forces
rank A₂ ≤ 1**. So **at a nonzero rank-2 point `U₀ > 0`** — only `U₁` vanishes there (threshold `c'<4`).
In the clean joint coordinates `X=(w₁A₂,δw₂A₂)∈ℝ⁸`, `Z=a_piv·v̄A₂∈ℝ⁴` (`U₀≍‖X‖²`, `U₁≍‖Z‖²`, simultaneous
vanishing ⟺ `A₂=0`), with deep measure `R⁷T³dRdT` (`R=‖X‖`, `T=‖Z‖`):

| sector | `S` | binding constraint |
|---|---|---|
| `T ≤ R` | `R^{−4}T^{4−2c'}` | `c' < 4` |
| `R ≤ T` | `R^{3−2c'}T^{−3}` | `c' < 11/2` |

Strongest deep constraint `c' < 4 > 7/2`. Even the exceptional `v̄∈W` case (transverse dim 8,
`‖X‖^{−2c'}`) gives `c'<4`. **No mixed / rank-2 stratum binds at `7/2`.** [FACT — Codex, exact.]

## 3. The deeper stratum — NON-binding, closed by codim-rescue (NOT a deeper peel)

The A₂-rank-drop complement (`{U_k < a}`, where `sjSlice_corner_two_block`'s hypotheses fail) is
**non-binding** (§1–2, rescued to `c'<4`). It does NOT require a separate deeper (S,J) peel for finiteness —
it is closed by the **codim-rescue norm-power (Morse) integral** `∫‖v̄A₂‖^{−2(c'−2)}dA₂ < ∞ ⟺ 2(c'−2)<4`,
a `Fin 4` Morse integral (banked-adjacent: `morseBox_sumSq_lt_top` / `sumSqND_box_lt_top` /
`lintegral_norm_rpow_neg_ball_lt_top`). **This REFINES the earlier certs' "explicit A₂-rank-drop
stratification → deeper stratum" (dps-instance §5, t4-merge §2): the complement is a Morse rescue, not a
recursion.** The coupling that could RLCT-collapse (independent scalar split → 3/2) is inside the SECTOR
slice, correctly handled by `sjSlice_corner_two_block`'s codims-add AM-GM (→7/2); the A₂-rank-drop is a
distinct, rescued matter. So there is no genuine deeper-corank binding stratum at (3,3,3,4). (Consistency:
the deepest corank-3 branch `{A₂=0}`→`c'<6` matches the `verdict.md` codim-3 non-binding `c'<4` reading —
both `>7/2`.) [FACT+INFERENCE — Codex: "no separate deeper resolution is analytically required for
finiteness in this concrete model, though a proof may still stratify the rank-drop tubes."]

## 4. VERDICT for the formaliser — BUILDABLE; the assembly

The (3,3,3,4) one-peel finiteness (`c'<7/2`) is BUILDABLE from banked + banked-adjacent pieces:

1. **Tonelli split:** `one-peel = ∫_{deep data (A₂, redChain residuals)} S(U₀(·),U₁(·)) dμ` (Fubini–Tonelli
   over the block-additive corner slice × the deep data). [measure plumbing]
2. **Sector `{U₀,U₁ ≥ a > 0}`:** the corner slice is bounded (`sjSlice_corner_two_block_lt_top (3,2)`,
   threshold `7/2`); `∫_{sector} S dμ ≤ (sup S)·vol < ∞`. [banked endpoint]
3. **Complement `{U_k < a}` (the A₂-rank-drop):** the codim-rescue — `S ≲ U₁^{−(c'−2)}` (resp.
   `U₀^{−(c'−3/2)}`) and `∫ ‖v̄A₂‖^{−2(c'−2)} dA₂ < ∞` for `c'<4` (resp. `∫‖(w₁A₂,w₂A₂)‖^{−2(c'−3/2)} < ∞`
   for `c'<11/2`), a `Fin 4` / `Fin 8` Morse norm-power integral. [banked-adjacent Morse]
4. **Cast `U₀,U₁` as `‖deep-linear-image‖²`** (`U₁=a_piv²‖v̄A₂‖²`, `U₀=‖w₁A₂‖²+δ²‖w₂A₂‖²`) so the codim =
   the rank of the linear map `A₂ ↦ (v̄A₂, w_iA₂)` (= 4, 8 for generic `v̄,w`). [carrier / chart algebra]

**Genuinely-new (buildable-as-labour, NO new constructor):** the Tonelli assembly (1); the codim-rescue
Morse lemma (3) — a norm-power integral over the deep matrix, reducible to the banked `morseBox_sumSq`
family (the deep-matrix analogue of `qbox`/`detGram`); the sector/complement cover (2)+(3); the
unit-as-norm casting (4). NOTHING here is a new carrier primitive.

### Firmest / most-likely-to-break / next
- **Firmest.** Joint closes at strict `c'<7/2`; A₂-rank-drop rescued (`{U₁=0}`→4, `{U₀=0}`→11/2,
  `{A₂=0}`→6, all `>7/2`); no mixed/rank-2 threshold; the `7/2` endpoint diverges via the SECTOR slice.
  Exact + MC + decorrelated-confirmed term-for-term.
- **Most likely to break.** The codim-rescue relies on the vanishing-locus codim being FULL (`d₁=4`, `d₀=8`)
  = the deep linear maps `A₂↦v̄A₂`, `A₂↦w_iA₂` having full rank. For generic `v̄,w` this holds; the build's
  admissible class must ensure the recursion does NOT force `v̄,w` into a degenerate (rank-deficient)
  configuration that lowers the codim (which would tighten the rescue — though it would need to drop below
  `7/2`, i.e. codim `d₁ < 3` for `U₁`, to bind). Width-general: the rescue codim is the product-rank tube
  codim (task #116 `D_prod`); for (3,3,3,4) it is the free-matrix codim (4,8), safely `>` the binding.
- **Next.** Feed §4 to the T4 formaliser as the (3,3,3,4) one-peel body: sector via
  `sjSlice_corner_two_block_lt_top`, complement via the codim-rescue Morse lemma (build it as a
  deep-matrix norm-power integral on the banked `morseBox_sumSq` family). The A₂-rank-drop is a Morse
  rescue, NOT a deeper peel — so the one-peel closes (3,3,3,4) directly without a redChain-IH detour for the
  rank-drop. The admissible-class closure + `m>2` remain the follow-on (per t4-merge §5).
