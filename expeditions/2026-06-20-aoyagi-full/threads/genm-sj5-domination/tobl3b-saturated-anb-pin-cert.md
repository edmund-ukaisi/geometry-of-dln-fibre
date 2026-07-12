# T-Obl3b saturated-shell pin cert — the `a≠b` surviving-corank domination at `(3,4,4)@t★`

**Seat:** pen-and-paper WITNESS (pin + adversarial stress-test), genm-sj5-domination. **Date:**
2026-07-12. **NO Lean, NO build.** Exact algebra (exact-`ℕ` `minAdmRec`/`redChain` recursion + charge
telescoping; freed-corner Gaussian-peel exponent by exact scaling / MC guide). Decorrelated
`local-codex-consult` (xhigh, conclusion WITHHELD): `codex/tobl3b-saturated-anb-{prompt,answer}.md`.
Reproducible scripts: `scripts/tobl3b/saturated_anb.py` (charge sweep + boundary), `scripts/tobl3b/
peel_exponent.py` (peel exponent → 0 at saturation).

**Anchor:** `(3,4,4)` — `M₀=3, M₁=4, M₂=4`, `minAdm=10`, `carrierThreshold=5`. Binding cuts `t★∈{1,2}`
(both give `minAdm=10`). At `t★=1`: `a=M₀−t★=2`, `b=M₁−t★=3`, `r=min(a,b)=2=a`, so `a<b` and `b−a=1`
**surviving corank row**. At `t★=2`: `a=1, b=2, r=1=a`, again `b−a=1`. This is the minimal `a≠b`
anchor — exactly ONE surviving corank row — the one corner the `(3,3,3)` `a=b=2` pin left untested.

**Consumed / read:** `tobl3b-pin-cert.md` (§2 reduced-weight, §5 saturated-shell remark + its flagged
`a≠b` green-gate); `final-assembly-design-cert.md` (§Obl-3b, §2 charge telescoping, §5 build tiles + the
single-`ε` correction); the LANDED `RouteMSJOnePeel334` (`cornerSliceAtUnits_le` + `sumSqND_box_lt_top`
— the Morse codim-rescue); `cornerComparator_adm` / `exists_cornerComparator_adm` / `cornerComparator_
decLoss` (`RouteMSJCornerComparator`); `freedSchurLoss_inner_peel_le` / `_bounded_le` (the atom bricks);
`minAdm_redChain_succ_ge` (`RouteMSJTransversality`), `carrierThreshold_shift` (`RouteMSJDecorated`),
`exists_binding_cut`; `RouteMSJSigMin.minStretch`; `redChain` / `minAdmRec` / `peelCharge`
(`RouteMLayerSplit`, `RouteMSJDecoratedCharge`).

---

## ★ VERDICT — the `a≠b` saturated shell CLOSES. No obstruction. Decorrelated-Codex-confirmed.

**The surviving-`(b−a)`-corank domination at saturation closes cleanly, for `c' < carrierThreshold(M)=
½·minAdm(M)`.** The one structural difference from the `a=b` anchor — the `b−a` corank rows the minor
CoV cannot reach — is **inert**: at the saturated shell the freed-corner peel frees `a−r=0` rows, so
its Gram-divisor exponent is `(a−r)/2 = 0` and the surviving-row weight is the **constant `1`**
(`Real.rpow_zero`), not a `det^{−½}` divisor. The surviving rows integrate over their bounded box
against `1` → a finite box factor; the deeper comparator at cut `t★+r = min(M₀,M₁)` carries the full
charge `C_r = minAdm(redChain(t★+r) M) ≥ minAdm(M)` (banked convexity) via its OWN Morse codim-rescue
(the LANDED `sumSqND_box_lt_top` pattern). No divergence, no undershoot.

```
SATURATED SHELL j=r=min(a,b) (a<b at the anchor):
  freed corner (a−r)×(b−r) = 0×(b−a)  →  #freed rows p = a−r = 0
  → freed-corner Gram exponent p/2 = 0  → surviving-(b−a)-corank weight = det(G_surv)^0 ≡ 1  (NO divisor)
  → surviving rows: ∫_box 1 = vol(box) < ∞  UNIFORMLY (even Q_U=0 / Z=0 / genuine rank-drop)
  → deeper comparator cornerComparator(redChain(t★+r) M) at exponent e_r = c'−0 = c'
     closed by arity-(L+1) decorated IH; its {Z→0} tube by the OnePeel334 Morse rescue (F4)
  CHARGE  C_r = 0 + minAdm(redChain(t★+r) M) ≥ minAdm(M)   [convexity telescoping, 0/3303 undershoots]
  BOUNDARY  t★+r = min(M₀,M₁)  → cuts t★+j, j>r, are ILLEGAL (redChain bottoms out)  [0/3303 violations]
```

---

## 1. THE SATURATED-SHELL INTEGRAND (task #1) — surviving-row weight × deeper comparator

**Setup at `(3,4,4)@t★=1`.** `a=2, b=3, r=2`. Freed corner `Γ∈box(a×b)=box(2×3)`; corank block
`A_cor∈box(b×M₂)=box(3×4)`; `Q_b=A_cor·Z` (`b×m=3×m`); deeper product `Z∈box(M₂×m)=box(4×m)`, `rank Z`
may drop. The Γ-first peel couples `Γ` to the tail only through `Γ·Q_b`.

**The freed-corner Gaussian peel (banked atom, `freedSchurLoss_inner_peel_le`).** Integrating a `p×b`
corner against a full-row-rank `b×m` matrix `Q` gives
`∫(w+‖C+Γ·Q‖²_F)^{−c'}dΓ = const·det(QQᵀ)^{−p/2}·(tail)^{−(c'−½pb)}` — the **Gram-divisor exponent is
`p/2` with `p =` number of FREED (peeled) rows.** Exact scaling law `I(λQ)/I(Q)=λ^{−pb}` (⟺ exponent
`p/2`) confirmed for `p=2,1,0` (`scripts/tobl3b/peel_exponent.py`, `b=3`): at `p=0` the ratio is exactly
`1.0` — the empty corner integrates to `(tail)^{−c'}` with **no det weight**.

**At the saturated shell `j=r=a` (`a<b`).** The nested peel at the deeper cut `t★+j` frees an
`(a−j)×(b−j)` corner; at `j=r=a` this is `0×(b−a) = 0×1` — **`p = a−r = 0` freed rows**. Hence the
leftover det-Gram weight over the `b−a` **surviving** corank rows (in the `M₂−r` strong subspace) is

> **`det(G_surv)^{−(a−r)/2} = det(G_surv)^0 ≡ 1`   (`Real.rpow_zero`; the ABSENT factor of the `p=0`
> peel, NOT a singular `0^0`).**

So the exact leftover integrand form (task #1) — surviving-row weight × deeper comparator — is:

> **`(saturated-shell integrand) ≤ const(ε) · [∫_{A_surv∈box((b−a)×(M₂−r))} 1 · dA_surv] ·
> (cornerComparator(redChain(t★+r) M) k jc integrand at exponent e_r = c'−½(a−r)(b−r) = c')`**,

i.e. `const(ε) · vol(box_{surv}) · (deeper comparator at c')`. The `[∫ 1]` factor is the surviving-row
Gram weight collapsed to its exponent-0 value; the fully-collapsed strong block is read by the deeper
comparator. This matches the tobl3b-pin §2 reduced-weight formula at `j=r`: "`(b−j)` corank rows in the
`(M₂−j)`-strong subspace with exponent `(a−j)/2`" specialised to `j=r=a` — `(b−a)` rows, exponent `0`.

**The contrast with the `a=b` anchor (`(3,3,3)@t★=1`, `a=b=2`).** There `b−a=0`, no surviving rows;
`A_cor` and `Γ` "fully absorb". The `a≠b` novelty is precisely the `b−a` unabsorbed corank rows — and
they enter with exponent-0 weight, so they are inert (a finite box factor), not a new singularity.

## 2. THE MORSE CODIM-RESCUE CLOSES IT (task #2) — no minor CoV, charge at `(3,4,4)`

**Why no minor CoV.** At `j=r` all `r` minor-peelable levels are exhausted; the freed corner is empty
(`p=0`) so there is **no Gram divisor to control** — the minor chart is not needed, and genuinely fails
(the `(M₂−r)`-minor can be `≤δ` for `Z→0`, no uniform inverse-Jacobian). The mechanism is instead the
deeper comparator's own **Morse codim-rescue**, the LANDED `RouteMSJOnePeel334` pattern:
`cornerSliceAtUnits_le` (weighted-AM-GM decoupling) + `sumSqND_box_lt_top` (the deep Morse integral
`∫_box(∑X²)^{−w·c'} < ∞` near the origin ⟺ codim large enough). The `{Z→0}` tube (incl. genuine
rank-drops, lumped into `S_r`) is closed HERE — not by a chart, by codimension.

**The surviving rows do not break it.** The `b−a` surviving corank rows contribute a bounded,
constant-weight (`≡1`) box factor **multiplying** the deeper comparator integral. A finite multiplicative
factor cannot break the comparator's finiteness. "Surviving-corank weight × comparator IH" is valid
**provided the weight is read as the constant `1`, not a hidden `det^{−½}`** (Codex Q1/Q2 sharpening,
preserved).

**Charge at `(3,4,4)` (task #2 "confirm the charge still ≥ minAdm(M)").** `minAdm(3,4,4)=10`,
`carrierThreshold=5`. At `t★=1`, `r=2`:

| shell `j` | cut `t★+j` | freed `(a−j)(b−j)` | `redChain` | `minAdm_red` | `C_j` | `C_j≥minAdm(=10)?` | Gram exp `(a−j)/2` |
|---|---|---|---|---|---|---|---|
| 0 | 1 | `2·3=6` | `(1,4)` | 4 | **10** | tight | `1` (borderline `a=M₂−b+1=2`, banked θ) |
| 1 | 2 | `1·2=2` | `(2,4)` | 8 | **10** | tight | `½` (strict conv `1<2`) |
| 2 = r | 3 | `0·1=0` | `(3,4)` | 12 | **12** | slack 2 | **`0`** (SATURATED, no minor) |

**Task #2 confirmed:** `C_r = (a−r)(b−r) + minAdm(redChain(t★+r) M) = 0 + minAdm(3,4) = 0 + 12 = 12 ≥ 10
= minAdm(M)`, with `a−r=0` so the freed corner charge is exactly `0` and ALL of `C_r` comes from the
deeper comparator. The comparator fires at `e_r = c' < 5 < 6 = carrierThreshold(3,4) = ½·minAdm(3,4)`,
so the arity-`(L+1)` decorated IH on the leaf `(3,4)` applies with strict margin. (At `t★=2`, `r=1`:
`C_r = 0 + minAdm(3,4) = 12 ≥ 10`, `e_r=c'<5<6` — identical.) Charges add via `carrierThreshold_shift`
+ `minAdm_redChain_succ_ge`.

## 3. THE SATURATION BOUNDARY `j=r=min(a,b)` IS THE RIGHT CUTOFF (task #3)

`t★+r = t★+min(a,b) = t★+min(M₀−t★, M₁−t★) = min(M₀,M₁)`. At `(3,4,4)`: `t★=1, r=2 → t★+r = 3 =
min(3,4)`; `t★=2, r=1 → t★+r = 3`. So the saturated cut is the **maximal legal cut**; any `t★+j` with
`j>r` gives `t★+j > min(M₀,M₁)`, illegal (`redChain` bottoms out — `minAdmRec`'s `t`-range is
`0..min(M₀,M₁)`). `(3,4,4)` bottoms cleanly at the leaf `redChain(3)(3,4,4) = (3,4)` (a `Fin 2` two-width
leaf, `minAdm = 3·4 = 12`). **Swept: `t★+r = min(M₀,M₁)` holds 3303/3303 binding-cut instances (arity
3/4/5, widths 1..6); 0 violations** (`scripts/tobl3b/saturated_anb.py`). The lumping shell `S_r` absorbs
ALL residual degeneracy (`≥r` small singular values), so no deeper cut is ever needed.

## 4. ADVERSARIAL — hunted for a surviving-corank divergence / undershoot (task #4)

- **Surviving-row box integral diverges?** NO. Its weight is `det(G_surv)^{−(a−r)/2}` with `a−r=0`
  (arithmetic, `r=min(a,b)=a` when `a<b`), i.e. the constant `1`. `∫_box 1 = vol(box) < ∞` **uniformly in
  every configuration** — `Q_U=0`, `Z=0`, genuine rank-drop. There is no exponent that can go negative:
  `a−r=0` is forced, not fine-tuned. (Setting `Z=0` makes `G_surv` singular, but `det(singular)^0 = 1`.)
- **Saturated charge undershoots `minAdm(M)`?** NO. `C_r = minAdm(redChain(t★+r) M) ≥ minAdm(M)` by the
  banked convexity telescoping (`minAdm_redChain_succ_ge` at each cut `t★+i`, telescoped `i=0..r−1`;
  `final-assembly-design-cert.md §2`), which holds **including when the freed corner is empty**. **Swept:
  0 undershoots / 3303 binding-cut instances; freed corner `(a−r)(b−r)=0` and surviving-side Gram
  exponent `min(a−r,b−r)/2 = 0` on ALL of them.**
- **★ The one genuine sharpening I found — the saturated charge CAN be TIGHT at `a≠b`.** The saturated
  slack `C_r − minAdm(M)` is `0` on **1060/2028** `a≠b` saturated instances (e.g. `(1,2,2)@t★=0`:
  `C_r=2=minAdm`). At `(3,4,4)` the slack is `2` (not tight). **This is NOT an obstruction:** the IH
  requirement is `e_r = c' < ½·C_r`, and `c' < carrierThreshold(M) = ½·minAdm(M) ≤ ½·C_r` is **STRICT**
  (the step hypothesis), so the IH fires even at slack 0 — the same strict-`c'` mechanism that makes the
  tight `j=0` binding cut work. No θ-interpolation is needed at the saturated shell (exponent 0, no
  borderline). So tightness is harmless.
- **The pointwise loss on the exact `{Z=0}` slice is `+∞` — does that leak?** NO (Codex-preserved
  inference-vs-fact distinction). The exact zero slice can have an infinite pointwise loss-power VALUE,
  but the surrounding JOINT integral is finite (the Morse rescue `sumSqND_box_lt_top`, F4). Infinite
  pointwise value on a measure-zero slice ≠ divergent integral. This is exactly the OnePeel334 mechanism
  (`{X→0}` closed by the deep Morse integral's integrability near the origin, not by a pointwise bound).

**No obstruction survived.** The `a≠b` saturated shell is sound.

## 5. DECORRELATED CODEX VERDICT (conclusion withheld in the prompt)

`codex/tobl3b-saturated-anb-{prompt,answer}.md` (xhigh; F1–F4 supplied — the peel exponent `p/2`, the
shell stratification, the charge/convexity fact, the OnePeel334 Morse rescue — my "CLOSES" conclusion
WITHHELD). **Codex verdict: CLOSES on all five, decorrelated.**
- **Q1 CLOSES** — independently reconstructed `p=a−r=0 ⟹ det(Q_UQ_Uᵀ)^0 ≡ 1` (the absent factor, not
  `0^0`); `∫_box 1 = vol < ∞` uniformly even when `Q_U=0`/`Z=0`/rank-drops. **Sharpening (preserved):
  the surviving-row "weight" is the constant `1`, NOT a hidden `det^{−½}` divisor** — the domination
  "surviving-corank weight × comparator IH" is valid under that reading.
- **Q2 CLOSES** — `e_r = c' < 5 < 6 = carrierThreshold(3,4)`; surviving rows are a finite-volume nuisance
  factor (or variables retained inside the reduced comparator), no extra determinant divisor; F4 supplies
  the `{Z→0}` joint integrability.
- **Q3 CLOSES** — `(a−r)(b−r)=0 ⟹ C_r = minAdm(redChain(t★+r) M) ≥ minAdm(M)` by F3 convexity, "including
  when the freed corner is empty; the zero corner is anticipated by the telescoping inequality."
- **Q4 CLOSES / no adversarial config** — cannot build either obstruction: `Z=0` gives exponent-0 weight
  `≡1`; undershoot would contradict F3. **Preserved distinction:** infinite pointwise loss on an exact
  zero slice ≠ under-charge or surviving-row divergence (F4 gives finite joint integral).
- **Q5 CLOSES** — `t★+r = min(M₀,M₁)`, cuts `j>r` illegal, bottoms at leaf `(3,4)` with threshold `6 >
  c'`. No inference of mine was fed in; the concurrence is decorrelated.

---

## 6. FOR THE T-Obl3b TIDE — the saturated-shell branch (banked pieces + owed obligation)

**Target (build tile #2's saturated branch, `final-assembly-design-cert.md §5` T-Obl3b / §7 OWED #3):**
on the lumping shell `S_r` (single-`ε` cover), `(shell-r off-sector integrand) ≤ const(ε)·vol(box_surv)·
(cornerComparator(redChain(t★+r) M) k jc integrand at e_r = c')`, closed by the step's decorated IH.

**BANKED (consume as black boxes):**
- `RouteMSJOnePeel334.cornerSliceAtUnits_le` + `sumSqND_box_lt_top` — the Morse codim-rescue for the
  `{Z→0}` tube (no minor CoV).
- `cornerComparator_adm` / `exists_cornerComparator_adm` / `cornerComparator_decLoss` — the deeper
  comparator `redChain(t★+r) M`; its `DecoratedBoxThresholdFinite` is the arity-`(L+1)` IH.
- `minAdm_redChain_succ_ge` + `exists_binding_cut` + `carrierThreshold_shift` — `C_r ≥ minAdm(M)` and
  `e_r = c' < ½·C_r` from `c' < carrierThreshold(M)` (STRICT, so tight `C_r` is fine).
- `RouteMSJSigMin.minStretch` + `Core.RankLocusClosed` — the single-`ε` shell predicate + finite cover.

**OWED (small, LABOUR — the exponent-0 collapse is the crux and it is trivial):**
1. **The `p=0` collapse.** State the freed-corner peel at cut `t★+r` with `#freed rows = a−r = 0`; the
   Gram divisor `det(·)^{−(a−r)/2}` reduces to `det(·)^0 = 1` by `Real.rpow_zero` — **the surviving-row
   weight is literally absent.** This is the ONE place the `a≠b` case differs from the LANDED `a=b`
   saturated branch, and it is a one-line `rpow_zero` simplification, not new analysis.
2. **The surviving-row box factor.** `∫_{A_surv∈box((b−a)×(M₂−r))} 1 = vol(box) < ∞` — a bounded-box
   constant; folds into `const(ε)` by `lintegral_const` + `Measure.restrict` finiteness of the box.
3. Then the residual is the deeper comparator at `e_r=c'`, closed by the IH exactly as in the `a=b`
   saturated branch. No minor CoV, no new Gram control.

---

## Close

- **Firmest result (pin cert, decorrelated-confirmed).** The `a≠b` saturated shell `j=r=min(a,b)`
  **CLOSES**. The `b−a` surviving corank rows the minor CoV cannot reach are **inert**: the freed-corner
  peel frees `a−r=0` rows, so their Gram-divisor exponent is `0` and their weight is the constant `1`
  (`Real.rpow_zero`), a finite box factor — not a `det^{−½}` divisor. The deeper comparator at cut
  `t★+r = min(M₀,M₁)` carries the full charge `C_r = minAdm(redChain(t★+r) M) = 12 ≥ 10 = minAdm(3,4,4)`
  (banked convexity; 0/3303 undershoots), fired at `e_r = c' < 5 < 6 = carrierThreshold(3,4)` via the
  arity-`(L+1)` IH, with the `{Z→0}` tube closed by the LANDED OnePeel334 Morse rescue.
- **Most likely to break it (the one nuance found).** The saturated charge **can be tight** (`C_r =
  minAdm(M)`, 1060/2028 `a≠b` instances) — harmless, because `c' < carrierThreshold(M) ≤ ½·C_r` is STRICT
  (same as the `j=0` binding cut) and the saturated shell needs no θ. And the surviving-row weight MUST be
  read as the constant `1`, not a hidden `det^{−½}` (Codex sharpening). Neither is a wall.
- **Next.** Hand this to the T-Obl3b tide as the saturated-shell branch (§6): the `p=0` `rpow_zero`
  collapse + the bounded-box surviving-row factor + the deeper-comparator IH. The `a=b` anchor was the
  clean case; the `a≠b` corner is now pinned and adds no new math — only a one-line exponent-0
  simplification. The T-Obl3b saturated branch is soundness-cleared at `a≠b`.
