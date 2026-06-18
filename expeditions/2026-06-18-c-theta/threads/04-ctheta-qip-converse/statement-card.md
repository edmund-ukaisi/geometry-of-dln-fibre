# Statement card — Layer 3b: the QIP converse (Thm 6.1, `≥`) — COMPLETE

Module `lean/DLNFibre/Core/CThetaQIPConverse.lean` (new, imports `Core.CThetaQIP`). Closes the QIP to
equality `cCodim d 0 = qipMin d` for **weakly-increasing** `d`. Work uncommitted in the `c-theta`
worktree; controller bumps SHA + wires the import on integration.

**Status: build GREEN, 0 sorries, 0 axiom / 0 native_decide; `#print axioms` clean (propext /
Classical.choice / Quot.sound only).** The ENTIRE converse is proved — the headline
`cCodim_eq_qipMin` closes the QIP to equality, with the `(2,2,2)` witness `cCodim_eq_qipMin_d222`.

**Hypothesis strengthening (vs brief).** The brief specified `d 0 ≥ 1`. The form-level exhaustiveness
argument (Codex-designed, numerically confirmed) routes through the edge `b|b+1`, never column `a-1`, so
**`Monotone d` alone suffices** — `d 0 ≥ 1` is dropped. Verified: `cCodim = qipMin` for all monotone `d`
incl. `d 0 = 0`, N≤4. (The `d=(1,0,1,0)` "walled" obstruction is non-monotone.)

---

## PROVED (sorry-free)

> **`cCodim_eq_qipMin` (headline).** `Monotone d → cCodim d 0 h = qipMin d hne`. — Proved by
> `le_antisymm` of committed `cCodim_le_qipMin` (easy ≤) and `cCodim_ge_qipMin` (this layer).
> **`cCodim_ge_qipMin`.** Proved from `minimiser_isHL` + `mOfE_surj_of_hl` via `Finset.exists_mem_eq_inf'`
> (the minimiser is HL ⟹ in the `mOfE`-image ⟹ value = `Gqip e ≥ qipMin`). **Fully proved given the two
> sorried lemmas it calls.**

> **Bilinear infrastructure.** `codimBil`, `codimBil_self`, `codimBil_add_left/right`, `codimForm_add`
> (`codimForm (A+B) = codimForm A + codimBil A B + codimBil B A + codimForm B`). All sorry-free.

> **The concat move.** `concatMove` (ℕ-array), `concatDelta` (ℤ-delta), and the load-bearing
> **`extendℤ_concatMove`**: `extendℤ (concatMove m a b c d') = extendℤ m + concatDelta a b c d'` under the
> move preconditions. Sorry-free (the hardest connection lemma — distinctness + no-underflow + box casing).

> **`extendℤ_fin_eq`, `extendℤ_nonneg`** — sorry-free.

> **`codimForm_concatMove_lt`** (the strict decrease): `codimForm (extendℤ (concatMove …)) <
> codimForm (extendℤ m)` given both sources `≥ 1`. **Proved given the 3 collapse sorries** — the rectangle
> domination (`single_le_sum` ×2, source entries `≥ 1`, entries `≥ 0`) and final `linarith` are sorry-free.

> **`mOfE_surj_of_hl` — feasibility half.** `∑ i, eOfm m i = d 0` (from `kostantAt … 0` + corner drop).
> Sorry-free. (`eOfm m i = m (0, i.castSucc)` is the constructive inverse.)

## PROVED since first checkpoint (now sorry-free)

> `codimBil_single_right`, `codimBil_concatDelta_right` — `codimBil M δ = −∑_{[a+1,c]×[c,d']} M(i-1)(j-1)`
> (right-slot single-point collapse + the 3-term telescoping via two `Icc` splits).
> `codimBil_single_left`, `codimBil_concatDelta_left` — `codimBil δ M = −∑_{[a+1,c]×[c,d']} M u v`
> (left-slot, with the `q+1 > N` edge case handled).
> `codimForm_concatDelta` — `codimForm δ = 1` (via the left collapse applied to `M = δ`; rectangle sum `−1`).
> **`codimForm_concatMove_lt`** — the strict decrease, now fully sorry-free (the flagged single-hardest
> obstruction). **`concatMove_mem`** — the move is a valid corner-`0` KP (per-key ℤ-cast + the disjoint-cover
> net-zero `[AD∈F] − [AB∈F] − [CD∈F] = 0` at every vertex).

## PROVED — the remaining two lemmas (now sorry-free)

> `mOfE_surj_of_hl` — HL ⟹ `mOfE`-image, via the constructive inverse `eOfm m i = m (0, i.castSucc)`:
> feasibility `∑ eOfm = d 0` (`kostantAt … 0` + corner drop); `mOfE d (eOfm m) = m` by cases on `(x,y)`
> (low column = `eOfm`, corner `0`, interior `0` by HL, top row by the adjacent-vertex identity
> `m (x,N) = m (0,x-1) + (d x − d(x-1))` `hid2`). The identity uses the same edge `hkey` as `ends_le_starts`,
> HL-collapsing `Starts_{x-1} = m(x,N)`, `Ends_{x-1} = m(0,x-1)`.
> `ends_le_starts` — the edge inequality `Ends_b ≤ Starts_b` from `d_b ≤ d_{b+1}` + the per-vertex identity
> `1_{Fb} + 1_{p.1=c} = 1_{Fc} + 1_{p.2=b}` (on the support triangle).
> `minimiser_isHL` — the single-step contradiction: non-HL ⟹ interior `[a,b]` ⟹ (`ends_le_starts`)
> `Starts_b > 0` ⟹ a concat move ⟹ `codimForm_concatMove_lt` + `concatMove_mem` contradict `inf'_le`.

---

## Audit (checkpoint)

- `lake build` GREEN (2080 jobs). `scripts/sorries`: `0 sorry, 0 #exit, 0 native_decide, 0 axiom`
  (whole library). `#print axioms` on `cCodim_eq_qipMin`, `cCodim_eq_qipMin_d222`, `minimiser_isHL`,
  `mOfE_surj_of_hl`: only `propext`, `Classical.choice`, `Quot.sound`.
- Numerics (sympy, exact): edge identity `d_b + Starts_b = d_{b+1} + Ends_b` (115556 cases); the rectangle
  collapses + `codimForm δ = 1` (7 dim-vectors); `HL = mOfE-image` and exhaustiveness (monotone `d`, N≤4);
  `cCodim = qipMin` for all monotone `d` incl `d 0 = 0` (N≤4).
- Fidelity review (Lean ↔ Thm 6.1 converse): **PASS** (reviewer, 2026-06-18; decorrelated Codex on the
  dropped `d 0 ≥ 1` hypothesis). All 8 checks survived: headline is genuine `=` (`le_antisymm` of committed
  easy `≤` + new `≥`); the `Monotone d`-only hypothesis is SOUND (edge argument never touches `d 0`;
  `cCodim = qipMin` holds at `d 0 = 0`; the `(1,0,1,0)` "walled" case is non-monotone, confirmed by
  `decide`); `IsHL`/`minimiser_isHL`/`mOfE_surj_of_hl`/Δ-engine faithful and non-vacuous; no overclaim
  (geometric reading still on deferred `hVoigt`); axioms clean; `(2,2,2)` witness consistent (all `= 3`).
  Paper citations verified (Thm 6.1 main.tex:1155, Lemma 6.4 :1230, QIP eq :1151). Reviewer's dead-tactic
  note **fixed**.
- **Status: sorry-free + reviewed; the QIP is closed to equality `cCodim = qipMin` for monotone `d`.**

## Codex consults

`threads/04-ctheta-qip-converse/codex/lean-structure-{prompt,answer}.md` (the proof structure: `eOfm`
inverse, B-only exhaustiveness via the edge identity, `Function.update`-free move encoding),
`delta-collapse-{prompt,answer}.md` (the rectangle-collapse split: `codimBil M δ = −rect₁`,
`codimBil δ M = −rect₂`, `codimForm δ = 1`, bound rectangles by source entries). Diagnoses used; all proofs
built locally. The B-only exhaustiveness (dropping `d 0 ≥ 1`) is Codex's decorrelated contribution.
