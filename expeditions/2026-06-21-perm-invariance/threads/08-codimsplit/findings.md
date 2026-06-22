# Thread 08 — `codimForm` split: pin the Lean-proof STRATEGY (no proving)

> Seat: `pen-and-paper`. Deliverable: the exact Lean form of the split + the build-ready
> proof strategy (each step a precise lemma/tactic). NO Lean written.
> All load-bearing claims EXACT-integer verified (6 scripts, ~990k checks, 0 fail) in the
> REAL landed-Lean indexing. Decorrelated Codex consult CONVERGED (see §6) — and supplied the
> recommended symmetric route.

**VERDICT: STRATEGY PINNED, build-ready.** The controller's Δ formula and math path are CORRECT.
The cleanest Lean route is **NOT** the raw four-`Icc` split nor the landed pair-double-sum
`codimForm_extendℤ_eq_sum_pairs` (which is fixed-`N`, does not transfer across `N+1`↔`N`), but the
**landed `codimForm_add` / `codimBil` / `codimForm_congr_onbox` machinery** (`Core.CThetaQIPConverse`
+ `Core.CCodimZeroMono`), expanding BOTH sides against a common "lower part" `A`. Codex (decorrelated)
independently derived the SAME Δ and the SAME machinery, and its symmetric `A/R/L` decomposition (§2)
is verified exact (`verify_codex_symmetric.py`) and is the recommended route.

---

## 1. The pinned target (exact Lean form, against the real defs)

For `m : Fin (N+2) × Fin (N+2) → ℕ`:

```
codimForm (N+1) (extendℤ m) = codimForm N (extendℤ (peelPart m)) + Δ
```

with the **Δ in the controller's form** (VERIFIED exact, `verify_codimsplit.py`, see §3):

```
Δ = ∑_{a ∈ Icc 0 (N+1)} ∑_{u ∈ Icc (a+1) (N+1)}  (extendℤ m) a (N) * (extendℤ m) u (N+1)
  = ∑_{0 ≤ a < u ≤ N+1}  m_{a,N} · m_{u,N+1}
```

i.e. the bilinear pairing of `m`'s **last two columns** (`b_a − x_a = m_{a,N}`, `x_u = m_{u,N+1}`):
the second-from-last column `N` against the last column `N+1`, over strictly-increasing row pairs
`a < u`. (`(extendℤ m) a N = m_{a,N}` on `0≤a≤N`, and `(extendℤ m) (N+1) N = 0` since `N+1 > N`
falls outside the box, so the first factor's `a` effectively stops at `N`; writing `Icc 0 (N+1)` is
harmless and uniform. Cleaner formaliser target: `a ∈ Icc 0 N`.)

**Index reconciliation (load-bearing).** The thread-07 script used `N_script = len(d)−1` with merge of
column `N_script` into `N_script−1`. The LANDED `peelPart` (read in `Core.QSeriesFivegon`) is stated
for `m : Fin(N+2)²` and merges **column `N+1` into column `N`**: `peelPart m (I, last N) = m(I⁺,N) +
m(I⁺,N+1)` (`peelPart_last`, `@[simp]`), `peelPart m (I, castSucc J₀) = m(I⁺, J₀⁺⁺)` for `J₀ < N`. So
the Lean `N` here = `N_script − 1`. All of §3 is redone in THIS (landed) indexing, not transported.

---

## 2. The Lean proof strategy — Codex's symmetric `A/R/L` route (VERIFIED, recommended)

Three landed lemmas carry it (`Core.CThetaQIPConverse` + `Core.CCodimZeroMono`):
`codimForm_add A B : codimForm K (A+B) = codimForm K A + codimBil K A B + codimBil K B A + codimForm K B`,
`codimBil` biadditivity, and `codimForm_congr_onbox` (`codimForm K F` reads `F` only on `{0≤α≤β≤K}`).

### Setup — three ℤ-arrays
```
A : ℤ→ℤ→ℤ := extendℤ (N:=N) m₀,   m₀ p := m (p.1.castSucc, p.2.castSucc)   -- "lower unmerged part", box bound N
                                   -- so A α β = m_{α,β} on 0≤α≤β≤N (RAW col N, NOT merged), else 0
R : ℤ→ℤ→ℤ := fun α β ↦ if 0≤α ∧ α≤(N:ℤ) ∧ β=(N:ℤ)     then m_{α,N+1} else 0   -- peeled last col, at bound N
L : ℤ→ℤ→ℤ := fun α β ↦ if 0≤α ∧ α≤(N+1:ℤ) ∧ β=(N+1:ℤ) then m_{α,N+1} else 0   -- true last col, at bound N+1
```
(`R`,`L` both carry the **value** `m_{α,N+1}`; they differ only in WHICH column slot they sit in —
`R` puts it in column `N`, `L` in column `N+1`.)

### Step A — the two on-box identifications (`codimForm_congr_onbox`). (VERIFIED, `verify_codex_symmetric.py`)
- **peel side**, on `{0≤α≤β≤N}`:  `extendℤ (peelPart m) α β = (A + R) α β`.
  - `β < N`: `peelPart m (α,β) = m(α,β)` (interior `castSucc` case) and `R = 0`, so `= A α β`.
  - `β = N`: `peelPart m (α, last N) = m_{α,N} + m_{α,N+1}` (`peelPart_last`) `= A α N + R α N`. ✓
- **big side**, on `{0≤α≤β≤N+1}`:  `extendℤ m α β = (A + L) α β`.
  - `β ≤ N`: `extendℤ m α β = m_{α,β} = A α β` and `L = 0`. `β = N+1`: `m_{α,N+1} = A α (N+1) + L α (N+1)`
    (here `A α (N+1) = 0`, box bound N). ✓

Lean: `codimForm N (extendℤ (peelPart m)) = codimForm N (A+R)` and
`codimForm (N+1) (extendℤ m) = codimForm (N+1) (A+L)`, each by
`codimForm_congr_onbox (fun α β hα hαβ hβ ↦ <pointwise eq>)`. The peel-side premise is the
`extendℤ`-transport of LANDED `peelPart_eq`.

### Step B — expand BOTH sides by `codimForm_add`.
```
codimForm N (A+R)     = codimForm N A   + codimBil N A R   + codimBil N R A   + codimForm N R
codimForm (N+1) (A+L) = codimForm(N+1)A + codimBil(N+1)A L + codimBil(N+1)L A + codimForm(N+1) L
```

### Step C — the `R`-first / `L`-first cross-terms vanish. (VERIFIED, `verify_codex_symmetric.py`)
`codimBil N R A = 0`, `codimForm N R = 0`, `codimBil (N+1) L A = 0`, `codimForm (N+1) L = 0`.
Reason (exact index range): in `codimBil K · ·` the FIRST factor is read at column index `j−1` with
`j ≤ K`, so `j−1 ≤ K−1`. `R` is nonzero only at column `N`, needing `j−1 = N` i.e. `j = N+1 > N`
(out of range at `K = N`). `L` is nonzero only at column `N+1`, needing `j = N+2 > N+1` (out of range
at `K = N+1`). So every first-slot term is `0`.
Lean: `Finset.sum_eq_zero` (four nested), each summand `R (i−1)(j−1)·_ = 0` because the guard `β = N`
forces `j = N+1`, contradicting `j ∈ Icc u N`; `omega`. (Or a one-liner `R α β = 0` for `β < N`,
`simp`.) Same for `L` at level `N+1`.

### Step D — `codimForm (N+1) A = codimForm N A`. (VERIFIED, `verify_codex_symmetric.py`)
`A` has box bound `N`, so `A u (N+1) = 0` and `A (i−1)(j−1)` needs `j−1 ≤ N` — the only EXTRA terms in
the `(N+1)`-form over the `N`-form have `v = N+1`, where `A u (N+1) = 0`. So they all vanish.
Lean: cleanest as `codimForm_congr_onbox`-style — but the slicker route is the **innermost-`v` peel**
(`Finset.sum_Icc_succ_top` on `v ∈ Icc j (N+1)`) with the residual `j,u,i = N+1` slices killed by the
empty-inner-sum cascade (the `A u (N+1) = 0` makes the peeled `v=N+1` term itself `0`, and
`Icc (N+1) N = ∅` collapses the rest — see `verify_finset_realiz.py`). Either works; this is the only
spot needing an `Icc`-range manipulation, and it touches `A` ALONE (clean, no merge).

### Step E — read off Δ.
Combining B–D:
```
codimForm N (extendℤ(peelPart m))   = codimForm N A + codimBil N A R
codimForm (N+1) (extendℤ m)         = codimForm N A + codimBil (N+1) A L
⟹ Δ = codimForm(N+1)(extendℤ m) − codimForm N (extendℤ(peelPart m))
     = codimBil (N+1) A L − codimBil N A R.
```
- `codimBil N A R   = ∑_{1≤i≤u≤j≤N}   m_{i−1,j−1}·m_{u,N+1}`  (R fixes `v = N`, value `m_{u,N+1}`).
- `codimBil (N+1) A L = ∑_{1≤i≤u≤j≤N+1} m_{i−1,j−1}·m_{u,N+1}` (L fixes `v = N+1`, value `m_{u,N+1}`).
- Difference = the `j = N+1` slice = `∑_{1≤i≤u≤N+1} m_{i−1,N}·m_{u,N+1} = ∑_{0≤a<u≤N+1} m_{a,N}·m_{u,N+1}
  = Δ`. (The `i−1 ↦ a` reindex; `a := i−1 ∈ Icc 0 N`.) **VERIFIED** (`verify_codex_symmetric.py`,
  `verify_mechanism.py`). Cleanest closing: prove the two `codimBil` collapses (each by fixing `v` and
  `Finset.sum_eq_single`/`sum_filter`, the pattern in `codimBil_extendℤ_boxℤ_right`), then `Finset.
  sum_Icc_succ_top` on the `j`-range to extract the `j=N+1` slice, then the `i−1↦a` reindex.

∎ (modulo the Lean grind, which is index bookkeeping + the `codimBil` collapses)

**Asymmetric variant (my original, also fully verified — `verify_extendpeel.py`/`verify_peellayer.py`):**
expand only the peel side with a single correction `Gcol α β := [0≤α≤N ∧ β=N]·m_{α,N+1}` (= `R`), giving
`codimForm N (extendℤ(peelPart m)) = codimForm N (extendℤ m) + codimBil N (extendℤ m) Gcol`, and peel
`v=N+1` from the big side: `codimForm(N+1)(extendℤ m) = codimForm N (extendℤ m) + L_layer`, so
`Δ = L_layer − codimBil N (extendℤ m) Gcol`. Equivalent; the symmetric `A/R/L` route is preferred
because both sides reduce to the SAME `codimForm N A` and the cross-term vanishings are uniform.

---

## 3. Exact verification (6 scripts, real landed indexing, 0 failures)

All in `scratch/`. Re-run: `python3 scratch/<name>.py`.

| script | what it certifies | checks |
|---|---|---|
| `verify_codimsplit.py` | endpoint `codimForm(N+1)(E)=codimForm N(E')+Δ_ctrl`, Δ in controller form | 23000 random (triangular + fully-arbitrary) + 6 hand non-monotone |
| `verify_mechanism.py` | staged decomposition: v≤N part = N-form, Stage-1 peel, E'→E col-N correction, `Δ==stage1b−correction==ctrl` | 24000×4 |
| `verify_extendpeel.py` | ℤ-bridge `E'=E+Gcol` pointwise (incl. off-box) + `codimForm_add` expansion + cross-terms VANISH + Δ | 660000+174000+18000 |
| `verify_peellayer.py` | innermost `v=N+1` peel `codimForm(N+1)=codimForm(N)+L` + `L−codimBil=Δ` | 24000 |
| `verify_finset_realiz.py` | empty-inner-sum cascade: residual after peeling `v` literally `= codimForm N E` | 24000 |
| `verify_codex_symmetric.py` | **Codex's A/R/L route**: both on-box ids, all 4 vanishings, `cf(N+1)A=cf(N)A`, transports, Δ, endpoint | 24000 |

Coverage: `N=1,2,3`; entries `0..3/0..4`; **triangular AND fully-arbitrary** (the identity is a pure
polynomial in the entries — no Kostant constraint is used, so it holds for any `m`); plus hand-built
sparse/corner-heavy/non-monotone cases. The split is robust to non-monotone dimension vectors.

---

## 4. The single most-likely-to-break Lean step

**Step A's peel-side on-box pointwise equality `extendℤ(peelPart m) α β = (A + R) α β`** — the
`Fin.castSucc`/`Fin.lastCases` ↔ `ℤ`/`Int.toNat` index correspondence. Codex (decorrelated) flagged
the SAME step (`?peel_onbox`). `extendℤ` reads its ℤ-argument back through `⟨α.toNat,_⟩ : Fin (N+1)`,
while `peelPart`'s value is stated with `castSucc`/`last`; matching them across the `β = N` vs `β < N`
split is the work. It is the `extendℤ`-transport of LANDED `peelPart_eq`. **De-risk:** land a standalone
`extendℤ_peelPart_onbox` (`∀ α β, 0≤α → α≤β → β≤N → extendℤ(peelPart m) α β = (A + R) α β`) FIRST and
build-check it before wiring B–E. The big-side `?big_onbox` (`extendℤ m = A + L`) is easier (no merge —
`extendℤ m α β = m_{α,β}` on its box, split by `β = N+1`). B–E are biadditivity + `omega` range work.

No q-series risk; `codimForm_add`/`codimBil`/`codimForm_congr_onbox` are LANDED and axiom-clean.

---

## 5. What does NOT transfer (ruled out, don't re-explore)

The landed **pair-double-sum** `codimForm_extendℤ_eq_sum_pairs : codimForm N (extendℤ m) = ∑_A ∑_B
(m A)(m B)·[pairBox A B]` (`Core.CCodimZeroStrict`) is **fixed-`N`**: both factors and `pairBox` live
over `Fin(N+1)`, and `pairBox`'s bound (`d ≤ N`) is N-dependent. It gives no clean `N+1`↔`N` bridge for
this split (the brief's option (ii) is a dead end here). Use the `codimForm_add`/`codimBil` route (§2)
instead — same machinery, but applied at the two different sizes separately and glued via the common
lower part `A`.

---

## 6. Codex consult — CONVERGED

`codex/split-prompt.md` (contract-shaped, hypothesis withheld — frame + facts in, my conclusion out);
`codex/split-answer.md` the reply (`high` effort; `xhigh`/first attempts failed on env, re-run landed).
Codex **independently derived the identical Δ** (`∑_{a=0}^{N}∑_{u=a+1}^{N+1} m_{a,N} m_{u,N+1}`) and the
identical machinery (`codimForm_add` + `codimBil` + `codimForm_congr_onbox`), and contributed the
**symmetric `A/R/L` decomposition** (expand BOTH sides against a common lower part `A`, with
`codimForm(N+1) A = codimForm N A`) — cleaner than my asymmetric peel; now §2, verified exact
(`verify_codex_symmetric.py`). Both Codex and I flag the SAME hardest step (the `peelPart`∘`extendℤ`
on-box identity). Codex's own caveat (preserved): it checked the formula + cancellation but not a full
Lean term, so helper-lemma names for the sum collapses are inferred — matching my §2/§4 risk note.

---

## 7. Close

- **Firmest result:** the split holds with the controller's Δ. Build-ready ladder = Codex's symmetric
  `A/R/L` route (§2): two `codimForm_congr_onbox` identifications, `codimForm_add` on both sides, four
  vanishing first-slot cross-terms (`omega` on column index), `codimForm(N+1)A = codimForm N A`, then
  read Δ off two `codimBil` collapses. 6 certificates, ~990k checks, 0 failures, real indexing. Codex
  decorrelated-converged.
- **Most likely to break:** Step A peel-side (`extendℤ(peelPart m) = A + R` on box — the
  `castSucc`/`toNat` correspondence, transport of LANDED `peelPart_eq`). De-risk by landing
  `extendℤ_peelPart_onbox` standalone first.
- **Next:** formaliser lands `extendℤ_peelPart_onbox`, build-checks it, then wires §2 B–E. If Step A
  fights, a focused Codex consult (from the main checkout) on that one identity with `peelPart_eq` +
  `extendℤ` in hand. Pair-double-sum confirmed NOT a shortcut (§5).
