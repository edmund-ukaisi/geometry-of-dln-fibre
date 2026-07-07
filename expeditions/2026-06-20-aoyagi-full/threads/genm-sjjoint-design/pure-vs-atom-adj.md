# Adjudication — rblowup2's "SAME WALL" (atom route) vs the pure R-BLOWUP

**Seat:** pen-and-paper (resolve a decorrelated CONFLICT that decides R1-UPPER; exact algebra +
decorrelated Codex xhigh with BOTH leanings withheld). **Conflict:** my de-risking probe
(`chart-lemma-probe.md`) found the PURE R-BLOWUP reaches normal crossing (verdict A); `rblowup2`, building
the integral-level weld via the anisotropic atom `gammaAtom_aniso_shifted_eq` (integrate Γ OUT →
`det(Q_bQ_bᵀ)^{−p/2}` Gram-det), found the OUTER `A'`-integral couples via shared `Z` → "SAME WALL",
Codex-confirmed.

---

## VERDICT: (A) — the PURE R-BLOWUP AVOIDS the wall. `rblowup2`'s wall is the ATOM B-trap.

**`rblowup2`'s "SAME WALL" is REAL for the atom route but is an ARTIFACT of integrating Γ out over FULL
SPACE (enlarge-before-shear), which OVER-COUNTS the box on the NULL degenerate `{det Q_b=0}` locus — the
design cert's §3 ∞-Beta / "discards-the-finite-cutoff" mechanism, recurring. The pure route (Γ a CHART
coordinate, blown up WITHIN the box; all layers resolved to normal crossing; monomial endpoint at the END)
respects the finite cutoff, dissolves the coupling into a monomial product, and is FINITE for
`c' < ½·minAdm`. Both routes compute the same true RLCT; the atom route cannot reach it via the outer
Gram-det integral (the artifact), the pure route can. This does NOT re-open the R1-UPPER scope question —
it stays bounded labor via the pure `(S,J)` chart-lemma build (`buildability.md`/`chart-lemma-probe.md`).**

My tentative read (that rblowup2 took the atom B-trap I flagged) is **CONFIRMED, and sharpened**: the
precise culprit is the atom's *full-space enlargement*, and the exact mechanism is the finite-cutoff
crossover the ∞-Beta discards. Decorrelated Codex (both leanings withheld) returned the same: **atom-artifact**.

## The exact algebra (mine — `sjj_pure_vs_atom.py`, `sjj_cutoff.py`)

Coupling caricature `F = α² + γ²(βs)²` (`α` = core/pivot, `γ` = top corank scalar, `βs` = a DEGENERATE
downstream PRODUCT — the faithful scalar reduction of rblowup2's `‖pivot‖² + ‖Γ·(product Q_b)‖²`, `p=q=1`):

| object | exact result | consequence |
|---|---|---|
| **PURE toric RLCT(F)** | `1` (Newton/toric; sanity `x²→½`, `x²+y²→1`) | `∫F^{−c'} < ∞ ⟺ c' < 1` — FINITE |
| **PURE, integrate CORE `α` first** | `∫(α²+m²)^{−c'}dα ∝ |γβs|^{1−2c'}` (`m=γβs`) → `∏∫|·|^{1−2c'}` | MONOMIAL product; `∫_0^1|x|^{1−2c'}<∞ ⟺ c'<1` ✓ |
| **ATOM, integrate CORANK `γ` over FULL SPACE** | `∫_ℝ(α²+γ²z²)^{−c'}dγ = √π·α^{1−2c'}·Γ(c'−½)/(z·Γ(c'))` → weight `|z|^{−1}` (z-exponent `−1`, sympy-confirmed) | `∫|βs|^{−1}dβds = (∫dβ/β)(∫ds/s) = +∞` — the "WALL" |
| **BOX `γ`-integral (pure, `z→0`)** | `∫_0^1(α²+z²γ²)^{−c'}dγ → α^{−2c'}` as `z→0` (sympy `limit`) | FINITE CUTOFF — **NO `|z|^{−1}`** |

**The decisive contradiction-resolution.** By Tonelli the nonneg box integral is order-independent and
FINITE for `c'<1`. The atom's `|z|^{−1}` divergence arises ONLY from integrating `γ` over **ℝ (full
space)** rather than the box: the full-space integral is exactly `|z|^{−1}α^{1−2c'}`, but this OVER-COUNTS
the box — the box `γ`-integral tends to `α^{−2c'}` (finite) as `z→0`, not `|z|^{−1}`. So the atom's Gram-det
weight is a valid but **too-loose upper bound** (`∫_box ≤ ∫_fullspace`) that LOSES finiteness on the null
`{z=0}` locus. Codex (verbatim): the `|βs|^{−1}` form "is only the large-parameter asymptotic when
`|βs|≫|α|` … not uniform near `βs=0` … The exact inner integral has a crossover … `|βs|^{1−2c}`, not
`|βs|^{−1}`. … the `|βs|^{−1}` wall is not the true wall." This is the design cert §3 mechanism ("the
∞-Beta discards the finite cutoff … manufactures a divergence the true integral does not have") and the
`cert.md` route-2 death, recurring via the full-space atom.

## Reconciling the two threads (same object, different route)

- My probe validated the **loss FACTORISATION** (sequential single-radial charts → reduced-chain × monomial,
  radials as passive prefactors) — the PURE route's mechanism.
- `rblowup2` built the **integral-level finiteness via the ATOM** (integrate Γ over full space → Gram-det)
  and hit the outer coupling — the ATOM route's artifact.
- These are the SAME underlying RLCT by DIFFERENT routes. The atom route replaces the exact inner integral
  by a full-space Gaussian whose constant `det(Q_bQ_bᵀ)^{−p/2}` blows up at downstream rank-drop; it has
  NOT computed the original integral there (Codex Q3). The pure route keeps Γ in the box (blows up its
  radial), respects the cutoff, and reaches a monomial where finiteness is a trivial product.
- Is the Gram-det coupling GENUINE or an atom artifact? **ATOM ARTIFACT** — the full-space enlargement on
  the null degenerate locus. The pure route has no Gram-det (Γ never integrated out).

## Q2 — does the pure route reach a coupling-free monomial? (with the one caveat)

YES — on each chart of a genuine normal-crossing resolution, `F = (monomial)²·U` (`U ≥ c₀ > 0`), Jacobian
monomial×unit, so `∫∏|y_i|^{κ_i−2c'N_i}·U^{−c'}dy < ∞ ⟺ κ_i−2c'N_i > −1` coordinatewise — **no surviving
Gram determinant, no downstream coupling** (Codex: "the coupling is gone by definition"). **Caveat (Codex +
me):** one must still prove the layer-by-layer single-radial blow-ups ACTUALLY reach normal-crossing form
— which is exactly the general-`(L,S,J)` chart lemma my `chart-lemma-probe.md` green-lit (sequential
single-radial reaches normal crossing for the coupled corank-2 case; radials are passive monomial
prefactors; hardest brick = the relative corank-step invariant). So the pure route's finiteness REDUCES to
reaching normal crossing (the chart lemma), which is separately validated — NOT to an outer Gram-det
coupling.

*Instrument caveat:* the caricature is a scalar (`p=q=1`) reduction; the toric RLCT, the box cutoff, and
the full-space over-count are EXACT for it and decisively show the wall is an atom artifact (a property of
the ROUTE, not of the true integral). For the full matrix `(3,3,3,4)`, "the pure route reaches normal
crossing" is the general-`L` chart lemma (green-lit, bounded, not yet a completed proof). A discarded
naive fixed-grid numeric (`sjj_converge_check.py`) was unreliable (heavy-tail grid artifacts) — NOT used;
the exact toric + exact cutoff + exact full-space over-count are the certificate.

## Codex INTERPRETATION (decorrelated, xhigh, BOTH leanings withheld — `codex/purevatom-{prompt,answer}.md`)

Q1 **atom-artifact**: toric RLCT `=1`, mult 3; the `|βs|^{−1}` is a non-uniform `|βs|≫|α|` asymptotic;
the crossover gives `|βs|^{1−2c}`, integrable `⟺ c<1`. Q2 **full blow-up avoids the coupling** (on each
chart `F=(monomial)²·U`, endpoint condition, no Gram-det), with the caveat that reaching normal crossing
must be proved. Q3 **same threshold**; if the atom walls while the blow-up is finite, "the atom route has
NOT computed the original integral — it replaced the exact inner integral by a full-rank/asymptotic
Gaussian formula whose constant blows up at downstream rank drop … the lost information is precisely the
cutoff `|α|≶|βs|`." Matches my exact algebra term for term.

---

## The corrected recursion spec (verdict-A deliverable — the formaliser runway)

**DO NOT** discharge the general-`L` outer integral via the atom (`gammaAtom_aniso_shifted_eq`) followed by
an outer `A'`-integral of the Gram-det — that route hits the full-space over-count wall on the degenerate
strata. **DO** use the PURE radial `(S,J)` recursion:

1. **`corankStep` (single-radial per layer, INCLUDING the tail).** At each `(S,J)`, blow up ONE radial `u`
   for the whole current corank block (`Γ` a CHART coordinate, NOT integrated out); charge `u` by the block
   codim; `Z`-independent unit block-elimination absorbed into the adjacent factor (deeper factors
   untouched); advance `(S,J)`; recurse on the reduced block × downstream product. [= `chart-lemma-probe.md`
   spec; banked radial `radial_morse_residual_power_le`, cover `pivotChartCover_matBox_le_sum`, templates
   `Case111`/`Case222`.] The tail `A'` is resolved by ITS layers' `corankStep`s — its radials enter the
   monomial, so no Gram-det ever forms.
2. **Monomial endpoint at the END only.** Fully-resolved loss `= (monomial)²·(unit≥1)` on each chart of the
   finite cover; finiteness by `monomialIntegrand_integrable_of_lt` (coordinatewise `κ_i−2c'N_i > −1`),
   below threshold since every terminal exponent `= Mval ≥ minAdm` (banked `minAdmRec_eq_minAdm`;
   threshold monotonicity `0/171`). No coupling, no Gram-det.
3. **The atom is retained ONLY for the generic/full-rank slice** (where `Z=Q_b` is bounded below and the
   full-space `|z|^{−1}` bound is harmless) — e.g. the `L=2`/`rrp` pieces. NOT for the degenerate outer
   integral.

**Single hardest (bounded) brick:** the relative corank-step invariant / the general-`(L,S,J)` single-radial
chart lemma (lift `Case111`/`Case222` to opaque widths). Bounded chart algebra, NOT resolution-of-singularities
(`buildability.md`). R1-UPPER stays bounded labor — **no scope-call re-opened.**

## Closing

- **Firmest.** The atom's Gram-det coupling wall is an ARTIFACT of the full-space Γ-enlargement over-counting
  the box on the null degenerate locus (exact caricature: toric RLCT `=1` finite; box cutoff `α^{−2c'}`;
  full-space `|z|^{−1}` divergent; Codex + design cert §3 agree). The pure R-BLOWUP dissolves the coupling
  into a monomial and is finite. **Verdict A: pure R-BLOWUP avoids the wall.**
- **What flips it (guarded).** Only if the general-`L` chart lemma FAILS to reach normal crossing (the
  `chart-lemma-probe` caveat) — but that probe green-lit it (sequential, radials passive). If a formaliser
  later finds the opaque-width `corankStep` cannot be made to reach `(monomial)²·unit` on a finite cover,
  THAT (not the atom's Gram-det) would be the genuine wall — the one thing left to watch.
- **Next.** Hand the formaliser the corrected pure-recursion spec (above); retire the atom→outer-Gram-integral
  approach for the degenerate strata. This decides R1-UPPER charges as bounded labor.
