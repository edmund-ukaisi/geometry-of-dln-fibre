# Thread 02 — L5 dimension-formula sizing (pen-and-paper, 2026-06-19)

**VERDICT: bounded small sub-library — 2–3 modules, days of tides. NOT greenfield catenary, NOT
multi-expedition.** Downgrades recon 01's "dominant risk / possible multi-expedition."

## The correction to recon 01
Recon 01's "`IsCatenary` 0% ⇒ greenfield" holds for the **catenary route (b)** but not for the
**integral-extension route (a)**, whose bricks are almost all present. Two pieces recon 01 flagged as biggest
gaps are already in Mathlib:
- `MvPolynomial.ringKrullDim_of_isNoetherianRing` ⇒ `dim k[x₁..xₙ] = n` is **PROVED** (the `proof_wanted
  MvPolynomial.fin_…` is a redundant `Fin`-restatement, not the formula being absent).
- `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` (`@[stacks 00ON]`, Matsumura 13.B) — per-prime
  height additivity over going-down — is **PROVED**.

## Chosen route — (a) integral-extension dimension invariance (trdeg-light)
`R/p` is a domain finite/integral over `A = k[x₁..x_s]` (Noether normalization); `dim(R/p) = dim A = s`;
`height p = n − s`. Stays in `WithBot ℕ∞`; `trdeg` is a downstream corollary, not load-bearing (avoids the
missing `Cardinal ↔ ℕ∞` bridge). Route (b) catenary/CM is greenfield (`IsCatenary`/`equidimensional` 0 hits;
only the `⨆`-form `krullDim = ⨆ a, height a + coheight a` exists — the per-prime equality is what's missing).

## Inventory (pinned Mathlib `8a17838`, v4.29)
- PROVED/free: `MvPolynomial.ringKrullDim_of_isNoetherianRing` (`dim k[x₁..xₙ]=n`).
- PROVED: `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`; Krull going-down instance for integral
  extensions of integrally-closed domains (`RingTheory/IntegralClosure/GoingDown.lean`); `k[x₁..x_s]` is a UFD
  (`MvPolynomial.uniqueFactorizationMonoid`) ⇒ `IsIntegrallyClosed` (`UniqueFactorizationMonoid.instIsIntegrallyClosed`).
- PRESENT: Noether normalization `exists_integral_inj_algHom_of_fg` (`@[stacks 00OW]`, existence only — `s`
  not tied to dimension); lying-over `exists_ideal_over_prime_of_isIntegral`; `IsIntegralClosure.comap_lt_comap`;
  order transport `Order.krullDim_le_of_strictMono`, `krullDim_le_of_strictComono_and_surj`,
  `krullDim_eq_of_orderIso`; `ringKrullDim_quotient`, `coheight_Ici`; full `Algebra.trdeg` API.
- ABSENT (the gap = assembly, not bricks): no file connects `ringKrullDim` to `Algebra.IsIntegral`/`LiesOver`/
  `HasGoingDown`; so no `dim S = dim A` for integral extensions, no `height p + dim(R/p) = dim R`.

## L5 sub-ladder (dependency order)
- **L5.0** `dim(MvPolynomial (Fin n) k) = n` — trivial corollary.
- **L5.1** `dim(R/p) = Order.coheight p` — `ringKrullDim_quotient` + `zeroLocus p = Ici p` + `coheight_Ici`.
- **L5.2** integral inj `A→ₐ S` ⇒ `dim S ≤ dim A` (strict-mono comap → `krullDim_le_of_strictMono`).
- **L5.3** ⇒ `dim A ≤ dim S` (lying-over → `krullDim_le_of_strictComono_and_surj`).
- **L5.4 [HARD #2]** `ringKrullDim_eq_of_integral_inj` — L5.2+L5.3; order/chain bookkeeping. Reusable, upstream-grade.
- **L5.5** `dim(R/p) = s` (Noether normalization + L5.4 + L5.0); `= trdeg` corollary.
- **L5.6 [HARD #1, dominant]** `height p + coheight p = n` for primes of `k[x₁..xₙ]` — the per-prime catenary
  content, by induction on normalization rank via `height_eq_height_add_of_liesOver_of_hasGoingDown` + a
  one-variable base step. *Guided* induction over a proved additivity lemma, not greenfield.
- **L5.7 (target)** `height p + dim(R/p) = n` (L5.6 + L5.1).
- **L5.8** geometric form `I.height = n − t` (consumes the L4 smoothness feed-in; lives at the L4/L5 seam).

## Hardest lemmas
1. **L5.6** `height + coheight = n` for `k[x₁..xₙ]` primes (the catenary content). Hardest.
2. **L5.4** integral-extension `ringKrullDim` invariance. Medium-hard.

## Kill-condition (watch during build)
If L5.6's going-down induction needs absent instance-propagation (`IsIntegrallyClosed`/`LiesOver`/`FaithfulSMul`
not carrying through the variable-peel, or a one-variable base `height` step that itself needs catenary), L5.6
inflates toward Codex's "weeks." **First build move that settles it:** a formaliser tide on **L5.4 + L5.1**
(both on present bricks, reusable); a green L5.4 confirms the order-transport machinery and de-risks L5.6.

## Codex (decorrelated, xhigh; `codex/dim-formula-{prompt,answer}.md`)
Independently chose route (a), confirmed catenary absent, named the same bricks and same two hardest lemmas.
Disagreement: magnitude — Codex "weeks, several modules" vs this seat "days, 2–3 modules"; traced to Codex not
folding the proved `height_eq_height_add_of_liesOver_of_hasGoingDown` + `dim k[x]=n` into its estimate. Codex's
end-to-end-`trdeg` closing not adopted (forces the missing `Cardinal↔ℕ∞` bridge). Down-weight to "verify in build."
