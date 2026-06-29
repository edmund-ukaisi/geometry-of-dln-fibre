# Statement card — R1: integral-extension dimension invariance (re-home)

**Rung:** R1 (`dimension-stack` expedition). **Tactic:** generalise-and-re-home (the content was already
field-general; R0 confirmed). **Status:** `sorry-free`, axiom-clean; awaiting fidelity review.

## What this rung produced

The integral-extension Krull-dimension-invariance content from the bespoke
`DLNFibre/Core/IntegralDimension.lean` (namespace `DLNFibre.Core`) is re-homed to a Mathlib-grade
sub-namespace `DLNFibre.Core.Dimension`, split by content into two files that mirror the eventual Mathlib
targets. The old file is **deleted** (true re-home, no stale duplicate).

| new module | namespace | mirrors Mathlib target | content |
|---|---|---|---|
| `lean/DLNFibre/Core/Dimension/Integral.lean` | `DLNFibre.Core.Dimension` | `Mathlib.RingTheory.KrullDimension.Integral` (absent at v4.29 — grep-verified) | the integral-extension headline + going-up chain-lift |
| `lean/DLNFibre/Core/Dimension/Basic.lean` | `DLNFibre.Core.Dimension` | `Mathlib.RingTheory.KrullDimension.{Polynomial,Field,Basic}` | the polynomial-over-field + quotient/coheight facts that were co-housed in the bespoke file but are **not** integral-extension content |

The two-file split (vs dumping everything into `Integral.lean`) is a name=content decision, decorrelated via
Codex (gpt-5.1-codex-max): file name matches content, and it leaves R2/R4's `Catenary`/`Codimension` rooms
clear.

## Headline declaration (the deliverable)

`Integral.lean`, namespace `DLNFibre.Core.Dimension`:

```lean
@[stacks 00OK]
theorem ringKrullDim_eq_of_integral_injective [CommRing A] [CommRing S] {f : A →+* S}
    (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim S = ringKrullDim A
```

**Gloss.** Krull dimension is invariant under an integral injective ring extension (Stacks 00OK:
"$R \subset S$, $S$ integral over $R$ ⟹ $\dim R = \dim S$"). Stated at `RingHom` generality over commutative
rings; the only hypotheses are integrality of `f` and injectivity of `f`. **Hypotheses are minimal:**
injectivity is genuinely load-bearing for the `dim A ≤ dim S` half (lying-over over `⊥` needs `comap ⊥ = ⊥`,
i.e. `ker f = ⊥`); the `dim S ≤ dim A` half (`ringKrullDim_le_of_integral`) drops injectivity entirely.

### Supporting public declarations (`Integral.lean`)

| name | signature (hyps) | role | tag |
|---|---|---|---|
| `strictMono_comap_of_isIntegral` | `[CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] : StrictMono (comap (algebraMap R S))` | comap strictly monotone on `PrimeSpectrum` for an integral algebra | (00GT cited in docstring, not as `@[stacks]` — strict-mono is a restatement, not the literal incomparability lemma) |
| `ringKrullDim_le_of_integral` | `{f : A →+* S} (hf : f.IsIntegral) : ringKrullDim S ≤ ringKrullDim A` | one half; integrality only (no injectivity) | `@[stacks 00OJ "the dimension inequality"]` (its dim-inequality conjunct; also one half of 00OK) |
| `exists_ltSeries_comap_last_of_isIntegral` | `[Algebra A S] [Algebra.IsIntegral A S] (hinj : Function.Injective (algebraMap A S)) (p : LTSeries (PrimeSpectrum A)) : ∃ q : LTSeries (PrimeSpectrum S), q.length = p.length ∧ comap (algebraMap A S) q.last = p.last` | going-up chain lift (equal length, matching last term) | `@[stacks 00GU "...chain-lift corollary"]` |
| `ringKrullDim_ge_of_integral_injective` | `{f : A →+* S} (hf : f.IsIntegral) (hinj : Function.Injective f) : ringKrullDim A ≤ ringKrullDim S` | other half; uses the chain lift | — (one half of 00OK) |

### `Basic.lean` declarations (re-homed Groups B + C)

| name | signature | note |
|---|---|---|
| `ringKrullDim_mvPolynomial_field` | `(k : Type*) [Field k] (ι : Type*) [Finite ι] : ringKrullDim (MvPolynomial ι k) = Nat.card ι` | field-specialisation of `MvPolynomial.ringKrullDim_of_isNoetherianRing` |
| `ringKrullDim_mvPolynomial_fin_field` | `(k : Type*) [Field k] (n : ℕ) : ringKrullDim (MvPolynomial (Fin n) k) = n` | `Fin n` form (the one consumers use) |
| `primeSpectrumQuotientOrderIsoIci` | `[CommRing R] (p : PrimeSpectrum R) : PrimeSpectrum (R ⧸ p.asIdeal) ≃o Set.Ici p` | `noncomputable def` |
| `ringKrullDim_quotient_eq_coheight` | `[CommRing R] (p : PrimeSpectrum R) : ringKrullDim (R ⧸ p.asIdeal) = (coheight p : WithBot ℕ∞)` | quotient/coheight identity |

## What moved, what shimmed

- **Moved (re-home):** all 9 declarations from the deleted `IntegralDimension.lean` — Group A → `Integral.lean`,
  Groups B+C → `Basic.lean`. No proof changed; only namespace (`DLNFibre.Core` → `DLNFibre.Core.Dimension`),
  docstrings (Mathlib-graded), and `@[stacks]` tags added.
- **Shimmed:** nothing. No thin re-export shim was needed.
- **Re-pointed importers (8 files):** the single-writer aggregator `DLNFibre.lean` (the one
  `import …IntegralDimension` line → the two new imports); 6 direct importers
  (`AffineDomainDimension`, `NoetherMonicPositioning`, `RadicalCatenary`, `AffineLocalizationNoDrop`,
  `SmoothLocalRelativeDimension`, `PolynomialDimension`) — each gets the new import(s) it actually uses
  (Integral and/or Basic) plus `open Dimension` (they reference the names unqualified from inside
  `namespace DLNFibre.Core`).

## Load-bearing surprise (the one hole generalising surfaced)

One **transitive** consumer needed more than a path change: `DLNFibre/Core/FibreSmoothBlockExists.lean`
uses `ringKrullDim_quotient_eq_coheight` unqualified **without importing the old file directly** — it picked
the name up transitively (via `FibreSmoothBlock → RadicalCatenary`) and relied on it living in the
`DLNFibre.Core` namespace. Moving the decl to `DLNFibre.Core.Dimension` broke the unqualified reference
(`Unknown identifier`), surfacing only in the full-aggregator build, not in the direct-importer set. Fix:
add `Dimension` to that file's `open` line. A sweep for every moved identifier across `DLNFibre/`
confirmed this was the **only** transitive consumer (complete consumer set = 2 new files + 6 direct
importers + this 1 transitive consumer).

## Gate

- **Build:** `./scripts/lb DLNFibre` (full aggregator) green. (Both new modules and all 8 re-pointed files
  build; the only warnings are pre-existing `linter.style.longLine`/`show` warnings in untouched files — the
  two new files are lint-clean.)
- **Sorries:** `scripts/sorries` → `0 sorry, 0 #exit, 0 native_decide, 0 axiom` library-wide.
- **Axioms:** `#print axioms` on all 7 substantive declarations (headline + the 4 Integral supports + the 2
  used Basic facts) = `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no new axiom.

## Review

Fidelity + soundness review (independent reviewer + decorrelated Codex) → **PASS**. Confirmed: name=content
on the headline + `@[stacks 00OK]`; minimal-hypotheses claim accurate (a `k[x] ↠ k` witness shows the
`dim A ≤ dim S` half genuinely needs injectivity, while `ringKrullDim_le_of_integral` is injectivity-free);
no mis-homing; and the moved declarations are **statement-identical** to the deleted file (normalized diff =
namespace + docstrings + `@[stacks]` only). One optional tag-precision item raised and **actioned**:
`ringKrullDim_le_of_integral` is literally the dimension-inequality conjunct of [Stacks, Tag 00OJ], now tagged
`@[stacks 00OJ "the dimension inequality"]` (with the comment-string flagging the conjunct status); the
chain-lift's `00GU` likewise carries a "corollary, not verbatim" comment.

## Provenance

Branch `expedition/dimension-stack`. HEAD of `expedition/dimension-stack` (see `git log` — the R1 re-home commit). Build verified green at this tree.
