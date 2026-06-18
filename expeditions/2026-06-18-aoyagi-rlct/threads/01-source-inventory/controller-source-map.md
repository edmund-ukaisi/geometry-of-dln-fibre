# Controller source map - Aoyagi 2023

Status: initial controller map from local `pdftotext` extraction. This is not a
checked reproduction. Source inventory thread 01 must verify page references
against the PDF.

Source used: `paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf`.

## Page anchors

| PDF page | Source item | Local use |
|---|---|---|
| 5 | Definition 1: log canonical threshold/RLCT and order; ideal convention via sum of squares | Claim A0 interface vocabulary |
| 5 | Lemma 1: ideal generator comparison for RLCT | Algebraic ideal replacement; likely proved if elementary enough or kept as analytic-interface side condition |
| 5 | Definition 2: matrix norm and generated ideal notation `⟨C⟩` | DLN loss/ideal translation |
| 6 | Hironaka/normal-crossing extraction formula for `λ` and `θ` | Cited normal-crossing-to-RLCT interface A0 |
| 6-7 | Theorem 1, cited from [12], three-layer formula | Context/special case; not the multi-layer main theorem |
| 8 | Main setup: matrices `A^(s)`, parameter set, true product rank `r` | Claims A2/A6 source hypotheses |
| 8-9 | Definition 3: `M^(s) = H^(s)-r`, selected set `M = {M^(S_j)}`, `ℓ`, integer `M`, and `a` | Final formula parameters; Claims A5/A6 |
| 9 | Theorem 2: multi-layer main theorem, formulas for `λ` and `θ` | Final target Claim A6 |
| 10-11 | Lemma 2: full-rank block/Schur-complement coordinate reduction | Claim A1 |
| 11-13 | Theorem 3: iterated product reduction to regular block and reduced product `∏ C^(s)` | Claim A2 |
| 13 | Regular-variable contribution after Theorem 3 | Claim A2/A6; interface-sensitive |
| 14 | Theorem 4: deepest singular point method | Claim A3; probe whether analytic or elementary |
| 14 | Reduction to `r(s)=r`; definitions of reduced matrices `C^(s)` | Claims A2/A4 |
| 14-15 | Inductive statement for blow-up bookkeeping; `T_{S,k}`, `b_i`, `D_J`, comparability invariant | Claim A4 |
| 15-18 | Case 1, including Case 1(1) and Case 1(2) charts | Claim A4 |
| 19-22 | Case 2 charts and induction with `S` increased | Claim A4 |
| 22 | Terminal diagonal ideal `⟨diag(b_i)⟩` and candidate exponent formula for `M_{s,k}` | Claims A4/A5 |
| 22-24 | Conversion from exponent vectors to `F_j` expression and quadratic form | Claim A5 |
| 24 | Lemma 3: finite quadratic minimisation | Claim A5 |
| 24-25 | Application of Lemma 3 to `2λ_O(||∏ C^(s)||^2)` | Claim A5/A6 |
| 25 | Lemma 4: interval of exponent vectors corresponding to `λ` | Claim A5 |
| 25-27 | Lemma 5: `θ = a(ℓ-a)+1` and construction of local coordinates reaching the bound | Claim A5 |
| 27 | Completion: construct blow-up process with the selected vectors | Claims A4/A6 |

## Immediate source-fidelity notes

- The multi-layer main theorem is Theorem 2 on PDF page 9. Theorem 1 is a
  cited earlier three-layer theorem and should not be named as the final target.
- Aoyagi's `θ` is RLCT pole order/multiplicity. Use `rlctOrder` in local names.
- The normal-crossing extraction formula on page 6 is the planned cited
  analytic boundary.
- The regular-variable contribution after Theorem 3 is the first place where
  an algebraic block reduction is converted into an RLCT contribution; this
  needs reproduction and analytic-interface checking before Lean formalisation.
