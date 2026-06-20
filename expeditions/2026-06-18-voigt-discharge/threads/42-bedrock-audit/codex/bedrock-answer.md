codex
**Naming & Scope**
- `codimRep_orbitRankLocus_eq_orbitLinearCodim`, `codimRepCanonical_orbitRankLocus_eq_*`, and the surrounding docstrings uniformly advertise “geometric codimension = expected codimension”. No identifier or prose hints at RLCT or a ½·codim payoff. Naming the discharge “Voigt’s lemma” matches the classical content (Ext¹ codimension equality), so there is no RLCT overclaim.
- The adjective “UNCONDITIONAL” is slightly loaded: the statements still require `[Field k] [IsAlgClosed k] [CharZero k]`. Internally “unconditional” only means “no extra `hVoigt` hypothesis”. That nuance is visible in the docstring parenthetical (“char 0, algebraically closed”), but the headline word could mislead a skim reader into thinking even char p is covered. Mild precision risk, not a blocker.

**Hypotheses**
- `[CharZero k]` is used solely to import the A4 submersion inequality; the code routes through `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`, whose proof chain explicitly needs CharZero (differential-independence). Given the recorded char‑p counterexamples, the hypothesis is honest and minimal.
- `[IsAlgClosed k]` flows in through the reverse inequality `finrank_range_deformationδ_le_varietyDim`: the proof demands the orbit ring be smooth at a k-point and uses residue-field identification; the docstring cites L1/M3. That dependence is real. The squeeze would collapse without it. No decorative assumptions detected.

**Finite Height vs `.toNat`**
- `codimRepCanonical_orbitRankLocus_eq_multSum_unconditional` states a ℤ-valued sum via `(codimRepCanonical …).toNat`. Since `codimRepCanonical` is an ENat height, `.toNat` would zero out ⊤. The safety net is the preceding ℕ∞ equality: `codimRepCanonical_orbitRankLocus_eq_finrank_deformationExt1_unconditional` proves the same codimension equals the finite `finrank` of Ext¹. That forces the height to live in ℕ, so `.toNat` is lossless. The right-hand quadratic sum is finite, so the final integer identity is meaningful. Headline 1 (pure ℕ∞) indeed keeps more information; Headline 2 merely repackages it for the quadratic-form formula.

**Additive Cancellation & Geometry**
- The cancellation step introduces `r : ℕ := finrank (range δ⁰)` before converting to ENat, so the addend is provably finite and the cancellability lemma applies. No ⊤ pathology.
- `codimRep (canonicalCoord d)` is the geometric codimension: earlier results identify `canonicalCoord` as the actual one-variable-per-entry embedding; `codimRep_add_varietyDim_eq_card` already computed dimension counts in that coordinate. No hidden coordinate dependence remains.
- The squeeze establishes smoothness of the orbit closure at the point, so the RLCT half-codim result can later sit on top without reopening dimensions; the Ext¹ identification is ready for analytic input.

**Primary Concern**
- The term “UNCONDITIONAL” risks reader confusion because theorems still demand `[IsAlgClosed k] [CharZero k]`. Consider renaming to “no Voigt hypothesis” or spelling the remaining assumptions in the name/docstring header.

No other precision defects surfaced.
tokens used
45,024
**Naming & Scope**
- `codimRep_orbitRankLocus_eq_orbitLinearCodim`, `codimRepCanonical_orbitRankLocus_eq_*`, and the surrounding docstrings uniformly advertise “geometric codimension = expected codimension”. No identifier or prose hints at RLCT or a ½·codim payoff. Naming the discharge “Voigt’s lemma” matches the classical content (Ext¹ codimension equality), so there is no RLCT overclaim.
- The adjective “UNCONDITIONAL” is slightly loaded: the statements still require `[Field k] [IsAlgClosed k] [CharZero k]`. Internally “unconditional” only means “no extra `hVoigt` hypothesis”. That nuance is visible in the docstring parenthetical (“char 0, algebraically closed”), but the headline word could mislead a skim reader into thinking even char p is covered. Mild precision risk, not a blocker.

**Hypotheses**
- `[CharZero k]` is used solely to import the A4 submersion inequality; the code routes through `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`, whose proof chain explicitly needs CharZero (differential-independence). Given the recorded char‑p counterexamples, the hypothesis is honest and minimal.
- `[IsAlgClosed k]` flows in through the reverse inequality `finrank_range_deformationδ_le_varietyDim`: the proof demands the orbit ring be smooth at a k-point and uses residue-field identification; the docstring cites L1/M3. That dependence is real. The squeeze would collapse without it. No decorative assumptions detected.

**Finite Height vs `.toNat`**
- `codimRepCanonical_orbitRankLocus_eq_multSum_unconditional` states a ℤ-valued sum via `(codimRepCanonical …).toNat`. Since `codimRepCanonical` is an ENat height, `.toNat` would zero out ⊤. The safety net is the preceding ℕ∞ equality: `codimRepCanonical_orbitRankLocus_eq_finrank_deformationExt1_unconditional` proves the same codimension equals the finite `finrank` of Ext¹. That forces the height to live in ℕ, so `.toNat` is lossless. The right-hand quadratic sum is finite, so the final integer identity is meaningful. Headline 1 (pure ℕ∞) indeed keeps more information; Headline 2 merely repackages it for the quadratic-form formula.

**Additive Cancellation & Geometry**
- The cancellation step introduces `r : ℕ := finrank (range δ⁰)` before converting to ENat, so the addend is provably finite and the cancellability lemma applies. No ⊤ pathology.
- `codimRep (canonicalCoord d)` is the geometric codimension: earlier results identify `canonicalCoord` as the actual one-variable-per-entry embedding; `codimRep_add_varietyDim_eq_card` already computed dimension counts in that coordinate. No hidden coordinate dependence remains.
- The squeeze establishes smoothness of the orbit closure at the point, so the RLCT half-codim result can later sit on top without reopening dimensions; the Ext¹ identification is ready for analytic input.

**Primary Concern**
- The term “UNCONDITIONAL” risks reader confusion because theorems still demand `[IsAlgClosed k] [CharZero k]`. Consider renaming to “no Voigt hypothesis” or spelling the remaining assumptions in the name/docstring header.

No other precision defects surfaced.
