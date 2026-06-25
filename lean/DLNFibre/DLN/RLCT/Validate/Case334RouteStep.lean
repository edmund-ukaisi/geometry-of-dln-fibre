import DLNFibre.DLN.RLCT.Validate.RouteMRecursion
import DLNFibre.DLN.RLCT.Validate.SchurState

/-!
# `DLNFibre.DLN.RLCT.Validate.Case334RouteStep` — the BINDING coupled `diag(b)` anchor `(3,3,4)` (fm3)

The third decide-checked anchor for the committed `RouteStep` / `PivotWitness` / `foldFamily` value-side,
alongside `(2,2,2)` (`Case222RouteStep`) and `(3,2,3)` (`Case323RouteStep`). This one is special: it is the
GENUINELY-BINDING coupled `diag(b)` witness the resolution-mechanism certificate
(`theory/aoyagi-2023-reproduction/verify-r1-diagb-334.md`) identifies as the case a *threshold-only /
per-row-multiplicity* recursion gets WRONG (it computes `3`, the true value is `4`).

`(3,3,4)` is an `L=2` reduced-rank-regression core (`C¹` `3×3`, `C²` `3×4`). Branch lattice (cert §1):
`Mval(t₁) = (3−t₁)² + 4·t₁ → 9, 8, 9, 12` for `t₁ = 0,1,2,3`. The **unique** minimiser is `t₁ = 1`,
`Mval = 8`, `rlct = ½·8 = 4` — anchored to the published Aoyagi-Watanabe (2005) RRR closed form (11/11
spot-checks, cert §1). The minimiser is a genuine **corank-`(2,2)` partial drop** (`0 < 1 < 3`) — the
smallest reduced-width vector whose every minimiser is corank-`≥2` partial.

## Why this anchor matters for the `RouteStep` datum (the reconciliation, controller task (A))
The certificate proves a per-row *multiplicity* recursion (which models the two bottom rows of the residual
`Δ`-block as INDEPENDENTLY weighted, `δ₁,δ₂`) computes the DS-part as `½+½=1`, hence total `2+1=3 ≠ 4` —
the WRONG core RLCT, and since `t=(1,0)` is the minimiser, the error BINDS. The certified fix is the
coupled symbolic support `support : Gen → Finset DivVar` with the SHARING identity (one radial `a` divides
all DS generators; the shear `e` couples the second row), which a per-row count cannot encode.

**The committed `RouteStep` datum does NOT use a per-row multiplicity, so the obstruction does not bind it.**
Its per-cell `codim : ℕ` is the GEOMETRIC codimension `(Mval M₀ T).toNat` of an admissible rank-pattern
stratum (the `PivotWitness M₀` field), read from the CLOSED Aoyagi `Mval` form anchored at the ROOT `M₀` —
NOT re-derived by a row-wise resolution recursion. The value fold `½·minAdm` is `½·8 = 4` here (this file's
`case334_routeStep_value`), the certified-correct value, BECAUSE it reads `Mval M₀ (1,0) = 8` directly. The
sharing identity is not "lost"; it is never re-derived per-row — it is encoded once, globally, in the
closed `Mval` form. This anchor LOCKS that: `(3,3,4)`, the witness the certificate says breaks a per-row
recursion, folds to the right value `4` over the committed datum.
-/

open scoped BigOperators ENNReal
namespace DLNFibre.DLN.RLCT

/-- The `(3,3,4)` chain: `M = (3,3,4)` on `Fin 3` (`L = 2`). The `L=2` RRR core; the binding coupled
`diag(b)` witness (cert `verify-r1-diagb-334.md`). -/
abbrev M334route : Fin 3 → ℕ := ![3, 3, 4]

/-! ## The two root-anchored pivot witnesses (the `(3,3,4)` admissible strata) -/

/-- `T = (0,0)` is admissible for `M334`, with `Mval = 9` (the `t₁=0` full-radial stratum, NON-binding —
`9 > 8 = minAdm`). The root-anchored `PivotWitness M334route 9`. -/
def pivotWitness334_root : PivotWitness M334route 9 where
  T := ![0, 0]
  hAdm := by decide
  hCodim := by decide

/-- `T = (1,0)` is admissible for `M334`, with `Mval = 8 = minAdm` (the BINDING corank-`(2,2)` partial-drop
stratum, the unique minimiser, `rlct = 4`). The root-anchored `PivotWitness M334route 8` — the achiever's
binding divisor, the genuinely-coupled `diag(b)` branch the certificate certifies at `4`. -/
def pivotWitness334_achiever : PivotWitness M334route 8 where
  T := ![1, 0]
  hAdm := by decide
  hCodim := by decide

/-- `minAdm(M334) = 8` (so `lambdaCore(3,3,4) = 4`, matching the published RRR closed form). -/
theorem minAdm_M334 :
    ((Adm M334route).inf' (Adm_nonempty M334route) (Mval M334route)).toNat = 8 := by decide

/-! ## The `(3,3,4)` value folds to `4` over the committed family — the certified-correct value -/

/-- The single binding-path leaf's codim-list `[9, 8]` — the `(3,3,4)` achiever path (root codim 9,
achiever codim 8 = minAdm). The `PivotWitness M334route` for each entry: `9 ↦ root`, `8 ↦ achiever`. -/
def codimsOf334 : Unit → List ℕ := fun _ => [9, 8]

/-- Every codim on the `(3,3,4)` leaf path carries a root-anchored `PivotWitness M334route`. (`9 ↦ root`,
`8 ↦ achiever`; the codim is recovered from the membership proof, then the matching witness is returned.) -/
def codimsOf334_witnessed :
    ∀ i : Unit, ∀ c ∈ codimsOf334 i, PivotWitness M334route c := by
  intro _ c hc
  refine if h9 : c = 9 then h9 ▸ pivotWitness334_root
    else if h8 : c = 8 then h8 ▸ pivotWitness334_achiever else ?_
  exfalso
  simp only [codimsOf334, List.mem_cons, List.not_mem_nil, or_false] at hc
  omega

/-- **The `(3,3,4)` value folds to `4` — the certified-correct value, NOT the threshold-only `3`.**
Over the one-leaf family with `codimsOf = [9, 8]` (the achiever path, both codims root-anchored-witnessed,
`8 = minAdm` binding), the `⨅` of the `foldDivisors` thresholds is `½·minAdm = ½·8 = 4 =
lambdaCore(3,3,4)`. This is the BINDING coupled `diag(b)` witness (cert `verify-r1-diagb-334.md`): a per-row
multiplicity recursion would get `3` here (the minimiser is mishandled), but the committed `Mval`-anchored
datum reads `Mval M₀ (1,0) = 8` directly and folds to the right value `4`. The corank-2 obstruction does NOT
bind the committed datum. -/
theorem case334_routeStep_value :
    (⨅ i : Unit, monomialThreshold (MonoData.foldDivisors (codimsOf334 i)).d
        (MonoData.foldDivisors (codimsOf334 i)).k (MonoData.foldDivisors (codimsOf334 i)).h)
      = 4 := by
  have hkey := foldFamily_iInf_eq_half_minAdm M334route codimsOf334
    (by rw [minAdm_M334]; omega) codimsOf334_witnessed ()
    (by rw [minAdm_M334]; simp only [codimsOf334, List.mem_cons]; decide)
  rw [hkey, minAdm_M334]
  -- `(8 : ℝ≥0∞) / 2 = 4`: `4 * 2 / 2 = 4` via `mul_div_cancel_right`.
  rw [show ((8 : ℕ) : ℝ≥0∞) = (4 : ℝ≥0∞) * 2 by norm_num,
    ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]

/-! ## A concrete `RouteStep M334 M334` BRANCH — the binding coupled datum is inhabited

The committed `RouteStep.branch` is exercised on the binding coupled witness: `schurState` splits, the two
codims `9`/`8`, and the two root-anchored `PivotWitness`es. Confirms the committed inductive's `branch`
admits a genuine (non-vacuous) `(3,3,4)` term carrying the certified binding codim `8`. `hlo` (the
`schurState` precondition) holds since `M334 s ≥ 3 ≥ 1`. -/

/-- `M334` satisfies the `schurState` precondition (`1 ≤ M s` at the pivot vertices `s ≤ 1`). -/
theorem M334_hlo : ∀ s : Fin 3, s.val ≤ 1 → 1 ≤ M334route s := by decide

/-- **The committed `RouteStep M334 M334` branch is inhabited with the binding coupled data.** Two pivot
cells (`Bool`), each with the `schurState M334` split, codims `9`/`8`, and the root-anchored
`PivotWitness M334route` (`root`/`achiever`). Confirms the `branch` constructor is inhabitable on the
BINDING coupled `diag(b)` anchor `(3,3,4)` — the case the resolution certificate identifies as breaking a
per-row recursion. The committed `Mval`-anchored datum carries the genuine binding codim `8`. -/
def case334_routeStep_branch : RouteStep M334route M334route :=
  .branch Bool inferInstance ⟨true⟩
    (fun _ => schurState M334route M334_hlo)
    (fun b => if b then 9 else 8)
    (fun b => by
      by_cases hb : b = true
      · simpa [hb] using pivotWitness334_root
      · simp only [Bool.not_eq_true] at hb
        simpa [hb] using pivotWitness334_achiever)

/-! ## The companion anchor `(4,4,2,2)` — the corank-2 branch is present but NON-binding

`(4,4,2,2)` (`L=3`: `C¹` `4×4`, `C²` `4×2`, `C³` `2×2`) is the witness the original R1 brief named (with a
target `7/2`), CORRECTED by the certificate (`verify-r1-diagb-4422.md`): the true core RLCT is `2`, not
`7/2`. The corank-`(2,2)` `diag(b)` branch `t=(2,1,0)` DOES occur and DOES carry `Mval = 7` (ratio `7/2`),
but it does **not** set the RLCT — the binding branch is the CLEAN radial `t=(4,2,0)` with `Mval = 4`, ratio
`2` (`minAdm = 4`, `lambdaCore = 2`). So `(4,4,2,2)` exercises the corank-2 mechanism on a NON-binding
branch: a recursion that mishandles it still lands the right value `2` (a different, clean branch binds).

This anchor LOCKS that distinction over the committed datum: a branch with both the non-binding corank-2
cell (codim `7`) and the binding clean cell (codim `4 = minAdm`), whose value fold is `½·4 = 2` — the `min`
correctly takes the clean binder, NOT `7/2`. It is the contrast partner to `(3,3,4)` (where the corank-2
branch IS the unique minimiser, so it sets the value). Per the certificate (§4), `(4,4,2,2)` must NOT be
used to assert a `7/2` value or as the binding corank-2 case; this anchor uses it correctly — as the
non-binding contrast. -/

/-- The `(4,4,2,2)` chain: `M = (4,4,2,2)` on `Fin 4` (`L = 3`). The brief's original (corrected) witness;
the corank-2 branch is non-binding here (cert `verify-r1-diagb-4422.md`). -/
abbrev M4422route : Fin 4 → ℕ := ![4, 4, 2, 2]

/-- `T = (2,1,0)` is admissible for `M4422`, with `Mval = 7` (the corank-`(2,2)` `diag(b)` branch, the
brief's named branch — but NON-binding, `7 > 4 = minAdm`). The root-anchored `PivotWitness M4422route 7`. -/
def pivotWitness4422_corank2 : PivotWitness M4422route 7 where
  T := ![2, 1, 0]
  hAdm := by decide
  hCodim := by decide

/-- `T = (4,2,0)` is admissible for `M4422`, with `Mval = 4 = minAdm` (the BINDING CLEAN radial branch,
layer-1 corank `(0,0)`, ratio `2`). The root-anchored `PivotWitness M4422route 4` — the achiever's binding
divisor (clean, NOT the corank-2 branch). -/
def pivotWitness4422_achiever : PivotWitness M4422route 4 where
  T := ![4, 2, 0]
  hAdm := by decide
  hCodim := by decide

/-- `minAdm(M4422) = 4` (so `lambdaCore(4,4,2,2) = 2`, NOT `7/2` — the certificate's correction). -/
theorem minAdm_M4422 :
    ((Adm M4422route).inf' (Adm_nonempty M4422route) (Mval M4422route)).toNat = 4 := by decide

/-- The `(4,4,2,2)` binding-path leaf's codim-list `[7, 4]` — the non-binding corank-2 codim `7` and the
binding clean codim `4 = minAdm`. The `PivotWitness M4422route` for each entry: `7 ↦ corank2`, `4 ↦
achiever`. -/
def codimsOf4422 : Unit → List ℕ := fun _ => [7, 4]

/-- Every codim on the `(4,4,2,2)` leaf path carries a root-anchored `PivotWitness M4422route`. (`7 ↦
corank2`, `4 ↦ achiever`.) -/
def codimsOf4422_witnessed :
    ∀ i : Unit, ∀ c ∈ codimsOf4422 i, PivotWitness M4422route c := by
  intro _ c hc
  refine if h7 : c = 7 then h7 ▸ pivotWitness4422_corank2
    else if h4 : c = 4 then h4 ▸ pivotWitness4422_achiever else ?_
  exfalso
  simp only [codimsOf4422, List.mem_cons, List.not_mem_nil, or_false] at hc
  omega

/-- **The `(4,4,2,2)` value folds to `2` — the corank-2 branch does NOT bind.** Over the family with
`codimsOf = [7, 4]` (the non-binding corank-2 codim `7` present alongside the binding clean codim `4 =
minAdm`), the `⨅` of the `foldDivisors` thresholds is `½·minAdm = ½·4 = 2 = lambdaCore(4,4,2,2)`. The `min`
correctly takes the clean binder, NOT the corank-2 branch's `7/2`. This is the certificate's correction
(`verify-r1-diagb-4422.md`): `(4,4,2,2)` is the corank-2 mechanism on a NON-binding branch — the contrast
partner to the binding `(3,3,4)`. -/
theorem case4422_routeStep_value :
    (⨅ i : Unit, monomialThreshold (MonoData.foldDivisors (codimsOf4422 i)).d
        (MonoData.foldDivisors (codimsOf4422 i)).k (MonoData.foldDivisors (codimsOf4422 i)).h)
      = 2 := by
  have hkey := foldFamily_iInf_eq_half_minAdm M4422route codimsOf4422
    (by rw [minAdm_M4422]; omega) codimsOf4422_witnessed ()
    (by rw [minAdm_M4422]; simp only [codimsOf4422, List.mem_cons]; decide)
  rw [hkey, minAdm_M4422]
  -- `(4 : ℝ≥0∞) / 2 = 2`: `2 * 2 / 2 = 2` via `mul_div_cancel_right`.
  rw [show ((4 : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) * 2 by norm_num,
    ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]

/-- `M4422` satisfies the `schurState` precondition (`1 ≤ M s` at the pivot vertices `s ≤ 1`). -/
theorem M4422_hlo : ∀ s : Fin 4, s.val ≤ 1 → 1 ≤ M4422route s := by decide

/-- `M4422` is not a leaf node (every width `≥ 1`). -/
theorem not_isLeafNode_M4422 : ¬ isLeafNode M4422route := by decide

/-- **The committed `RouteStep M4422 M4422` branch is inhabited with the non-binding corank-2 + binding
clean data.** Two pivot cells (`Bool`): the corank-2 `diag(b)` cell (codim `7`, NON-binding) and the clean
binding cell (codim `4 = minAdm`). Confirms the `branch` constructor carries BOTH the corank-2 branch (the
brief's named branch) AND the clean binder that actually sets the value — the certificate's correction made
concrete. -/
def case4422_routeStep_branch : RouteStep M4422route M4422route :=
  .branch Bool inferInstance ⟨true⟩
    (fun _ => schurState M4422route M4422_hlo)
    (fun b => if b then 7 else 4)
    (fun b => by
      by_cases hb : b = true
      · simpa [hb] using pivotWitness4422_corank2
      · simp only [Bool.not_eq_true] at hb
        simpa [hb] using pivotWitness4422_achiever)

/-! ## The deep-sharing `L=3` anchor `(3,3,5,4)` — a coupled minimiser NOT reducible to the `L=2` RRR row

`(3,3,4)` is an `L=2` RRR core, so its coupled `diag(b)` mechanism is the `Δ`-internal shear (cert §6 — no
shared DEEPER layer `Cˢ`). The `(3,3,4)` certificate flags the next construction: an `L=3` binder whose
minimiser has both corank-≥2 AND a shared deep factor, exercising the deep-factor sharing too. `(3,3,5,4)`
(`L=3`: `C¹` `3×3`, `C²` `3×5`, `C³` `5×4`) is exactly such a case (a decorrelated-Codex stress proposal,
red-teaming the value-fold reconciliation): its UNIQUE minimiser is `T = (1,1,0)` with `Mval = 8`, an
INTERIOR partial drop (`T₁ = 1 > 0` — the property-breaker shape, not the trivial `T* = (1,0)` of the `L=2`
anchors), giving `rlct = ½·8 = 4`.

This anchor LOCKS the value fold on an `L=3` coupled minimiser not reducible to the `L=2` RRR closed form —
strengthening the bedrock past the "11 spot-checks are evidence, not a theorem" caveat: the committed
`Mval`-anchored datum reads `Mval M₀ (1,1,0) = 8` directly and folds to `4`, independent of any `L=2`
reduction. -/

/-- The `(3,3,5,4)` chain: `M = (3,3,5,4)` on `Fin 4` (`L = 3`). The deep-sharing `L=3` coupled witness; its
unique minimiser `T=(1,1,0)` is an interior partial drop (cert §6 "next construction"). -/
abbrev M3354route : Fin 4 → ℕ := ![3, 3, 5, 4]

/-- `T = (0,0,0)` is admissible for `M3354`, with `Mval = 9` (the full-radial stratum, NON-binding —
`9 > 8 = minAdm`). The root-anchored `PivotWitness M3354route 9`. -/
def pivotWitness3354_root : PivotWitness M3354route 9 where
  T := ![0, 0, 0]
  hAdm := by decide
  hCodim := by decide

/-- `T = (1,1,0)` is admissible for `M3354`, with `Mval = 8 = minAdm` (the BINDING interior partial-drop
stratum, the unique minimiser, `rlct = 4`). The root-anchored `PivotWitness M3354route 8` — the `L=3`
deep-sharing achiever (interior `T₁ = 1 > 0`, NOT reducible to the `L=2` RRR row). -/
def pivotWitness3354_achiever : PivotWitness M3354route 8 where
  T := ![1, 1, 0]
  hAdm := by decide
  hCodim := by decide

/-- `minAdm(M3354) = 8` (so `lambdaCore(3,3,5,4) = 4`); the minimiser `T=(1,1,0)` is unique. -/
theorem minAdm_M3354 :
    ((Adm M3354route).inf' (Adm_nonempty M3354route) (Mval M3354route)).toNat = 8 := by decide

/-- The `(3,3,5,4)` binding-path leaf's codim-list `[9, 8]` — the non-binding root codim `9` and the binding
interior-partial-drop codim `8 = minAdm`. (`9 ↦ root`, `8 ↦ achiever`.) -/
def codimsOf3354 : Unit → List ℕ := fun _ => [9, 8]

/-- Every codim on the `(3,3,5,4)` leaf path carries a root-anchored `PivotWitness M3354route`. -/
def codimsOf3354_witnessed :
    ∀ i : Unit, ∀ c ∈ codimsOf3354 i, PivotWitness M3354route c := by
  intro _ c hc
  refine if h9 : c = 9 then h9 ▸ pivotWitness3354_root
    else if h8 : c = 8 then h8 ▸ pivotWitness3354_achiever else ?_
  exfalso
  simp only [codimsOf3354, List.mem_cons, List.not_mem_nil, or_false] at hc
  omega

/-- **The `(3,3,5,4)` value folds to `4` on an `L=3` coupled minimiser.** Over the family with `codimsOf =
[9, 8]` (the binding interior-partial-drop codim `8 = minAdm`), the `⨅` of the `foldDivisors` thresholds is
`½·minAdm = ½·8 = 4 = lambdaCore(3,3,5,4)`. The deep-sharing `L=3` witness (cert §6): the committed
`Mval`-anchored datum reads `Mval M₀ (1,1,0) = 8` directly — folding to the right value on a coupled
minimiser NOT reducible to the `L=2` RRR row. -/
theorem case3354_routeStep_value :
    (⨅ i : Unit, monomialThreshold (MonoData.foldDivisors (codimsOf3354 i)).d
        (MonoData.foldDivisors (codimsOf3354 i)).k (MonoData.foldDivisors (codimsOf3354 i)).h)
      = 4 := by
  have hkey := foldFamily_iInf_eq_half_minAdm M3354route codimsOf3354
    (by rw [minAdm_M3354]; omega) codimsOf3354_witnessed ()
    (by rw [minAdm_M3354]; simp only [codimsOf3354, List.mem_cons]; decide)
  rw [hkey, minAdm_M3354]
  -- `(8 : ℝ≥0∞) / 2 = 4`.
  rw [show ((8 : ℕ) : ℝ≥0∞) = (4 : ℝ≥0∞) * 2 by norm_num,
    ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]

/-- `M3354` satisfies the `schurState` precondition (`1 ≤ M s` at the pivot vertices `s ≤ 1`). -/
theorem M3354_hlo : ∀ s : Fin 4, s.val ≤ 1 → 1 ≤ M3354route s := by decide

/-- `M3354` is not a leaf node (every width `≥ 1`). -/
theorem not_isLeafNode_M3354 : ¬ isLeafNode M3354route := by decide

/-- **The committed `RouteStep M3354 M3354` branch is inhabited with the `L=3` deep-sharing data.** Two pivot
cells (`Bool`): the non-binding root cell (codim `9`) and the binding interior-partial-drop cell (codim
`8 = minAdm`). Confirms the `branch` constructor carries a genuine `L=3` coupled minimiser whose `T=(1,1,0)`
has an interior nonzero entry — the deep-sharing leg the `(3,3,4)` certificate flagged. -/
def case3354_routeStep_branch : RouteStep M3354route M3354route :=
  .branch Bool inferInstance ⟨true⟩
    (fun _ => schurState M3354route M3354_hlo)
    (fun b => if b then 9 else 8)
    (fun b => by
      by_cases hb : b = true
      · simpa [hb] using pivotWitness3354_root
      · simp only [Bool.not_eq_true] at hb
        simpa [hb] using pivotWitness3354_achiever)

end DLNFibre.DLN.RLCT
