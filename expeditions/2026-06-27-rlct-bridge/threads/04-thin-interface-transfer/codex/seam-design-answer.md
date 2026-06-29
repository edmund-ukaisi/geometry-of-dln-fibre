**(1) SEAM**

Choose **(a)** for this tide: keep a clean, self-contained thin interface on the existing payoff side. The real `rlctAt` layer is local, `ℝ≥0∞`-valued, `Params H`-based, and currently in-progress; the payoff API is global, `Tuple ℝ d`-based, and axiom-clean. Forcing (b) now pulls in `Params↔Tuple`, index reversal, trace-loss vs SOS-loss, and global `inf local rlctAt` all at once.

Minimal non-re-buried seam:

```lean
structure RlctInterface (d : Fin (N+1) → ℕ)
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] (ι : ℝ →+* K) where
  rlct : (Tuple (k := ℝ) d → ℝ) → ℝ
  realCodim : Set (Tuple (k := ℝ) d) → ℕ∞

  cited_quad_block : ...          -- C1
  cited_sumSq_upper : ...         -- C2
  cited_nc_lower : ...            -- C3, via explicit resolution datum
  transfer_real_complex : ...     -- T
```

Add later, separately, not now:

```lean
-- future bridge, not part of this clean tide
rlct_eq_iInf_rlctAt_after_transport :
  I.rlct F = ENNReal.toReal (⨅ w ∈ zeroSet F, rlctAt H (F transported_to_Params) w)
```

**(2) TRANSFER T**

**No**, not honestly provable in one tide from `realizerD` rationality alone. That fact gives real points on intended top components, but Lean still needs a real/complex dimension bridge: real smooth/top-dimensional locus, Zariski density of real points in each relevant component, real analytic dimension = algebraic dimension, and comparison with complex Krull height. I do not see that bridge already available in this repo, and I would not assume Mathlib v4.29 has it.

Do **not** use

```lean
codimRepCanonical (k := ℝ) (fibre (k := ℝ) d B)
```

as the analytic intermediate. Over non-algebraically-closed fields this is height of the vanishing ideal of real points; it can differ from complex geometric codimension in general. The honest intermediate for C2 is a **real analytic/semialgebraic codimension** of the real zero locus, not `codimRepCanonical` over `ℝ`.

State T directly:

```lean
transfer_real_complex :
  ∀ (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) (r : ℕ),
    0 < N →
    B.rank = r →
    r ≤ Finset.univ.inf' Finset.univ_nonempty d →
    realCodim (fibre (k := ℝ) d B)
      = codimRepCanonical (fibre (k := K) d (B.map ι))
```

If you later prove it via `codimRepCanonical (k := ℝ)`, that should be an internal lemma plus an extra theorem `realCodim = codimRepCanonical ℝ`, not the public factorization.

**(3) C2/C3/R2/R3**

Use residual generators explicitly:

```lean
def residuals (d) (B) :
    TargetCoord d → Tuple (k := ℝ) d → ℝ := ...

def sos (f : Fin m → X → ℝ) (x : X) : ℝ :=
  ∑ i, (f i x)^2

def commonZero (f : Fin m → X → ℝ) : Set X :=
  {x | ∀ i, f i x = 0}
```

C2:

```lean
cited_sumSq_upper :
  ∀ {m : ℕ} (f : Fin m → Tuple (k := ℝ) d → ℝ),
    rlct (sos f) ≤ ((realCodim (commonZero f)).toNat : ℝ) / 2
```

C3 must mention the ideal generators, not just the set:

```lean
structure NCLogPrincipalization
    (f : Fin m → Tuple (k := ℝ) d → ℝ) where
  Div : Type
  fintypeDiv : Fintype Div
  nonemptyDiv : Nonempty Div
  k h : Div → ℕ
  -- plus the actual chart / pullback / unit / Jacobian-order data,
  -- or else name it AssumedNCLogPrincipalization.

def ncThreshold (D : NCLogPrincipalization f) : ℝ :=
  ((⨅ j : D.Div, ((D.h j + 1 : ℝ≥0∞) / (2 * (D.k j : ℝ≥0∞)))).toReal)

cited_nc_lower :
  ∀ {m} (f : Fin m → Tuple (k := ℝ) d → ℝ)
    (D : NCLogPrincipalization f),
    ncThreshold D ≤ rlct (sos f)
```

Named matching hypotheses:

```lean
R2_upper_match :
  realCodim (commonZero (residuals d B))
    = codimRepCanonical (fibre (k := K) d (B.map ι))
-- preferably proved from residual-zero-set = real fibre + transfer_real_complex.

R3_lower_match :
  ncThreshold D
    = ((codimRepCanonical (fibre (k := K) d (B.map ι))).toNat : ℝ) / 2
```

Derived theorem shape:

```lean
theorem cited_aoyagi_dln_derived
    (I : RlctInterface d K ι)
    (D : NCLogPrincipalization (residuals d B))
    (hloss : lossDLN d B = sos (residuals d B))
    (hR2 : R2_upper_match I B)
    (hR3 : R3_lower_match D B) :
    I.rlct (lossDLN d B)
      = ((codimRepCanonical (fibre (k := K) d (B.map ι))).toNat : ℝ) / 2 :=
by
  rw [hloss]
  exact le_antisymm
    ((I.cited_sumSq_upper _).trans_eq (by rw [hR2]))
    (by rw [← hR3]; exact I.cited_nc_lower _ D)
```

**(4) NAME=CONTENT**

Avoid these traps:

1. Do not keep a field named `cited_aoyagi_dln`; make it a **derived theorem** with `D`, `R2`, `R3`, and `transfer_real_complex` visible.

2. Do not name `codimRepCanonical (k := ℝ)` as `realCodim`. That hides the non-algebraically-closed issue.

3. Do not let `NCLogPrincipalization` be only `(k h : Div → ℕ)`. Then C3 would prove lower bounds from arbitrary numbers. Either include real chart/principalization data, or name it `AssumedNCLogPrincipalization`.

**(5) VERDICT**

Proceed with **(a)**: clean opaque global `rlct` interface on `Tuple`, C1/C2/C3 split out, and **T as an explicit carried field**, not proved this tide.