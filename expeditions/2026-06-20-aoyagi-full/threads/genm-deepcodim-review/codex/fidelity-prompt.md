<task>
You are an independent Lean-4/Mathlib + algebraic-geometry reviewer. Audit ONE theorem for
FIDELITY: does the Lean statement + hypotheses faithfully capture the informal claim, with no
overclaim, no vacuity, no hidden gap, and an honest residual? I have withheld my own conclusion.
Give me YOUR independent read. Distinguish what you can prove/verify from what you are inferring.

## The informal claim being discharged
"CRrec = geometric κ_k" (a paper 'Finding B(2)'): the GEOMETRIC CODIMENSION of the closed
product-rank-≤r locus  Σ̄^r = { tuple of composable matrices A=(A_1,…,A_N) | rank(A_N⋯A_1) ≤ r }
in the tuple parameter space equals a combinatorial "composite-rank recursion" value κ, evaluated
at the shifted width vector d−r. This is a CODIMENSION identity only (NO analytic / RLCT / ½·codim
content is supposed to appear). It lives over an algebraically closed field of characteristic 0.

## The Lean theorem under review
```lean
theorem codimRepCanonical_productRankLocusLE_eq_minAdmRec
    {N : ℕ} {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (hN : 1 ≤ N) (hr : ∀ i, r ≤ d i) :
    codimRepCanonical (productRankLocusLE (k := k) d r) = (minAdmRec (dminus d r) : ℕ∞) := by
  have h_dr : (kostantPartitions d r).Nonempty := kostantPartitions_nonempty_of_le hN hr
  have h_d0 : (kostantPartitions (dminus d r) 0).Nonempty :=
    kostantPartitions_nonempty_of_le hN (fun _ => Nat.zero_le _)
  have hkey : (cCodim d r h_dr).toNat = minAdmRec (dminus d r) := by
    rw [← cCodim_rankShift hr h_d0 h_dr, ← minAdm_eq_cCodim (dminus d r) hN h_d0,
      Int.toNat_natCast, minAdmRec_eq_minAdm]
  rw [codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h_dr, hkey]
```

## The relevant definitions (verbatim, verified present at the reviewed commit)
```lean
-- mult d A = A_N ⋯ A_1  (product of the composable matrices)
def productRankLocusLE (d : Fin (N + 1) → ℕ) (r : ℕ) : Set (Tuple d) :=
  {A | (mult d A).rank ≤ r}

-- genuine geometric codimension: height of the vanishing ideal of the (canonical linear flattening)
-- image of Z in the polynomial ring, one variable per matrix entry.  ℕ∞-valued (Ideal.height).
noncomputable def codimRepCanonical (Z : Set (Tuple d)) : ℕ∞ :=
  codimRep (canonicalCoord d) Z
noncomputable def codimRep (coord) (Z) : ℕ∞ :=
  Ideal.height (MvPolynomial.vanishingIdeal (coord '' Z))

def dminus (d : Fin (N + 1) → ℕ) (r : ℕ) : Fin (N + 1) → ℕ := fun k ↦ d k - r  -- ℕ truncated sub

-- the layer-peeling composite-rank recursion κ:
def minAdmRec : {L : ℕ} → (M : Fin (L + 1) → ℕ) → ℕ
  | 0, _ => 0                                   -- single width (Fin 1)
  | 1, M => M 0 * M 1                           -- two widths (leaf)
  | (_ + 1 + 1), M =>                           -- ≥3 widths
      (Finset.range (min (M 0) (M 1) + 1)).inf'
        (fun t => (M 0 - t) * (M 1 - t) + minAdmRec (redChain t M))
-- redChain t M = Fin.cons t (fun i => M i.succ.succ)  (drops M 0,M 1, prepends the pivot rank t)
```

## The four banked lemmas the proof chains (verbatim signatures, verified present)
```lean
-- geometric side (quiver/orbit-closure; needs alg-closed + char 0):
theorem codimRepCanonical_productRankLocusLE_eq_cCodim_enat [IsAlgClosed k] [CharZero k]
    (d : Fin (N+1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty) :
    codimRepCanonical (productRankLocusLE (k:=k) d r) = ((cCodim d r h).toNat : ℕ∞)
-- cCodim d r h : ℤ ; a separate banked fact shows 0 ≤ cCodim d r h.

-- rank shift (LR Lemma 4.5):
theorem cCodim_rankShift {d : Fin (N+1) → ℕ} {r : ℕ} (hr : ∀ k, r ≤ d k)
    (h₀ : (kostantPartitions (dminus d r) 0).Nonempty)
    (hr' : (kostantPartitions d r).Nonempty) :
    cCodim (dminus d r) 0 h₀ = cCodim d r hr'

-- QIP ↔ Ext identity (needs 1 ≤ L):
theorem minAdm_eq_cCodim (M : Fin (L+1) → ℕ) (hL : 1 ≤ L)
    (h : (kostantPartitions M 0).Nonempty) : (minAdm M : ℤ) = cCodim M 0 h

-- layer-peel (all widths, NO hypotheses):
theorem minAdmRec_eq_minAdm (M : Fin (L+1) → ℕ) : minAdmRec M = minAdm M

-- helper: needs 1 ≤ N (at N=0 the corner IS the diagonal, forcing r = d₀):
theorem kostantPartitions_nonempty_of_le {d : Fin (N+1) → ℕ} {r : ℕ}
    (hN : 1 ≤ N) (hr : ∀ k, r ≤ d k) : (kostantPartitions d r).Nonempty
```

<context>
- `cCodim d r h : ℤ` and there is a banked proof it is ≥ 0, so `.toNat` is lossless.
- N+1 widths ⟹ N weight matrices; the hypothesis hr : ∀ i, r ≤ d i restricts r to [0, min_i d_i].
- The final `rw` closes by reflexivity after both sides become `(minAdmRec (dminus d r) : ℕ∞)`.
</context>

<questions>
1. ASSEMBLY: does the proof genuinely chain the four lemmas (+ Int.toNat_natCast) to the stated
   conclusion, or is there a step that only type-checks vacuously / a cast that silently drops
   information? Trace the goal state through each rewrite and confirm it closes honestly.
2. HYPOTHESES: are `hN : 1 ≤ N` and `hr : ∀ i, r ≤ d i` correct and (roughly) minimal? Is a needed
   hypothesis missing (⟹ the stated equality could be FALSE for some instance in scope), or is an
   extra hypothesis silently narrowing a claim that actually holds more generally (⟹ under-claim)?
   Consider the r-range endpoints r=0 and r=min_i d_i (where dminus has a 0 entry) specifically.
3. CAST / ℕ∞: the equality is at type ℕ∞, RHS is a coercion of a ℕ. Any edge where LHS could be ⊤,
   or a ⊥/0 slip, or a coercion mismatch? Is the r = min_i d_i case (whole space, codim should be 0)
   consistent on BOTH sides (does minAdmRec of a vector with a 0 entry give 0)?
4. RESIDUAL / SCOPE: the theorem is over [IsAlgClosed][CharZero] (i.e. ℂ-like), not the real
   parameter space. Is it legitimate to call this an honest discharge of the informal claim with a
   NAMED (not faked) ℝ/ℂ residual? Does anything in the statement smuggle in analytic/RLCT content?
5. VACUITY: is the theorem non-vacuous — is {rank ≤ r} at r=0 (the zero-product locus) a genuine
   proper subvariety with a genuine finite positive codim, and does the (2,2,2), r=0 instance give a
   sensible nonzero value (the paper's C=3)?
</questions>

<output_contract>
For EACH of the 5 questions: a one-line verdict (OK / CONCERN / CANNOT-TELL) then ≤3 lines of
justification. If you find a genuine fidelity defect, give the specific instance (concrete d, r) and
the minimal repair. End with an overall one-line verdict: FAITHFUL / OVERCLAIM / UNDERCLAIM / VACUOUS
/ UNDER-SPECIFIED. Be terse and object-level. Do not restate the question text.
</output_contract>
</task>
