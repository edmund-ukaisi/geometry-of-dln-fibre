<task>
A formalisation has a FALSE-as-stated proof obligation. I have CONFIRMED (exact index
algebra + a numeric witness) that it is false for a non-front pivot. I need you to
INDEPENDENTLY adjudicate the obstruction and rank repair routes. This is L=2 deep linear
network RLCT geometry; pure linear algebra, no Lean.

## CONFIRMED FACTS (do not re-derive; adjudicate whether they imply the obstruction)

Objects: H0, Hmid, H2=H_last widths; rank r; pivot embedding `J : Fin r ↪ Fin H2` (B's r pivot columns,
NOT necessarily {0..r-1}). `rThr` = `Fin n ≃ Fin r ⊕ Fin(n-r)` splitting off first r. `pivotThr J` =
`Fin H2 ≃ Fin r ⊕ Fin(H2-r)` whose left block enumerates sorted pivot columns range(J).
`colPerm_J(M)(i,j) = M(i, π_J(j))`, `π_J = rThr.symm ∘ (pivotThr J)`, a column permutation of the H2 side.

FACT 1 (established): the framed reconstruction's last layer satisfies
  `F_1 = Pf_1·deepest_1·Qf_1 + Pf_1·colPerm_J(deviation_1)·Qf_1`
so the framed product carries colPerm_J on the H2 (output) columns, applied BEFORE the endpoint
frame `QL = Qf_1` (which is a nontrivial unit and mixes columns).

FACT 2 (index identity, verified numerically): for any matrix M with NO trailing QL,
  `reindex(rThr_row, pivotThr J_col)( colPerm_J(M) ) = reindex(rThr_row, rThr_col)( M )`.
The pivot reindex applied to a colPerm'd matrix collapses to the THRESHOLD reindex of the un-permuted M.

FACT 3 (numeric witness, r=1,H0=1,H2=2,J:0↦1, nontrivial QL): the two quantities
  Sfull := residual-block energy of `reindex(rThr,pivotThr J)( colPerm_J(M_noQL)·QL )`     [what `deepestEFull` reads]
  Sconj := residual-block energy of `reindex(rThr,pivotThr J)( M_noQL·QL )`                 [the `hconj` blocks]
DIFFER: 17.98 vs 23.65. So the obligation `Sfull = Sconj` (conjunct b) is FALSE.

## DOWNSTREAM STRUCTURE (what the obligation is FOR)

The final loss bound is built by `dlnLoss_two_sided_of_frame`, which takes ONLY:
  - `hconj`: blocks P00,P01,P10,P11 := toBlocks of `reindex(rThr, pivotThr J)(P0·(prod(symm w) − B)·QL)`,
  - `hleak`: ∑(P10·⅟P00·P01)² ≤ t²·Sreg,  Sreg := ∑(P00−1)²+∑P01²+∑P10².
and yields  dlnLoss ≍ Sreg + Score  (Score the Schur core). The PIVOT reindex is REQUIRED because it is
what normalizes B: `reindex(rThr, pivotThr J)(P0·B·QL) = fromBlocks 1 0 0 0` (B has pivot columns range J).

Conjunct (b) `∑deepestEFull² = Sreg` is used ONLY to bridge Sreg (the hconj/loss object) to the PIN1
reg-straightening output `deepestEFull` (so the final Φ is in straightening coordinates). `deepestEFull`
reads `reindex(rThr, pivotThr J)(prod framedParamsPivot)` — which by FACT 1+2 equals the THRESHOLD residual
of the clean product, mismatching the PIVOT residual of `hconj`.

## QUESTIONS

Q1. Confirm or refute: conjunct (b) as stated is a genuine obstruction (not a notational artifact),
    rooted in deepestEFull being THRESHOLD-effective while hconj is PIVOT. Yes/no + one-line why.

Q2. Repair routes — rank by soundness + minimal disruption to the DOWNSTREAM (which NEEDS pivot for B-norm):
   (R1) Redefine `deepestEFull` to reindex by `pivotThr J` AFTER undoing colPerm — i.e. make the framed
        last layer read pivot columns so the product is pivot-aligned (option β: pivot-aware reads). Does this
        make Sfull = Sconj? Cost?
   (R2) Pre-permute B's columns by π_J^{-1} (a fixed relabel) so the effective pivot is FRONT {0..r-1};
        then pivotThr = rThr everywhere and FACT 2 makes everything coincide. Is this sound (B-rank, loss
        invariance under a fixed orthogonal column permutation absorbed into QL)? What breaks?
   (R3) Change conjunct (b) to compare deepestEFull energy to the THRESHOLD residual of the clean product,
        and separately prove the THRESHOLD residual energy = PIVOT residual energy (is that true? a column
        permutation preserves total energy but the r⊕(n-r) block split moves the bottom-left block —
        is the SUM Sreg invariant even if blocks individually differ?).
   (R4) Accept it is false; the headline needs re-architecting at the controller level.

Q3. For R3 specifically: is the TOTAL Sreg = ∑(P00−1)²+∑P01²+∑P10² invariant under swapping the column
    reindex from pivotThr to rThr (i.e. permuting which columns land in the left r-block)? Give the exact
    reason (the −1 corner is on the diagonal r-block; a column permutation that does NOT fix the pivot set
    moves columns between left and right blocks AND moves the diagonal of the corner). Decisive yes/no.
</task>

<output_contract>
1. Q1 verdict (1 line).
2. Q2 ranked routes with soundness + cost for each (R1–R4), best first.
3. Q3 decisive yes/no + the exact reason re the −1 corner and block-crossing.
4. Flag inference vs derived-fact. Under ~450 words.
</output_contract>

<grounding_rules>
Reason from the stated facts. The numeric witness (FACT 3) is ground truth that (b) is false in that config.
Do not claim a repair is sound without naming what must be checked (B rank-preservation, loss invariance,
the corner diagonal). If R3's energy-invariance is false, say so decisively — that kills the cheapest repair.
</grounding_rules>
