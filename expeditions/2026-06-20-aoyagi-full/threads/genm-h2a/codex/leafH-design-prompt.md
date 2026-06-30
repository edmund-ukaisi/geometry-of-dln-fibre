<task>
I am formalising a small Lean 4 + Mathlib atom (call it H2a) inside a larger proof.
I must DEFINE a function and PROVE one lemma about its value at one index. I need a
design sanity-check on the cleanest faithful construction, NOT Lean code.

CONTEXT (the math object).
- `M : Fin (L+1) → ℕ` a width vector; `N := routeMAmbient M` an ambient dimension (a ℕ).
- There is a noncomputable bijection `chartIdxEquiv : Fin N ≃ ChartIdx M t` where
  `ChartIdx M t = Σ k : Fin L, Fin (schurDim k) ⊕ Fin (liftDim k)`. This bijection is OPAQUE
  (built from `Fintype.equivFin`); you cannot decide which `ChartIdx` value a given `Fin N`
  index maps to, EXCEPT by going through the equiv.
- A "K-diagonal flat slot" at boundary `k : Fin L`, matrix-diagonal entry `i` (where
  `i : Fin (Text M t (k.val+2))`), is the flat index
      `chartIdxEquiv.symm ⟨k, Sum.inl (frameSplitEquiv ... .symm (Sum.inl (Sum.inl (Sum.inl (finProdFinEquiv (i,i))))))⟩`.
- The "pivot" is the LITERAL flat index `structPivot := (⟨0, hN⟩ : Fin N)` (raw index 0). The radial
  scalar is read from `x ⟨0,_⟩` DIRECTLY, NOT through chartIdxEquiv.

WHAT I MUST BUILD.
- `lduleafH M ha hN : Fin N → ℕ`, an exponent vector that should be:
    * `minAdm M − 1` at the pivot index `⟨0,hN⟩` (radial blow-up exponent),
    * `(r_k + c_k) + 2·(t_k − 1 − i)` at the K-diagonal flat slot at boundary `k`, diagonal entry `i`,
      where (per a brief) `t_k = Text M (tach M) (k+1)` [the K-core size], `r_k`, `c_k` residual widths,
    * `0` on every other flat index.
- `lduleafH_pivot`: `lduleafH M ha hN ⟨0,hN⟩ = minAdm M − 1`.

THE ONLY THEOREM I OWE NOW is `lduleafH_pivot`. The K-diagonal exponent values are pinned down ONLY by a
SEPARATE later lemma (H2b: ∏_j |u_j|^{lduleafH_j} = product of per-factor Jacobian dets) that is NOT my task.

THE DESIGN TENSION. The pivot is raw index 0. The K-diagonal slots are images of chartIdxEquiv.symm of
specific ChartIdx values. I cannot prove (or disprove) that raw index 0 is or is not one of the K-diagonal
slots, because chartIdxEquiv is opaque. So if I naively define lduleafH(j) = "if j is a K-diagonal slot then
(r+c)+2(t-1-i) else 0" WITHOUT special-casing the pivot, I cannot prove lduleafH(⟨0⟩) = minAdm−1.

In the validated concrete instance (3,3,3,3, L=3, N=27): leafH(0)=5=minAdm−1 (radial), and the K-diagonal /
LDU pivots are at indices 1,4,9 (disjoint from 0). So index 0 is NOT a K-diagonal slot there — but that is a
computed fact in a decidable concrete case, not available at opaque width.

MY PROPOSED DESIGN: define
   lduleafH j := if j = ⟨0,hN⟩ then (minAdm M − 1) else kDiagPart j
where kDiagPart places (r+c)+2(t-1-i) at K-diagonal slots and 0 elsewhere. Then lduleafH_pivot is `if_pos rfl`.
</task>

<output_contract>
Answer in 4 short sections, terse:
1. VERDICT: Is the "if j = pivot then minAdm−1 else kDiagPart" design sound for proving the pivot lemma
   cleanly AND faithful for the later H2b det-bookkeeping? YES/NO + one sentence.
2. THE RISK: Does special-casing the pivot index create a HIDDEN INCONSISTENCY for H2b — i.e., could the
   pivot index 0 ALSO be a genuine K-diagonal slot, so that H2b needs lduleafH(0) to be the K-exponent
   (r+c)+2(t-1-i) rather than minAdm−1, making my override wrong? Reason about whether radial-axis index 0 can
   coincide with a K-diagonal slot, given the radial axis is read directly (not via chartIdxEquiv) but ALSO the
   decoder reads block data from the same vector through chartIdxEquiv. State clearly whether this is a real
   risk or not, and what the cheapest disambiguating check is.
3. ALTERNATIVE: If the override is risky, what is the cleaner faithful construction? (e.g. define the K-diag
   placement to EXCLUDE the pivot by construction, or prove index 0 is not a K-slot, or have kDiagPart already
   return minAdm−1 at the pivot.) Rank options by Lean-proof-cost for the pivot lemma.
4. INDEXING: the brief says t_k = Text M (tach M)(k+1) but readK's K-block has size Text M t (k+2) at boundary
   k:Fin L. Flag whether "t_k" (brief) vs "Text(k+2)" (readK) is an off-by-one I should reconcile, or just two
   indexings of the same quantity. One sentence.
</output_contract>

<grounding_rules>
You do not have the repo. Reason from the structural facts I gave. Mark any claim that depends on a fact you
cannot verify from this prompt as "INFERENCE (unverified)". Do not emit Lean code; give design guidance only.
</grounding_rules>
