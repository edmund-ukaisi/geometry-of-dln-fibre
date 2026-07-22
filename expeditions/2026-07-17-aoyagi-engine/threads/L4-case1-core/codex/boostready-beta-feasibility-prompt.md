<task>
Setting: Lean4/Mathlib formalisation of Aoyagi's resolution of DLN singularities. A resolution tree
of blow-ups; along a real branch `p` (a `TreePath`), the "fold residual" `foldResid p : Fin nR → (Fin D → ℝ) → ℝ`
is the composite `coreGen ∘ (per-step strict-transform maps)`, where `coreGen k u = (A_{N-1}···A_1·A_0)[·]`
are the entries of a product of matrices whose entries are the flat coordinates `u` (via a homeomorphism
`e : (Fin D → ℝ) ≃ₜ Tuple`; `e` is ARBITRARY unless a hypothesis pins it). Each per-step map is a block
blow-up composed with a unipotent shear pinned (on a real branch) to `canonNormalizationOf` = a
pivot-shifted Schur reduction PLUS a deeper-layer recoordinatization `A_{S+1} → A_{S+1}·Q₁⁻¹`.

I must prove this lemma (call it BOOSTREADY), for ARBITRARY `e`:

  hyps:
    hδ    : the parent node `p` has `cleared = 0` (δ=1, first clear of the current layer S = p.layer);
    hc11  : the outgoing edge `ed` is a "case11" merge (reuses an EARLIER-born divisor `f`);
    hbranch : `(p.extend ed)` is a real branch (⟹ all shears along the path to p, and ed's shear, are
              `canonNormalizationOf`; ed's blow-up center/pivot are the canonical slots);
    hslot : the CARRIED parent invariant — for every residual entry j,
            `foldResid p j` is "Deg1SupportedSlot" on `support := blockCoords(S)` (the layer-S block):
              (∃ c : (Fin D)→(Fin D→ℝ)→ℝ, (∀i, Continuous (c i)) ∧
                 ∀ u, foldResid p j u = ∑_{i ∈ support} c i u * u i)     -- degree-1 on `support`
              AND a per-layer-affine grade.  [The c i are ARBITRARY continuous functions — no further
              structure.]
  goal:
    `Deg1SupportedOn (foldResid p) center`, where `center = {pivot} ∪ partialBlock`,
      pivot        = the reused divisor f's birth corner (a coordinate at an EARLIER layer than S),
      partialBlock = {i ∈ support : col(i) < runLen}   (a SUBSET of `support`, runLen = divTilde(f)),
    and `Deg1SupportedOn (foldResid p) center` means: ∃ c', continuous, with
      `∀ u, foldResid p j u = ∑_{i ∈ center} c' i u * u i`  (⟹ foldResid p j VANISHES when every
      coordinate in `center` is set to 0).
    Note `center ⊊ support` on the block part (SHRINK): extraBlock := support ∖ partialBlock =
      {i ∈ support : col(i) ≥ runLen} is DROPPED from the center; pivot (earlier layer) is ADDED.

The intended math ("b-chain boost split", from Aoyagi worked.tex + a verified sympy certificate on the
smallest instance d=(2,2,2,2)): foldResid p j = ∑_{partialBlock} α_i u_i + u_pivot · ∑_{extraBlock} β_i u_i,
i.e. every extra-block coordinate's coefficient carries the factor `u_pivot`. THIS is what makes
`foldResid p` vanish when `center → 0` (both partialBlock and pivot zeroed ⟹ the α-terms vanish (u_i=0)
and the β-terms vanish (u_pivot=0)).

MY WORRY (the question): the factor `u_pivot` on the extra-block coefficients (the "b-chain") is NOT
present in `hslot` — hslot's `c i` are arbitrary continuous functions with no vanishing-at-pivot=0
property. Concretely: from hslot alone, `foldResid p j |_{center→0} = ∑_{extraBlock} c_i u_i` (extra
coords are untouched by center→0), which is generally ≠ 0. So `Deg1SupportedOn center` does NOT follow
from hslot alone. The `u_pivot` factor is introduced at divisor f's EARLIER birth-clear (a case2/case12
step deeper in the path) and is carried in `foldResid p` through the intervening steps — i.e. it is
INDUCTIVE path-content, not local to node p. Extracting it seems to require unfolding `foldResid p`
along the whole path back to the root `coreGen`, whose degree-1-on-block-0 base fact is FALSE for a
scrambling `e` (e.g. e-scrambled `coreGen 0 u = u₀u₁ + u₁²`) — so any such unfolding re-imports an
`e = canonFlatten` dependence, contradicting the "arbitrary e" statement.

A proposed rescue ("route β" from the lead): "hslot is CARRIED, so for a scrambling e where hslot is
unsatisfiable the lemma is vacuous; for the good e where hslot holds, derive the boost split by
unfolding foldResid via the value-pin (shears = canonNormalizationOf) and reading the b-chain off the
deeper recoord." The claim is that this is ∀e-honest and needs no root/canonFlatten base.
</task>

<output_contract>
Answer in <=600 words, in this order:
1. VERDICT: Is BOOSTREADY provable from (hslot + hbranch) for arbitrary e, WITHOUT any e=canonFlatten /
   root-base hypothesis? One of: YES-LOCAL (the b-chain is extractable locally at p) / NO-NEEDS-INDUCTION
   (the b-chain is inductive path-content, hslot insufficient) / NO-NEEDS-BASE (any route re-imports the
   canonFlatten root base) / DEPENDS (state the discriminating condition).
2. THE KEY QUESTION: does `hslot` (arbitrary continuous c_i, degree-1 on `support`) + the fact that on a
   real branch the shears are canonNormalizationOf, LOGICALLY FORCE the extra-block coefficients to carry
   u_pivot? If yes, sketch WHY (what forces it). If no, give the crisp reason (the 1-line counterexample
   shape suffices — e.g. a continuous c_i on the extra block with no u_pivot factor that is still
   consistent with hslot and the real-branch shears).
3. If NO: what is the MINIMAL extra ingredient that makes BOOSTREADY provable ∀e — a stronger carried
   invariant (state its shape), or an explicit root/base hypothesis, or something else? Is there any way
   to keep the statement ∀e and provable without touching the carried invariant?
4. Flag explicitly which of your claims are logical necessities vs plausible-but-unverified.
</output_contract>

<grounding_rules>
This is a design-feasibility question, not a request for Lean code. Reason from the logical structure
given. Do NOT assume facts not stated (e.g. do not assume `e` is linear or block-respecting — it is
arbitrary). If a claim depends on a property of `canonNormalizationOf` or `coreGen` I have not stated,
name the property as an assumption and say the verdict is conditional on it. Distinguish "follows
logically from the stated hyps" from "true in the intended model but not forced by the hyps."
</grounding_rules>
