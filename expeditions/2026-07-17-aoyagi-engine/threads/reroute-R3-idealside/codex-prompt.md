<task>
Adjudicate the generality of an algebraic-geometry claim underlying a Lean formalisation of
Aoyagi's resolution of the deep-linear-network loss. Exact-algebra reasoning; be adversarial.
Withhold nothing. I give the setting, verified facts, and 3 sub-questions.

SETTING. Aoyagi resolves F = ‖∏_k C^(k)‖² (a coupled product of matrices) at 0 by a recursion that,
per layer, does: (1) a Schur/block ELIMINATION clearing a pivot from the current residual block
(coupling coefficients arbitrary), then (2) a RADIAL (affine pivot) BLOW-UP making the pivot
coordinate u_p the dominant exceptional E, leaving a "fresh lower-depth core" (deeper layers
untouched). Iterating peels every layer; at the terminal (all layers peeled) the chart ideal
⟨(∏C)∘g⟩ compresses to a single principal monomial ⟨b_{k0}⟩. The formal object is a per-chart TWO-SIDED
ideal identity `RegionRepresents G F V` (:= ∃ cofactors continuous ON V with Gᵢ = Σⱼ aᵢⱼ Fⱼ on V),
carried on a region V; the chart also carries a Jacobian cert |det Dg| = monomial·unit on V.

VERIFIED FACTS (in-repo, sorry-free, at the corank-2 witness (3,3,4) t=(1,0), Mval=8, rlct=4 — a
genuinely coupled L=2 core, NOT reachable by any corank-≤1 peel):
- The pivot entry of the Schur-cleared block, pulled back through the composite chart g, equals the
  dominant exceptional EXACTLY: `peeled₀₀ ∘ g = E` (pivot quotient = 1, not E·unit). So the REVERSE
  ideal inclusion ⟨E⟩ ⊆ ⟨peeled∘g⟩ has a CONSTANT cofactor (1 at the pivot, 0 else) — no 1/unit.
- The forward inclusion ⟨peeled∘g⟩ ⊆ ⟨E⟩ has POLYNOMIAL cofactors (each entry = E·polynomial).
- The block-elim maintenance step is two-sided with cofactors ±cᵢ·rᵢ, where cᵢ is the (arbitrary)
  coupling coefficient and rᵢ = bᵢ/b_p is the b-CHAIN quotient; rᵢ is a genuine MONOMIAL (continuous
  on all of V) PROVIDED the divisibility chain b_p | bᵢ holds. The chain b_1|…|b_M holds "by
  construction" (bᵢ = ∏ of the exceptionals born before it).
- Consequently the concrete (3,3,4) chart carries the two-sided ideal identity on V = the FULL space
  (nbhd = univ): NO region shrink, and the Jacobian unit ≡ 1 EXACTLY (all steps are unipotent
  shears det≡1 + exact-monomial blow-ups).
- The abstract terminal lemma `terminal_bezout` (general form) DOES shrink: given a general
  nonvanishing unit (unit 0 ≠ 0), it restricts V to V ∩ {unit ≠ 0}. The concrete construction never
  triggers this because it produces unit ≡ 1.
- At the shared-deep-factor witnesses (4,4,4) t=(2,0) and (3,3,3,2,2) t=(2,2,1,0), the TERMINAL
  chart's ideal is again a single principal chain (corner-join restores principality), verified by
  Gröbner ideal-EQUALITY (not coefficient matching). INTERMEDIATE charts can be non-principal — the
  single-chain is a TERMINAL invariant. A "thread-28 certificate" flags DEEPER MIXED instances as an
  open end (verified up to these witnesses, inferred beyond).
- The downstream cover interface is UP-TO-NULL: hcover := volume(U \ ⋃ charts.g''dom) = 0; each
  chart's certs hold on an OPEN nbhd, with a COMPACT dom ⊆ nbhd doing the covering.
</task>

<sub_questions>
(a) COMPOSITION down a general-d branch. Does the two-sided `RegionRepresents` compose down an
    arbitrary-depth, genuinely-coupled (corank ≥ 2) branch — BOTH directions — via
    precompose(regionRepresents_comp) + restrict(.mono) + chain(.trans) + the two-sided block-elim,
    given the b-chain is maintained as a threaded conjunct? Is the REVERSE direction (⟨residual
    system⟩ ⊆ ⟨coreGen∘gPath⟩) genuinely as cheap as the forward here, or is there a hidden place it
    needs a discontinuous 1/monomial cofactor? (A "value-from-threshold-data mirage" was retired 3×;
    is that the SAME failure as an ideal-composition wall, or a different, value-level, issue?)
(b) Is `nbhd = univ` (no terminal shrink; the two-sided ideal identity on the full space) a
    GENERAL-d fact or a corank-2 ACCIDENT? Specifically: does "pivot quotient = 1 exactly" (⟹ reverse
    cofactor constant) + "Jacobian unit ≡ 1 exactly" (unipotent + exact-monomial) hold at arbitrary
    corank/depth by the affine-pivot-blow-up mechanism, or does deep coupling force a genuinely
    nonvanishing-but-not-1 unit somewhere (⟹ region = {unit≠0} ⊊ univ, reviving a shrink-vs-cover
    coupling: a compact dom in an open {unit≠0} stays ε away from {unit=0}, missing a positive-measure
    tube that other charts must then cover)?
(c) Could a clearing at a DEEP node ever need to READ (subtract a multiple involving) a coordinate
    already CLEARED at a shallower node — breaking the "reads-only-kept, deeper-layers-untouched"
    structure — especially with SHARED deep factors across branches? Or do shallower-cleared
    coordinates only ever appear as b-monomial spectator LEFT-factors (the diag(b) invariant), with
    sharing resolved by the corner-join?
</sub_questions>

<output_contract>
For EACH of (a)(b)(c): a one-word verdict (COMPOSES / WALLS / CONDITIONAL for a; GENERAL / CORANK-2-
SPECIAL / CONDITIONAL for b; SAFE / READS-CLEARED / CONDITIONAL for c), then ≤6 sentences of exact
reasoning, then the single cheapest concrete discriminating test or the exact witness that would break
it. Then "STOP-OR-GO": is there a genuine ideal-side MONUMENT wall that should trigger a re-scope /
objects-only fallback, or is the open part bounded detail-at-scale (a verification extension of a
corank-agnostic exact mechanism)? Distinguish what you can prove from what you infer. No Lean code.
</output_contract>

<grounding_rules>
Ground every claim in the facts above. If you need a fact not given, state it as an explicit
assumption. Preserve fact-vs-inference. Do not rubber-stamp; if (b)'s "unit≡1 general" is too clean,
say exactly where it could fail.
</grounding_rules>
