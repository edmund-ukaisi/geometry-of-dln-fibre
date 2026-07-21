<task>
TARGETED CONFIRMATION pass (round 3) on a Lean 4 blueprint, v4.1 (commit f8db23000). You (in earlier rounds) produced verified kills against v3 and v4; v4.1 claims to fix every remaining one via statement-local edits. This is NOT a full re-audit — confirm or break the SPECIFIC fixes. Your two earlier counterexample classes MUST now be rejected by the records; verify that mechanically.

READ (checkout at f8db23000):
- /tmp/aoyagi-v3-review/lean/DLNFibre/Core/Aoyagi/ProductResolution.lean  (Chart/Resolution, dom-wide certificates, restored injectivity)
- /tmp/aoyagi-v3-review/lean/DLNFibre/Core/Aoyagi/IdealInvariance.lean    (RegionRepresents; weighted lemmas + measurability; LocallyNullZerosW DELETED)
- /tmp/aoyagi-v3-review/lean/DLNFibre/DLN/Aoyagi/LearningCoefficient.lean (e 0 = 0; flatten as ≃ₜ)

CONFIRM/BREAK, per item:
1. **D1 dom-wide certificates.** `Chart` now has `nbhd` open ⊇ `dom`, with hjac/hunit (continuous-on, nonvanishing-on)/hideal_fwd/bwd (`RegionRepresents` — coefficients ContinuousOn nbhd) all quantified over nbhd. VERIFY: (a) your round-2 remote-branch counterexample g(s,t)=(s(1−s),st) with dom at s≈1 is now REJECTED (which field fails, exactly — the bwd coefficient 1/(1−s) at s=1 ∈ nbhd?); (b) the elder's g_B=(v(u−2),v) far-cover is REJECTED (ideal identity unsatisfiable at u=2 ∈ nbhd); (c) the two-chart ℝ² blow-up STILL inhabits the strengthened record (identities global — check each strengthened field); (d) with dom-wide certificates + restored a.e.-injectivity, can you STILL construct any atlas satisfying every field where `rlctAt_sumSqFam_eq_iInf_charts` fails? Attack once more, hard — this is the load-bearing equality.
2. **D2 injectivity restored**: `excep`/`hexcep_null`/`hg_inj : InjOn g (nbhd \ excep)` — sufficient for the ≤ direction's bounded-multiplicity need (or is InjOn off a null set still too weak for transporting DIVERGENCE downstairs — the N(w) multiplicity argument)?
3. **D3 + the LocallyNullZerosW DELETION (judgment call — audit hard).** The weighted lemmas now guard only `LocallyNullZeros (sumSqFam G)` (i.e. on K's zero set), with `Measurable W` + family measurability added. The architect argues: integrand is W·K^(−c); rpow junk lives at {K=0} only; W ≥ 0 zeros only shrink the integrand (helping integrability) and W is SHARED by both sides. Is the deletion sound — or can a positive-measure {W=0} still invert a comparison somewhere in the weighted chain (e.g. the two-sided equality where the junk-symmetry argument needs the SAME null set on both sides)? Construct a counterexample or confirm.
4. **e0/homeomorphism fixes**: `exists_coreResolution` now takes `he0 : e 0 = 0`; the flatten is `≃ₜ`. Your round-2 kills (translated flatten; discontinuous flatten) both rejected? Any residual (e.g. does coreReduction need measure-preservation AND homeomorphism together — is the measure-preservation hypothesis still present after the ≃ᵐ→≃ₜ change)?
</task>

<output_contract>
Per item 1–4: CONFIRMED-FIXED (with the exact field/hypothesis that now blocks each old counterexample) or NEW-KILL (explicit structure + arithmetic). Then OVERALL: does v4.1 clear the "no false frontier statements" bar — YES/NO, ranked kills if NO. Mark VERIFIED vs INFERRED throughout.
</output_contract>

<grounding_rules>
Read the actual record fields at f8db23000 — do not trust the summary. For item 1(d) especially: spend real effort on one more adversarial construction attempt; a lazy pass here would be worse than useless. For item 4: check the actual hypothesis list of coreReduction (measure-preservation must not have been silently lost in the ≃ᵐ→≃ₜ swap).
</grounding_rules>
