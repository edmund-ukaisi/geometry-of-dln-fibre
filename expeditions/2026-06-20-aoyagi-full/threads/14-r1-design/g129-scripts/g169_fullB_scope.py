# CRITICAL scope: rlctAt_deepest_le_of_optimal is on FULL dlnLoss H B (B≠0, not homogeneous). My light P1
# (nbhd-monotonicity + L1-a homogeneity) needs HOMOGENEITY, which B≠0 breaks. So: can D1 (a) reduce to
# the B=0 CORE (post-L2) where P1 applies, or is the full-B statement intrinsically harder?
print("=== Full-B dlnLoss H B is NOT homogeneous (docstring confirms) — does P1 still apply? ===")
print("""
dlnLoss H B = ‖∏C − B‖². For B≠0 this is NOT homogeneous in C (the −B breaks the scaling). So:
 - L1-a (scaling-invariance rlctAt(t·v)=rlctAt(v)) FAILS for the full B≠0 loss.
 - the scaling ray t·v → 0 does NOT stay in optimalSet (∏(t·v) = t^L ∏v = t^L B ≠ B for t≠1) — so t·v
   ISN'T even a fibre point, and 0 isn't the deepest for B≠0.
⟹ my light P1 (g166-g168) is for the B=0 CORE, NOT the full B≠0 loss. The full-B D1 (a) needs a bridge.
""")
print("=== The L2 bridge: does D1 (a) reduce to the core where P1 applies? ===")
print("""
L2 (product_reduction): rlctAt(dlnLoss H B) at a fibre point = (regular shift n/2) + rlctAt(core) at
the corresponding core point, where the core = ‖∏C'‖² on the reduced widths M=H−r (B→0 core, HOMOGENEOUS).
So IF L2 applies at EVERY fibre point v (not just the deepest), then:
  rlctAt(dlnLoss H B)(v) = n_v/2 + rlctAt(core)(v-core)
  rlctAt(dlnLoss H B)(deepest) = n_d/2 + rlctAt(core)(0)   [deepest core = origin]
and D1 (a) reduces to: n_d/2 + rlctAt(core)(0) ≤ n_v/2 + rlctAt(core)(v-core). IF n_d = n_v (same
regular dimension at every fibre point — the rank-r regular shift is constant on optimalSet) AND
rlctAt(core)(0) ≤ rlctAt(core)(v-core) [the CORE D1, B=0, homogeneous — where my light P1 applies!],
then D1 (a) follows. 
BUT: (i) is n_v constant over optimalSet? The regular shift n/2 = r(H_0+H_L−r) depends only on r (the
PRODUCT rank, = rank B, CONSTANT on optimalSet) — NOT on the per-layer ranks. So n_v = n_d = r(H_0+H_L−r)
constant. ✓ (ii) does L2 apply at a general (non-rank-exact) v? L2's gauge chart at v needs... the
non-rank-exact issue again. Hmm.
""")
print("=== HONEST verdict on the scope ===")
print("""
The CLEAN path: D1 (a) reduces to the CORE D1 (rlctAt(core)(0) ≤ rlctAt(core)(v-core), B=0 homogeneous)
via L2 at every fibre point + the constant regular shift (n_v = r(H_0+H_L−r), const on optimalSet since
r = rank B is constant). Then the CORE D1 is my LIGHT P1 (nbhd-monotonicity + L1-a homogeneity of the
B=0 core). So:
 - P1 (the light nbhd-monotonicity + homogeneity) is for the CORE D1 (B=0). LIGHT, value-independent,
   provable from rlctAt's def. ✓
 - the FULL-B D1 (a) = the core D1 (P1) + L2-at-every-fibre-point + the constant-regular-shift fact.
   The L2-at-every-v is the 'L2-downstream' the docstring flags — it needs L2's gauge chart at a general
   (possibly non-rank-exact) v, which is the broader-split issue crux2 raised.
So P1 IS light (the core D1), BUT the full-B D1 (a) wraps it in L2-at-every-v (heavier, the non-rank-exact
charting). The CLEANEST: state D1 (a) at the CORE level (B=0) where P1 is light, and let L2 lift it — IF
the spine allows D1 to be core-level. If D1 (a) must be the full-B statement directly, it needs the
L2-at-every-v wrapper (the non-rank-exact gauge chart).
""")
print("⟹ REFINED P1 verdict: P1 (the core D1, B=0) is LIGHT (nbhd-monotonicity + homogeneity, from the")
print("rlctAt def — controller's hint confirmed). The FULL-B D1 (a) = P1 + L2-at-every-fibre-point. The")
print("question for the spine: can D1 be applied at the CORE level (post-L2) so P1 suffices, or must it be")
print("full-B (needing the L2-at-every-v wrapper)? If core-level: P1 light, done. If full-B: P1 + the L2 lift.")
