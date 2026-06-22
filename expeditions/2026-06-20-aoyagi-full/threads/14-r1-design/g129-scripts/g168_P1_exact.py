# Sharpen the EXACT P1 statement + check airtightness. The core lemma is even SIMPLER than "along the
# scaling ray" — it's a direct nbhd-monotonicity of rlctAt.
print("=== The EXACT P1 lemma (minimal, provable from the rlctAt def) ===")
print("""
LEMMA (rlctAt nbhd-monotonicity, the P1 core — call it rlctAt_le_of_nhds_le):
  If p₀ is in the CLOSURE of a set S and ... no, simplest form:
  
  rlctAt_mono_basepoint: if q → p₀ (q in every nbhd of p₀) then rlctAt(F, p₀) ≤ ... 
  
  Cleanest: for any point q and any c' ∈ A(p₀) [∃ U₀∈𝓝 p₀, ∫_U₀|F|^{-c'}<∞], IF q ∈ U₀ (q in that
  specific admissible nbhd), then c' ∈ A(q) [U₀ ∈ 𝓝 q since U₀ open ∋ q] ⟹ c' ≤ rlctAt(F,q).
  
  So: rlctAt(F, p₀) ≤ rlctAt(F, q) WHENEVER q lies in EVERY admissible nbhd of p₀ — i.e. q is
  arbitrarily close to p₀ in the sense that every U₀∈𝓝 p₀ contains a point where rlctAt ≥ the threshold.
""")
print("""
ACTUALLY the cleanest exact statement for D1 (a), avoiding liminf subtleties:

  P1 (rlctAt_deepest_le_along_ray): F homogeneous, deepest = 0, v a point. For each c' ∈ A(0) and each
  ε>0, ∃ s∈(0,ε] with c' ∈ A(s·v) [since s·v → 0 enters any U₀ ∈ A(0)'s nbhd]. Combined with L1-a
  (rlctAt(s·v) = rlctAt(v)): c' ≤ rlctAt(s·v) = rlctAt(v). Sup over c'∈A(0): rlctAt(0) ≤ rlctAt(v).

  The Lean shape:
   step (i) [L1-a, g162]: rlctAt(F, s·v) = rlctAt(F, v) for s∈(0,1] [scaling diffeo + t^D unit invariance;
            comp_homeomorph + unit_invariant, banked].
   step (ii) [the P1 core, NEW but LIGHT]: for c' admissible at 0 (∃ U₀∈𝓝 0, IntegrableOn |F|^{-c'} U₀),
            and any nbhd U₀, ∃ s small with s·v ∈ U₀ [s·v → 0, U₀∈𝓝 0]; then U₀ ∈ 𝓝 (s·v) [U₀ open],
            so c' admissible at s·v ⟹ c' ≤ rlctAt(s·v).
   step (iii): rlctAt(0) = sSup A(0) ≤ rlctAt(v) [each c'∈A(0) ≤ rlctAt(v) via i+ii; sSup_le].
""")
print("=== Airtightness checks ===")
print("""
1. 's·v ∈ U₀ for small s': U₀ ∈ 𝓝 0 ⟹ U₀ ⊇ a ball around 0 ⟹ s·v ∈ U₀ for s < (ball radius)/‖v‖. ✓
   (needs U₀ a genuine nbhd of 0, which it is by def of A(0).)
2. 'U₀ ∈ 𝓝 (s·v)': need U₀ OPEN (or s·v in its interior). The rlctAt def uses U ∈ 𝓝 wstar (nbhd, has
   interior); WLOG U₀ open (shrink to its interior, integrability inherited by mono_set). s·v ∈ U₀ open
   ⟹ U₀ ∈ 𝓝 (s·v). ✓
3. 'c' admissible at s·v': ∫_{U₀}|F|^{-c'} < ∞ and U₀ ∈ 𝓝(s·v) ⟹ c' ∈ A(s·v) by def. ✓
4. L1-a rlctAt(s·v)=rlctAt(v): homogeneity (g162). For B=0 CORE (post-L2), F=‖∏C‖² homogeneous. ✓
   [Scope: this is the B=0 core after L2; the deepest is the origin of the core. ✓]
5. sSup_le: rlctAt(0)=sSup A(0), each elt ≤ rlctAt(v) ⟹ sSup ≤ rlctAt(v). ✓ (ENNReal sSup_le.)
ALL AIRTIGHT. P1 = step-(ii) the nbhd-monotonicity (NEW, ~10-line Lean from the def) + L1-a (banked).
NOT a heavy primitive — the controller's hint nailed it: it follows from rlctAt's ∃-nbhd structure.
""")
print("⟹ MAJOR SIMPLIFICATION of g160: P1 is NOT a heavy analytic primitive (no Fatou/Varchenko/")
print("semicontinuity-theorem). It is the ELEMENTARY nbhd-monotonicity of rlctAt (from the ∃ U∈𝓝 def) +")
print("L1-a scaling-invariance (banked). D1 (a) is LIGHT and value-independent. crux2's tractability read")
print("should be GREEN (small Lean from the team's own rlctAt def).")
