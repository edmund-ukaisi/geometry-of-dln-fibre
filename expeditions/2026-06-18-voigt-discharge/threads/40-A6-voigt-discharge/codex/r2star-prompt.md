<task>
Red-team a Lean 4 + Mathlib v4.29 R2★ proof design (AG formalisation, DLNFibre). Tell me where it breaks in Lean and the cleanest realization. Concrete Mathlib lemma names. Flag any secretly-false step.

LANDED (exact names):
- R = MvPolynomial (RepCoord d) k, k a Field. RepCoord d = Σ i:Fin N, Fin(d i.succ)×Fin(d i.castSucc).
- cochain0 d d = ∀ v:Fin(N+1), Matrix(Fin(d v))(Fin(d v)) k; cochain1 d d = Tuple d = ∀ i:Fin N, Matrix(Fin(d i.succ))(Fin(d i.castSucc)) k (DEFEQ).
- deformationδ M M : cochain0→ₗ[k]cochain1, (δ⁰φ) i = φ i.succ * M i − M i * φ i.castSucc.
- canonicalCoord d : Tuple d ≃ (RepCoord d→k), canonicalCoord d A ⟨i,s,t⟩=A i s t (rfl).
- orbitPullback M : R →ₐ[k] groupRing d = aeval(genericOrbitCoord M); genericOrbitCoord M ⟨i,s,t⟩=(genericUnit(i.succ)*genericFactor M i*genericUnitInv(i.castSucc)) s t.
- groupRing d = Localization.Away(groupDenom d) over MvPolynomial(GroupCoord d) k.
- I = orbitIdeal M = RingHom.ker(orbitPullback M).toRingHom (needs [Infinite k]).
- LANDED evalGroupRing P (P:BaseChangeGroup k d):groupRing d→+*k = IsLocalization.Away.lift, with evalGroupRing_genericUnit/_genericFactor/_genericUnitInv and evalGroupRing_orbitPullback M P g = MvPolynomial.eval (orbitMap M P) g (orbitMap M P=canonicalCoord(P•M)).
- LANDED dual number: orbitAction_eps_eq_deformationδ M φ i: (1+ε•liftMat(φ i.succ))*liftMat(M i)*(1−ε•liftMat(φ i.castSucc))=liftMat(M i)+ε•liftMat((δ⁰φ) i) over DualNumber k. liftMat A=A.map(algebraMap k (DualNumber k)). one_add_eps_mul_one_sub_eps.
- DualNumber: snd_mul (snd(xy)=fst x*snd y+snd x*fst y), fst_eps=0, snd_eps=1, eps_mul_eps=0, fstHom(alg hom into k), sndHom(linear). MvPolynomial.mkDerivation k (v:σ→A):Derivation k R A, mkDerivation_X, derivation_ext.

GOAL R2★: f∈I, φ:cochain0 d d, v:=canonicalCoord d (δ⁰φ):RepCoord d→k ⟹ (mkDerivation k v) f = 0.

DESIGN (dual-number): p_ε:RepCoord d→DualNumber k, p_ε⟨i,s,t⟩=((1+ε•liftMat(φ i.succ))*liftMat(M i)*(1−ε•liftMat(φ i.castSucc))) s t.
A: ψ:groupRing d→ₐ[k]DualNumber k via IsLocalization.Away.lift(det(1+εφ) unit, fst=1). ψ∘orbitPullback M = aeval p_ε (per-generator).
B: f∈I ⟹ aeval p_ε f=ψ(orbitPullback M f)=ψ 0=0.
C: orbitAction_eps ⟹ fst(p_ε x)=a_M x, snd(p_ε x)=v x.
D: g:f↦snd(aeval p_ε f) is k-derivation along aeval a_M (snd_mul), =mkDerivation k v (derivation_ext on X), so mkDerivation k v f=snd 0=0.
</task>
<output_contract>
Q1: Step A over DualNumber k (NOT a field) — IsLocalization.Away.lift clean? slicker path? does orbit machinery being over a Field block reuse?
Q2: Step D — cleanest "g is a Derivation"? Mathlib idiom "snd of alg hom into A[ε] is a derivation" (TrivSqZeroExt)? or build Derivation record by hand from snd_mul? which is less friction?
Q3: Is the Polynomial k curve route (c(t)=canonicalCoord((1+tφ)•M), reuse evalGroupRing_orbitPullback over the FIELD k) lower-friction than dual numbers? Compare concretely.
≤6 sentences/answer, lemma names where possible.
</output_contract>
