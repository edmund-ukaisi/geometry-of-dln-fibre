<task>
DLN RLCT formalisation (Lean 4 / Mathlib v4.29). I must decide BOUNDED vs WALL for "H_indep at general v" before charging a multi-tide Lean build. Two sharp questions.

SETUP. dlnLoss H B A = ∑_{ij} g_ij(A)², g_ij(A)=(prod A − B)_ij, prod A = A⁽¹⁾·A⁽²⁾ (L=2; A⁽¹⁾ is H0×H1, A⁽²⁾ is H1×H2). v is a GENERAL optimal point: prod v = B, rank B = r (all g_ij(v)=0). nReg := r(H0+H2−r). The gradient ∇g_ij(v) acts on (δ¹,δ²) by (δ¹ A²_v + A¹_v δ²)_ij.

I already PROVED (banked, clean): rlctAtOn_eq_of_contDiff_chart — the §SEL selected-minor IFT chart-transfer: given a ContDiff² self-map Φ of the flat param space fixing the basepoint with INVERTIBLE derivative f' there + the germ loss=ᶠF∘Φ, then rlctAt v = rlctAtOn F 0. And the D1 ≥-leg consumer deepest_le_of_optimal_of_iftResidual takes this hchart (F = ∑s²+∑q², m=nReg) + a C¹ residual q, and concludes rlctAt(deepest) ≤ rlctAt(v). The chart's f' invertible ⟺ the nReg selected gradients ∇g_S(v) are linearly independent (top block) = "H_indep". I have prodAuxEntryDeriv (the explicit Fréchet derivative of each prod entry) banked.

MY DECORRELATED ANALYSIS (verify or refute): the gradient image {δ¹A²_v + A¹_v δ²} ⊆ Mat_{H0×H2} has dim = H0·rank(A²_v) + rank(A¹_v)·H2 − rank(A¹_v)·rank(A²_v) = "nReg_v". At the deepest point (rank A¹_v=rank A²_v=r): = rH0+rH2−r² = nReg. At a middle stratum (ranks r+a, r+b): > nReg. So rank Dg(v) = nReg_v ≥ nReg ALWAYS at an optimal v ⟹ an independent nReg-subset of {∇g_ij(v)} always exists ⟹ H_indep holds at EVERY optimal v (general-v, not deepest-only). Mathlib exists_linearIndependent' extracts the subset.
</task>

<output_contract>
Q1 (BOUNDED/WALL). Is my dim formula dim{δ¹A²+A¹δ²} = H0·rk(A²)+rk(A¹)·H2−rk(A¹)·rk(A²) CORRECT (the intersection {δ¹A²}∩{A¹δ²} = A¹·Mat·A² has dim rk(A¹)·rk(A²))? Does it give rank Dg(v) ≥ nReg at EVERY optimal v? If yes, is formalising "rank Dg(v) ≥ nReg ⟹ ∃ nReg independent gradients" BOUNDED via prodAuxEntryDeriv + a rank/exists_linearIndependent' argument, or does it need NEW infra (e.g. the determinantal-tangent-space or a Gauss-Newton Dg-rank fact formalised from scratch)? Give the cleanest Lean route OR name the wall.

Q2 (★ the lightener). Does deepest_le_of_optimal_of_iftResidual genuinely need H_indep (the chart) at ALL optimal v, or only at v where rlctAt(v) is "small" (close to the deepest value)? The conclusion is rlctAt(deepest) ≤ rlctAt(v). If at v where the regular gradients are NOT independent (if such optimal v even exist — Q1 says they don't, rank ≥ nReg always) the inequality held by a CRUDER argument (e.g. rlctAt(v) is even larger there), the chart could be needed only on a sub-locus. GIVEN Q1 (rank ≥ nReg everywhere), is the chart needed at every optimal v anyway, or is there a sub-locus where a cheaper bound suffices? Pin precisely which optimal v genuinely need the IFT chart.

≤ 1.5 screens. Lead each answer with BOUNDED / WALL / verdict.
</output_contract>

<grounding_rules>
Flag inference vs known fact. If my dim formula is wrong, give the counterexample (specific A¹,A² at H=(2,2,2),r=1). Do not invent Mathlib lemma names — if unsure of a name, say "a lemma of the form …".
</grounding_rules>
