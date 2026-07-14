<task>
Lean 4 / Mathlib formalisation. I am assembling a "rendezvous" branch that wires a proved analytic crux into
a downstream headline. I need you to (A) confirm a hypothesis-strip is SOUND, and (B) sanity-check my
re-home architecture for a nasty import-topology, flagging any cycle or gap I missed.

## The import topology (VERIFIED from `import` lines)
Files (arrows = "is imported by", i.e. upstream -> downstream):
  DeeperFlagCore  ->  HeadSplitDom  ->  PivotDom  ->  PivotFin
DeeperFlagCore is ALSO imported by: GoodConnector, DecoratedStep.
DecoratedStep is imported by WaistConnector (which also imports WaistReversalCoV).
The headline mint file (HeadlineL1Mint) imports RouteMSJMint + DeepestBaseL1 (NOT the crux/connectors).

## What lives where
- PivotFin (MOST DOWNSTREAM) holds the PROVED crux, sorry-free:
    pivotPeel_domination (M u) (hu:1<=u) (he) (c')(hc0:0<=c')(hnd:forall i,1<=M i)(hpiv) {m}(hcvg)(hmM){e'}(he')
       (Zf)(hZfMeas)(U_sf)(hUs)(hrank)(hfloor) : exists C<top, pivotDomLHS M u e c' Zf <= C * pivotDomRHS M u c' Zf
    forward_LHS_finiteness (... same frame ...)(hRHS:pivotDomRHS<top) : pivotDomLHS<top
    pivotDom_finiteness_impl (... same frame, NO hu ...)(hRHS) : pivotDomLHS<top
      -- body: rcases Nat.eq_zero_or_pos u; u=0 -> pivotDom_finiteness_uzero -> pivotDom_uzero (a SORRY
      --       stub in the UPSTREAM PivotDom); u>=1 -> forward_LHS_finiteness.
  The bodies of pivotPeel_domination/forward_LHS_finiteness I have READ: pivotPeel_domination calls
  only pivotDomRHS_ne_zero_aux, pivotDomRHS_eq_top_of_critical, minAdm_add_peel_le,
  pivotDomLHS_lt_top_of_pos, pivotDomLHS_lt_top_of_zero -- NONE take m/hcvg/hmM/e'/he'/U_sf/hUs/hrank/hfloor.
  forward_LHS_finiteness just calls pivotPeel_domination then ENNReal.mul_lt_top.

- The UPSTREAM assembly chain (all currently `sorry` at the crux interface, cannot see PivotFin):
    DeeperFlagCore.headSplit_domination (STUB sorry) -- consumed by
    DeeperFlagCore.deeperFlag_spineToCore (sorry-free body EXCEPT it calls the stub) -- consumed by
    DeeperFlagCore.deeperFlag_shell_le (sorry-free body, calls spineToCore).
    HeadSplitDom.headSplit_pivotDom (STUB sorry) + shellSpine_le_hsQ_box (STUB sorry, a MECHANICAL
      measure-reorg fill, no crux) + headSplit_domination_impl (sorry-free body, calls the two stubs).
      -- I have READ headSplit_domination_impl: it does `refine <0, genBox, ?_>`, obtains from
      --   headSplit_pivotDom, then `le_trans (shellSpine_le_hsQ_box ...) hle`.
      -- shellSpine_le_hsQ_box's signature takes (kappa,e,c',ht,hj,hjr,ht1,hnd,hrange,e',he',he'le,Zf,hagree,
      --   hGmeas) -- it does NOT take U_sf/hUs/hrank/hfloor/m/hcvg/hmM.
    PivotDom.pivotDom_finiteness/pivotDom_RHS_ne_zero/pivotDom_uzero (STUBS) + headSplit_pivotDom_impl
      (sorry-free body, ratio trick calling the three stubs).

- Connectors (PARAMETERIZED, take crux-derived facts as hyps -- do NOT import PivotFin):
    GoodConnector.deeperFlagGood_finite_impl (M D)(hD)(hgoodpiv:forall u,minAdm(redChain u M)<=u*tailMinWidth M)
      (hIH)(hnd:forall i,1<=M i)(hstrict)(hsat)(hsector) : DecoratedBoxThresholdFinite D  -- sorry-free body.
      hstrict/hsat/hsector conclude `shellSpineIntegrand ... < top` at 1<=j<r / j=r / j=0.  They each take
      (t j kappa e)(he:0<e)(c')(t<=min(M0)(M1))(hj:j<=min(M0-t)(M1-t))(forall i,1<=M i)(hpiv per-cut)
      (c'<carrierThreshold M)(the j-position clause) -> shellSpineIntegrand < top.  NO hIH argument.
    WaistConnector.deeperFlagWaist_finite_impl (M D)(hD)(hwaist)(hM1<>1)(hIH)
      (hred:forall{K}(M' D'),adm->RouteMBoxThresholdFinite M'->DecoratedBoxThresholdFinite D') : ...
      -- body: L=0 -> routeMBoxThresholdFinite_mnp; L>=1 -> calls DecoratedStep.deeperFlagGood_finite
      --       (a SORRY STUB) on M o Fin.rev with the trivial decoration + reversal CoV routeMBoxThresholdFinite_of_rev.
    DecoratedStep.decoratedStepHyp_dispatch : DecoratedStepHyp adm (sorry-free body) dispatches:
      M1<deepTailMin & M1=1 -> (e) deeperFlagWaistM1_finite (FILLED sorry-free);
      M1<deepTailMin & M1<>1 -> (c) deeperFlagWaist_finite (STUB);
      else -> (d) deeperFlagGood_finite (STUB).
      (a) deeperFlagStrictShell_finite and (b) deeperFlagSaturatedShell_finite are STUBS NOT called by the
      dispatch (they were meant as inputs to (d), but (d)=GoodConnector takes hstrict/hsat as hyps instead).

- Target: DecoratedDescent := exists adm, adm_trivial /\ DecoratedStepHyp adm /\ DecoratedBaseHyp adm.
  decoratedBaseHyp_faithful : DecoratedBaseHyp adm, adm_trivial, adm all UPSTREAM (sorry-free).
  Driver routeMBoxThresholdFinite_of_decoratedDescent : DecoratedDescent -> forall n M, RouteMBoxThresholdFinite M.
  Mint hole (HeadlineL1Mint): `have hDescent : DecoratedDescent := sorry`.

  DecoratedStepHyp adm := forall L M, (forall M':Fin(L+1+1) D', adm(L+1)M'D' -> DecoratedBoxThresholdFinite D')
     -> forall D, adm(L+1+1)M D -> DecoratedBoxThresholdFinite D.

## Threshold facts
DecoratedBoxThresholdFinite D := forall c'<carrierThreshold M, D.integral c'<top. carrierThreshold M = minAdm M/2.
RouteMBoxThresholdFinite M := forall c'<minAdm M/2, routeMLayerBoxIntegral M c' 1<top.
minAdm_le_head_mul_tailInf : minAdm N <= N 0 * inf'(N 1 .. N last)  (so ANY zero width ==> minAdm=0).
minAdm_redChain_le_deepTailMin M u : minAdm(redChain u M) <= u*deepTailMin M.

## My PLAN
1. STRIP the vestigial frame {m,hcvg,hmM,e',he',U_sf,hUs,hrank,hfloor} from PivotFin's
   pivotPeel_domination/forward_LHS_finiteness/pivotDom_finiteness_impl (keep Zf/hZfMeas/hpiv/he/hc0/hnd).
2. uzero moot: add (hu:1<=u) to pivotDom_finiteness_impl, delete its u=0 branch, DELETE
   pivotDom_finiteness_uzero (PivotFin) + pivotDom_uzero (PivotDom).
3. Fill shellSpine_le_hsQ_box in HeadSplitDom (mechanical measure-reorg; a filled NON-shell version exists on
   another branch to adapt).
4. DELETE the dead upstream stubs that can never be wired without a cycle:
   PivotDom: pivotDom_finiteness, pivotDom_RHS_ne_zero, headSplit_pivotDom_impl (keep pivotDomLHS/RHS defs).
   HeadSplitDom: headSplit_pivotDom, headSplit_domination_impl (keep shellSpine_le_hsQ_box + defs/helpers).
   DeeperFlagCore: headSplit_domination stub, deeperFlag_spineToCore, deeperFlag_shell_le (move to R).
   DecoratedStep: (a),(b),(c) and decoratedStepHyp_dispatch (keep (e) + the sorry-free bricks + deepTailMin).
     PROBLEM: WaistConnector calls DecoratedStep.(d) deeperFlagGood_finite -- so I CANNOT delete (d).
5. Create NEW file R RouteMSJHeadSplitJoin downstream of PivotFin + GoodConnector + WaistConnector. In R:
   - headSplit_domination_R (clean) := headSplit_domination_impl's body, using shellSpine_le_hsQ_box
     + pivotPeel_domination (with hu:1<=t+j from ht1, frame stripped).
   - re-home deeperFlag_spineToCore + deeperFlag_shell_le bodies into R (copy, ~120 lines), calling
     headSplit_domination_R instead of the stub. -> clean deeperFlag_shell_le_R.
   - produce hstrict/hsat from deeperFlag_shell_le_R + hIH; hsector from #120 (see QUESTION 3).
   - clean (d): dGood M' D' hD' hgood' hIH' := deeperFlagGood_finite_impl M' D' hD' hgoodpiv' hIH' hnd' ...
     with by_cases hnd' (degenerate minAdm=0 ==> vacuous).
   - clean (c): need WaistConnector's impl but it calls the DecoratedStep (d) STUB internally.
   - decoratedStepHyp_dispatch_R : DecoratedStepHyp adm mirroring DecoratedStep's dispatch but with clean (c)/(d).
   - decoratedDescent_holds : DecoratedDescent := <adm, adm_trivial, decoratedStepHyp_dispatch_R, decoratedBaseHyp_faithful>.
6. HeadlineL1Mint imports R, replaces the sorry with decoratedDescent_holds.

## The WaistConnector/(d)-stub knot (my biggest worry)
WaistConnector.deeperFlagWaist_finite_impl bakes a call to DecoratedStep.(d) deeperFlagGood_finite
(a sorry stub) into its proof. To make (c) clean I must either (i) fill DecoratedStep.(d) [IMPOSSIBLE -- it
needs the crux which is downstream of DecoratedStep], or (ii) refactor deeperFlagWaist_finite_impl to take
the (d) statement as a hypothesis hgoodconn and drop the stub call (WaistConnector keeps its DecoratedStep
import for deepTailMin/adm/etc). Then R supplies hgoodconn = the clean (d). Is (ii) right, or a cleaner move?
</task>

<output_contract>
Four sections, terse:
1. FRAME-STRIP SOUNDNESS: Given the body descriptions, is stripping {m,hcvg,hmM,e',he',U_sf,hUs,hrank,hfloor}
   from the three PivotFin theorems sound (bodies never use them)? Any hidden dependency risk (a hyp used
   only for a by_cases or an instance) to double-check by re-reading a specific spot?
2. RE-HOME ARCHITECTURE: Does the plan have a cycle or a gap? Confirm R (downstream of PivotFin + both
   connectors) is a valid sink. Confirm deleting the listed upstream stubs breaks nothing I haven't accounted
   for. Rank copy-vs-parameterize for deeperFlag_spineToCore/deeperFlag_shell_le (copy ~120 lines into R, vs
   add a hypothesis to the DeeperFlagCore theorems and keep them in place).
3. WAIST/(d) KNOT: Endorse option (ii) or propose better. Note the arity: in deeperFlagWaist_finite_impl
   at M:Fin(L+1+1+1), the L>=1 branch instantiates (d) at M o Fin.rev : Fin(L+1+1+1) with SAME L and SAME hIH.
4. DEGENERATE hnd: my by_cases forall i,1<=M i -- in the neg case, exists i,M i=0 ==> minAdm M=0 (via
   minAdm_le_head_mul_tailInf) ==> carrierThreshold=0 ==> DecoratedBoxThresholdFinite vacuous. Sound? Any i
   where this bound doesn't apply (i=0 vs i>=1)?
</output_contract>

<grounding_rules>
You are reasoning from my structural descriptions, not the source. Flag any conclusion that depends on a
body detail I did NOT give you. Do not invent Mathlib lemma names. Mark inference vs. fact.
</grounding_rules>
