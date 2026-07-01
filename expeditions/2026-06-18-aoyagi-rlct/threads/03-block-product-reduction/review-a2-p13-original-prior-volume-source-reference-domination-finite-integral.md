# Review - A2 p.13 Original-prior Volume-source-reference Domination Finite Integral

Date: 2026-07-01.

Status: PASS after focused Lean checks, full local build, and one successful
xhigh read-only review. One earlier xhigh reviewer was blocked by the VM shell
launcher before inspecting files; that is recorded as a tool failure, not as a
mathematical finding.

## Scope/math reviewer

Reviewer: Pascal the 2nd, xhigh explorer.

Verdict: blocked/no-shell.

The reviewer could not run even read-only commands because every shell command
failed before execution with `CreateProcess ... No such file or directory`.
From the prompt alone, it identified the right risks to check: scalar order,
measure-inequality direction, distinction from the exact-pullback sibling, and
avoidance of original-prior/global/RLCT overclaims. It did not inspect the
diff, so this is not counted as positive review evidence.

## Lean/math reviewer

Reviewer: James the 2nd, xhigh explorer.

Verdict: PASS.

Checked:

- The generic handoff composes `mu <= C • sourceRef` with
  `Measure.map readback sourceRef <= Csource • thetaRef` and concludes
  `(C * Csource) • thetaRef`.
- The p.13 specialization sets `C := (c : ENNReal) * D` and concludes exactly
  `(((c : ENNReal) * D) * Csource) • thetaRef`.
- The inequality directions are the intended upper-bound directions:
  restricted original-volume domination gives
  `muP13 <= ((c : ENNReal) * D) • sourceRef`, then readback pushforward and
  source-reference pullback domination give the coordinate-source bound.
- The exact-pullback sibling still uses
  `Measure.map readback sourceRef = coordinateSourceMeasure.restrict W` and
  scalar `(cHaar : ENNReal) * D`; the new sibling instead assumes
  `Measure.map readback sourceRef <= Csource • coordinateSourceMeasure.restrict W`,
  `Csource < infinity`, and scalar `((cHaar : ENNReal) * D) * Csource`.
- The reproduction and statement card match the formal theorem and keep the
  same nonclaim boundary.

Residual risk noted by the reviewer: the generic handoff docstring says
"finite scalar domination" although the generic theorem itself does not assume
`Csource < infinity`; the finite-integral consumer does assume it, so this is a
docstring imprecision rather than a formal overclaim.

## Local controller checks

- `lake env lean DLNFibre/DLN/Aoyagi/LocalMeasureHandoff.lean` passed.
- `lake build DLNFibre.DLN.Aoyagi.LocalMeasureHandoff` passed.
- `lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13SourceMeasureBridge.lean` passed.
- `lake build DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13SourceMeasureBridge` passed.
- `lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13ReadbackFiniteIntegral.lean` passed.
- `lake build DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13ReadbackFiniteIntegral` passed.
- `lake env lean DLNFibre.lean` passed.
- Full local `lake build DLNFibre` passed.
- `lean/scripts/sorries` reported `0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `git diff --check` passed.
- Direct axiom probes for the three new public theorem names reported only
  `[propext, Classical.choice, Quot.sound]`.

## Nonclaims

This review confirms only the conditional domination-wrapper shape. It does
not certify a concrete `sourceRef`, restricted-volume domination, source
coverage, chart-image equality, source-rank coverage, Haar scalar
normalization, normal crossings, pole order, RLCT extraction, or global
original-prior integrability beyond the supplied local chart piece.
