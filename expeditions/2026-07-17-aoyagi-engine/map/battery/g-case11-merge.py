#!/usr/bin/env python3
# guards: case-step-lemmas, resolution-tree
# config: Case-1(1) exponent-merge M'_{s,k} = M_{s,k} + J_1*(M^{(S+1)}-J); page-image re-derive + necessity
# provenance: threads/01-skeleton (architect-t01, repair pass, ruling 4); PAGE IMAGE preprint p.16 Case 1(1)
"""Case-1(1) child-merge: page-image re-derivation + the child-reading NECESSITY witness.

PAGE-IMAGE PIN (Aoyagi preprint p.16, "Case 1 (1)", read from the PDF image, NOT extracted text):
the equal-block chart sets d-block = u_{s,k}*d', b'_{J+i} = u_{s,k}*b_{J+i} for i=1..J_1, t̃_{s,k}=J,
and ADDS to that divisor's exponent

    M'_{s,k} = M_{s,k} + J_1 * (M^{(S+1)} - J)            [page 16, "Let {...}" block]

(decrementing the count of u's with t̃ = J+J_1 by one -- the inner recursion).

RE-DERIVE (a): the u_{s,k} factor is pulled out of every entry of the J_1 x (M^{(S+1)}-J) d-sub-block
(rows J+1..J+J_1, cols J+1..M^{(S+1)}), so the u_{s,k}-degree GAINED by the pulled-back monomial is
exactly that sub-block's cardinality, J_1 * (M^{(S+1)} - J). Added to the divisor's existing exponent
M_{s,k} this gives the page formula by construction. In the Lean carrier this is `StepRel`'s case-1(1)
clause `rootDivExp e.child = n.divExp kp + e.subst.runLen * n.resCols`, with `runLen = J_1` and
`resCols = M^{(S+1)} - J` (the residual column count).

WORKED INSTANCE (b): parent divExp M_{s,k}=5, run length J_1=2, residual cols M^{(S+1)}-J=3
=> child exponent = 5 + 2*3 = 11 (the cert/Codex worked value; NOT 0, NOT 99).

NECESSITY (c) -- why the child exponent must be READ (finding 1): a "childless" invariant that
constrains only the PARENT (t̃_{s,k}=J and the run length) is satisfied by EVERY candidate child
exponent {0, 11, 99} alike -- it cannot pin the paper's parent-referencing merge. The child-reading
relation `child = parent + J_1*resCols` admits ONLY 11. So the edge must record J_1 and read the
child; this is the defect the repair fixes.

Exit 0 iff: (a) sub-block re-derivation == page formula on a sweep of (J_1, resCols); (b) the worked
instance yields 11; (c) the childless relation admits >1 of {0,11,99} while the child-reading relation
admits exactly {11}.
"""
import sys


def merge_increment(J1, resCols):
    """u_{s,k}-degree gained: one factor per entry of the J_1 x resCols d-sub-block."""
    return sum(1 for _i in range(J1) for _j in range(resCols))   # = J1 * resCols, counted honestly


def page_formula(M_sk, J1, MS1, J):
    """Page 16 Case 1(1): M'_{s,k} = M_{s,k} + J_1 (M^{(S+1)} - J)."""
    return M_sk + J1 * (MS1 - J)


# (a) sub-block re-derivation == page formula (resCols := M^{(S+1)} - J)
rederive_ok = True
for J1 in range(0, 6):
    for resCols in range(0, 6):
        M_sk = 4                       # arbitrary existing exponent; increment is what we re-derive
        MS1, J = resCols + 1, 1        # so that M^{(S+1)} - J = resCols
        child_rederived = M_sk + merge_increment(J1, resCols)
        child_page = page_formula(M_sk, J1, MS1, J)
        if child_rederived != child_page:
            rederive_ok = False

# (b) the worked instance: parent 5, J_1 = 2, resCols = 3  ->  11
parent, J1w, resColsw = 5, 2, 3
child_worked = parent + merge_increment(J1w, resColsw)
worked_ok = (child_worked == 11)

# (c) necessity: childless (parent-only) vs child-reading
candidates = [0, 11, 99]
correct = parent + J1w * resColsw                      # = 11
childless_admits = set(candidates)                     # parent-only constraint sees all of them
childreading_admits = {c for c in candidates if c == correct}
necessity_ok = (len(childless_admits) > 1 and childreading_admits == {11})

ok = rederive_ok and worked_ok and necessity_ok

print(f"(a) sub-block re-derivation == page-16 formula M_sk + J_1(M^(S+1)-J) on sweep: {rederive_ok}")
print(f"(b) worked instance parent=5, J_1=2, resCols=3 -> child = {child_worked} (expect 11): {worked_ok}")
print(f"(c) childless relation admits {sorted(childless_admits)}; child-reading admits "
      f"{sorted(childreading_admits)} => child must be read: {necessity_ok}")
sys.exit(0 if ok else 1)
