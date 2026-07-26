#!/usr/bin/env python3
"""Generate the pattern-B over-vanishing leaf modules from per-leaf data (verified by
patternB_verify.py). Mirrors the proven (20,6,7) module; cover section is quadratic or cubic
per the leaf's actual phi max-degree."""
import os

LEANDIR = os.path.join(os.path.dirname(__file__), "lean/DLNFibre/DLN/Aoyagi")

# per-leaf: (p2, p3, block_start, vm_sorted, phi_slots)
# phi_slots: list of (block_coord, term1_factors, term2_factors); slot = -(prod(t1) + prod(t2))
LEAVES = {
 (6,1): dict(block=12, vm=[1,6,20], slots=[
    (12,[0,11],[1,16,7]), (13,[1,17,7],[11,2]), (14,[1,18,7],[11,3]), (15,[1,19,7],[11,4])]),
 (6,5): dict(block=12, vm=[5,6,20], slots=[
    (12,[0,11],[16,5,7]), (13,[11,2],[17,5,7]), (14,[11,3],[18,5,7]), (15,[11,4],[19,5,7])]),
 (6,6): dict(block=12, vm=[6,20], slots=[
    (12,[0,11],[16,6,7]), (13,[11,2],[17,6,7]), (14,[11,3],[18,6,7]), (15,[11,4],[19,6,7])]),
 (7,1): dict(block=16, vm=[1,7,20], slots=[
    (16,[0,11],[1,12,6]), (17,[1,13,6],[11,2]), (18,[1,14,6],[11,3]), (19,[1,15,6],[11,4])]),
 (7,5): dict(block=16, vm=[5,7,20], slots=[
    (16,[0,11],[12,5,6]), (17,[11,2],[13,5,6]), (18,[11,3],[14,5,6]), (19,[11,4],[15,5,6])]),
 (7,6): dict(block=16, vm=[6,7,20], slots=[
    (16,[0,11],[12,6]), (17,[11,2],[13,6]), (18,[11,3],[14,6]), (19,[11,4],[15,6])]),
 (7,7): dict(block=16, vm=[7,20], slots=[
    (16,[0,11],[12,6,7]), (17,[11,2],[13,6,7]), (18,[11,3],[14,6,7]), (19,[11,4],[15,6,7])]),
}

def prod_str(fs):
    return " * ".join(f"u {c}" for c in fs)
def prod_str_x(fs):
    return " * ".join(f"x {c}" for c in fs)

def slot_expr(t1, t2, var="u"):
    ps = prod_str if var=="u" else prod_str_x
    return f"-({ps(t1)} + {ps(t2)})"

A1_ARGS = "A1_00 A1_01 A1_02 A1_10 A1_11 A1_12 A1_20 A1_21 A1_22 A1_30 A1_31 A1_32"

ENTRY_SIMP = """  simp (config := { decide := true }) only [gCanon, psiCanon, phiCanon, blockShear,
    A0, A1_00, A1_01, A1_02, A1_10, A1_11, A1_12, A1_20, A1_21, A1_22, A1_30, A1_31, A1_32,
    nativeChart1, nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm,
    t1P20, t2P20, Function.comp_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply, Fin.isValue, Option.elim,
    if_true, if_false]"""

def entry_thm(row, col, zc, vm_prod):
    return f"""set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option linter.unusedSimpArgs false in
set_option linter.style.maxHeartbeats false in
/-- Entry `({row},{col})`, `zc = {zc}`. -/
theorem entry_{row}{col} (u : Fin 21 → ℝ) :
    coreGen dvec eWrap (finProdFinEquiv (({row} : Fin 4), ({col} : Fin 3))) (gCanon (psiCanon u))
      = {vm_prod} * u {zc} := by
  rw [coreGen_eWrap_entry]
  simp only [Equiv.symm_apply_apply, Fin.isValue]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
{ENTRY_SIMP}
  ring
"""

def gen(p2, p3, d):
    block = d['block']; vm = d['vm']; slots = d['slots']
    coinc = (p2 == p3)
    cubic = any(len(t1)>=3 or len(t2)>=3 for (_,t1,t2) in slots)
    ns = f"OverVanishB_20_{p2}_{p3}"
    blockset = [block, block+1, block+2, block+3]
    vm_prod = " * ".join(f"u {c}" for c in vm)
    vm_or = " ∨ ".join(f"d = {c}" for c in vm)
    # zc: col0 -> {0:0,1:2,2:3,3:4}; col2 -> block+row
    col0zc = {0:0,1:2,2:3,3:4}
    def zc_of(row,col): return col0zc[row] if col==0 else block+row
    Zset = sorted([0,2,3,4] + blockset)
    Zset_str = ", ".join(str(c) for c in Zset)
    # read coords for phiCanon_read
    reads = sorted(set(c for (_,t1,t2) in slots for c in (t1+t2)))
    reads_haves = "\n  ".join(f"have h{c} := h {c} (by decide)" for c in reads)
    reads_list = ", ".join(f"h{c}" for c in reads)
    # keepCanon
    keep = " ∧ ".join(f"i ≠ {c}" for c in blockset)
    keep_neg = ", ".join(f"if_neg h{c}" for c in blockset)
    obtain = ", ".join(f"h{c}" for c in blockset)
    # phiCanon def
    phidef_lines = []
    first = True
    for (bc,t1,t2) in slots:
        kw = "if" if first else "else if"
        phidef_lines.append(f"  {kw} i = {bc} then {slot_expr(t1,t2)}")
        first = False
    phidef = "\n".join(phidef_lines) + "\n  else 0"
    # prod_vmExpCanon
    if len(vm)==3:
        filter_show = f"{{{vm[0]}, {vm[1]}, {vm[2]}}}"
        prod_tac = ("Finset.prod_insert (by decide), Finset.prod_insert (by decide), "
                    "Finset.prod_singleton]\n  ring")
    else:
        filter_show = f"{{{vm[0]}, {vm[1]}}}"
        prod_tac = "Finset.prod_insert (by decide), Finset.prod_singleton]"
    # zcPair
    pairs = [(0,0),(0,2),(1,0),(1,2),(2,0),(2,2),(3,0),(3,2)]
    zcpair_lines = []
    for i,(r,c) in enumerate(pairs[:-1]):
        kw = "if" if i==0 else "else if"
        zcpair_lines.append(f"{kw} p = ({r}, {c}) then {zc_of(r,c)}")
    zcpair = "\n  ".join(zcpair_lines) + f"\n  else {zc_of(3,2)}"
    # entries
    entries = "\n".join(entry_thm(r,c,zc_of(r,c),vm_prod) for (r,c) in pairs)
    entry_firsts = " | ".join(f"exact entry_{r}{c} u" for (r,c) in pairs)
    # open line
    cubic_open = " blockShear_covers_cubic" if cubic else ""
    open_line = (f"open DLNFibre.DLN.Aoyagi.OverVanishCanon334 (coreGen_eWrap_entry\n"
                 f"  {A1_ARGS}{cubic_open})")
    # cover section
    if cubic:
        # cubic norm bound + cover
        slot_apps = []
        for (bc,t1,t2) in slots:
            def h(t): return f"(hq {t[0]} {t[1]})" if len(t)==2 else f"(hcube {t[0]} {t[1]} {t[2]})"
            slot_apps.append(
              f"  by_cases h{bc} : i = {bc}\n"
              f"  · rw [h{bc}, show phiCanon x {bc} = {slot_expr(t1,t2,'x')} from rfl]\n"
              f"    exact slot _ _ {h(t1)} {h(t2)}")
        slot_block = "\n".join(slot_apps)
        cover = f"""/-! ## §6 — the CUBIC cover-transport (φ has a degree-3 term) -/

/-- **The cubic displacement bound** `‖φ x‖ ≤ 2·r³` for `r ≥ 1` (each block slot is a sum of two
products of ≤ 3 kept coords; `|quad| ≤ r² ≤ r³`, `|cubic| ≤ r³`). -/
theorem phiCanon_norm_bound {{x : Fin 21 → ℝ}} {{r : ℝ}} (hr1 : 1 ≤ r) (hx : ‖x‖ ≤ r) :
    ‖phiCanon x‖ ≤ 2 * r ^ 3 := by
  have hr0 : 0 ≤ r := by linarith
  have hr23 : r ^ 2 ≤ r ^ 3 := by nlinarith [sq_nonneg r, hr1]
  have habs : ∀ i : Fin 21, |x i| ≤ r := fun i => by
    rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm x i).trans hx
  have hq : ∀ a b : Fin 21, |x a * x b| ≤ r ^ 3 := fun a b => by
    have h2 : |x a * x b| ≤ r ^ 2 := by
      rw [abs_mul, sq]; exact mul_le_mul (habs a) (habs b) (abs_nonneg _) hr0
    exact le_trans h2 hr23
  have hcube : ∀ a b c : Fin 21, |x a * x b * x c| ≤ r ^ 3 := fun a b c => by
    rw [abs_mul, abs_mul]
    calc |x a| * |x b| * |x c| ≤ r * r * r :=
          mul_le_mul (mul_le_mul (habs a) (habs b) (abs_nonneg _) hr0) (habs c) (abs_nonneg _)
            (by positivity)
      _ = r ^ 3 := by ring
  have slot : ∀ A B : ℝ, |A| ≤ r ^ 3 → |B| ≤ r ^ 3 → |(-(A + B))| ≤ 2 * r ^ 3 :=
    fun A B hA hB => by
      rw [abs_neg]
      calc |A + B| ≤ |A| + |B| := abs_add_le _ _
        _ ≤ r ^ 3 + r ^ 3 := add_le_add hA hB
        _ = 2 * r ^ 3 := by ring
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs]
{slot_block}
  · rw [phiCanon_keep x i ⟨{obtain}⟩, abs_zero]; positivity

/-- **The canonical cubic cover-transport** — `closedBall 0 r ⊆ Ψ '' closedBall 0 (r + 2·r³)` (`r ≥ 1`). -/
theorem psiCanon_cubic_cover {{r : ℝ}} (hr1 : 1 ≤ r) :
    closedBall (0 : Fin 21 → ℝ) r ⊆ psiCanon '' closedBall 0 (r + 2 * r ^ 3) := by
  unfold psiCanon
  exact blockShear_covers_cubic keepCanon phiCanon_keep phiCanon_read
    (fun x hx => phiCanon_norm_bound hr1 hx)

/-- **The folded-chart cover survives the cubic fold.** -/
theorem image_comp_psiCanon_cubic_superset (g : (Fin 21 → ℝ) → (Fin 21 → ℝ)) {{r : ℝ}}
    (hr1 : 1 ≤ r) :
    g '' closedBall 0 r ⊆ (g ∘ psiCanon) '' closedBall 0 (r + 2 * r ^ 3) := by
  calc g '' closedBall (0 : Fin 21 → ℝ) r
      ⊆ g '' (psiCanon '' closedBall 0 (r + 2 * r ^ 3)) :=
        Set.image_mono (psiCanon_cubic_cover hr1)
    _ = (g ∘ psiCanon) '' closedBall 0 (r + 2 * r ^ 3) := (Set.image_comp g psiCanon _).symm
"""
    else:
        slot_apps = []
        for (bc,t1,t2) in slots:
            args = f"{t1[0]} {t1[1]} {t2[0]} {t2[1]}"
            slot_apps.append(
              f"  by_cases h{bc} : i = {bc}\n"
              f"  · rw [h{bc}, show phiCanon x {bc} = {slot_expr(t1,t2,'x')} from rfl]; "
              f"exact slot {args}")
        slot_block = "\n".join(slot_apps)
        cover = f"""/-! ## §6 — the QUADRATIC cover-transport (φ has max degree 2) -/

/-- **The quadratic displacement bound** `‖φ x‖ ≤ 2·r²` (each block slot is a sum of two quadratic
products of kept coords). -/
theorem phiCanon_norm_bound {{x : Fin 21 → ℝ}} {{r : ℝ}} (hr : 0 ≤ r) (hx : ‖x‖ ≤ r) :
    ‖phiCanon x‖ ≤ 2 * r ^ 2 := by
  have habs : ∀ i : Fin 21, |x i| ≤ r := fun i => by
    rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm x i).trans hx
  have hq : ∀ a b : Fin 21, |x a * x b| ≤ r ^ 2 := fun a b => by
    rw [abs_mul, sq]; exact mul_le_mul (habs a) (habs b) (abs_nonneg _) hr
  have slot : ∀ a b c d : Fin 21, |(-(x a * x b + x c * x d))| ≤ 2 * r ^ 2 := fun a b c d => by
    rw [abs_neg]
    calc |x a * x b + x c * x d| ≤ |x a * x b| + |x c * x d| := abs_add_le _ _
      _ ≤ r ^ 2 + r ^ 2 := add_le_add (hq a b) (hq c d)
      _ = 2 * r ^ 2 := by ring
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs]
{slot_block}
  · rw [phiCanon_keep x i ⟨{obtain}⟩, abs_zero]; positivity

/-- **The folded-chart cover survives the quadratic fold.** -/
theorem image_comp_psiCanon_superset (g : (Fin 21 → ℝ) → (Fin 21 → ℝ)) {{r : ℝ}} :
    g '' closedBall 0 r ⊆ (g ∘ psiCanon) '' closedBall 0 (r + 2 * r ^ 2) := by
  unfold psiCanon
  exact image_comp_blockShear_superset g keepCanon phiCanon_keep phiCanon_read
    (fun x hx => phiCanon_norm_bound (le_trans (norm_nonneg x) hx) hx)
"""

    coinc_note = "COINCIDING (`p2 = p3`), " if coinc else "NON-coinciding, "
    cover_note = ("its `φ` carries a degree-3 term, so the CUBIC cover atom applies"
                  if cubic else "its `φ` is genuinely QUADRATIC (max degree 2), quadratic cover atom")
    module = f"""import DLNFibre.DLN.Aoyagi.Corank2OverVanishCanon334

/-!
# `DLN.Aoyagi.Corank2OverVanishB_20_{p2}_{p3}` — pattern-B over-vanishing leaf `(20,{p2},{p3})`

The pattern-B per-type deliverables for the over-vanishing leaf `(p1,p2,p3) = (20,{p2},{p3})`, mirroring
the canonical `(20,1,1)` template (`Corank2OverVanishCanon334`). Pattern B = reg-seq DROPS column
`c = 1` (keeps columns `c = 0, 2`), `S = {{0,2,3,5,6,8,9,11}}`; straighten-block `{{{blockset[0]}, {blockset[1]}, {blockset[2]}, {blockset[3]}}}` (`p2 = {p2}`).

`(20,{p2},{p3})` is {coinc_note}`vm = {' · '.join('u'+str(c) for c in vm)}`; {cover_note}. The 8
reg-seq entry values are `sympy`-verified end-to-end vs the Lean `gFlat` (`a3f030 @4ceface15`,
independently cross-checked by this seat, max err `1.3e-15`).
-/

open Matrix MeasureTheory Set Metric
open DLNFibre.Core.Aoyagi
open DLNFibre.DLN.Aoyagi.NativeFan334
open DLNFibre.DLN.Aoyagi.NativePerm334
open DLNFibre.DLN.Aoyagi.NativeShear334
open DLNFibre.DLN.Aoyagi.NativeJac334
open DLNFibre.DLN.Aoyagi.OverVanish334
open DLNFibre.DLN.Aoyagi.Corank2CoreGenWrap
{open_line}

namespace DLNFibre.DLN.Aoyagi.{ns}

/-! ## §0 — the leaf and its composite -/

/-- The over-vanishing leaf index `(p1,p2,p3) = (20,{p2},{p3})`. -/
def idxCanon : Idx := ⟨⟨20, by decide⟩, ⟨{p2}, by decide⟩, ⟨{p3}, by decide⟩⟩

/-- The leaf composite `gFlat idxCanon`. -/
noncomputable def gCanon : (Fin 21 → ℝ) → (Fin 21 → ℝ) := fun w =>
  blockBlowupMap S1 20 (nativeChart1 20
    (blockBlowupMap (sigmaC1Fs 20) {p2} (blockBlowupMap (sigmaC2Fs 20) {p3} w)))

/-- `gFlat idxCanon = gCanon`. -/
theorem gFlat_idxCanon : gFlat idxCanon = gCanon := by funext w; rfl

/-! ## §1 — the straightening shear `Ψ = psiCanon` -/

/-- The straightening displacement `φ` (pattern-B, block `{{{blockset[0]},{blockset[1]},{blockset[2]},{blockset[3]}}}`). -/
def phiCanon : (Fin 21 → ℝ) → (Fin 21 → ℝ) := fun u i =>
{phidef}

/-- The straightening `Ψ = blockShear φ`. -/
noncomputable def psiCanon : (Fin 21 → ℝ) → (Fin 21 → ℝ) := blockShear phiCanon

/-- The kept coordinates: everything outside the straightened block. -/
abbrev keepCanon : Fin 21 → Prop := fun i => {keep}

/-- `φ` fixes every kept coordinate. -/
theorem phiCanon_keep (u : Fin 21 → ℝ) (i : Fin 21) (hi : keepCanon i) : phiCanon u i = 0 := by
  obtain ⟨{obtain}⟩ := hi
  simp only [phiCanon, {keep_neg}]

set_option linter.unusedSimpArgs false in
/-- `φ` reads only kept coordinates. -/
theorem phiCanon_read (u v : Fin 21 → ℝ) (h : ∀ i, keepCanon i → u i = v i) :
    phiCanon u = phiCanon v := by
  {reads_haves}
  funext i
  simp only [phiCanon]
  split_ifs <;> simp only [{reads_list}]

set_option linter.unusedSimpArgs false in
/-- `φ` is differentiable. -/
theorem differentiable_phiCanon : Differentiable ℝ phiCanon := by
  apply differentiable_pi.2
  intro i
  fin_cases i <;>
    simp (config := {{ decide := true }}) only [phiCanon, Fin.isValue, if_true, if_false] <;>
    fun_prop

/-- `Ψ` is differentiable. -/
theorem differentiable_psiCanon : Differentiable ℝ psiCanon := by
  unfold psiCanon blockShear
  exact differentiable_id.add differentiable_phiCanon

/-- **`|jacDet Ψ| = 1`**. -/
theorem jacDet_psiCanon (u : Fin 21 → ℝ) : jacDet psiCanon u = 1 := by
  unfold psiCanon
  exact jacDet_blockShear phiCanon keepCanon differentiable_phiCanon phiCanon_keep phiCanon_read u

/-- `Ψ` fixes every coordinate outside the block. -/
theorem psiCanon_apply_offblock (u : Fin 21 → ℝ) (d : Fin 21) (hd : keepCanon d) :
    psiCanon u d = u d := by
  unfold psiCanon blockShear
  simp only [Pi.add_apply, phiCanon_keep u d hd, add_zero]

/-! ## §2 — the per-type data -/

/-- The dominant monomial exponent `vm`. -/
def vmExpCanon : Fin 21 → ℕ := fun d => if {vm_or} then 1 else 0

/-- `∏_d (u d)^(vmExpCanon d) = {vm_prod}`. -/
theorem prod_vmExpCanon (u : Fin 21 → ℝ) : (∏ d, (u d) ^ vmExpCanon d) = {vm_prod} := by
  have h1 : ∀ d : Fin 21, u d ^ vmExpCanon d = if {vm_or} then u d else 1 :=
    fun d => by simp only [vmExpCanon]; split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one,
    show Finset.filter (fun d : Fin 21 => {vm_or}) Finset.univ = {filter_show} from by decide,
    {prod_tac}

/-- The 8 reg-seq `(row, col)` pairs (pattern B: columns `c = 0, 2`). -/
def pairsCanon : Finset (Fin 4 × Fin 3) :=
  {{(0, 0), (0, 2), (1, 0), (1, 2), (2, 0), (2, 2), (3, 0), (3, 2)}}

/-- The 8-element regular-sequence entry-index set `S`. -/
def Scanon : Finset (Fin (dvec (Fin.last 2) * dvec 0)) := pairsCanon.image finProdFinEquiv

/-- The straightening coordinate map on `(row, col)` pairs. -/
def zcPair : Fin 4 × Fin 3 → Fin 21 := fun p =>
  {zcpair}

/-- The straightening coordinate map `zc`. -/
def zcCanon : Fin (dvec (Fin.last 2) * dvec 0) → Fin 21 := fun k => zcPair (finProdFinEquiv.symm k)

/-- The `jac`-free regular-sequence coordinate block `Z = zc '' S`. -/
def Zcanon : Finset (Fin 21) := {{{Zset_str}}}

theorem hzc_inj : ∀ x ∈ Scanon, ∀ y ∈ Scanon, zcCanon x = zcCanon y → x = y := by decide

theorem hzc_img : Scanon.image zcCanon = Zcanon := by decide

/-! ## §3 — the 8 reg-seq entry identities -/

{entries}
set_option linter.unusedSimpArgs false in
/-- **The 8 reg-seq entry identities.** -/
theorem canon_hentry (u : Fin 21 → ℝ) (k : Fin (dvec (Fin.last 2) * dvec 0)) (hk : k ∈ Scanon) :
    coreGen dvec eWrap k (gFlat idxCanon (psiCanon u))
      = (∏ d, (u d) ^ vmExpCanon d) * u (zcCanon k) := by
  rw [gFlat_idxCanon, prod_vmExpCanon]
  simp only [Scanon, Finset.mem_image] at hk
  obtain ⟨p, hp, rfl⟩ := hk
  simp only [zcCanon, Equiv.symm_apply_apply]
  fin_cases hp <;>
    first
      | {entry_firsts}

/-! ## §4 — the assembled per-type domination -/

/-- **The over-vanishing product-germ domination (per-type FACT).** -/
theorem canon_domination (u : Fin 21 → ℝ) :
    monoSumSqGerm vmExpCanon Zcanon u
      ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘ (gFlat idxCanon ∘ psiCanon)) u :=
  monoSumSqGerm_le_of_regSeq_entries (S := Scanon) (zc := zcCanon) canon_hentry hzc_inj hzc_img u

/-! ## §5 — the folded Jacobian -/

set_option linter.unusedSimpArgs false in
/-- Every binding axis of `jacExp idxCanon` is outside the straightened block. -/
theorem hfix_jacExp (u : Fin 21 → ℝ) :
    ∀ d, 0 < jacExp idxCanon d → psiCanon u d = u d := by
  intro d hd
  apply psiCanon_apply_offblock u d
  refine ⟨{', '.join('?_' for _ in blockset)}⟩ <;>
    (intro h; subst h
     simp (config := {{ decide := true }}) only [jacExp, idxCanon, Pi.add_apply,
       NativeJac334.single, sigmaC2Fs, Fin.isValue, Finset.mem_insert, Finset.mem_singleton,
       if_true, if_false, add_zero, zero_add, lt_self_iff_false] at hd)

/-- **The folded Jacobian.** -/
theorem canon_foldedJac (u : Fin 21 → ℝ) :
    |jacDet (gFlat idxCanon ∘ psiCanon) u| = jacWeight (jacExp idxCanon) u := by
  rw [jacDet_comp u (differentiable_gFlat idxCanon).differentiableAt
    differentiable_psiCanon.differentiableAt, abs_mul, jacDet_psiCanon, abs_one, mul_one,
    hjac_gFlat idxCanon (psiCanon u)]
  exact jacWeight_fixOn (jacExp idxCanon) (hfix_jacExp u)

{cover}
end DLNFibre.DLN.Aoyagi.{ns}
"""
    return module

for (p2,p3), d in LEAVES.items():
    fn = os.path.join(LEANDIR, f"Corank2OverVanishB_20_{p2}_{p3}.lean")
    with open(fn, "w") as f:
        f.write(gen(p2,p3,d))
    print("wrote", fn)
