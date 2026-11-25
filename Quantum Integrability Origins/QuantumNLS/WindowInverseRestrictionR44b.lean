import QuantumNLS.Def021ChartR41b
import QuantumNLS.Reg015HFinal
import QuantumNLS.LossSobolev

open scoped NNReal
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000

/-! R-E59628C9: use the named conditional REG-015 theorem directly, for the
accepted actual chart; combine it with the accepted loss lemma. REG-015 is
pending review, as recorded in gaps.json. Its statement is not assumed here. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local instance] InnerProductSpace.complexToReal
open Set
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.PhysicalTensor QuantumNLS.Reg015Setting QuantumNLS.LossSobolev
namespace QuantumNLS.WindowInverseRestrictionR44b
variable {L κ : ℝ} [Fact (0 < L)]

def baseHomeo (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) : L2T L ≃ₜ Seq where
  toFun := C.Φ
  invFun := C.Ψ
  left_inv := C.left_inverse
  right_inv := C.right_inverse
  continuous_toFun := continuous_iff_continuousAt.mpr fun u => (C.analytic u).continuousAt
  continuous_invFun := continuous_iff_continuousAt.mpr fun z => (C.inverse_analytic z).continuousAt

def targetUniv (s : ℝ) (hs : 0 ≤ s) : h02 L s ≃ₜ Target (L := L) univ s hs where
  toFun z := ⟨z,mem_univ _⟩
  invFun z := z.val
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_id.subtype_mk _
  continuous_invFun := continuous_subtype_val

/-- The actual inverse restriction, with no supplied Sobolev premise. -/
theorem inverse_restriction (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (s : ℝ) (hs : 0 ≤ s) :
    ∃ g : h02 L s → H02 L s, Continuous g ∧
      ∀ z, (g z).val = C.Ψ (toBase s hs z) := by
  let e : L2T L ≃ₜ (univ : Set Seq) := (baseHomeo hκ C).trans (Homeomorph.Set.univ Seq).symm
  have hm : ExactModuli e hκ := C.actions
  obtain ⟨F,hF⟩ := (Reg015HFinal.REG015_final hκ s hs).2.2 univ e hm
  let G : H02 L s ≃ₜ h02 L s := F.trans (targetUniv s hs).symm
  refine ⟨G.symm,G.symm.continuous,?_⟩
  intro z
  have hc : C.Φ (G.symm z).val = toBase s hs z := by
    apply lp.ext
    funext n
    have he := hF (G.symm z) n
    change (G (G.symm z)).val n = C.Φ (G.symm z).val n at he
    rw [G.apply_symm_apply] at he
    exact he.symm.trans (toBase_apply s hs z n).symm
  rw [← hc,C.left_inverse]

/-- Literal zero-order lift, with no choice of inverse representative. -/
def zeroLift : L2T L →ₗ[ℂ] H02 L 0 where
  toFun u := WField.mk u (by
    have h := summable_sq_of_lp (QuantumNLS.Fourier.fourierL2 L u)
    simpa [def002] using h)
  map_add' _ _ := WField.ext rfl
  map_smul' _ _ := WField.ext rfl

@[simp] theorem zeroLift_val (u : L2T L) : (zeroLift u : H02 L 0).val = u := rfl

def zeroLiftCLM : L2T L →L[ℝ] H02 L 0 :=
  ((zeroLift (L := L)).mkContinuous 1 (fun u => by
    simpa only [one_mul,zeroLift_val] using (H02.norm_zero (zeroLift u)).symm.le)).restrictScalars ℝ

@[simp] theorem zeroLiftCLM_val (u : L2T L) : (zeroLiftCLM u : H02 L 0).val = u := rfl

/-- The exact h^S to H^q C¹ restriction of the accepted analytic inverse.
The supplied inequalities are numerical orders, not chart regularity claims. -/
theorem inverse_loss (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (q S : ℝ≥0) (hq : 0 < q) (hS : 2*(q : ℝ) < S) (hqS : q ≤ S)
    (g : h02 L (S : ℝ) → H02 L (S : ℝ)) (hg : Continuous g)
    (hgc : ∀ z, (g z).val = C.Ψ (toBase S S.2 z)) :
    ContDiff ℝ 1 (fun x => (fieldScale L).emb S q hqS (g x)) := by
  let Z : L2T L →L[ℝ] (fieldScale L).Y 0 := zeroLiftCLM
  have hf : AnalyticOnNhd ℝ (fun z : Seq => Z (C.Ψ z)) univ :=
    fun z _ => (Z.analyticAt _).comp (C.inverse_analytic z)
  have hres : ∀ x : h02 L (S : ℝ),
      (fieldScale L).emb S 0 (Loss.nn_zero_le S) (g x) = Z (C.Ψ (toBase S S.2 x)) := by
    intro x
    apply WField.ext
    change (g x).val = C.Ψ (toBase S S.2 x)
    exact hgc x
  exact (loss_analytic (fieldScale L) ((toBase S S.2).restrictScalars ℝ)
    (k := 1) (by norm_num) hq (by norm_num; exact hS) hqS
    (fun z : Seq => Z (C.Ψ z)) hf g hg hres).1

/-- The printed choice q=2d+4, S=4d+9 meets the loss threshold strictly. -/
theorem window_orders (d : ℕ) :
    0 < (2*(d : ℝ)+4) ∧ 2*(2*(d : ℝ)+4) < 4*(d : ℝ)+9 := by
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) d]

end QuantumNLS.WindowInverseRestrictionR44b

#print axioms QuantumNLS.WindowInverseRestrictionR44b.inverse_restriction
#print axioms QuantumNLS.WindowInverseRestrictionR44b.inverse_loss

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowInverseRestrictionR44b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowInverseRestrictionR44b." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R44b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
