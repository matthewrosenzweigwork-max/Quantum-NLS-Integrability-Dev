import QuantumNLS.L1TransferParameter
import QuantumNLS.L2SpatialTransfer
import QuantumNLS.RootDiscriminant
import QuantumNLS.RootDiscriminantContinuity

/-! Reality of the actual L2ST1 discriminant, proved from the L1 Volterra
integral equation. No continuous representative or spectral premise is used. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set ComplexConjugate
open scoped Matrix
namespace QuantumNLS.L2DiscriminantRegularity
open QuantumNLS.SpatialTransfer QuantumNLS.L1SpatialTransfer
open QuantumNLS.L2SpatialTransfer QuantumNLS.RootDiscriminant
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid
variable {L : ℝ} [Fact (0 < L)]

/-- Conjugate-swap as a continuous map for the same matrix norm as L2ST1. -/
def swapOp : Mat2 →L[ℝ] Mat2 := LinearMap.toContinuousLinearMap cswap

theorem swapOp_apply (m : Mat2) (i j : Fin 2) :
    swapOp m i j = conj (m i.rev j.rev) := rfl

theorem swapOp_one : swapOp (1 : Mat2) = 1 := cswap_one

theorem swapOp_mul_coef (κ : ℝ) (u : ℝ → ℂ) (t x : ℝ) (Y : Mat2) :
    swapOp (balCoef κ u (t : ℂ) x * Y) = balCoef κ u (t : ℂ) x * swapOp Y :=
  cswap_mul_coef κ u t x Y

/-- Conjugate-swap symmetry of the actual absolutely continuous transfer. -/
theorem transfer_symm (κ : ℝ) (u : PhysicalTensor.L2T L) (t : ℝ) :
    EqOn (fun x => swapOp (L2SpatialTransfer.spatialTransfer κ u (t : ℂ) x))
      (L2SpatialTransfer.spatialTransfer κ u (t : ℂ)) (Icc 0 L) := by
  let A := balCoef κ (profile u) (t : ℂ)
  let U := L2SpatialTransfer.spatialTransfer κ u (t : ℂ)
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  have hi : IntervalIntegrable A volume 0 L :=
    intervalIntegrable_coef (intervalIntegrable_profile u) _ _ _
  have hc : ContinuousOn U (Icc 0 L) := continuousOn_transfer hL hi
  have hp : IntervalIntegrable (fun x => A x * U x) volume 0 L :=
    hi.mul_continuousOn (by
      rw [uIcc_of_le hL]
      exact continuousOn_transfer hL hi)
  apply integral_solution_unique hL hi
    (swapOp.continuous.comp_continuousOn hc) hc
  · intro x hx
    have hs : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) L := by
      rw [uIcc_of_le hx.1, uIcc_of_le hL]
      exact Icc_subset_Icc_right hx.2
    change swapOp (U x) = 1 + ∫ s in (0 : ℝ)..x, A s * swapOp (U s)
    rw [show U x = 1 + ∫ s in (0 : ℝ)..x, A s * U s from
      spatialTransfer_integral_eq κ u (t : ℂ) hx,
      map_add, swapOp_one]
    apply congrArg (fun y : Mat2 => 1 + y)
    calc
      swapOp (∫ s in (0 : ℝ)..x, A s * U s) =
          ∫ s in (0 : ℝ)..x, swapOp (A s * U s) :=
        (swapOp.intervalIntegral_comp_comm (hp.mono_set hs)).symm
      _ = ∫ s in (0 : ℝ)..x, A s * swapOp (U s) := by
        apply intervalIntegral.integral_congr
        intro s _
        exact swapOp_mul_coef κ (profile u) t s (U s)
  · exact fun x hx => spatialTransfer_integral_eq κ u (t : ℂ) hx

/-- Reality for every arbitrary L2 equivalence class, including discontinuous inputs. -/
theorem discriminant_real (κ : ℝ) (u : PhysicalTensor.L2T L) (t : ℝ) :
    (L2SpatialTransfer.discriminant κ u (t : ℂ)).im = 0 := by
  have he := transfer_symm κ u t (show L ∈ Icc 0 L from
    ⟨(Fact.out : 0 < L).le, le_rfl⟩)
  have h11 := congrArg (fun m : Mat2 => m 1 1) he
  simp only [swapOp_apply] at h11
  have hrev : (1 : Fin 2).rev = 0 := rfl
  rw [hrev] at h11
  unfold L2SpatialTransfer.discriminant
  rw [Matrix.trace_fin_two, ← h11]
  simp

/-- The actual L2 monodromy depends continuously on the complex parameter.
A single L1 coefficient majorant controls all Dyson terms on each closed ball. -/
theorem continuous_transfer (κ : ℝ) (u : PhysicalTensor.L2T L)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    Continuous (fun z : ℂ => L2SpatialTransfer.spatialTransfer κ u z x) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let R : ℝ := ‖z₀‖ + 1
  let g : ℝ → ℝ := fun t => R / 2 + Real.sqrt κ * ‖profile u t‖
  have hg : IntervalIntegrable g volume 0 L :=
    intervalIntegrable_const.add ((intervalIntegrable_profile u).norm.const_mul _)
  have hb : ∀ z ∈ Metric.closedBall z₀ 1, ∀ t ∈ Icc 0 L,
      ‖balCoef κ (profile u) z t‖ ≤ g t := by
    intro z hz t ht
    have hzR : ‖z‖ ≤ R := by
      have hh : ‖z - z₀‖ ≤ 1 := by simpa [dist_eq_norm] using hz
      have := norm_le_norm_add_norm_sub' z z₀
      dsimp [R]
      linarith [norm_sub_rev z z₀]
    exact (QuantumNLS.RootDiscriminantContinuity.norm_balCoef_le κ (profile u) z t).trans
      (by dsimp [g]; linarith)
  have hc : ∀ t ∈ Icc 0 L,
      ContinuousOn (fun z : ℂ => balCoef κ (profile u) z t) (Metric.closedBall z₀ 1) := by
    intro t ht
    apply Continuous.continuousOn
    unfold balCoef coef
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  have h := QuantumNLS.L1TransferParameter.continuousOn_transfer
    (Fact.out : 0 < L).le
    (fun z _ => intervalIntegrable_coef (intervalIntegrable_profile u) _ _ z)
    hg hb hc hx
  exact h.continuousAt (Metric.closedBall_mem_nhds z₀ one_pos)

/-- This supplies SourceFacts.continuous_discriminant on the actual L2 carrier. -/
theorem continuous_discriminant (κ : ℝ) (u : PhysicalTensor.L2T L) :
    Continuous (L2SpatialTransfer.discriminant κ u) := by
  unfold L2SpatialTransfer.discriminant
  simp only [Matrix.trace_fin_two]
  have hc := continuous_transfer κ u (show L ∈ Icc 0 L from
    ⟨(Fact.out : 0 < L).le, le_rfl⟩)
  exact (hc.matrix_elem 0 0).add (hc.matrix_elem 1 1)

end QuantumNLS.L2DiscriminantRegularity

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.L2DiscriminantRegularity.swapOp
#print axioms QuantumNLS.L2DiscriminantRegularity.swapOp_apply
#print axioms QuantumNLS.L2DiscriminantRegularity.swapOp_one
#print axioms QuantumNLS.L2DiscriminantRegularity.swapOp_mul_coef
#print axioms QuantumNLS.L2DiscriminantRegularity.transfer_symm
#print axioms QuantumNLS.L2DiscriminantRegularity.discriminant_real
#print axioms QuantumNLS.L2DiscriminantRegularity.continuous_transfer
#print axioms QuantumNLS.L2DiscriminantRegularity.continuous_discriminant

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.L2DiscriminantRegularity." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
