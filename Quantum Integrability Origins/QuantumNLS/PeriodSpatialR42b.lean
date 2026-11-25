import QuantumNLS.PeriodFieldR42b

/-! Spatial-system transport at arbitrary physical L2 regularity, by a
change of variables in each actual Volterra iterate. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ComplexConjugate
namespace QuantumNLS.PeriodSpatialR42b
open PhysicalTensor (L2T)
open PeriodFieldR42b
open SpatialTransfer (Mat2 balCoef coef)

/-- A real change of time in the defining iterated integrals. -/
theorem dyson_scale {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (B : ℝ → A) (c : ℝ) (n : ℕ) (x : ℝ) :
    LinearFundamental.dyson (fun s => c • B (c*s)) n x =
      LinearFundamental.dyson B n (c*x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [LinearFundamental.dyson, ih, smul_mul_assoc]
    rw [intervalIntegral.integral_smul]
    simpa only [mul_zero] using intervalIntegral.smul_integral_comp_mul_left
      (a := 0) (b := x) (fun s => B s * LinearFundamental.dyson B n s) c

theorem transfer_scale {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (B : ℝ → A) (c x : ℝ) :
    L1SpatialTransfer.transfer (fun s => c • B (c*s)) x =
      L1SpatialTransfer.transfer B (c*x) :=
  tsum_congr (fun n => dyson_scale B c n x)

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid
variable {L κ : ℝ} [Fact (0 < L)]

theorem coefficient_scale (hκ : 0 < κ) (u : L2T L) (z : ℂ) (x : ℝ) :
    balCoef (κ*L) (fun y => (Real.sqrt L : ℂ)*L2SpatialTransfer.profile u (L*y)) z x =
      L • balCoef κ (L2SpatialTransfer.profile u) (z/(L:ℂ)) (L*x) := by
  have hL : 0 < L := Fact.out
  have hs : Real.sqrt (κ*L)*Real.sqrt L = L*Real.sqrt κ := by
    rw [Real.sqrt_mul hκ.le]
    calc
      Real.sqrt κ * Real.sqrt L * Real.sqrt L = Real.sqrt κ * (Real.sqrt L)^2 := by ring
      _ = L*Real.sqrt κ := by rw [Real.sq_sqrt hL.le]; ring
  have hsc : (Real.sqrt (κ*L) : ℂ)*(Real.sqrt L : ℂ) = (L:ℂ)*(Real.sqrt κ : ℂ) := by
    exact_mod_cast hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [balCoef, coef, Matrix.smul_apply, Complex.real_smul,
      ← mul_assoc, hsc] <;> field_simp [hL.ne']

/-- Every entry of the actual L2 fundamental matrix obeys the printed
change of period; no smooth representative is required. -/
theorem spatial_scale (hκ : 0 < κ) (u : L2T L) (z : ℂ) {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    L2SpatialTransfer.spatialTransfer (κ*L) (period L u) z x =
      L2SpatialTransfer.spatialTransfer κ u (z/(L:ℂ)) (L*x) := by
  have hp := L2SpatialTransfer.profile_ae_of_representative (period L u) (period_ae L u).symm
  have he : balCoef (κ*L) (L2SpatialTransfer.profile (period L u)) z =ᵐ[volume.restrict (Icc (0:ℝ) 1)]
      fun s => L • balCoef κ (L2SpatialTransfer.profile u) (z/(L:ℂ)) (L*s) := by
    filter_upwards [hp] with s hs
    change (Real.sqrt L : ℂ)*u (HierarchyScaling.dilation L (s : AddCircle (1:ℝ))) = _ at hs
    rw [dilation_coe] at hs
    rw [show balCoef (κ*L) (L2SpatialTransfer.profile (period L u)) z s =
      balCoef (κ*L) (fun y => (Real.sqrt L : ℂ)*L2SpatialTransfer.profile u (L*y)) z s by
        simp only [balCoef, coef, ← hs]; rfl]
    exact coefficient_scale hκ u z s
  exact (L1SpatialTransfer.transfer_eq_of_ae (by norm_num : (0:ℝ) ≤ 1) he hx).trans
    (transfer_scale _ L x)

/-- Literal discriminant conversion at every complex spectral parameter. -/
theorem discriminant_scale (hκ : 0 < κ) (u : L2T L) (z : ℂ) :
    L2SpatialTransfer.discriminant (κ*L) (period L u) z =
      L2SpatialTransfer.discriminant κ u (z/(L:ℂ)) := by
  unfold L2SpatialTransfer.discriminant
  rw [spatial_scale hκ u z (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num), mul_one]

end QuantumNLS.PeriodSpatialR42b

#print axioms QuantumNLS.PeriodSpatialR42b.dyson_scale
#print axioms QuantumNLS.PeriodSpatialR42b.transfer_scale
#print axioms QuantumNLS.PeriodSpatialR42b.coefficient_scale
#print axioms QuantumNLS.PeriodSpatialR42b.spatial_scale
#print axioms QuantumNLS.PeriodSpatialR42b.discriminant_scale

-- R42b final aggregate audit
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PeriodSpatialR42b." ||
        n.toString.startsWith "_private.QuantumNLS.PeriodSpatialR42b." then
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
  Lean.logInfo m!"R42b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
