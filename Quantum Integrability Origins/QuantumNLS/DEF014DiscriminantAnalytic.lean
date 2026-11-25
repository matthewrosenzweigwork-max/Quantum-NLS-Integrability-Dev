import QuantumNLS.DEF014VolterraAnalytic
import QuantumNLS.DEF014Joint

/-! The physical L2 L2SpatialTransfer.discriminant is jointly real analytic in the L2SpatialTransfer.profile and
the complex spectral parameter, at fixed coupling. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Set Filter Topology MeasureTheory ComplexConjugate
open scoped Matrix Interval
namespace QuantumNLS.DEF014DiscriminantAnalytic
open SpatialTransfer L2SpatialTransfer DEF014VolterraOperator
open PhysicalTensor (L2T)
open RootDiscriminantBound (row_sum_le_norm norm_le_of_row_sums)
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid
variable {L : ℝ} [Fact (0 < L)]

theorem profile_add (u v : L2T L) :
    (fun x : ℝ => L2SpatialTransfer.profile (u + v) x) =ᵐ[volume.restrict (Ioc (0 : ℝ) L)] fun x => L2SpatialTransfer.profile u x + L2SpatialTransfer.profile v x := by
  have h := (AddCircle.measurePreserving_mk L 0).quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_add u v)
  simpa [L2SpatialTransfer.profile, Function.comp_def, zero_add] using h

theorem profile_smul (c : ℝ) (u : L2T L) :
    (fun x : ℝ => L2SpatialTransfer.profile (c • u) x) =ᵐ[volume.restrict (Ioc (0 : ℝ) L)] fun x => c • L2SpatialTransfer.profile u x := by
  have h := (AddCircle.measurePreserving_mk L 0).quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_smul c u)
  simpa [L2SpatialTransfer.profile, Function.comp_def, zero_add] using h

theorem norm_balCoef_le (κ : ℝ) (u : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    ‖balCoef κ u z x‖ ≤ ‖z‖ / 2 + Real.sqrt κ * ‖u x‖ := by
  refine norm_le_of_row_sums _ (by positivity) fun i => ?_
  fin_cases i <;> simp [balCoef, coef, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg κ), add_comm]

def physicalFamily (κ : ℝ) : Family (L2T L × ℂ) Mat2 L where
  coef p := balCoef κ (L2SpatialTransfer.profile p.1) p.2
  integrable p := intervalIntegrable_coef (intervalIntegrable_profile p.1) _ _ p.2
  add_ae p q := by
    filter_upwards [profile_add p.1 q.1] with t ht
    ext i j
    fin_cases i <;> fin_cases j <;> simp [balCoef, coef, ht, mul_add, add_div, add_comm]
  smul_ae c p := by
    filter_upwards [profile_smul c p.1] with t ht
    ext i j
    fin_cases i <;> fin_cases j <;> simp [balCoef, coef, ht, Complex.real_smul,
      mul_div_assoc, mul_left_comm]
    ring
  bound := L / 2 + Real.sqrt κ * Real.sqrt L
  bound_nonneg := by have hL : 0 < L := Fact.out; positivity
  norm_integral_le p := by
    have hL : 0 < L := Fact.out
    have hcoef := intervalIntegrable_coef (intervalIntegrable_profile p.1)
      (Real.sqrt κ) (Real.sqrt κ) p.2
    calc
      _ ≤ ∫ t in (0 : ℝ)..L, ‖p.2‖ / 2 + Real.sqrt κ * ‖L2SpatialTransfer.profile p.1 t‖ :=
        intervalIntegral.integral_mono_on hL.le hcoef.norm
          (intervalIntegrable_const.add ((intervalIntegrable_profile p.1).norm.const_mul _))
          (fun t _ => norm_balCoef_le κ _ _ t)
      _ = L * (‖p.2‖ / 2) + Real.sqrt κ * (∫ t in (0 : ℝ)..L, ‖L2SpatialTransfer.profile p.1 t‖) := by
        rw [intervalIntegral.integral_add intervalIntegrable_const
          ((intervalIntegrable_profile p.1).norm.const_mul _), intervalIntegral.integral_const,
          intervalIntegral.integral_const_mul]
        simp [smul_eq_mul]
      _ ≤ L * (‖p.2‖ / 2) + Real.sqrt κ * (Real.sqrt L * ‖p.1‖) := by
        gcongr
        exact DiscParamContinuity.integral_profile_le p.1
      _ ≤ (L / 2 + Real.sqrt κ * Real.sqrt L) * ‖p‖ := by
        have h1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
        have h2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
        nlinarith [mul_le_mul_of_nonneg_left h1
          (mul_nonneg (Real.sqrt_nonneg κ) (Real.sqrt_nonneg L)),
          mul_le_mul_of_nonneg_left h2 hL.le]

/-- Actual matrix entries as bounded real-linear functionals in the chosen operator norm. -/
def entryCLM (i j : Fin 2) : Mat2 →L[ℝ] ℂ :=
  ({ toFun := fun m => m i j
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : Mat2 →ₗ[ℝ] ℂ).mkContinuous 1 (by
    intro m
    change ‖m i j‖ ≤ 1 * ‖m‖
    rw [one_mul]
    have hi := row_sum_le_norm m i
    have he : ‖m i j‖ ≤ ∑ k : Fin 2, ‖m i k‖ :=
      Finset.single_le_sum (fun k _ => norm_nonneg _) (Finset.mem_univ j)
    exact he.trans (by simpa only [Fin.sum_univ_two] using hi))

/-- Convergent real multilinear series in the actual physical field, including
its conjugate, and in the spectral parameter. -/
theorem analyticAt_discriminant_joint (κ : ℝ) (p : L2T L × ℂ) :
    AnalyticAt ℝ (fun q : L2T L × ℂ => L2SpatialTransfer.discriminant κ q.1 q.2) p := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  have hp := DEF014VolterraAnalytic.analyticAt_transferPath hL (physicalFamily κ) p
  have hm := ((ContinuousMap.evalCLM ℝ (⟨L, hL, le_rfl⟩ : Icc (0 : ℝ) L)).analyticAt _).comp hp
  have he (i j : Fin 2) := ((entryCLM i j).analyticAt _).comp hm
  have ht := (he 0 0).add (he 1 1)
  change AnalyticAt ℝ (fun q : L2T L × ℂ =>
    L1SpatialTransfer.transfer (balCoef κ (L2SpatialTransfer.profile q.1) q.2) L 0 0 +
    L1SpatialTransfer.transfer (balCoef κ (L2SpatialTransfer.profile q.1) q.2) L 1 1) p at ht
  simpa only [L2SpatialTransfer.discriminant, L2SpatialTransfer.spatialTransfer,
    Matrix.trace_fin_two] using ht

/-- Individual L2SpatialTransfer.profile analyticity, for arbitrary physical L2 input. -/
theorem analyticAt_discriminant (κ : ℝ) (z : ℂ) (u : L2T L) :
    AnalyticAt ℝ (fun v : L2T L => L2SpatialTransfer.discriminant κ v z) u :=
  (analyticAt_discriminant_joint κ (u,z)).comp (f := fun v : L2T L => (v,z))
    (analyticAt_id.prod analyticAt_const)

end QuantumNLS.DEF014DiscriminantAnalytic

-- ROUND 4 AUTHOR AUDIT
#print axioms QuantumNLS.DEF014DiscriminantAnalytic.physicalFamily
#print axioms QuantumNLS.DEF014DiscriminantAnalytic.analyticAt_discriminant_joint
#print axioms QuantumNLS.DEF014DiscriminantAnalytic.analyticAt_discriminant

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.DEF014DiscriminantAnalytic." then
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
  Lean.logInfo m!"DEF014DiscriminantAnalytic audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
