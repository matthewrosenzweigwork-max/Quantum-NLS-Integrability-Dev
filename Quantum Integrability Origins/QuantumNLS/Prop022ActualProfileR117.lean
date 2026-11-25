import QuantumNLS.Prop022ClassicalTimeR116
import QuantumNLS.Prop001Flow

/-! The factorial kernels construct the actual unit Hartree trajectory.
All path regularity, unit norm and speed bounds below are conclusions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped InnerProductSpace Topology ContDiff
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
namespace QuantumNLS.Prop022ActualProfileR117
open TensorCarrier PhysicalTensor BetheCoefficientTransform
open Prop022TensorCompressionR115 Prop022FactorialCoefficientsR115
open Prop022FactorialMajorantR115 Prop022ClassicalTimeR116
variable {L : ℝ} [Fact (0 < L)]
local instance : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup

/-- Every fixed polynomial rank moment follows from the report bound. -/
lemma kernel_rank_summable (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A) (q : ℕ) :
    Summable (fun n => ((n+1 : ℕ) : ℝ)^q * ‖B (n+1)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _
    (((summable_nat_add_iff 1).mpr (weight_summable q A hA)).mul_left M)
  intro n
  calc
    _ ≤ ((n+1 : ℕ) : ℝ)^q * (M * A^(n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (hB (n+1) (by omega)) (by positivity)
    _ = _ := by unfold weight; ring

/-- An exponential rank margin, proved for the actual factorial kernels. -/
lemma kernel_exponential_summable (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A) :
    Summable (fun n => ((n+1 : ℕ) : ℝ) * ‖B (n+1)‖ * Real.exp (1 * n)) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _
    (((summable_nat_add_iff 1).mpr (weight_summable 1 (A * Real.exp 1) (by positivity))).mul_left M)
  intro n
  have he : Real.exp (1 * (n : ℝ)) ≤ Real.exp 1 ^ (n+1) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  calc
    _ ≤ ((n+1 : ℕ) : ℝ) * ‖B (n+1)‖ * Real.exp 1 ^ (n+1) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ ((n+1 : ℕ) : ℝ) * (M * A^(n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ)) *
        Real.exp 1 ^ (n+1) := by
      gcongr
      exact hB (n+1) (by omega)
    _ = _ := by unfold weight; rw [mul_pow]; ring

/-- The source flow data are derived from B, with no supplied path. -/
def classicalData (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m) :
    Prop001.ClassicalData (L2T L) where
  A n := B (n+1)
  selfAdjoint n := hs (n+1)
  a := 1
  a_pos := by norm_num
  cubic := kernel_rank_summable B M A hA hB 3
  exponential := kernel_exponential_summable B M A hA hB

/-- The actual trajectory, selected by the accepted global construction. -/
def profile (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) : ℝ → L2T L :=
  Prop001.trajectory (classicalData B M A hA hB hs) u₀

def velocity (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) : L2T L :=
  Ext025A8.sourceHartreeField (fun n => B (n+1)) u

lemma velocity_bound (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ)
    (hA : 0 ≤ A) (hB : FactorialBound B M A) (u : L2T L) (hu : ‖u‖ = 1) :
    ‖velocity B u‖ ≤ M * ∑' n, weight 1 A (n+1) := by
  let E := fun n => TensorPlacements.extendSymKernel (B (n+1))
  have hd (n : ℕ) : ‖Ext025A8.hartreeTerm E n u‖ ≤ M * weight 1 A (n+1) := by
    calc
      _ ≤ ((n+1 : ℕ) : ℝ) * ‖E n‖ * ‖u‖^(2*n+1) := Ext025A8.hartreeTerm_norm E n u
      _ ≤ ((n+1 : ℕ) : ℝ) * ‖B (n+1)‖ := by
        rw [hu, one_pow, mul_one]
        exact mul_le_mul_of_nonneg_left (TensorPlacements.norm_extendSymKernel_le _) (by positivity)
      _ ≤ ((n+1 : ℕ) : ℝ) * (M * A^(n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (hB (n+1) (by omega)) (by positivity)
      _ = _ := by unfold weight; ring
  have h := tsum_of_norm_bounded
    ((((summable_nat_add_iff 1).mpr (weight_summable 1 A hA)).mul_left M).hasSum) hd
  simpa only [velocity, Ext025A8.sourceHartreeField, Ext025A8.hartreeField,
    norm_smul, norm_neg, Complex.norm_I, one_mul, tsum_mul_left, E] using h

theorem profile_spec (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) :
    let u := profile B M A hA hB hs u₀
    u 0 = u₀.val ∧ ContDiff ℝ 1 u ∧
      (∀ t, ‖u t‖ = 1) ∧ (∀ t, HasDerivAt u (velocity B (u t)) t) ∧
      (∀ t, ‖velocity B (u t)‖ ≤ M * ∑' n, weight 1 A (n+1)) := by
  dsimp only
  have h := Prop001.trajectory_spec (classicalData B M A hA hB hs) u₀
  exact ⟨h.1, h.2.1, fun t => (h.2.2.1 t).1, fun t => (h.2.2.1 t).2,
    fun t => velocity_bound B M A hA hB _ (h.2.2.1 t).1⟩

/-- R116's hypotheses are discharged for the constructed factorial path. -/
theorem actual_classicalSeries_hasDerivAt
    (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) (t : ℝ) :
    let u := profile B M A hA hB hs u₀
    HasDerivAt (fun s => classicalSeries B (u s))
      (classicalSeriesRate B (u t) (velocity B (u t))) t := by
  dsimp only
  have h := profile_spec B M A hA hB hs u₀
  exact classicalSeries_hasDerivAt B M A (M * ∑' n, weight 1 A (n+1)) hA hB
    (mul_nonneg hM (tsum_nonneg (fun n => by unfold weight; positivity)))
    _ _ h.2.2.2.1 h.2.2.1 h.2.2.2.2 t

theorem actual_classicalSeries_C1
    (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) :
    ContDiff ℝ 1 (fun s => classicalSeries B (profile B M A hA hB hs u₀ s)) := by
  have h := profile_spec B M A hA hB hs u₀
  exact classicalSeries_time_C1 B M A (M * ∑' n, weight 1 A (n+1)) hA hB
    (mul_nonneg hM (tsum_nonneg (fun n => by unfold weight; positivity)))
    _ _ h.2.1 h.2.2.2.1 h.2.2.1 h.2.2.2.2

theorem actual_coefficients_continuous
    (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L)) :
    let u := profile B M A hA hB hs u₀
    Continuous (fun t => numberCoefficient B (u t)) ∧
      Continuous (fun t => pairCoefficient B (u t)) := by
  dsimp only
  have h := profile_spec B M A hA hB hs u₀
  exact ⟨Prop022TensorCalculusR116.numberCoefficient_time_continuous B M A hA hB _
      h.2.1.continuous h.2.2.1,
    Prop022TensorCalculusR116.pairCoefficient_time_continuous B M A hA hB _
      h.2.1.continuous h.2.2.1⟩
end QuantumNLS.Prop022ActualProfileR117
#print axioms QuantumNLS.Prop022ActualProfileR117.profile_spec
#print axioms QuantumNLS.Prop022ActualProfileR117.actual_classicalSeries_hasDerivAt
#print axioms QuantumNLS.Prop022ActualProfileR117.actual_classicalSeries_C1
#print axioms QuantumNLS.Prop022ActualProfileR117.actual_coefficients_continuous

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022ActualProfileR117." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022ActualProfileR117." then
      pending := pending.push n
  let roots := pending.size
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
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R117 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
