import QuantumNLS.RootMassFourierR27
import QuantumNLS.TerraMultiRound73Truncation
import QuantumNLS.TerraMultiRound74Majorant

/-! REG-010, low orders: bounded regularizations on the actual L² carrier.
No Sobolev or moment finiteness hypothesis is used here. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace BoundedContinuousFunction
namespace QuantumNLS.Reg010LowBasic
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit
open QuantumNLS.RootH1PositiveSpectral

variable {L : ℝ} [Fact (0 < L)]

/-- The printed low-order correction, using the actual physical and free laws. -/
def correction (κ : ℝ) (hκ : 0 < κ) (u : L2T L) (Y : ℝ) : ℝ :=
  (∫ t, kernel Y t ∂(PhysicalQuantumMeasure.measure hκ u)) -
    ∫ t, kernel Y t ∂(freeMeasure L u)

theorem free_finite (u : L2T L) : IsFiniteMeasure (freeMeasure L u) := by
  rw [← QuantumNLS.FullMass.Mmeas_zero_coupling]
  infer_instance

theorem kernel_le (Y t : ℝ) : kernel Y t ≤ Y ^ 2 := by
  by_cases h : Y ^ 2 + t ^ 2 = 0
  · simp only [kernel, h, div_zero]
    positivity
  · unfold kernel
    apply (div_le_iff₀ (lt_of_le_of_ne (by positivity) (Ne.symm h))).mpr
    nlinarith [sq_nonneg Y, sq_nonneg t]

theorem regularization_bounds (μ : Measure ℝ) [IsFiniteMeasure μ] {Y : ℝ}
    (hY : 0 < Y) :
    0 ≤ (∫ t, kernel Y t ∂μ) ∧ (∫ t, kernel Y t ∂μ) ≤ Y ^ 2 * μ.real univ := by
  refine ⟨integral_nonneg (kernel_nonneg Y), ?_⟩
  calc
    _ ≤ ∫ _t : ℝ, Y ^ 2 ∂μ := integral_mono (kernel_integrable hY μ)
      (integrable_const _) (kernel_le Y)
    _ = _ := by simp [mul_comm]

/-- The stronger constant 1 is available because both positive terms lie in
the same interval [0,Y²m]. In particular this implies the printed constant 2. -/
theorem small_bound (κ : ℝ) (hκ : 0 < κ) (u : L2T L) {Y : ℝ} (hY : 0 < Y) :
    |correction κ hκ u Y| ≤ Y ^ 2 * ‖u‖ ^ 2 := by
  haveI := free_finite u
  obtain ⟨hp, hp'⟩ := regularization_bounds (PhysicalQuantumMeasure.measure hκ u) hY
  obtain ⟨hf, hf'⟩ := regularization_bounds (freeMeasure L u) hY
  rw [measureReal_def, PhysicalQuantumMeasure.full_mass hκ u] at hp'
  have hm : (freeMeasure L u).real univ = ‖u‖ ^ 2 := by
    rw [← QuantumNLS.FullMass.Mmeas_zero_coupling, measureReal_def,
      QuantumNLS.FullMass.Mmeas_univ, ENNReal.toReal_ofReal (sq_nonneg _)]
  rw [hm] at hf'
  rw [correction, abs_le]
  constructor <;> linarith

/-- Compatibility with the already frozen REG-014 family, at r=1. -/
theorem correction_eq_Dfun (κ : ℝ) (hκ : 0 < κ) (u : L2T L) {Y : ℝ} (hY : 0 < Y) :
    correction κ hκ u Y = QuantumNLS.Reg014Moments.Dfun κ hκ 1 u Y := by
  haveI := free_finite u
  have hi : Integrable (fun t : ℝ => t ^ (2 * 0)) (freeMeasure L u) := by
    simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (freeMeasure L u))
  have hs := QuantumNLS.Reg014Moments.free_kernel_sum hY u 0 hi
  simpa only [correction, QuantumNLS.Reg014Moments.Dfun,
    QuantumNLS.TerraMultiRound60Kernel.kernel, kernel, Nat.reduceAdd, Nat.reduceMul] using
    congrArg (fun x : ℝ => (∫ t, kernel Y t ∂(PhysicalQuantumMeasure.measure hκ u)) - x) hs

def kernelBCF (Y : ℝ) (hY : 0 < Y) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨kernel Y, by
    unfold kernel
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    positivity⟩ (Y ^ 2) (by
      intro x y
      change dist (kernel Y x) (kernel Y y) ≤ Y ^ 2
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [kernel_nonneg Y x, kernel_nonneg Y y, kernel_le Y x, kernel_le Y y])

theorem fixed_Y_continuous (κ : ℝ) (hκ : 0 < κ) {Y : ℝ} (hY : 0 < Y) :
    Continuous (fun u : L2T L => correction κ hκ u Y) := by
  have hp := QuantumNLS.Reg014Continuity.integral_Mmeas_continuous (L := L) κ hκ.le (kernelBCF Y hY)
  have hf := QuantumNLS.Reg014Continuity.integral_Mmeas_continuous (L := L) 0 le_rfl (kernelBCF Y hY)
  convert hp.sub hf using 1
  funext u
  rw [correction, PhysicalL2Normalization.measure_eq_Mmeas,
    ← QuantumNLS.FullMass.Mmeas_zero_coupling]
  rfl

theorem correction_measurable (κ : ℝ) (hκ : 0 < κ) (u : L2T L) :
    Measurable (correction κ hκ u) := by
  haveI := free_finite u
  have hm : StronglyMeasurable (Function.uncurry kernel) := by
    apply Measurable.stronglyMeasurable
    unfold Function.uncurry kernel
    fun_prop
  exact hm.integral_prod_right.measurable.sub hm.integral_prod_right.measurable

#print axioms regularization_bounds
#print axioms small_bound
#print axioms correction_eq_Dfun
#print axioms fixed_Y_continuous
#print axioms correction_measurable
end QuantumNLS.Reg010LowBasic

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowBasic." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowBasic." then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Round45 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
