import QuantumNLS.Reg010LowCorrection

/-! Fourth-power Schur estimates and their specialization to the actual
periodic derivative resolvent. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.Reg010LowL4Resolvent
open QuantumNLS.BetheIntegralOperator

theorem quartic_young (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    4 * a ^ 3 * b ≤ 3 * a ^ 4 + b ^ 4 := by
  have h := mul_nonneg (sq_nonneg (b - a))
    (show 0 ≤ b ^ 2 + 2 * a * b + 3 * a ^ 2 by positivity)
  nlinarith

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- A row estimate requiring only first and fourth integrability. -/
theorem row_fourth (k : X → ℂ) (hk : Measurable k) (K : ℝ) (_hK : 0 ≤ K)
    (hkK : ∀ x, ‖k x‖ ≤ K) (f : X → ℂ) (hf : Integrable f μ)
    (hf4 : Integrable (fun x => ‖f x‖ ^ 4) μ) (a : ℝ) (ha : 0 < a)
    (hrow : (∫ x, ‖k x‖ ∂μ) ≤ a) :
    ‖∫ x, k x * f x ∂μ‖ ^ 4 ≤ a ^ 3 * ∫ x, ‖k x‖ * ‖f x‖ ^ 4 ∂μ := by
  have hki : Integrable (fun x => ‖k x‖) μ :=
    (integrable_const K).mono' hk.norm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [norm_norm] using hkK x)
  have h1 : Integrable (fun x => ‖k x‖ * ‖f x‖) μ :=
    (hf.norm.const_mul K).mono' (hk.norm.aestronglyMeasurable.mul hf.norm.aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (hkK x) (norm_nonneg _))
  have h4 : Integrable (fun x => ‖k x‖ * ‖f x‖ ^ 4) μ :=
    (hf4.const_mul K).mono' (hk.norm.aestronglyMeasurable.mul hf4.aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (hkK x) (by positivity))
  let N := ‖∫ x, k x * f x ∂μ‖
  have hN : 0 ≤ N := norm_nonneg _
  have hND : N ≤ ∫ x, ‖k x‖ * ‖f x‖ ∂μ := by
    simpa only [norm_mul] using (norm_integral_le_integral_norm (fun x => k x * f x))
  have hpoly := integral_mono (h1.const_mul (4 * N ^ 3 * a))
    ((hki.const_mul (3 * N ^ 4)).add (h4.const_mul (a ^ 4))) (fun x => by
      have h := mul_le_mul_of_nonneg_left (quartic_young N (a * ‖f x‖) hN (by positivity))
        (norm_nonneg (k x))
      dsimp only [Pi.add_apply]
      nlinarith)
  simp only [Pi.add_apply] at hpoly
  rw [integral_const_mul, integral_add (hki.const_mul _) (h4.const_mul _),
    integral_const_mul, integral_const_mul] at hpoly
  have hleft := mul_le_mul_of_nonneg_left hND (show 0 ≤ 4 * N ^ 3 * a by positivity)
  have hright := mul_le_mul_of_nonneg_left hrow (show 0 ≤ 3 * N ^ 4 by positivity)
  have hfinal : a * N ^ 4 ≤ a * (a ^ 3 * ∫ x, ‖k x‖ * ‖f x‖ ^ 4 ∂μ) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ ha).mp hfinal

/-- The fourth-power Schur bound on the existing bounded-kernel carrier. -/
theorem schur_fourth (k : Kernel μ) (a : ℝ) (ha : 0 < a)
    (hrow : ∀ x, (∫ y, ‖k.fn (x, y)‖ ∂μ) ≤ a)
    (hcol : ∀ y, (∫ x, ‖k.fn (x, y)‖ ∂μ) ≤ a) (f : H μ)
    (hf4 : Integrable (fun x => ‖f x‖ ^ 4) μ) :
    Integrable (fun x => ‖k.operator f x‖ ^ 4) μ ∧
      (∫ x, ‖k.operator f x‖ ^ 4 ∂μ) ≤ a ^ 4 * ∫ x, ‖f x‖ ^ 4 ∂μ := by
  have hkm : AEStronglyMeasurable (fun p => ‖k.fn p‖) (μ.prod μ) :=
    k.measurable.norm.aestronglyMeasurable
  have hprod : Integrable (fun p : X × X => ‖k.fn p‖ * ‖f p.2‖ ^ 4) (μ.prod μ) := by
    refine (((integrable_const (1 : ℝ)).mul_prod hf4).const_mul k.bound).mono'
      (hkm.mul hf4.aestronglyMeasurable.comp_snd) ?_
    filter_upwards with p
    simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖k.fn p‖ * ‖f p.2‖ ^ 4), one_mul]
    exact mul_le_mul_of_nonneg_right (k.norm_le p) (by positivity)
  have hpoint : ∀ᵐ x ∂μ, ‖k.operator f x‖ ^ 4 ≤
      a ^ 3 * ∫ y, ‖k.fn (x, y)‖ * ‖f y‖ ^ 4 ∂μ := by
    filter_upwards [k.operator_apply_ae f] with x hx
    rw [hx]
    exact row_fourth (fun y => k.fn (x, y)) (k.measurable.comp (measurable_const.prodMk measurable_id))
      k.bound k.bound_nonneg (fun y => k.norm_le (x, y)) f (integrable_vector f) hf4 a ha (hrow x)
  have hi : Integrable (fun x => ‖k.operator f x‖ ^ 4) μ := by
    apply (hprod.integral_prod_left.const_mul (a ^ 3)).mono'
      ((Lp.aestronglyMeasurable (k.operator f)).norm.pow 4)
    filter_upwards [hpoint] with x hx
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖k.operator f x‖ ^ 4)] using hx
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, a ^ 3 * ∫ y, ‖k.fn (x, y)‖ * ‖f y‖ ^ 4 ∂μ ∂μ :=
      integral_mono_ae hi (hprod.integral_prod_left.const_mul _) hpoint
    _ = a ^ 3 * ∫ p : X × X, ‖k.fn p‖ * ‖f p.2‖ ^ 4 ∂μ.prod μ := by
      rw [integral_const_mul, integral_prod _ hprod]
    _ ≤ a ^ 3 * (a * ∫ y, ‖f y‖ ^ 4 ∂μ) := by
      gcongr
      rw [integral_prod_symm _ hprod, ← integral_const_mul]
      apply integral_mono hprod.integral_prod_right (hf4.const_mul _)
      intro y
      change (∫ x, ‖k.fn (x, y)‖ * ‖f y‖ ^ 4 ∂μ) ≤ a * ‖f y‖ ^ 4
      rw [integral_mul_const]
      exact mul_le_mul_of_nonneg_right (hcol y) (by positivity)
    _ = _ := by ring

open QuantumNLS.PhysicalTensor QuantumNLS.HaarResolvent
open QuantumNLS.RootH1RatioOperator QuantumNLS.RootH1RatioL2
open QuantumNLS.HaarKernelFactorization
variable {L : ℝ} [hLf : Fact (0 < L)]

/-- Sharp L⁴ contraction of the actual resolvent, in fourth-integral form. -/
theorem resolvent_fourth {Y : ℝ} (hY : 0 < Y) (u : L2T L)
    (hu4 : Integrable (fun x => ‖u x‖ ^ 4) volume) :
    Integrable (fun x => ‖resolvent Y u x‖ ^ 4) volume ∧
      (∫ x, ‖resolvent Y u x‖ ^ 4) ≤ (1 / Y) ^ 4 * ∫ x, ‖u x‖ ^ 4 := by
  apply schur_fourth (R1ker L (Real.exp (-Y * L)) ((Y : ℂ) * Complex.I))
    (1 / Y) (by positivity) _ _ u hu4
  · intro x
    change (∫ t : AddCircle L, ‖Rk _ _ (rep1 L x) (rep1 L t)‖) ≤ _
    rw [integral_rep (fun t => ‖Rk (Real.exp (-Y * L)) ((Y : ℂ) * Complex.I) (rep1 L x) t‖)]
    exact (norm_kernel_row hY ⟨(rep1_bounds L x).1, (rep1_bounds L x).2.le⟩).le
  · intro t
    change (∫ x : AddCircle L, ‖Rk _ _ (rep1 L x) (rep1 L t)‖) ≤ _
    rw [integral_rep (fun x => ‖Rk (Real.exp (-Y * L)) ((Y : ℂ) * Complex.I) x (rep1 L t)‖)]
    exact (norm_kernel_col hY ⟨(rep1_bounds L t).1, (rep1_bounds L t).2.le⟩).le

#print axioms quartic_young
#print axioms row_fourth
#print axioms schur_fourth
#print axioms resolvent_fourth
end QuantumNLS.Reg010LowL4Resolvent

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowL4Resolvent." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowL4Resolvent." then
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
