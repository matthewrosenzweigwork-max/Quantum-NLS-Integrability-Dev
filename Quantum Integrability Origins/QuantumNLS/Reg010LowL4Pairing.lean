import QuantumNLS.Reg010LowL4Resolvent

/-! Quartic control of a cubic pairing for kernels with finite Schur bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace QuantumNLS.Reg010LowL4Pairing
open QuantumNLS.BetheIntegralOperator

theorem four_factor_young (a b c : ℝ) :
    4 * a * b * c ^ 2 ≤ a ^ 4 + b ^ 4 + 2 * c ^ 4 := by
  nlinarith [sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
    mul_nonneg (sq_nonneg (a - b)) (sq_nonneg c)]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem weighted_snd (k : Kernel μ) (a : ℝ)
    (hcol : ∀ y, (∫ x, ‖k.fn (x, y)‖ ∂μ) ≤ a) (h : X → ℝ)
    (hh : Integrable h μ) (h0 : ∀ x, 0 ≤ h x) :
    Integrable (fun p : X × X => ‖k.fn p‖ * h p.2) (μ.prod μ) ∧
      (∫ p : X × X, ‖k.fn p‖ * h p.2 ∂μ.prod μ) ≤ a * ∫ x, h x ∂μ := by
  have hi : Integrable (fun p : X × X => ‖k.fn p‖ * h p.2) (μ.prod μ) := by
    refine (((integrable_const (1 : ℝ)).mul_prod hh).const_mul k.bound).mono'
      (k.measurable.norm.aestronglyMeasurable.mul hh.aestronglyMeasurable.comp_snd) ?_
    filter_upwards with p
    simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (h0 _)), one_mul]
    exact mul_le_mul_of_nonneg_right (k.norm_le p) (h0 _)
  refine ⟨hi, ?_⟩
  rw [integral_prod_symm _ hi, ← integral_const_mul]
  apply integral_mono hi.integral_prod_right (hh.const_mul _)
  intro y
  change (∫ x, ‖k.fn (x, y)‖ * h y ∂μ) ≤ a * h y
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right (hcol y) (h0 y)

theorem weighted_fst (k : Kernel μ) (a : ℝ)
    (hrow : ∀ x, (∫ y, ‖k.fn (x, y)‖ ∂μ) ≤ a) (h : X → ℝ)
    (hh : Integrable h μ) (h0 : ∀ x, 0 ≤ h x) :
    Integrable (fun p : X × X => ‖k.fn p‖ * h p.1) (μ.prod μ) ∧
      (∫ p : X × X, ‖k.fn p‖ * h p.1 ∂μ.prod μ) ≤ a * ∫ x, h x ∂μ := by
  have hi : Integrable (fun p : X × X => ‖k.fn p‖ * h p.1) (μ.prod μ) := by
    refine ((hh.mul_prod (integrable_const (1 : ℝ))).const_mul k.bound).mono'
      (k.measurable.norm.aestronglyMeasurable.mul hh.aestronglyMeasurable.comp_fst) ?_
    filter_upwards with p
    simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (h0 _)), mul_one]
    exact mul_le_mul_of_nonneg_right (k.norm_le p) (h0 _)
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi, ← integral_const_mul]
  apply integral_mono hi.integral_prod_left (hh.const_mul _)
  intro x
  change (∫ y, ‖k.fn (x, y)‖ * h x ∂μ) ≤ a * h x
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right (hrow x) (h0 x)

/-- Scaled four-factor estimate. The a.e. cubic identity is an identity of
the actual integrand, not a bound or correction conclusion. -/
theorem cubic_form_bound (k : Kernel μ) (a : ℝ)
    (hrow : ∀ x, (∫ y, ‖k.fn (x, y)‖ ∂μ) ≤ a)
    (hcol : ∀ y, (∫ x, ‖k.fn (x, y)‖ ∂μ) ≤ a)
    (u g : H μ) (r : X → ℂ) (hg : g =ᵐ[μ] fun x => star (u x) * (r x) ^ 2)
    (hu4 : Integrable (fun x => ‖u x‖ ^ 4) μ)
    (hr4 : Integrable (fun x => ‖r x‖ ^ 4) μ) (Z : ℝ) (hZ : 0 < Z) :
    ‖k.form u g‖ ≤ a / (4 * Z ^ 2) *
      (2 * (∫ x, ‖u x‖ ^ 4 ∂μ) + 2 * Z ^ 4 * ∫ x, ‖r x‖ ^ 4 ∂μ) := by
  obtain ⟨hfi, hfb⟩ := weighted_fst k a hrow (fun x => ‖u x‖ ^ 4) hu4 (fun x => by positivity)
  obtain ⟨hsi, hsb⟩ := weighted_snd k a hcol (fun x => ‖u x‖ ^ 4) hu4 (fun x => by positivity)
  obtain ⟨hri, hrb⟩ := weighted_snd k a hcol (fun x => ‖r x‖ ^ 4) hr4 (fun x => by positivity)
  let F : X × X → ℝ := fun p => (1 / (4 * Z ^ 2)) *
    (‖k.fn p‖ * ‖u p.1‖ ^ 4 + ‖k.fn p‖ * ‖u p.2‖ ^ 4 +
      (2 * Z ^ 4) * (‖k.fn p‖ * ‖r p.2‖ ^ 4))
  have hF : Integrable F (μ.prod μ) := ((hfi.add hsi).add (hri.const_mul _)).const_mul _
  have hnorm : ‖k.form u g‖ ≤ ∫ p, F p ∂μ.prod μ := by
    apply norm_integral_le_of_norm_le hF
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae_eq_comp hg] with p hp
    simp only [Function.comp_apply] at hp
    simp only [Kernel.integrand, hp, norm_mul, norm_star, norm_pow, Complex.norm_conj]
    dsimp only [F]
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ (by positivity : 0 < 4 * Z ^ 2)).mpr
    have hb := mul_le_mul_of_nonneg_left
      (four_factor_young ‖u p.1‖ ‖u p.2‖ (Z * ‖r p.2‖)) (norm_nonneg (k.fn p))
    nlinarith
  have he : (∫ p, F p ∂μ.prod μ) = (1 / (4 * Z ^ 2)) *
      ((∫ p : X × X, ‖k.fn p‖ * ‖u p.1‖ ^ 4 ∂μ.prod μ) +
       (∫ p : X × X, ‖k.fn p‖ * ‖u p.2‖ ^ 4 ∂μ.prod μ) +
       (2 * Z ^ 4) * ∫ p : X × X, ‖k.fn p‖ * ‖r p.2‖ ^ 4 ∂μ.prod μ) := by
    dsimp only [F]
    have hsum : Integrable (fun p : X × X => ‖k.fn p‖ * ‖u p.1‖ ^ 4 +
        ‖k.fn p‖ * ‖u p.2‖ ^ 4) (μ.prod μ) := hfi.add hsi
    rw [integral_const_mul, integral_add hsum (hri.const_mul _),
      integral_add hfi hsi, integral_const_mul]
  rw [he] at hnorm
  calc
    _ ≤ _ := hnorm
    _ ≤ (1 / (4 * Z ^ 2)) *
        (a * (∫ x, ‖u x‖ ^ 4 ∂μ) + a * (∫ x, ‖u x‖ ^ 4 ∂μ) +
          (2 * Z ^ 4) * (a * ∫ x, ‖r x‖ ^ 4 ∂μ)) := by gcongr
    _ = _ := by ring

#print axioms four_factor_young
#print axioms weighted_snd
#print axioms weighted_fst
#print axioms cubic_form_bound
end QuantumNLS.Reg010LowL4Pairing

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowL4Pairing." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowL4Pairing." then
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
