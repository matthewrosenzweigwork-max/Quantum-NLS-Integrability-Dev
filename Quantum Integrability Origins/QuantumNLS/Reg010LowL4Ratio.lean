import QuantumNLS.Reg010LowL4Resolvent

/-! The L⁴ improvement for the actual rough-input nonlinear ratio. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.Reg010LowL4Ratio
open QuantumNLS.PhysicalTensor QuantumNLS.RootH1RatioOperator
open QuantumNLS.RootH1RatioBounds QuantumNLS.RootH1RatioNonlinear
open QuantumNLS.Reg010LowL4Resolvent

variable {L : ℝ} [Fact (0 < L)]

theorem forcing_pointwise (κ : ℝ) (hκ : 0 ≤ κ) (u : L2T L) (r : Linfty L) :
    ∀ᵐ x, ‖forcing κ u r x‖ ≤ (1 + κ * ‖r‖ ^ 2) * ‖u x‖ := by
  filter_upwards [Lp.coeFn_sub u ((κ : ℂ) • cubic u r),
    Lp.coeFn_smul (κ : ℂ) (cubic u r), coe_cubic u r, ae_norm_le r] with x hs hm hc hr
  change ‖(u - (κ : ℂ) • cubic u r) x‖ ≤ _
  rw [hs, Pi.sub_apply, hm, Pi.smul_apply, smul_eq_mul, hc]
  calc
    _ ≤ ‖u x‖ + ‖(κ : ℂ) * (star (u x) * (r x) ^ 2)‖ := norm_sub_le _ _
    _ = ‖u x‖ + κ * (‖u x‖ * ‖r x‖ ^ 2) := by
      rw [norm_mul, norm_mul, norm_star, norm_pow, Complex.norm_real, Real.norm_of_nonneg hκ]
    _ ≤ (1 + κ * ‖r‖ ^ 2) * ‖u x‖ := by
      have hh := pow_le_pow_left₀ (norm_nonneg _) hr 2
      nlinarith [mul_le_mul_of_nonneg_left hh (mul_nonneg hκ (norm_nonneg (u x)))]

theorem forcing_fourth (κ : ℝ) (hκ : 0 ≤ κ) (u : L2T L) (r : Linfty L)
    (hu4 : Integrable (fun x => ‖u x‖ ^ 4) volume) :
    Integrable (fun x => ‖forcing κ u r x‖ ^ 4) volume ∧
      (∫ x, ‖forcing κ u r x‖ ^ 4) ≤ (1 + κ * ‖r‖ ^ 2) ^ 4 * ∫ x, ‖u x‖ ^ 4 := by
  have hp : ∀ᵐ x, ‖forcing κ u r x‖ ^ 4 ≤ (1 + κ * ‖r‖ ^ 2) ^ 4 * ‖u x‖ ^ 4 := by
    filter_upwards [forcing_pointwise κ hκ u r] with x hx
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hx 4
  have hi : Integrable (fun x => ‖forcing κ u r x‖ ^ 4) volume := by
    apply (hu4.const_mul ((1 + κ * ‖r‖ ^ 2) ^ 4)).mono'
      ((Lp.aestronglyMeasurable (forcing κ u r)).norm.pow 4)
    filter_upwards [hp] with x hx
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖forcing κ u r x‖ ^ 4)] using hx
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono_ae hi (hu4.const_mul _) hp

/-- The L⁴ norm of the nonlinear ratio is at most 2‖u‖₄/Y, without any H¹
hypothesis on u. The statement uses fourth integrals to retain the L² carrier. -/
theorem ratio_fourth {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y * L)
    (hκ : 0 ≤ κ) (u : L2T L) (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y)
    (hu4 : Integrable (fun x => ‖u x‖ ^ 4) volume) :
    Integrable (fun x => ‖ratioL2 hY hlog hκ u hsmall x‖ ^ 4) volume ∧
      (∫ x, ‖ratioL2 hY hlog hκ u hsmall x‖ ^ 4) ≤
        (2 / Y) ^ 4 * ∫ x, ‖u x‖ ^ 4 := by
  let r := ratio hY hlog hκ u hsmall
  obtain ⟨hf, hfb⟩ := forcing_fourth κ hκ u r hu4
  obtain ⟨hi, hib⟩ := resolvent_fourth hY (forcing κ u r) hf
  refine ⟨hi, ?_⟩
  calc
    _ ≤ (1 / Y) ^ 4 * ((1 + κ * ‖r‖ ^ 2) ^ 4 * ∫ x, ‖u x‖ ^ 4) :=
      hib.trans (mul_le_mul_of_nonneg_left hfb (by positivity))
    _ ≤ (2 / Y) ^ 4 * ∫ x, ‖u x‖ ^ 4 := by
      have hs := ratio_small hY hlog hκ u hsmall
      have hc : (1 + κ * ‖r‖ ^ 2) ^ 4 ≤ 2 ^ 4 :=
        pow_le_pow_left₀ (by positivity) (by change 1 + κ * ‖ratio hY hlog hκ u hsmall‖ ^ 2 ≤ 2; linarith) 4
      have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ (1 / Y) ^ 4 by positivity)
      have hU : 0 ≤ ∫ x : AddCircle L, ‖u x‖ ^ 4 := integral_nonneg (fun x => by positivity)
      have hh := mul_le_mul_of_nonneg_right hm hU
      convert hh using 1 <;> ring

theorem ratioInf_fourth {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y * L)
    (hκ : 0 ≤ κ) (u : L2T L) (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y)
    (hu4 : Integrable (fun x => ‖u x‖ ^ 4) volume) :
    Integrable (fun x => ‖ratio hY hlog hκ u hsmall x‖ ^ 4) volume ∧
      (∫ x, ‖ratio hY hlog hκ u hsmall x‖ ^ 4) ≤
        (2 / Y) ^ 4 * ∫ x, ‖u x‖ ^ 4 := by
  obtain ⟨hi, hb⟩ := ratio_fourth hY hlog hκ u hsmall hu4
  have he : (fun x => ‖ratioL2 hY hlog hκ u hsmall x‖ ^ 4) =ᵐ[volume]
      (fun x => ‖ratio hY hlog hκ u hsmall x‖ ^ 4) :=
    (ratioL2_ae hY hlog hκ u hsmall).fun_comp (fun z : ℂ => ‖z‖ ^ 4)
  exact ⟨hi.congr he, (integral_congr_ae he).symm.trans_le hb⟩

#print axioms forcing_pointwise
#print axioms forcing_fourth
#print axioms ratio_fourth
#print axioms ratioInf_fourth
end QuantumNLS.Reg010LowL4Ratio

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowL4Ratio." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowL4Ratio." then
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
