import QuantumNLS.Reg010LowL4Pairing
import QuantumNLS.Reg010LowL4Ratio

/-! The printed constant-in-height L⁴ estimate on the actual correction. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace QuantumNLS.Reg010LowL4Error
open QuantumNLS.PhysicalTensor QuantumNLS.RootH1RatioOperator
open QuantumNLS.RootH1RatioBounds QuantumNLS.RootH1RatioNonlinear
open QuantumNLS.RootH1RatioConvergence QuantumNLS.RootH1RatioL2
open QuantumNLS.Reg010LowBasic QuantumNLS.Reg010LowRiccati
open QuantumNLS.Reg010LowL4Pairing QuantumNLS.Reg010LowL4Ratio
open QuantumNLS.BetheIntegralOperator QuantumNLS.HaarResolvent
open QuantumNLS.HaarKernelFactorization

variable {L : ℝ} [hLf : Fact (0 < L)]

theorem resolvent_kernel_schur {Y : ℝ} (hY : 0 < Y) :
    (∀ x, (∫ t : AddCircle L, ‖(R1ker L (Real.exp (-Y * L)) ((Y : ℂ) * Complex.I)).fn (x,t)‖) ≤ 1 / Y) ∧
    (∀ t, (∫ x : AddCircle L, ‖(R1ker L (Real.exp (-Y * L)) ((Y : ℂ) * Complex.I)).fn (x,t)‖) ≤ 1 / Y) := by
  constructor
  · intro x
    change (∫ t : AddCircle L, ‖Rk _ _ (rep1 L x) (rep1 L t)‖) ≤ _
    rw [integral_rep (fun t => ‖Rk (Real.exp (-Y * L)) ((Y : ℂ) * Complex.I) (rep1 L x) t‖)]
    exact (norm_kernel_row hY ⟨(rep1_bounds L x).1, (rep1_bounds L x).2.le⟩).le
  · intro t
    change (∫ x : AddCircle L, ‖Rk _ _ (rep1 L x) (rep1 L t)‖) ≤ _
    rw [integral_rep (fun x => ‖Rk (Real.exp (-Y * L)) ((Y : ℂ) * Complex.I) x (rep1 L t)‖)]
    exact (norm_kernel_col hY ⟨(rep1_bounds L t).1, (rep1_bounds L t).2.le⟩).le

/-- The printed Riccati cubic identity; the adjoint can equivalently be moved
to the first argument of this pairing. -/
theorem correction_cubic {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y * L)
    (hκ : 0 < κ) (u : L2T L) (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y) :
    correction κ hκ u Y = κ * Y ^ 3 *
      (inner ℂ u (RootH1RatioOperator.resolvent Y (cubic u (ratio hY hlog hκ.le u hsmall)))).re := by
  have he : ratioL2 hY hlog hκ.le u hsmall - RootH1RatioOperator.resolvent Y u =
      -(κ : ℂ) • RootH1RatioOperator.resolvent Y (cubic u (ratio hY hlog hκ.le u hsmall)) := by
    change RootH1RatioOperator.resolvent Y (u - (κ : ℂ) • cubic u (ratio hY hlog hκ.le u hsmall)) -
      RootH1RatioOperator.resolvent Y u = _
    rw [(RootH1RatioOperator.resolvent Y).map_sub, (RootH1RatioOperator.resolvent Y).map_smul]
    module
  rw [correction_pairing hY hlog hκ u hsmall, he, smul_smul, inner_smul_right]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
    Complex.neg_im, neg_zero, mul_zero, zero_mul, sub_zero]
  ring

theorem cubic_pairing_bound {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y * L)
    (hκ : 0 ≤ κ) (u : L2T L) (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y)
    (hu4 : Integrable (fun x => ‖u x‖ ^ 4) volume) :
    ‖inner ℂ u (RootH1RatioOperator.resolvent Y (cubic u (ratio hY hlog hκ u hsmall)))‖ ≤
      4 / Y ^ 3 * ∫ x, ‖u x‖ ^ 4 := by
  obtain ⟨hr4, hrb⟩ := ratioInf_fourth hY hlog hκ u hsmall hu4
  obtain ⟨hrow, hcol⟩ := resolvent_kernel_schur (L := L) hY
  let k := R1ker L (Real.exp (-Y * L)) ((Y : ℂ) * Complex.I)
  let r := ratio hY hlog hκ u hsmall
  have hb := cubic_form_bound k (1 / Y) hrow hcol u (cubic u r) r (coe_cubic u r)
    hu4 hr4 (Y / 2) (by positivity)
  rw [← Kernel.inner_operator] at hb
  change ‖inner ℂ u (RootH1RatioOperator.resolvent Y (cubic u r))‖ ≤ _ at hb
  calc
    _ ≤ (1 / Y) / (4 * (Y / 2) ^ 2) *
        (2 * (∫ x, ‖u x‖ ^ 4) + 2 * (Y / 2) ^ 4 * ∫ x, ‖r x‖ ^ 4) := hb
    _ ≤ (1 / Y) / (4 * (Y / 2) ^ 2) *
        (2 * (∫ x, ‖u x‖ ^ 4) + 2 * (Y / 2) ^ 4 * ((2 / Y) ^ 4 * ∫ x, ‖u x‖ ^ 4)) := by
      gcongr
    _ = _ := by field_simp; ring

/-- For every L² field with a finite L⁴ integral, the correction is bounded
by 4κ‖u‖₄⁴ for all heights above the original L² threshold. -/
theorem L4_large_bound (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (hu4 : Integrable (fun x => ‖u x‖ ^ 4) volume) {Y : ℝ}
    (hYB : threshold κ u ≤ Y) :
    |correction κ hκ u Y| ≤ 4 * κ * ∫ x, ‖u x‖ ^ 4 := by
  obtain ⟨hY, hlog, hsmall⟩ := height_spec u hYB
  rw [correction_cubic hY hlog hκ u hsmall, abs_mul,
    abs_of_nonneg (show 0 ≤ κ * Y ^ 3 by positivity)]
  have hb := cubic_pairing_bound hY hlog hκ.le u hsmall hu4
  calc
    _ ≤ κ * Y ^ 3 * (4 / Y ^ 3 * ∫ x, ‖u x‖ ^ 4) :=
      mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hb) (by positivity)
    _ = _ := by field_simp

#print axioms resolvent_kernel_schur
#print axioms correction_cubic
#print axioms cubic_pairing_bound
#print axioms L4_large_bound
end QuantumNLS.Reg010LowL4Error

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowL4Error." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowL4Error." then
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
