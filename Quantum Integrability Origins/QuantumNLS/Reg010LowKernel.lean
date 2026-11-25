import QuantumNLS.Reg010LowBasic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-! Positive low fractional kernels with a fully specified integral normalization. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.Reg010LowKernel
open QuantumNLS.RootH1PositiveSpectral

def normalization (s : ℝ) : ℝ :=
  (∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t 1) / 2

def weightedKernel (s Y x : ℝ) : ℝ := Y ^ (2*s-3) * kernel Y x

theorem normalization_pos (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    0 < normalization s := by
  exact div_pos (Real.integral_rpowIntegrand₀₁_one_pos ⟨hs, hs'⟩) (by norm_num)

theorem weightedKernel_nonneg (s Y x : ℝ) (hY : 0 ≤ Y) : 0 ≤ weightedKernel s Y x := by
  unfold weightedKernel
  exact mul_nonneg (Real.rpow_nonneg hY _) (kernel_nonneg Y x)

/-- The square substitution, pointwise on positive heights. -/
theorem square_substitution (s x Y : ℝ) (hs : 0 < s) (hs' : s < 1) (hY : 0 < Y) :
    (2 * Y ^ ((2:ℝ)-1)) * Real.rpowIntegrand₀₁ s (Y ^ (2:ℝ)) (x^2) =
      2 * weightedKernel s Y x := by
  rw [Real.rpow_two, Real.rpowIntegrand₀₁_eq_pow_div ⟨hs,hs'⟩ (sq_nonneg Y) (sq_nonneg x)]
  norm_num only [show (2:ℝ)-1=1 by norm_num, Real.rpow_one]
  have h₁ := Real.rpow_add hY (2*s-3) 2
  have h₂ := Real.rpow_add hY 1 (2*(s-1))
  rw [Real.rpow_two] at h₁
  rw [Real.rpow_one] at h₂
  have h₃ : (Y^2)^(s-1) = Y^(2*(s-1)) := by
    rw [Real.rpow_mul hY.le, Real.rpow_two]
  rw [h₃]
  have he : 2*s-3+2 = 1+2*(s-1) := by ring
  rw [he] at h₁
  have hh : Y^(2*s-3)*Y^2 = Y*Y^(2*(s-1)) := h₁.symm.trans h₂
  unfold weightedKernel kernel
  calc
    _ = 2 * (Y*Y^(2*(s-1))) * x^2 / (Y^2+x^2) := by ring
    _ = 2 * (Y^(2*s-3)*Y^2) * x^2 / (Y^2+x^2) := by rw [hh]
    _ = _ := by ring

theorem weightedKernel_integrable (s x : ℝ) (hs : 0 < s) (hs' : s < 1) :
    IntegrableOn (fun Y => weightedKernel s Y x) (Ioi 0) := by
  have hi := Real.integrableOn_rpowIntegrand₀₁_Ioi ⟨hs,hs'⟩ (sq_nonneg x)
  have h := (integrableOn_Ioi_comp_rpow_iff (fun t => Real.rpowIntegrand₀₁ s t (x^2))
    (p := 2) (by norm_num)).mpr hi
  have he : IntegrableOn (fun Y => 2 * weightedKernel s Y x) (Ioi 0) := by
    apply h.congr_fun
    · intro Y hY
      simpa only [smul_eq_mul, abs_of_pos (by norm_num : (0:ℝ)<2)] using
        square_substitution s x Y hs hs' hY
    · exact measurableSet_Ioi
  have hfinal := he.const_mul (1/2:ℝ)
  simpa only [IntegrableOn, ← mul_assoc, show (1/2:ℝ)*2=1 by norm_num, one_mul] using hfinal

/-- Positive scalar representation, including x=0, in the printed Y variable. -/
theorem scalar_identity (s x : ℝ) (hs : 0 < s) (hs' : s < 1) :
    (∫ Y in Ioi 0, weightedKernel s Y x) = normalization s * |x|^(2*s) := by
  have hchange := integral_comp_rpow_Ioi_of_pos
    (g := fun t => Real.rpowIntegrand₀₁ s t (x^2)) (p := 2) (by norm_num)
  have heq : (∫ Y in Ioi 0, 2 * weightedKernel s Y x) =
      ∫ t in Ioi 0, Real.rpowIntegrand₀₁ s t (x^2) := by
    rw [← hchange]
    exact setIntegral_congr_fun measurableSet_Ioi (fun Y hY =>
      (square_substitution s x Y hs hs' hY).symm)
  rw [integral_const_mul] at heq
  have h := Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const ⟨hs,hs'⟩ (sq_nonneg x)
  have hx : (x^2)^s = |x|^(2*s) := by
    rw [Real.rpow_mul (abs_nonneg x), Real.rpow_two, sq_abs]
  rw [hx] at h
  unfold normalization
  linarith

#print axioms normalization_pos
#print axioms weightedKernel_nonneg
#print axioms square_substitution
#print axioms weightedKernel_integrable
#print axioms scalar_identity
end QuantumNLS.Reg010LowKernel

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowKernel." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowKernel." then
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
  Lean.logInfo m!"Round46 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
