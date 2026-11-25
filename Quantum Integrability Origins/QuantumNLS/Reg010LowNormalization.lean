import QuantumNLS.Reg010LowKernel
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! Evaluation of the low positive kernel normalization by the beta integral. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.Reg010LowNormalization
open QuantumNLS.Reg010LowKernel

/-- The elementary fractional-linear substitution in the beta integral. -/
theorem beta_substitution (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    (∫ y in Ioo (0:ℝ) 1, y^(s-1)*(1-y)^(-s)) =
      ∫ t in Ioi (0:ℝ), t^(s-1)/(1+t) := by
  let f : ℝ → ℝ := fun t => t/(1+t)
  have hd : ∀ t ∈ Ioi (0:ℝ), HasDerivWithinAt f ((1+t)^2)⁻¹ (Ioi 0) t := by
    intro t ht
    change 0<t at ht
    have hn : 1+t ≠ 0 := by linarith
    have h := (hasDerivAt_id t).div ((hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)) hn
    convert h.hasDerivWithinAt (s := Ioi 0) using 1
    · rfl
    · dsimp
      ring
  have hinj : InjOn f (Ioi 0) := by
    intro t ht u hu he
    change 0<t at ht
    change 0<u at hu
    have hn : 1+t ≠ 0 := by linarith [ht]
    have hm : 1+u ≠ 0 := by linarith [hu]
    have h := (div_eq_div_iff hn hm).mp he
    nlinarith
  have himg : f '' Ioi (0:ℝ) = Ioo 0 1 := by
    ext y
    constructor
    · rintro ⟨t, ht,rfl⟩
      change 0<t at ht
      dsimp [f]
      constructor
      · positivity
      · apply (div_lt_one (by linarith : 0<1+t)).mpr
        linarith
    · intro hy
      refine ⟨y/(1-y), (show 0<y/(1-y) from div_pos hy.1 (sub_pos.mpr hy.2)), ?_⟩
      dsimp [f]
      have hn : 1-y ≠ 0 := by linarith [hy.2]
      field_simp
      <;> ring
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj
    (fun y : ℝ => y^(s-1)*(1-y)^(-s))
  rw [himg] at he
  rw [he]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht' : 0<t := ht
  have hb : 0<1+t := by linarith
  have hone : 1-t/(1+t) = (1+t)⁻¹ := by field_simp; ring
  simp only [f, smul_eq_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (1+t)))]
  rw [hone, Real.div_rpow ht'.le hb.le, Real.inv_rpow hb.le]
  have hr : (1+t)^(s-1) * (1+t)^(-s) = (1+t)⁻¹ := by
    rw [← Real.rpow_add hb]
    rw [show s-1+-s = (-1:ℝ) by ring, Real.rpow_neg_one]
  have h1 : (1+t)^(s-1) ≠ 0 := (Real.rpow_pos_of_pos hb _).ne'
  have h2 : (1+t)^(-s) ≠ 0 := (Real.rpow_pos_of_pos hb _).ne'
  have h3 : 1+t ≠ 0 := hb.ne'
  have hr2 : (1+t)*((1+t)^(s-1)*(1+t)^(-s)) = 1 := by
    rw [hr, mul_inv_cancel₀ h3]
  field_simp
  nlinarith [hr2]

/-- The real beta integral at complementary arguments. -/
theorem real_beta_complement (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    (∫ y in Ioo (0:ℝ) 1, y^(s-1)*(1-y)^(-s)) = Real.pi / Real.sin (Real.pi*s) := by
  have hc := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (s:ℂ)) (t := (1-s:ℝ)) (by simpa using hs) (by simpa using sub_pos.mpr hs')
  have harg : (s:ℂ) + ((1-s:ℝ):ℂ) = 1 := by push_cast; ring
  rw [harg, Complex.Gamma_one, one_mul] at hc
  have href := Complex.Gamma_mul_Gamma_one_sub (s:ℂ)
  have he : Complex.betaIntegral (s:ℂ) ((1-s:ℝ):ℂ) =
      ((∫ y in Ioo (0:ℝ) 1, y^(s-1)*(1-y)^(-s)):ℝ) := by
    unfold Complex.betaIntegral
    rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
    calc
      _ = ∫ y in Ioo (0:ℝ) 1, ((y^(s-1)*(1-y)^(-s):ℝ):ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro y hy
        have hy0 : 0≤y := hy.1.le
        have hy1 : 0≤1-y := by linarith [hy.2]
        dsimp only
        rw [Complex.ofReal_mul, Complex.ofReal_cpow hy0, Complex.ofReal_cpow hy1]
        push_cast
        congr 1 <;> congr 1 <;> ring
      _ = _ := integral_ofReal
  rw [← hc] at he
  have href' : Complex.Gamma (s:ℂ)*Complex.Gamma ((1-s:ℝ):ℂ) =
      ((Real.pi / Real.sin (Real.pi*s):ℝ):ℂ) := by
    convert href using 1 <;> push_cast <;> rfl
  rw [href'] at he
  exact_mod_cast he.symm

theorem normalization_eq (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    normalization s = Real.pi / (2 * Real.sin (Real.pi*s)) := by
  have h := (beta_substitution s hs hs').symm.trans (real_beta_complement s hs hs')
  have he : (∫ t in Ioi (0:ℝ), Real.rpowIntegrand₀₁ s t 1) =
      ∫ t in Ioi (0:ℝ), t^(s-1)/(1+t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [Real.rpowIntegrand₀₁_eq_pow_div ⟨hs,hs'⟩ ht.le (by norm_num)]
    ring
  rw [normalization, he, h]
  ring

#print axioms beta_substitution
#print axioms real_beta_complement
#print axioms normalization_eq
end QuantumNLS.Reg010LowNormalization

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowNormalization." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowNormalization." then
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
