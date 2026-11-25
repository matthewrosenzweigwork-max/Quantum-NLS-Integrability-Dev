import QuantumNLS.HaarResolvent

/-! Scalar periodic exponential kernel used for the small L² Riccati ratio.
The value on its diagonal is immaterial to the integral. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.RootH1RatioKernel

def wrapExp (c L x t : ℝ) : ℝ :=
  if t < x then Real.exp (-c * (x-t)) else Real.exp (-c * (x+L-t))

lemma primitive_exp (c a b d : ℝ) (hc : c ≠ 0) :
    (∫ t in a..b, Real.exp (c*t+d)) =
      (Real.exp (c*b+d)-Real.exp (c*a+d))/c := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (c*t+d)/c)
      (Real.exp (c*t+d)) t := by
    convert (((hasDerivAt_id t).const_mul c).add_const d).exp.div_const c using 1 <;>
      simp [hc]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (fun t _ => hd t)
      ((by fun_prop : Continuous (fun t : ℝ => Real.exp (c*t+d))).intervalIntegrable a b)
  simpa only [div_sub_div_same] using he

lemma integral_wrapExp {c L x : ℝ} (hc : c ≠ 0) (hx : x ∈ Icc 0 L) :
    (∫ t in (0 : ℝ)..L, wrapExp c L x t) = (1-Real.exp (-c*L))/c := by
  have hleft : (fun t => wrapExp c L x t) =ᵐ[volume.restrict (uIoc 0 x)]
      (fun t => Real.exp (c*t-c*x)) := by
    apply (ae_restrict_iff' measurableSet_uIoc).2
    have hn : ∀ᵐ t : ℝ, t ≠ x := by simp [ae_iff]
    filter_upwards [hn] with t ht hm
    rw [uIoc_of_le hx.1] at hm
    rw [wrapExp, ite_eq_left (lt_of_le_of_ne hm.2 ht)]
    congr 1; ring
  have hright : (fun t => wrapExp c L x t) =ᵐ[volume.restrict (uIoc x L)]
      (fun t => Real.exp (c*t-c*(x+L))) := by
    apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [] with t hm
    rw [uIoc_of_le hx.2] at hm
    rw [wrapExp, ite_eq_right (not_lt.mpr hm.1.le)]
    congr 1; ring
  have hil : IntervalIntegrable (wrapExp c L x) volume 0 x :=
    ((by fun_prop : Continuous (fun t : ℝ => Real.exp (c*t-c*x))).intervalIntegrable 0 x).congr_ae hleft.symm
  have hir : IntervalIntegrable (wrapExp c L x) volume x L :=
    ((by fun_prop : Continuous (fun t : ℝ => Real.exp (c*t-c*(x+L)))).intervalIntegrable x L).congr_ae hright.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals hil hir,
    intervalIntegral.integral_congr_ae_restrict hleft,
    intervalIntegral.integral_congr_ae_restrict hright,
    show (∫ t in (0:ℝ)..x, Real.exp (c*t-c*x)) =
      (Real.exp (c*x-c*x)-Real.exp (c*0-c*x))/c by
        simpa only [sub_eq_add_neg] using primitive_exp c 0 x (-(c*x)) hc,
    show (∫ t in x..L, Real.exp (c*t-c*(x+L))) =
      (Real.exp (c*L-c*(x+L))-Real.exp (c*x-c*(x+L)))/c by
        simpa only [sub_eq_add_neg] using primitive_exp c x L (-(c*(x+L))) hc]
  have e1 : c*x-c*x = 0 := by ring
  have e2 : c*L-c*(x+L) = -c*x := by ring
  have e3 : c*x-c*(x+L) = -c*L := by ring
  simp only [e1, e2, e3, mul_zero, zero_sub, Real.exp_zero]
  ring

lemma wrapExp_sq (c L x t : ℝ) : wrapExp c L x t ^ 2 = wrapExp (2*c) L x t := by
  unfold wrapExp
  split_ifs <;> rw [pow_two, ← Real.exp_add] <;> congr 1 <;> ring

lemma log_three_bound {c L : ℝ} (hc : 0 < c) (_hL : 0 < L)
    (h : Real.log 3 ≤ c*L) :
    (1+Real.exp (-c*L))/(2*c*(1-Real.exp (-c*L))) ≤ 1/c := by
  have he : Real.exp (-c*L) ≤ 1/3 := by
    have hh := Real.exp_le_exp.mpr (neg_le_neg h)
    simpa [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<3)] using hh
  have hp : 0 < 1-Real.exp (-c*L) := by linarith
  rw [div_le_div_iff₀ (by positivity : 0 < 2*c*(1-Real.exp (-c*L))) hc]
  nlinarith

def normalized (c L x t : ℝ) : ℝ := wrapExp c L x t / (1-Real.exp (-c*L))

lemma normalized_nonneg {c L x t : ℝ} (hc : 0 < c) (hL : 0 < L) :
    0 ≤ normalized c L x t := by
  have hq : Real.exp (-c*L) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  unfold normalized wrapExp
  split_ifs <;> positivity

lemma integral_normalized {c L x : ℝ} (hc : 0 < c) (hL : 0 < L)
    (hx : x ∈ Icc 0 L) :
    (∫ t in (0:ℝ)..L, normalized c L x t) = 1/c := by
  have hq : Real.exp (-c*L) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  simp only [normalized, intervalIntegral.integral_div,
    integral_wrapExp hc.ne' hx]
  have hd : 1-Real.exp (-c*L) ≠ 0 := (sub_pos.mpr hq).ne'
  simp only [neg_mul] at hd ⊢
  field_simp [hc.ne', hd]

lemma integral_normalized_sq {c L x : ℝ} (hc : 0 < c) (hL : 0 < L)
    (hx : x ∈ Icc 0 L) :
    (∫ t in (0:ℝ)..L, normalized c L x t ^ 2) =
      (1+Real.exp (-c*L))/(2*c*(1-Real.exp (-c*L))) := by
  have hq : Real.exp (-c*L) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have he : Real.exp (-(2*c)*L) = Real.exp (-c*L)^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1; ring
  simp only [normalized, div_pow, wrapExp_sq,
    intervalIntegral.integral_div, integral_wrapExp (by positivity : 2*c ≠ 0) hx, he]
  have hd : 1-Real.exp (-c*L) ≠ 0 := (sub_pos.mpr hq).ne'
  simp only [neg_mul] at hd ⊢
  field_simp [hc.ne', hd]; ring

lemma norm_Rk {c L x t : ℝ} (hc : 0 < c) (hL : 0 < L) (ht : t ≠ x) :
    ‖QuantumNLS.HaarKernelFactorization.Rk (Real.exp (-c*L)) ((c:ℂ)*Complex.I) x t‖ =
      normalized c L x t := by
  have hq : Real.exp (-c*L) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hd : ‖(1:ℂ)-(Real.exp (-c*L):ℂ)‖ = 1-Real.exp (-c*L) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hn : ‖Complex.exp (Complex.I * ((c:ℂ)*Complex.I) * ((x-t:ℝ):ℂ))‖ =
      Real.exp (-c*(x-t)) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  unfold QuantumNLS.HaarKernelFactorization.Rk normalized wrapExp
  rcases lt_or_gt_of_ne ht with h | h
  · simp only [ite_eq_left h, norm_div, hd, hn, mul_one]
  · simp only [ite_eq_right (not_lt.mpr h.le), ite_eq_left h,
      norm_mul, norm_div, hd, hn, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    congr 2; ring

lemma integral_norm_Rk_sq {c L x : ℝ} (hc : 0 < c) (hL : 0 < L)
    (hx : x ∈ Icc 0 L) :
    (∫ t in (0:ℝ)..L,
      ‖QuantumNLS.HaarKernelFactorization.Rk (Real.exp (-c*L)) ((c:ℂ)*Complex.I) x t‖^2) =
      (1+Real.exp (-c*L))/(2*c*(1-Real.exp (-c*L))) := by
  rw [← integral_normalized_sq hc hL hx]
  apply intervalIntegral.integral_congr_ae
  have hn : ∀ᵐ t : ℝ, t ≠ x := by simp [ae_iff]
  filter_upwards [hn] with t ht _
  rw [norm_Rk hc hL ht]

#print axioms primitive_exp
#print axioms integral_wrapExp
#print axioms wrapExp_sq
#print axioms log_three_bound
#print axioms normalized_nonneg
#print axioms integral_normalized
#print axioms integral_normalized_sq
#print axioms norm_Rk
#print axioms integral_norm_Rk_sq
end QuantumNLS.RootH1RatioKernel

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1RatioKernel." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1RatioKernel." then
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
