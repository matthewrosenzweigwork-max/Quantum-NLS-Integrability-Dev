import QuantumNLS.RootH1RatioBounds
import QuantumNLS.RootTraceSymbolUpper

/-! Exact branch comparison at YL≥log 3, with no strengthened height cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
open QuantumNLS.PhysicalTensor QuantumNLS.RootH1RatioBounds
namespace QuantumNLS.RootH1RatioPhase
variable {L : ℝ} [hLf : Fact (0 < L)]

lemma log_three_lower : (2/3:ℝ) ≤ Real.log 3 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<3)
  norm_num at h ⊢
  exact h

lemma exp_pair_unique {b : ℝ} {x y : ℂ} (hb : 1/3 ≤ b)
    (hx : ‖x‖ ≤ 5/64) (hy : ‖y‖ ≤ 1/16)
    (ht : Complex.exp ((b:ℂ)+x)+(Complex.exp ((b:ℂ)+x))⁻¹ =
      Complex.exp ((b:ℂ)+y)+(Complex.exp ((b:ℂ)+y))⁻¹) : x = y := by
  let a := Complex.exp ((b:ℂ)+x)
  let d := Complex.exp ((b:ℂ)+y)
  have ha : a ≠ 0 := Complex.exp_ne_zero _
  have hd : d ≠ 0 := Complex.exp_ne_zero _
  have hag : 1 < ‖a‖ := by
    rw [Complex.norm_exp, Real.one_lt_exp_iff]
    simp only [Complex.add_re,Complex.ofReal_re]
    have h := (abs_le.mp (Complex.abs_re_le_norm x)).1
    linarith
  have hdg : 1 < ‖d‖ := by
    rw [Complex.norm_exp, Real.one_lt_exp_iff]
    simp only [Complex.add_re,Complex.ofReal_re]
    have h := (abs_le.mp (Complex.abs_re_le_norm y)).1
    linarith
  have hpoly : (a-d)*(a*d-1) = 0 := by
    change a+a⁻¹ = d+d⁻¹ at ht
    field_simp [ha,hd] at ht
    linear_combination ht
  have had : a = d := by
    rcases mul_eq_zero.mp hpoly with he | he
    · exact sub_eq_zero.mp he
    · have hm : a*d = 1 := sub_eq_zero.mp he
      have hh := congrArg norm hm
      rw [norm_mul,norm_one] at hh
      nlinarith
  have himx := abs_le.mp ((Complex.abs_im_le_norm x).trans hx)
  have himy := abs_le.mp ((Complex.abs_im_le_norm y).trans hy)
  have hxy := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := (b:ℂ)+x) (y := (b:ℂ)+y)
    (by simp only [Complex.add_im,Complex.ofReal_im,zero_add]; linarith [Real.pi_gt_three])
    (by simp only [Complex.add_im,Complex.ofReal_im,zero_add]; linarith [Real.pi_gt_three])
    (by simp only [Complex.add_im,Complex.ofReal_im,zero_add]; linarith [Real.pi_gt_three])
    (by simp only [Complex.add_im,Complex.ofReal_im,zero_add]; linarith [Real.pi_gt_three]) had
  exact add_left_cancel hxy

lemma cauchy_bound {Y : ℝ} (hY : 0 < Y) (κ : ℝ) (u : L2T L) :
    ‖CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) ((Y:ℂ)*Complex.I)‖ ≤ ‖u‖^2/Y := by
  have hi : (((Y:ℂ)*Complex.I):ℂ).im = Y := by simp
  have h := EmpiricalRapidity.norm_cauchyTransform_le (FullMass.Mmeas κ u)
    ((Y:ℂ)*Complex.I) (by simpa using hY.ne')
  simpa only [hi,abs_of_pos hY,Measure.real,FullMass.Mmeas_univ,
    ENNReal.toReal_ofReal (sq_nonneg _),div_eq_mul_inv,
    EmpiricalRapidity.cauchyTransform,CauchyUniqueness.cauchyTransform] using h

lemma phase_trace {Y κ : ℝ} (hY : 0 < Y) (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    L2SpatialTransfer.discriminant κ u ((Y:ℂ)*Complex.I) =
      Complex.exp ((Y:ℂ)*L/2+Complex.I*(κ:ℂ)*
        CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) ((Y:ℂ)*Complex.I)) +
      (Complex.exp ((Y:ℂ)*L/2+Complex.I*(κ:ℂ)*
        CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) ((Y:ℂ)*Complex.I)))⁻¹ := by
  have ht := RootTraceSymbolUpper.upper_cosine hκ hu (z := (Y:ℂ)*Complex.I) (by simpa using hY)
  rw [PhysicalL2Normalization.measure_eq_Mmeas,Complex.two_cos] at ht
  have he : -(SpatialTransfer.boundaryPhase L κ (FullMass.Mmeas κ u) ((Y:ℂ)*Complex.I))*Complex.I =
      (Y:ℂ)*L/2+Complex.I*(κ:ℂ)*CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) ((Y:ℂ)*Complex.I) := by
    unfold SpatialTransfer.boundaryPhase EmpiricalRapidity.cauchyTransform CauchyUniqueness.cauchyTransform
    linear_combination -(L:ℂ)*(Y:ℂ)/2*Complex.I_mul_I
  rw [he,show SpatialTransfer.boundaryPhase L κ (FullMass.Mmeas κ u) ((Y:ℂ)*Complex.I)*Complex.I =
      -((Y:ℂ)*L/2+Complex.I*(κ:ℂ)*CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) ((Y:ℂ)*Complex.I)) by
        linear_combination -he,Complex.exp_neg] at ht
  exact ht.symm.trans (add_comm _ _)

#print axioms log_three_lower
#print axioms exp_pair_unique
#print axioms cauchy_bound
#print axioms phase_trace
end QuantumNLS.RootH1RatioPhase

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1RatioPhase." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1RatioPhase." then
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
