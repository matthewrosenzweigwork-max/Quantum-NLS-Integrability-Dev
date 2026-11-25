import QuantumNLS.RootBracketDilationR8
import QuantumNLS.RootGBoundaryBracket
import QuantumNLS.RootMassScaling
import QuantumNLS.DEF014PhaseAnalytic

/-! Full Hilbert Cauchy-transform involution on the actual mass-dependent
closed high half-plane. The dilation is fixed in a full neighborhood of
its base input; no differentiation on the sphere is substituted for a
full differential. Spectral continuation to the mass contours remains
an obligation of R-507DD869. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Topology MeasureTheory ComplexConjugate
attribute [local instance] InnerProductSpace.complexToReal
namespace QuantumNLS.RootCauchyFullBracketR8
open PhysicalTensor (L2T)
open SymplecticBracket RootBracketDilationR8
variable {L κ : ℝ} [Fact (0 < L)]

def G (hκ : 0 < κ) (z : ℂ) : L2T L → ℂ :=
  fun u => EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ u) z

theorem G_dilate (hκ : 0 < κ) {r : ℝ} (hr : 0 < r) (z : ℂ) (u : L2T L) :
    G hκ z (r • u) = ((r^2 : ℝ) : ℂ) * G (mul_pos hκ (sq_pos_of_pos hr)) z u := by
  have hc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hn : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
  have hs : r • u = (r : ℂ) • u := RCLike.real_smul_eq_coe_smul (K := ℂ) r u
  have hm := RootMassScaling.measure_smul hκ (r : ℂ) hc u
  have hm' : PhysicalQuantumMeasure.measure hκ (r • u) = ENNReal.ofReal (r^2) •
      PhysicalQuantumMeasure.measure (mul_pos hκ (sq_pos_of_pos hr)) u := by
    simpa only [← hs, hn] using hm
  unfold G
  rw [hm', RootMassScaling.cauchy_smul_emp, ENNReal.toReal_ofReal (sq_nonneg r), Complex.real_smul]

theorem G_even (hκ : 0 < κ) (z : ℂ) (u : L2T L) : G hκ z (-u) = G hκ z u := by
  have hm : FullMass.Mmeas κ ((-1 : ℂ) • u) = FullMass.Mmeas κ u :=
    FullMass.Mmeas_phase hκ u (by simp)
  have hm' : PhysicalQuantumMeasure.measure hκ (-u) = PhysicalQuantumMeasure.measure hκ u := by
    simpa only [neg_one_smul, PhysicalL2Normalization.measure_eq_Mmeas] using hm
  exact congrArg (fun μ => EmpiricalRapidity.cauchyTransform μ z) hm'

/-- Both complex brackets, including the conjugate, vanish at vacuum.
The proof uses actual differentiability and evenness, not a totalized
missing derivative. -/
theorem G_bracket_vacuum (hκ : 0 < κ) (z w : ℂ) (hz : 0 < z.im) (_hw : 0 < w.im) :
    pbC (G hκ z) (G hκ w) (0 : L2T L) = 0 ∧
    pbC (G hκ z) (fun v => conj (G hκ w v)) (0 : L2T L) = 0 := by
  have hd := (DEF014PhaseAnalytic.analyticAt_cauchy_upper hκ (0 : L2T L) hz).differentiableAt
  have hre := even_fderiv_zero (fun v => (G hκ z v).re)
    (RootGBracket.diff_re_im hd.hasFDerivAt).1 (fun v => congrArg Complex.re (G_even hκ z v))
  have him := even_fderiv_zero (fun v => (G hκ z v).im)
    (RootGBracket.diff_re_im hd.hasFDerivAt).2 (fun v => congrArg Complex.im (G_even hκ z v))
  constructor <;> apply Complex.ext <;> simp [pbC, pbR, hre, him]

/-- Extension of the accepted closed-domain unit bracket to the full
physical Hilbert space at its natural mass-dependent height. -/
theorem G_full_high_bracket_zero (hκ : 0 < κ) (z w : ℂ) (u : L2T L)
    (hz4 : 4 * (κ * ‖u‖^2) ≤ z.im) (hzL : Real.log 16 ≤ L * z.im)
    (hw4 : 4 * (κ * ‖u‖^2) ≤ w.im) (hwL : Real.log 16 ≤ L * w.im) :
    pbC (G hκ z) (G hκ w) u = 0 ∧
    pbC (G hκ z) (fun v => conj (G hκ w v)) u = 0 := by
  have hlog : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have hL : 0 < L := Fact.out
  have hz : 0 < z.im := by nlinarith
  have hw : 0 < w.im := by nlinarith
  by_cases hu : u = 0
  · subst u
    exact G_bracket_vacuum hκ z w hz hw
  let r : ℝ := ‖u‖
  have hr : 0 < r := norm_pos_iff.mpr hu
  let v : L2T L := r⁻¹ • u
  have hv : ‖v‖ = 1 := by
    change ‖r⁻¹ • u‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    change r⁻¹ * r = 1
    exact inv_mul_cancel₀ hr.ne' 
  have hrv : r • v = u := by simp [v, smul_smul, hr.ne']
  let heff : 0 < κ * r^2 := mul_pos hκ (sq_pos_of_pos hr)
  have hunit : pbC (G heff z) (G heff w) v = 0 ∧
      pbC (G heff z) (fun x => conj (G heff w x)) v = 0 := by
    delta G
    simpa only [PhysicalL2Normalization.measure_eq_Mmeas,
      CauchyUniqueness.cauchyTransform, EmpiricalRapidity.cauchyTransform] using
      RootGBoundaryBracket.G_pbC_zero_closed L (κ*r^2) heff z w hz4 hzL hw4 hwL v hv
  have hzκ : DifferentiableAt ℝ (G hκ z) (r • v) :=
    (DEF014PhaseAnalytic.analyticAt_cauchy_upper hκ (r • v) hz).differentiableAt
  have hwκ : DifferentiableAt ℝ (G hκ w) (r • v) :=
    (DEF014PhaseAnalytic.analyticAt_cauchy_upper hκ (r • v) hw).differentiableAt
  have hzEff := RootGBracket.diff_re_im
    (DEF014PhaseAnalytic.analyticAt_cauchy_upper heff v hz).differentiableAt.hasFDerivAt
  have hwEff := RootGBracket.diff_re_im
    (DEF014PhaseAnalytic.analyticAt_cauchy_upper heff v hw).differentiableAt.hasFDerivAt
  have hnon : ((r^2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero _ hr.ne')
  constructor
  · have hzero : pbC (fun x => G hκ z (r • x)) (fun x => G hκ w (r • x)) v = 0 := by
      calc
        _ = pbC (fun x => ((r^2 : ℝ) : ℂ)*G heff z x)
            (fun x => ((r^2 : ℝ) : ℂ)*G heff w x) v :=
          congrArg₂ (fun A B : L2T L → ℂ => pbC A B v)
            (funext fun x => G_dilate hκ hr z x) (funext fun x => G_dilate hκ hr w x)
        _ = ((r^2 * r^2 : ℝ) : ℂ) * pbC (G heff z) (G heff w) v :=
          RootBracketScalars.pbC_real_scalar (r^2) (r^2) _ _ v hzEff.1 hzEff.2 hwEff.1 hwEff.2
        _ = 0 := by rw [hunit.1, mul_zero]
    have hdil := pbC_dilate (G hκ z) (G hκ w) r v hzκ hwκ
    have hh := (mul_eq_zero.mp (hdil.symm.trans hzero)).resolve_left hnon
    exact (congrArg (fun x : L2T L => pbC (G hκ z) (G hκ w) x) hrv).symm.trans hh
  · have hwc := (RootGBracket.hasFDerivAt_conj hwκ.hasFDerivAt).differentiableAt
    have hwcEff := RootGBracket.diff_re_im (RootGBracket.hasFDerivAt_conj
      (DEF014PhaseAnalytic.analyticAt_cauchy_upper heff v hw).differentiableAt.hasFDerivAt)
    have hew : (fun x : L2T L => conj (G hκ w (r • x))) =
        fun x => ((r^2 : ℝ) : ℂ)*conj (G heff w x) := by
      funext x
      rw [G_dilate hκ hr w x, map_mul, Complex.conj_ofReal]
    have hzero : pbC (fun x => G hκ z (r • x)) (fun x => conj (G hκ w (r • x))) v = 0 := by
      calc
        _ = pbC (fun x => ((r^2 : ℝ) : ℂ)*G heff z x)
            (fun x => ((r^2 : ℝ) : ℂ)*conj (G heff w x)) v :=
          congrArg₂ (fun A B : L2T L → ℂ => pbC A B v)
            (funext fun x => G_dilate hκ hr z x) hew
        _ = ((r^2 * r^2 : ℝ) : ℂ) * pbC (G heff z) (fun x => conj (G heff w x)) v :=
          RootBracketScalars.pbC_real_scalar (r^2) (r^2) _ _ v hzEff.1 hzEff.2 hwcEff.1 hwcEff.2
        _ = 0 := by rw [hunit.2, mul_zero]
    have hdil := pbC_dilate (G hκ z) (fun x => conj (G hκ w x)) r v hzκ hwc
    have hh := (mul_eq_zero.mp (hdil.symm.trans hzero)).resolve_left hnon
    exact (congrArg (fun x : L2T L => pbC (G hκ z) (fun y => conj (G hκ w y)) x) hrv).symm.trans hh

end QuantumNLS.RootCauchyFullBracketR8
#print axioms QuantumNLS.RootCauchyFullBracketR8.G_full_high_bracket_zero

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootCauchyFullBracketR8." ||
        n.toString.startsWith "_private.QuantumNLS.RootCauchyFullBracketR8." then
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
  Lean.logInfo m!"RootCauchyFullBracketR8 audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
