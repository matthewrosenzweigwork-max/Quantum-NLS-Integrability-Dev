import QuantumNLS.ActionTorus
import QuantumNLS.Ext025BIntegration

/-! LOCAL-017: the literal bounded-angle rotation and path velocity on ℓ².
This proves the fixed-vector parameter regularity from summable coordinate
tails. The construction of the nonlinear source beta and its common Taylor
bounds, and the angular primitive identity, are separate open clauses. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter Topology
open scoped ENNReal
namespace QuantumNLS.Ext025B7LocalPath
open ResetNormalizationUniqueness ActionTorus
abbrev H := S2 ℤ
abbrev AngleBox := ℤ → Set.Icc (-Real.pi) Real.pi
abbrev PathParameter := AngleBox × Set.Icc (0 : ℝ) 1

def rotationAngles (p : PathParameter) : ℤ → Circle :=
  fun n => Circle.exp (p.2.val * (p.1 n).val)

theorem rotationAngles_continuous : Continuous rotationAngles := by
  apply continuous_pi
  intro n
  exact Circle.exp.continuous.comp
    ((continuous_subtype_val.comp continuous_snd).mul
      (continuous_subtype_val.comp ((continuous_apply n).comp continuous_fst)))

/-- Exactly R_(t theta) z from the local scalar path formula. -/
def rotation (p : PathParameter) (z : H) : H := rotate (rotationAngles p) z

theorem rotation_continuous : Continuous (fun p : PathParameter × H => rotation p.1 p.2) :=
  continuous_rotate.comp ((rotationAngles_continuous.comp continuous_fst).prodMk continuous_snd)

theorem rotation_norm (p : PathParameter) (z : H) : ‖rotation p z‖ = ‖z‖ := by
  apply norm_eq_of_norm_apply_eq
  intro n
  simp only [rotation,rotate_apply,norm_mul,Circle.norm_coe,one_mul]

theorem angle_bound (θ : AngleBox) (n : ℤ) : |(θ n).val| ≤ Real.pi :=
  abs_le.mpr (θ n).property

/-- The path derivative i Theta, constructed as a bounded operator. -/
def velocityLinear (θ : AngleBox) : H →ₗ[ℂ] H where
  toFun z := ⟨fun n => Complex.I * ((θ n).val : ℂ) * z n, by
    apply ((Real.pi : ℂ) • z).property.mono'
    intro n
    simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      lp.coeFn_smul,Pi.smul_apply,norm_smul,abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_right (angle_bound θ n) (norm_nonneg _)⟩
  map_add' z w := by
    ext n
    change Complex.I*((θ n).val : ℂ)*(z n+w n) =
      Complex.I*((θ n).val : ℂ)*z n+Complex.I*((θ n).val : ℂ)*w n
    ring
  map_smul' c z := by
    ext n
    change Complex.I*((θ n).val : ℂ)*(c*z n) = c*(Complex.I*((θ n).val : ℂ)*z n)
    ring

theorem velocity_bound (θ : AngleBox) (z : H) :
    ‖velocityLinear θ z‖ ≤ Real.pi * ‖z‖ := by
  calc
    ‖velocityLinear θ z‖ ≤ ‖(Real.pi : ℂ) • z‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      change ‖Complex.I * ((θ n).val : ℂ) * z n‖ ≤ ‖(Real.pi : ℂ) • z n‖
      simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,norm_smul,
        abs_of_pos Real.pi_pos]
      exact mul_le_mul_of_nonneg_right (angle_bound θ n) (norm_nonneg _)
    _ = _ := by
      rw [norm_smul]
      simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]

def velocity (θ : AngleBox) : H →L[ℂ] H :=
  (velocityLinear θ).mkContinuous Real.pi (velocity_bound θ)

theorem velocity_norm_le (θ : AngleBox) (z : H) :
    ‖velocity θ z‖ ≤ Real.pi*‖z‖ := velocity_bound θ z

theorem velocity_apply (θ : AngleBox) (z : H) (n : ℤ) :
    velocity θ z n = Complex.I * ((θ n).val : ℂ) * z n := rfl

/-- Fixed-vector continuity in all angle coordinates follows from the actual
summable ℓ² tail, rather than from operator-norm continuity of Theta. -/
theorem velocity_fixed_continuous (z : H) : Continuous (fun θ : AngleBox => velocity θ z) := by
  apply continuous_iff_continuousAt.mpr
  intro θ₀
  apply continuousAt_of_tail (fun θ => velocity θ z) θ₀
    (fun n => (2*Real.pi)^2 * ‖z n‖^2) ((summable_sq z).mul_left _)
  · intro θ n
    simp only [velocity_apply]
    have hnorm : ‖Complex.I * ((θ n).val : ℂ) * z n -
        Complex.I * ((θ₀ n).val : ℂ) * z n‖ ≤ 2*Real.pi*‖z n‖ := by
      calc
        _ ≤ ‖Complex.I * ((θ n).val : ℂ) * z n‖ +
          ‖Complex.I * ((θ₀ n).val : ℂ) * z n‖ := norm_sub_le _ _
        _ = (|(θ n).val|+|(θ₀ n).val|)*‖z n‖ := by
          simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [angle_bound θ n,angle_bound θ₀ n]) (norm_nonneg _)
    have hh := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    simpa only [mul_pow] using hh
  · intro n
    change ContinuousAt (fun θ : AngleBox => Complex.I*((θ n).val : ℂ)*z n) θ₀
    exact (((continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp (continuous_apply n)))).mul continuous_const)).continuousAt

theorem velocity_continuous : Continuous (fun p : AngleBox × H => velocity p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨θ₀,z₀⟩
  have hfixed := ((velocity_fixed_continuous z₀).tendsto θ₀).comp
    (continuous_fst.tendsto (θ₀,z₀))
  have hsmall : Tendsto (fun p : AngleBox × H => velocity p.1 (p.2-z₀))
      (𝓝 (θ₀,z₀)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : ∀ p : AngleBox × H, ‖velocity p.1 (p.2-z₀)‖ ≤ Real.pi*‖p.2-z₀‖ :=
      fun p => velocity_norm_le p.1 (p.2-z₀)
    have hz : Tendsto (fun p : AngleBox × H => Real.pi*‖p.2-z₀‖) (𝓝 (θ₀,z₀)) (𝓝 0) := by
      simpa only [sub_self,norm_zero,mul_zero] using
        (((continuous_snd.tendsto (θ₀,z₀)).sub_const z₀).norm.const_mul Real.pi)
    exact squeeze_zero (fun _ => norm_nonneg _) hb hz
  have h := hfixed.add hsmall
  change Tendsto (fun p : AngleBox × H => velocity p.1 p.2) (𝓝 (θ₀,z₀)) (𝓝 (velocity θ₀ z₀))
  simpa [Function.comp_def] using h

/-- The scalar integrand in the source formula, with its displayed sign
applied only when forming the outer primitive. -/
def pathIntegrand (β : H → H →L[ℝ] ℝ) (z : H) (p : PathParameter) : ℝ :=
  β (rotation p z) (velocity p.1 (rotation p z))

/-- Parameter continuity of the literal path expression for every continuous
covector field. Source construction/analyticity of beta is not assumed here. -/
theorem pathIntegrand_continuous (β : H → H →L[ℝ] ℝ) (hβ : Continuous β) (z : H) :
    Continuous (pathIntegrand β z) := by
  have hrot : Continuous (fun p : PathParameter => rotation p z) :=
    rotation_continuous.comp (continuous_id.prodMk continuous_const)
  exact (hβ.comp hrot).clm_apply
    (velocity_continuous.comp (continuous_fst.prodMk hrot))

/-- Every fixed-vector path evaluation is Borel measurable on the full
compact angle cube times [0,1]. -/
theorem pathIntegrand_measurable (β : H → H →L[ℝ] ℝ) (hβ : Continuous β) (z : H) :
    Measurable (pathIntegrand β z) := (pathIntegrand_continuous β hβ z).measurable

theorem pathIntegrand_integrable (μ : Measure PathParameter) [IsFiniteMeasure μ]
    (β : H → H →L[ℝ] ℝ) (hβ : Continuous β) (z : H) :
    Integrable (pathIntegrand β z) μ := by
  simpa using (pathIntegrand_continuous β hβ z).continuousOn.integrableOn_compact
    (μ := μ) isCompact_univ

end QuantumNLS.Ext025B7LocalPath

#print axioms QuantumNLS.Ext025B7LocalPath.H
#print axioms QuantumNLS.Ext025B7LocalPath.AngleBox
#print axioms QuantumNLS.Ext025B7LocalPath.PathParameter
#print axioms QuantumNLS.Ext025B7LocalPath.rotationAngles
#print axioms QuantumNLS.Ext025B7LocalPath.rotationAngles_continuous
#print axioms QuantumNLS.Ext025B7LocalPath.rotation
#print axioms QuantumNLS.Ext025B7LocalPath.rotation_continuous
#print axioms QuantumNLS.Ext025B7LocalPath.rotation_norm
#print axioms QuantumNLS.Ext025B7LocalPath.angle_bound
#print axioms QuantumNLS.Ext025B7LocalPath.velocityLinear
#print axioms QuantumNLS.Ext025B7LocalPath.velocity_bound
#print axioms QuantumNLS.Ext025B7LocalPath.velocity
#print axioms QuantumNLS.Ext025B7LocalPath.velocity_norm_le
#print axioms QuantumNLS.Ext025B7LocalPath.velocity_apply
#print axioms QuantumNLS.Ext025B7LocalPath.velocity_fixed_continuous
#print axioms QuantumNLS.Ext025B7LocalPath.velocity_continuous
#print axioms QuantumNLS.Ext025B7LocalPath.pathIntegrand
#print axioms QuantumNLS.Ext025B7LocalPath.pathIntegrand_continuous
#print axioms QuantumNLS.Ext025B7LocalPath.pathIntegrand_measurable
#print axioms QuantumNLS.Ext025B7LocalPath.pathIntegrand_integrable

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B7LocalPath." then
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
  Lean.logInfo m!"Ext025B7LocalPath audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
