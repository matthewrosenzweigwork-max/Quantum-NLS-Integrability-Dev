import NlsGge.GK38.EigenvalueCompactnessScalarODE

/-! # S7/D2: realization of the actual clockwise phase for every unit direction

The actual first-component AE equation is integrated before normalization.
-/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

def periodicLogDerivative38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (r : ℝ) : ℂ :=
  -Complex.I * (x : ℂ) + Complex.I * e02Pot38 u r *
    (periodicState38 u x a r 1 / periodicState38 u x a r 0)

theorem periodicLogDerivative_integrable38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (ha : a ≠ 0) :
    IntervalIntegrable (periodicLogDerivative38 u x a) volume 0 2 := by
  have hi : IntervalIntegrable (fun r => e02Pot38 u r *
      (periodicState38 u x a r 1 / periodicState38 u x a r 0)) volume 0 2 :=
    (intervalIntegrable_coverRep38_two u).mul_continuousOn (periodicState_ratio_continuousOn38 u x a ha)
  change IntervalIntegrable (fun r => -Complex.I * (x : ℂ) + Complex.I * e02Pot38 u r *
    (periodicState38 u x a r 1 / periodicState38 u x a r 0)) volume 0 2
  simpa only [mul_assoc] using
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => -Complex.I * (x : ℂ)) volume 0 2).add
      (hi.const_mul Complex.I)

theorem periodicState_log_derivative38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (ha : a ≠ 0) :
    ∀ᵐ r ∂volume, r ∈ uIcc (0 : ℝ) 2 →
      HasDerivAt (fun s => periodicState38 u x a s 0)
        (periodicLogDerivative38 u x a r * periodicState38 u x a r 0) r := by
  filter_upwards [actualPhysicalFloquetState_ae_hasDerivAt33 u (x : ℂ) (realInitial38 a) 0] with r hr
  intro hmem
  have hn := periodicState_first_ne_zero38 u x a ha r
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using hmem)
  have he : periodicLogDerivative38 u x a r * periodicState38 u x a r 0 =
      (zsCoefficientComplex (e02Pot38 u) (x : ℂ) r).mulVec (periodicState38 u x a r) 0 := by
    simp only [periodicLogDerivative38, zsCoefficientComplex, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
  rw [he]
  exact hr hmem

theorem periodicState_first_exp38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (ha : ‖a‖ = 1) (t : Time38) :
    periodicState38 u x a t 0 = a * Complex.exp (∫ r in (0 : ℝ)..(t : ℝ), periodicLogDerivative38 u x a r) := by
  have h := ac_scalar_integrating_factor38 (fun r => periodicState38 u x a r 0) (periodicLogDerivative38 u x a)
    (actualPhysicalFloquetState_AC33 u (x : ℂ) (realInitial38 a) 0)
    (periodicLogDerivative_integrable38 u x a (unit_direction_ne_zero38 a ha))
    (periodicState_log_derivative38 u x a (unit_direction_ne_zero38 a ha)) t
    (by rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]; exact ⟨t.2.1, t.2.2.trans (by norm_num)⟩)
  simpa only [periodicState38, actualPhysicalFloquetState_initial33, realInitial38, Matrix.cons_val_zero] using h

theorem normalizedFirst_exp38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (ha : ‖a‖ = 1) (t : Time38) :
    normalizedFirst38 u x a t = Complex.exp (∫ r in (0 : ℝ)..(t : ℝ), periodicLogDerivative38 u x a r) := by
  rw [normalizedFirst_eq_state38, periodicState_first_exp38 u x a ha t]
  field_simp [unit_direction_ne_zero38 a ha]

theorem periodicLogPrimitive_im38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (ha : ‖a‖ = 1) (t : Time38) :
    (∫ r in (0 : ℝ)..(t : ℝ), periodicLogDerivative38 u x a r).im = -periodicPhase38 u x a t := by
  have hq := (periodicLogDerivative_integrable38 u x a (unit_direction_ne_zero38 a ha)).mono_set
    (uIcc_subset_uIcc (left_mem_uIcc : (0 : ℝ) ∈ uIcc (0 : ℝ) 2)
      (by rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]; exact ⟨t.2.1, t.2.2.trans (by norm_num)⟩))
  have he : (fun r => (periodicLogDerivative38 u x a r).im) =
      fun r => -x + (e02Pot38 u r * (periodicState38 u x a r 1 / periodicState38 u x a r 0)).re := by
    funext r
    simp only [periodicLogDerivative38, Complex.add_im]
    rw [mul_assoc]
    simp [Complex.mul_im]
  change Complex.imCLM (∫ r in (0 : ℝ)..(t : ℝ), periodicLogDerivative38 u x a r) = _
  rw [← Complex.imCLM.intervalIntegral_comp_comm hq]
  change (∫ r in (0 : ℝ)..(t : ℝ), (periodicLogDerivative38 u x a r).im) = _
  rw [he]
  simp only [periodicState38]
  rw [intervalIntegral.integral_add (f := fun _ : ℝ => -x) intervalIntegrable_const
    (periodicPhase_intervalIntegrable38 u x a ha t), intervalIntegral.integral_const]
  simp only [periodicPhase38, smul_eq_mul, sub_zero]
  ring

theorem periodicPhase_realization38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (ha : ‖a‖ = 1) :
    ContinuousOn (periodicPhase38 u x a) (Icc 0 1) ∧ periodicPhase38 u x a 0 = 0 ∧
    ∀ t : Time38, normalizedFirst38 u x a t ≠ 0 ∧
      normalizedFirst38 u x a t / (‖normalizedFirst38 u x a t‖ : ℂ) =
        Complex.exp (-Complex.I * (periodicPhase38 u x a t : ℂ)) := by
  refine ⟨periodicPhase_continuous38 u x a ha, periodicPhase_zero38 u x a, fun t =>
    ⟨normalizedFirst_ne_zero38 u x a ha t, ?_⟩⟩
  rw [normalizedFirst_exp38 u x a ha t, complex_exp_normalized38, periodicLogPrimitive_im38 u x a ha t]
  congr 1
  push_cast
  ring

end
end NlsGge.GK38
