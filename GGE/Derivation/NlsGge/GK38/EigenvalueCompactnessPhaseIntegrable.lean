import NlsGge.GK38.EigenvalueCompactnessState

/-! # S7: integrability before actual clockwise phase primitives

The ratio has norm one and is continuous on the doubled interval.
-/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem periodicState_continuousOn38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (i : Fin 2) :
    ContinuousOn (fun t => periodicState38 u x a t i) (uIcc (0 : ℝ) 2) :=
  (actualPhysicalFloquetState_AC33 u (x : ℂ) (realInitial38 a) i).continuousOn

theorem periodicState_ratio_continuousOn38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (ha : a ≠ 0) :
    ContinuousOn (fun t => periodicState38 u x a t 1 / periodicState38 u x a t 0) (uIcc (0 : ℝ) 2) := by
  apply (periodicState_continuousOn38 u x a 1).div (periodicState_continuousOn38 u x a 0)
  intro t ht
  exact periodicState_first_ne_zero38 u x a ha t (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using ht)

theorem periodicPhase_integrand_integrable38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (ha : a ≠ 0) :
    IntervalIntegrable (fun r => (e02Pot38 u r *
      (periodicState38 u x a r 1 / periodicState38 u x a r 0)).re) volume 0 2 := by
  have hi : IntervalIntegrable (fun r => e02Pot38 u r *
      (periodicState38 u x a r 1 / periodicState38 u x a r 0)) volume 0 2 := by
    change IntervalIntegrable (fun r => coverRep38 u r *
      (periodicState38 u x a r 1 / periodicState38 u x a r 0)) volume 0 2
    exact (intervalIntegrable_coverRep38_two u).mul_continuousOn (periodicState_ratio_continuousOn38 u x a ha)
  exact intervalIntegrable_iff.mpr (Complex.reCLM.integrable_comp hi.def')

theorem unit_direction_ne_zero38 (a : ℂ) (ha : ‖a‖ = 1) : a ≠ 0 := by
  intro he
  rw [he, norm_zero] at ha
  norm_num at ha

theorem periodicPhase_intervalIntegrable38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (ha : ‖a‖ = 1)
    (t : Time38) : IntervalIntegrable (fun r => (e02Pot38 u r *
      (actualPhysicalFloquetState33 u (x : ℂ) (realInitial38 a) r 1 /
        actualPhysicalFloquetState33 u (x : ℂ) (realInitial38 a) r 0)).re) volume 0 (t : ℝ) := by
  exact (periodicPhase_integrand_integrable38 u x a (unit_direction_ne_zero38 a ha)).mono_set
    (uIcc_subset_uIcc (left_mem_uIcc : (0 : ℝ) ∈ uIcc (0 : ℝ) 2)
      (by rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]; exact ⟨t.2.1, t.2.2.trans (by norm_num)⟩))

theorem normalizedFirst_eq_state38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (t : Time38) :
    normalizedFirst38 u x a t = periodicState38 u x a t 0 / a := by
  rw [normalizedFirst38, fundPair_realSlice]
  rfl

theorem normalizedFirst_ne_zero38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (ha : ‖a‖ = 1) (t : Time38) :
    normalizedFirst38 u x a t ≠ 0 := by
  rw [normalizedFirst_eq_state38]
  exact div_ne_zero (periodicState_first_ne_zero38 u x a (unit_direction_ne_zero38 a ha) t
    ⟨t.2.1, t.2.2.trans (by norm_num)⟩) (unit_direction_ne_zero38 a ha)

theorem periodicPhase_continuous38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (ha : ‖a‖ = 1) :
    ContinuousOn (periodicPhase38 u x a) (Icc (0 : ℝ) 1) := by
  have hInt := periodicPhase_integrand_integrable38 u x a (unit_direction_ne_zero38 a ha)
  have hp := hInt.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc : (0 : ℝ) ∈ uIcc (0 : ℝ) 2)
  apply (show ContinuousOn (fun s : ℝ => x * s) (Icc 0 1) from (by fun_prop : Continuous _).continuousOn).sub
  exact hp.continuousOn.mono (by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro t ht; exact ⟨ht.1, ht.2.trans (by norm_num)⟩)

theorem periodicPhase_zero38 (u : PhysicalL2) (x : ℝ) (a : ℂ) : periodicPhase38 u x a 0 = 0 := by
  simp only [periodicPhase38, mul_zero, intervalIntegral.integral_same, sub_zero]

end
end NlsGge.GK38
