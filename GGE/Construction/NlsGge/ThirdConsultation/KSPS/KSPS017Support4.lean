import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Support10

                                                                                                                    
                                                                                                  
                                                                                                             
                                                                                                          
                                         
                                                                                                                      
                                                                                                                   
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators Topology Interval

namespace NlsGge.ThirdConsultation.KSPS017W
noncomputable section
open NlsGge.Pilot NlsGge.GK38

theorem hasDerivAt_endpointOsc {H : ℝ → ℂ} (hH : IntervalIntegrable H volume 0 1) (μ0 : ℂ) :
    HasDerivAt (fun μ : ℂ => KSPSWKB.endpointOsc μ H)
      (KSPSWKB.endpointOsc μ0 (fun t => Complex.I * ((1 - 2 * t : ℝ) : ℂ) * H t)) μ0 := by
  unfold KSPSWKB.endpointOsc
  have hHm : AEStronglyMeasurable H (volume.restrict (Ι (0 : ℝ) 1)) := hH.def'.aestronglyMeasurable
  have hc : ∀ μ : ℂ, Continuous (fun t : ℝ => Complex.exp (Complex.I * μ * ((1 - 2 * t : ℝ) : ℂ))) :=
    fun μ => by fun_prop
  have hb : ∀ t ∈ Ι (0 : ℝ) 1, ∀ x ∈ Metric.ball μ0 1,
      ‖Complex.exp (Complex.I * x * ((1 - 2 * t : ℝ) : ℂ)) * (Complex.I * ((1 - 2 * t : ℝ) : ℂ) * H t)‖ ≤
        Real.exp (|μ0.im| + 1) * ‖H t‖ := by
    intro t ht x hx
    rw [uIoc_of_le zero_le_one] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have him : |x.im| ≤ |μ0.im| + 1 := by
      have h1 : |x.im - μ0.im| ≤ ‖x - μ0‖ := by
        rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
      have h2 : ‖x - μ0‖ < 1 := by rw [← dist_eq_norm]; exact hx
      have h3 := abs_sub_abs_le_abs_sub x.im μ0.im
      linarith
    have he := KSPSWKB.norm_exp_osc_le him ht'
    have h12 : ‖Complex.I * ((1 - 2 * t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [ht'.1, ht'.2]
    rw [norm_mul, norm_mul]
    calc ‖Complex.exp (Complex.I * x * ((1 - 2 * t : ℝ) : ℂ))‖ * (‖Complex.I * ((1 - 2 * t : ℝ) : ℂ)‖ * ‖H t‖)
        ≤ Real.exp (|μ0.im| + 1) * (1 * ‖H t‖) := by gcongr
      _ = Real.exp (|μ0.im| + 1) * ‖H t‖ := by ring
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun μ t => Complex.exp (Complex.I * μ * ((1 - 2 * t : ℝ) : ℂ)) * H t)
    (F' := fun μ t => Complex.exp (Complex.I * μ * ((1 - 2 * t : ℝ) : ℂ)) *
      (Complex.I * ((1 - 2 * t : ℝ) : ℂ) * H t))
    (x₀ := μ0) (s := Metric.ball μ0 1) (bound := fun t => Real.exp (|μ0.im| + 1) * ‖H t‖)
    (Metric.ball_mem_nhds μ0 one_pos)
    (Eventually.of_forall (fun μ => (hc μ).aestronglyMeasurable.mul hHm))
    (hH.continuousOn_mul (hc μ0).continuousOn)
    ((hc μ0).aestronglyMeasurable.mul ((by fun_prop : Continuous (fun t : ℝ =>
      Complex.I * ((1 - 2 * t : ℝ) : ℂ))).aestronglyMeasurable.mul hHm))
    (Eventually.of_forall (fun t ht x hx => hb t ht x hx))
    (hH.norm.const_mul _)
    (Eventually.of_forall (fun t _ x _ => by
      have hd : HasDerivAt (fun y : ℂ => Complex.I * y * ((1 - 2 * t : ℝ) : ℂ))
          (Complex.I * 1 * ((1 - 2 * t : ℝ) : ℂ)) x :=
        ((hasDerivAt_id x).const_mul Complex.I).mul_const _
      refine (hd.cexp.mul_const (H t)).congr_deriv ?_
      ring))
  exact h.2

theorem norm_deriv_le_of_sphere {f : ℂ → ℂ} {c : ℂ} {r M : ℝ} (hr : 0 < r)
    (hf : ∀ z ∈ Metric.closedBall c r, DifferentiableAt ℂ f z)
    (hM : ∀ z ∈ Metric.sphere c r, ‖f z‖ ≤ M) : ‖deriv f c‖ ≤ M / r := by
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr ?_ hM
  refine DifferentiableOn.diffContOnCl ?_
  rw [closure_ball c hr.ne']
  exact fun z hz => (hf z hz).differentiableWithinAt

end
end NlsGge.ThirdConsultation.KSPS017W
