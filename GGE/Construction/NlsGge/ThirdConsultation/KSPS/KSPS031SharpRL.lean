import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS031Analytic

                                                                         
                                                                                                          
                                                                                         
                                                                                                 
                                                                                                   
                                                                                                   
                                                                                           
                                                                                  
                                                                                                               
                                                                                                 
set_option autoImplicit false
open Filter Topology MeasureTheory Set

namespace NlsGge.ThirdConsultation.KSPS031SharpRL
noncomputable section

theorem tendsto_scale_cobounded {r : ℝ} (hr : r ≠ 0) :
    Tendsto (fun ω : ℝ => r * ω) (Bornology.cobounded ℝ) (Bornology.cobounded ℝ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  have h : (fun ω : ℝ => ‖r * ω‖) = fun ω => |r| * ‖ω‖ := by
    funext ω
    rw [norm_mul, Real.norm_eq_abs]
  rw [h]
  exact tendsto_norm_cobounded_atTop.const_mul_atTop (abs_pos.2 hr)

/-- Riemann–Lebesgue lemma on an interval. -/
theorem rl_interval (a b : ℝ) (hab : a ≤ b) (g : ℝ → ℂ) :
    Tendsto (fun ω : ℝ => ∫ t in a..b, Complex.exp (↑ω * ↑t * Complex.I) * g t)
      (Bornology.cobounded ℝ) (𝓝 0) := by
  have hRL := Real.tendsto_integral_exp_smul_cocompact (Set.indicator (Set.Ioc a b) g)
  rw [← Metric.cobounded_eq_cocompact] at hRL
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hc : (-(2 * Real.pi))⁻¹ ≠ 0 := inv_ne_zero (neg_ne_zero.2 hpi)
  have hcomp := hRL.comp (tendsto_scale_cobounded hc)
  refine Tendsto.congr (fun ω => ?_) hcomp
  simp only [Function.comp]
  rw [intervalIntegral.integral_of_le hab, ← integral_indicator measurableSet_Ioc]
  congr 1
  funext v
  by_cases hv : v ∈ Ioc a b
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, Circle.smul_def, Real.fourierChar_apply,
      smul_eq_mul]
    have e : (2 * Real.pi * -(v * ((-(2 * Real.pi))⁻¹ * ω)) : ℝ) = ω * v := by
      field_simp
    rw [e]
    push_cast
    ring_nf
  · simp [hv]

/-- The endpoint oscillatory integral tends to zero along real frequencies. -/
theorem osc_tendsto (H : ℝ → ℂ) :
    Tendsto (fun ω : ℝ => ∫ t in (0 : ℝ)..1,
        Complex.exp (Complex.I * (ω : ℂ) * ((1 - 2 * t : ℝ) : ℂ)) * H t)
      (Bornology.cobounded ℝ) (𝓝 0) := by
  have h := (rl_interval 0 1 zero_le_one H).comp (tendsto_scale_cobounded (r := -2) (by norm_num))
  have hn := h.norm
  rw [norm_zero] at hn
  refine squeeze_zero_norm (fun ω => le_of_eq ?_) hn
  simp only [Function.comp]
  have e : (∫ t in (0 : ℝ)..1, Complex.exp (Complex.I * (ω : ℂ) * ((1 - 2 * t : ℝ) : ℂ)) * H t) =
      Complex.exp ((ω : ℂ) * Complex.I) *
        ∫ t in (0 : ℝ)..1, Complex.exp (↑(-2 * ω) * ↑t * Complex.I) * H t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem norm_exp_real_I (x : ℝ) (s : ℝ) :
    ‖Complex.exp (2 * Complex.I * (x : ℂ) * (s : ℂ))‖ = 1 := by
  rw [show 2 * Complex.I * (x : ℂ) * (s : ℂ) = ((2 * x * s : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem norm_exp_neg_real_I (x : ℝ) (s : ℝ) :
    ‖Complex.exp (-(2 * Complex.I * (x : ℂ) * (s : ℂ)))‖ = 1 := by
  rw [show -(2 * Complex.I * (x : ℂ) * (s : ℂ)) = ((-(2 * x * s) : ℝ) : ℂ) * Complex.I by
      push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- The double oscillatory integral tends to zero along real frequencies (dominated convergence). -/
theorem tz_tendsto (c d : ℝ → ℂ) (hc : IntervalIntegrable c volume 0 1)
    (hd : IntervalIntegrable d volume 0 1) :
    Tendsto (fun ω : ℝ => ∫ t in (0 : ℝ)..1,
        (Complex.exp (-(2 * Complex.I * (ω : ℂ) * (t : ℂ))) * c t) *
          ∫ s in t..1, Complex.exp (2 * Complex.I * (ω : ℂ) * (s : ℂ)) * d s)
      (Bornology.cobounded ℝ) (𝓝 0) := by
  haveI : (Bornology.cobounded ℝ).IsCountablyGenerated := by
    rw [← comap_norm_atTop]
    infer_instance
  set K : ℝ := ∫ s in (0 : ℝ)..1, ‖d s‖ with hK
  have hdn : IntervalIntegrable (fun s => ‖d s‖) volume 0 1 := hd.norm
  have hinner_int : ∀ ω : ℝ, IntervalIntegrable
      (fun s : ℝ => Complex.exp (2 * Complex.I * (ω : ℂ) * (s : ℂ)) * d s) volume 0 1 := by
    intro ω
    have hcont : Continuous fun s : ℝ => Complex.exp (2 * Complex.I * (ω : ℂ) * (s : ℂ)) := by
      fun_prop
    exact hd.continuousOn_mul hcont.continuousOn
  have hG : ∀ ω : ℝ, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖∫ s in t..1, Complex.exp (2 * Complex.I * (ω : ℂ) * (s : ℂ)) * d s‖ ≤ K := by
    intro ω t ht
    have h1 : ‖∫ s in t..1, Complex.exp (2 * Complex.I * (ω : ℂ) * (s : ℂ)) * d s‖ ≤
        ∫ s in t..1, ‖d s‖ := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht.2
        (Eventually.of_forall (fun s _ => ?_)) ?_
      · rw [norm_mul, norm_exp_real_I, one_mul]
      · exact hdn.mono_set (by
          rw [uIcc_of_le ht.2, uIcc_of_le zero_le_one]
          exact Icc_subset_Icc ht.1 le_rfl)
    refine h1.trans ?_
    exact intervalIntegral.integral_mono_interval ht.1 ht.2 le_rfl
      (Eventually.of_forall (fun s => norm_nonneg _)) hdn
  have hGlim : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto
      (fun ω : ℝ => ∫ s in t..1, Complex.exp (2 * Complex.I * (ω : ℂ) * (s : ℂ)) * d s)
      (Bornology.cobounded ℝ) (𝓝 0) := by
    intro t ht
    have h := (rl_interval t 1 ht.2 d).comp (tendsto_scale_cobounded (r := 2) two_ne_zero)
    refine Tendsto.congr (fun ω => ?_) h
    simp only [Function.comp]
    congr 1
    funext s
    congr 2
    push_cast
    ring
  have hGcont : ∀ ω : ℝ, ContinuousOn
      (fun t => ∫ s in t..1, Complex.exp (2 * Complex.I * (ω : ℂ) * (s : ℂ)) * d s)
      (uIcc (0 : ℝ) 1) := fun ω => by
    apply intervalIntegral.continuousOn_primitive_interval_left
    rw [uIcc_of_le zero_le_one]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1 (hinner_int ω)
  have hFint : ∀ ω : ℝ, IntervalIntegrable (fun t : ℝ =>
      (Complex.exp (-(2 * Complex.I * (ω : ℂ) * (t : ℂ))) * c t) *
        ∫ s in t..1, Complex.exp (2 * Complex.I * (ω : ℂ) * (s : ℂ)) * d s) volume 0 1 := by
    intro ω
    have hcont : Continuous fun t : ℝ => Complex.exp (-(2 * Complex.I * (ω : ℂ) * (t : ℂ))) := by
      fun_prop
    exact (hc.continuousOn_mul hcont.continuousOn).mul_continuousOn (hGcont ω)
  have key := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := 0) (b := 1) (l := Bornology.cobounded ℝ)
    (F := fun (ω : ℝ) (t : ℝ) => (Complex.exp (-(2 * Complex.I * (ω : ℂ) * (t : ℂ))) * c t) *
        ∫ s in t..1, Complex.exp (2 * Complex.I * (ω : ℂ) * (s : ℂ)) * d s)
    (f := fun _ => (0 : ℂ)) (fun t => ‖c t‖ * K)
    (Eventually.of_forall (fun ω => (hFint ω).def'.aestronglyMeasurable))
    (Eventually.of_forall (fun ω => Eventually.of_forall (fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      rw [norm_mul, norm_mul, norm_exp_neg_real_I, one_mul]
      exact mul_le_mul_of_nonneg_left (hG ω t htI) (norm_nonneg _))))
    (hc.norm.mul_const K)
    (Eventually.of_forall (fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have hn := ((hGlim t htI).norm).const_mul ‖c t‖
      rw [norm_zero, mul_zero] at hn
      refine squeeze_zero_norm (fun ω => le_of_eq ?_) hn
      rw [norm_mul, norm_mul, norm_exp_neg_real_I, one_mul]))
  simpa using key

/-! ### Sequences along half-nodes -/

theorem eventually_cofinite_of_natAbs (P : ℤ → Prop) (M : ℕ)
    (h : ∀ j : ℤ, M ≤ j.natAbs → P j) : ∀ᶠ j in cofinite, P j := by
  rw [Filter.eventually_cofinite]
  apply (Set.finite_Icc (-(M : ℤ)) M).subset
  intro j hj
  simp only [Set.mem_setOf_eq] at hj
  simp only [Set.mem_Icc]
  by_contra hc
  apply hj (h j ?_)
  have h2 : ((j.natAbs : ℕ) : ℤ) = |j| := Int.natCast_natAbs j
  have h1 : (M : ℤ) ≤ |j| := by
    rcases not_and_or.1 hc with hc | hc
    · rw [abs_of_neg (by omega)]
      omega
    · rw [abs_of_pos (by omega)]
      omega
  have h3 : (M : ℤ) ≤ ((j.natAbs : ℕ) : ℤ) := h2 ▸ h1
  exact_mod_cast h3

theorem natAbs_threshold_of_eventually {P : ℤ → Prop} (h : ∀ᶠ j in cofinite, P j) :
    ∃ M : ℕ, ∀ j : ℤ, M ≤ j.natAbs → P j := by
  rw [Filter.eventually_cofinite] at h
  obtain ⟨B, hB⟩ := (h.image Int.natAbs).bddAbove
  refine ⟨B + 1, fun j hj => ?_⟩
  by_contra hP
  have := hB (Set.mem_image_of_mem Int.natAbs (show j ∈ {x : ℤ | ¬P x} from hP))
  omega

theorem halfNode_tendsto (σ : ℝ) (hσ : σ ≠ 0) :
    Tendsto (fun j : ℤ => σ * (((j : ℝ) + 1 / 2) * Real.pi)) cofinite (Bornology.cobounded ℝ) := by
  rw [← tendsto_norm_atTop_iff_cobounded, tendsto_atTop]
  intro b
  apply eventually_cofinite_of_natAbs _ (⌈b / |σ|⌉₊)
  intro j hj
  have h1 := NlsGge.ThirdConsultation.KSPS031Analytic.natAbs_le_norm_halfNode_expr j
  rw [NlsGge.ThirdConsultation.KSPS031Analytic.norm_halfNode_expr] at h1
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  have hσ' : 0 < |σ| := abs_pos.2 hσ
  have h2 : b / |σ| ≤ (j.natAbs : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hj)
  rw [div_le_iff₀ hσ'] at h2
  nlinarith [mul_le_mul_of_nonneg_left h1 hσ'.le]

theorem halfNode_abs_tendsto :
    Tendsto (fun j : ℤ => |((j : ℝ) + 1 / 2) * Real.pi|) cofinite atTop := by
  have h := tendsto_norm_atTop_iff_cobounded.2 (halfNode_tendsto 1 one_ne_zero)
  simpa using h

end
end NlsGge.ThirdConsultation.KSPS031SharpRL
