import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform1

                                                                                 
                                                                                                                
                                                                                                                
                                                                                                       
                                                                                                             
                                                                                                
                                                                                                                  
                                                                                                     
                          
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS017U2
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS017W

/-- The pointwise estimate of offdiag_deriv_sq_summable (landed body), on one tail index. -/
theorem offdiag_pointwise (b : Bool) (a : ℝ) (ha : 0 ≤ a) (C L : ℝ) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (cc : ℝ → ℂ) (hcii : IntervalIntegrable cc volume 0 1)
    (xi : ℤ → ℂ) (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n)
    (g : ℂ → ℂ) (hgd : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ g z)
    (happ : ∀ z : ℂ, z ≠ 0 → L ≤ ‖z‖ → |z.im| ≤ a + 1 →
      ‖g z - (if b then -Complex.I else Complex.I) *
        NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((if b then (-1 : ℂ) else 1) * z) cc‖ ≤ C / ‖z‖)
    (n : ℤ) (hnabs : a + L + 2 ≤ |(n : ℝ)|) :
    ‖deriv g (xi n)‖ ≤ 2 * C * (1 / |(n : ℝ)|) +
      ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc (((if b then (-1 : ℤ) else 1 : ℤ) : ℂ) * xi n)
        (fun t => Complex.I * ((1 - 2 * t : ℝ) : ℂ) * cc t)‖ := by
  set σc : ℂ := if b then (-1 : ℂ) else 1 with hσc
  set κ : ℂ := if b then -Complex.I else Complex.I with hκdef
  have hκ : ‖κ‖ = 1 := by cases b <;> simp [hκdef]
  have hσn : ‖σc‖ = 1 := by cases b <;> simp [hσc]
  set σ : ℤ := if b then -1 else 1 with hσdef
  have hσσ : ((σ : ℤ) : ℂ) = σc := by cases b <;> simp [hσdef, hσc]
  set H' : ℝ → ℂ := fun t => Complex.I * ((1 - 2 * t : ℝ) : ℂ) * cc t with hH'def
  have hOd : ∀ z : ℂ, HasDerivAt (fun w : ℂ => κ * NlsGge.ThirdConsultation.KSPSWKB.endpointOsc (σc * w) cc)
      (κ * (σc * NlsGge.ThirdConsultation.KSPSWKB.endpointOsc (σc * z) H')) z := by
    intro z
    have h1 := (hasDerivAt_endpointOsc hcii (σc * z)).comp z ((hasDerivAt_id z).const_mul σc)
    refine (h1.const_mul κ).congr_deriv ?_
    simp only [hH'def]
    ring
  -- tail facts
  have hδ0 := hxi n
  have hw1 := NlsGge.ThirdConsultation.KSPS.one_le_indexWeight n
  have hπ : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hm0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
  have hnpi : ‖(n : ℂ) * (Real.pi : ℂ)‖ = Real.pi * |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; ring
  have hδa : a / indexWeight n ≤ a := div_le_self ha hw1
  have hξ : |(n : ℝ)| + L + 2 ≤ ‖xi n‖ := by
    have h1 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) (xi n)
    rw [norm_sub_rev, hnpi] at h1
    have : 3 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := mul_le_mul_of_nonneg_right hπ hm0
    linarith
  have hξ2 : 2 ≤ ‖xi n‖ := by linarith
  have hn1 : 0 < |(n : ℝ)| := by linarith
  have hz : xi n ≠ 0 := by intro h; rw [h, norm_zero] at hξ2; norm_num at hξ2
  -- the remainder E
  set E : ℂ → ℂ := fun w => g w - κ * NlsGge.ThirdConsultation.KSPSWKB.endpointOsc (σc * w) cc with hEdef
  have hEd : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ E z := fun z hz0 =>
    (hgd z hz0).sub (hOd z).differentiableAt
  have hball : ∀ z ∈ Metric.closedBall (xi n) 1, ‖xi n‖ - 1 ≤ ‖z‖ ∧ |z.im| ≤ a + 1 := by
    intro z hzb
    rw [Metric.mem_closedBall, dist_eq_norm] at hzb
    have h1 := norm_sub_norm_le (xi n) z
    have h4 : ‖xi n - z‖ ≤ 1 := by rw [norm_sub_rev]; exact hzb
    have h2 : |z.im - (xi n).im| ≤ ‖z - xi n‖ := by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have h3 := abs_sub_abs_le_abs_sub z.im (xi n).im
    have himξ : |(xi n).im| ≤ a := by
      have : (xi n).im = (xi n - (n : ℂ) * Real.pi).im := by simp
      rw [this]; exact (Complex.abs_im_le_norm _).trans (hδ0.trans hδa)
    constructor <;> linarith
  have hEdb : ∀ z ∈ Metric.closedBall (xi n) 1, DifferentiableAt ℂ E z := by
    intro z hzb
    have h := (hball z hzb).1
    have hz0 : z ≠ 0 := by intro h0; rw [h0, norm_zero] at h; linarith
    exact hEd z hz0
  have hEs : ∀ z ∈ Metric.sphere (xi n) 1, ‖E z‖ ≤ 2 * C / ‖xi n‖ := by
    intro z hzs
    have hzb : z ∈ Metric.closedBall (xi n) 1 := Metric.sphere_subset_closedBall hzs
    obtain ⟨h1, h2⟩ := hball z hzb
    have hz0 : z ≠ 0 := by intro h0; rw [h0, norm_zero] at h1; linarith
    have hzL : L ≤ ‖z‖ := by linarith
    have hb := happ z hz0 hzL h2
    refine hb.trans ?_
    have hzpos : 0 < ‖z‖ := by linarith
    have hhalf : ‖xi n‖ / 2 ≤ ‖z‖ := by linarith
    rw [div_le_div_iff₀ hzpos (by linarith)]
    nlinarith
  have hcauchy := norm_deriv_le_of_sphere one_pos hEdb hEs
  rw [div_one] at hcauchy
  have hgE : deriv g (xi n) = deriv E (xi n) + κ * (σc * NlsGge.ThirdConsultation.KSPSWKB.endpointOsc (σc * xi n) H') := by
    have h1 : HasDerivAt E (deriv g (xi n) - κ * (σc * NlsGge.ThirdConsultation.KSPSWKB.endpointOsc (σc * xi n) H')) (xi n) :=
      (hgd (xi n) hz).hasDerivAt.sub (hOd (xi n))
    rw [h1.deriv]; ring
  have hprin : ‖κ * (σc * NlsGge.ThirdConsultation.KSPSWKB.endpointOsc (σc * xi n) H')‖ =
      ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((σ : ℂ) * xi n) H'‖ := by
    rw [norm_mul, norm_mul, hκ, hσn, one_mul, one_mul, hσσ]
  have hξn : 2 * C / ‖xi n‖ ≤ 2 * C * (1 / |(n : ℝ)|) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (by positivity) hn1 (by linarith)
  rw [hgE]
  refine (norm_add_le _ _).trans ?_
  rw [hprin]
  linarith

/-- Uniform (finite-sum) S017-3, generic form: one constant K before cc, ξ, g, F. -/
theorem offdiag_deriv_tail_U (b : Bool) (a : ℝ) (ha : 0 ≤ a) (C L : ℝ) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (Bc : ℝ) (hBc : 0 ≤ Bc) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (cc : ℝ → ℂ),
      MemLp cc 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure → AEStronglyMeasurable cc volume →
      IntervalIntegrable (fun t => ‖cc t‖ ^ 2) volume 0 1 → (∫ t in (0 : ℝ)..1, ‖cc t‖ ^ 2) ≤ Bc →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ (g : ℂ → ℂ), (∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ g z) →
      (∀ z : ℂ, z ≠ 0 → L ≤ ‖z‖ → |z.im| ≤ a + 1 →
        ‖g z - (if b then -Complex.I else Complex.I) *
          NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((if b then (-1 : ℂ) else 1) * z) cc‖ ≤ C / ‖z‖) →
      ∀ F : Finset ℤ, (∀ n ∈ F, ((⌈2 * a + L + 2⌉₊ : ℕ) : ℤ) ≤ |n|) →
      ∑ n ∈ F, ‖deriv g (xi n)‖ ^ 2 ≤ K := by
  set E2 : ℝ := Real.exp (2 * a) + 1 with hE2
  have hE20 : 0 ≤ E2 := by positivity
  set Z : ℝ := ∑' n : ℤ, (1 / |(n : ℝ)|) ^ 2 with hZ
  have hZ0 : 0 ≤ Z := NlsGge.ThirdConsultation.KSPS017U0.inv_abs_tsum_nonneg
  set Km : ℝ := 2 * C + 1 with hKm
  have hKm0 : 0 ≤ Km := by positivity
  refine ⟨Km ^ 2 * (((2 : ℕ) : ℝ) * (Z + 2 * E2 * Bc)), by positivity,
    fun cc hcmem hcm hc2 hBcc xi hxi g hgd happ F hF => ?_⟩
  have hcii : IntervalIntegrable cc volume 0 1 := NlsGge.ThirdConsultation.KSPSWKB.intervalIntegrable_of_memLp hcmem
  set σ : ℤ := if b then -1 else 1 with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by cases b <;> simp [hσdef]
  set H' : ℝ → ℂ := fun t => Complex.I * ((1 - 2 * t : ℝ) : ℂ) * cc t with hH'def
  have hH'mem : MemLp H' 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure :=
    NlsGge.ThirdConsultation.KSPSSupport.h150_memLp_mul_bdd cc (fun t => Complex.I * ((1 - 2 * t : ℝ) : ℂ))
      hcmem (Continuous.continuousOn (by fun_prop))
  have hH'm : AEStronglyMeasurable H' volume :=
    (by fun_prop : Continuous fun t : ℝ => Complex.I * ((1 - 2 * t : ℝ) : ℂ)).aestronglyMeasurable.mul hcm
  have hH'pt : ∀ t ∈ Icc (0 : ℝ) 1, ‖H' t‖ ^ 2 ≤ ‖cc t‖ ^ 2 := by
    intro t ht
    simp only [hH'def, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    have h1 : (1 - 2 * t) ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    calc (1 - 2 * t) ^ 2 * ‖cc t‖ ^ 2 ≤ 1 * ‖cc t‖ ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = ‖cc t‖ ^ 2 := one_mul _
  have hH'2 : IntervalIntegrable (fun t => ‖H' t‖ ^ 2) volume 0 1 := by
    refine hc2.mono_fun ((hH'm.norm.pow 2).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [uIoc_of_le zero_le_one] at ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
    exact hH'pt t ⟨ht.1.le, ht.2⟩
  have hCH' : ∫ t in (0 : ℝ)..1, ‖H' t‖ ^ 2 ≤ ∫ t in (0 : ℝ)..1, ‖cc t‖ ^ 2 :=
    intervalIntegral.integral_mono_on zero_le_one hH'2 hc2 hH'pt
  have hn0' : 2 * a + L + 2 ≤ ((⌈2 * a + L + 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hFn : ∀ n ∈ F, 2 * a + L + 2 ≤ |(n : ℝ)| := by
    intro n hn
    have h1 : ((((⌈2 * a + L + 2⌉₊ : ℕ) : ℤ)) : ℝ) ≤ ((|n| : ℤ) : ℝ) := Int.cast_le.2 (hF n hn)
    rw [Int.cast_abs] at h1
    simp only [Int.cast_natCast] at h1
    linarith
  have hOH := NlsGge.ThirdConsultation.KSPSQ1.osc_sq_finite hH'mem a ha xi hxi σ hσ F
  refine NlsGge.ThirdConsultation.KSPS017U0.sum_sq_le_fin F _
    ![fun n => 1 / |(n : ℝ)|, fun n => ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((σ : ℂ) * xi n) H'‖] Km hKm0 ?_
    ![Z, 2 * E2 * Bc] ?_ |>.trans (le_of_eq ?_)
  · intro n hn
    refine ⟨norm_nonneg _, ?_⟩
    have hp := offdiag_pointwise b a ha C L hC hL cc hcii xi hxi g hgd happ n (by linarith [hFn n hn])
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    refine hp.trans ?_
    have hi : 0 ≤ 1 / |(n : ℝ)| := by positivity
    have hO : 0 ≤ ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((σ : ℂ) * xi n) H'‖ := norm_nonneg _
    have k1 : 2 * C * (1 / |(n : ℝ)|) ≤ Km * (1 / |(n : ℝ)|) :=
      mul_le_mul_of_nonneg_right (by rw [hKm]; linarith) hi
    have k2 : ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((σ : ℂ) * xi n) H'‖ ≤ Km * ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((σ : ℂ) * xi n) H'‖ := by
      have : 1 ≤ Km := by rw [hKm]; linarith
      nlinarith
    calc _ ≤ Km * (1 / |(n : ℝ)|) + Km * ‖NlsGge.ThirdConsultation.KSPSWKB.endpointOsc ((σ : ℂ) * xi n) H'‖ := by linarith
      _ = _ := by ring
  · intro j
    fin_cases j
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      exact NlsGge.ThirdConsultation.KSPS017U0.inv_abs_sum_le F
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]
      refine hOH.trans ?_
      exact mul_le_mul_of_nonneg_left (hCH'.trans hBcc) (by positivity)
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

end
end NlsGge.ThirdConsultation.KSPS017U2
