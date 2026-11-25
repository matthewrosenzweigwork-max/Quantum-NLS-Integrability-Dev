import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Support7

/- KSPS-012 SUPPORT8 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS012Support8.lean.
   core_l2: square summability of index_n * |D_n| with
     D_n = -e^{-2 i mu_n} osc mu_n (q_n c) - ((-1)^n/(2 i mu_n)) int u c,   mu_n = sigma * xi_n, q_n t = int_t^1 e^{2 i mu_n s} u s ds. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem core_l2 (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) (w : PhysicalL2) (a : ℝ) (ha : 0 ≤ a)
    (xi : ℤ → ℂ) (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    RealSqSummable (fun n : ℤ => indexWeight n * ‖
      -Complex.exp (-(2 * Complex.I * ((σ : ℂ) * xi n))) *
        endpointOsc ((σ : ℂ) * xi n) (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * ((σ : ℂ) * xi n) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 u) s) * coverRep38 w t) -
      (-1 : ℂ) ^ n / (2 * Complex.I * ((σ : ℂ) * xi n)) *
        ∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 u) t * coverRep38 w t‖) := by
  set uh := coverRep38 (physicalSobolevEmbed 1 u) with huh
  set dh := coverRep38 (physicalSobolevDerivative38 1 u) with hdh
  set c := coverRep38 w with hc
  set P : ℂ := ∫ t in (0 : ℝ)..1, uh t * c t with hP
  set pv1 : ℂ := sobolevPointValue 1 u 1 with hpv1
  set Ld : ℝ := ∫ s in (0 : ℝ)..1, ‖dh s‖ with hLd
  set Lc : ℝ := ∫ t in (0 : ℝ)..1, ‖c t‖ with hLc
  set Kc : ℝ := 4 * (Real.exp (2 * a) + 1) * Ld * Lc with hKc
  have hσc : (σ : ℂ) * (σ : ℂ) = 1 := by rcases hσ with rfl | rfl <;> simp
  have hσn : ‖(σ : ℂ)‖ = 1 := by rcases hσ with rfl | rfl <;> simp
  have hcci : IntervalIntegrable c volume 0 1 := intervalIntegrable_coverRep38_one w
  have hdhi : IntervalIntegrable dh volume 0 1 := intervalIntegrable_coverRep38_one _
  have hLd0 : 0 ≤ Ld := intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _)
  have hLc0 : 0 ≤ Lc := intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _)
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  -- square-summable majorants
  have hmem : MemLp c 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure :=
    NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc w
  have S_osc : RealSqSummable (fun n : ℤ => ‖endpointOsc ((σ : ℂ) * xi n) c‖) :=
    osc_sq_seq hmem a ha xi hxi σ hσ
  have S_T := Tz_sq_summable w (physicalSobolevDerivative38 1 u) σ hσ
  have S_inv := realSqSummable_inv_abs
  set C1 : ℝ := 2 * a * ‖P‖ + Real.exp a * Kc * a with hC1
  have Stot := ((S_osc.mul_left ‖pv1‖).add (S_inv.mul_left C1)).add (S_T.mul_left (Real.exp a))
  refine RealSqSummable.of_eventually_le Stot ?_
  set N0 : ℕ := ⌈2 * a + 2⌉₊ with hN0
  filter_upwards [eventually_cofinite_natAbs N0] with n hn
  have hN0r : 2 * a + 2 ≤ (N0 : ℝ) := Nat.le_ceil _
  have hnabs : 2 * a + 2 ≤ |(n : ℝ)| := by
    have h1 : ((N0 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := Int.cast_le.2 hn
    rw [Int.cast_abs] at h1
    simp only [Int.cast_natCast] at h1
    linarith
  have hm1 : 1 ≤ |(n : ℝ)| := by linarith
  set m : ℝ := |(n : ℝ)| with hmdef
  have hmpos : 0 < m := by linarith
  have hw := indexWeight_pos n
  have hwm : indexWeight n ≤ 2 * m := iw_le_two_mul n hm1
  have hmw : m ≤ indexWeight n := abs_le_indexWeight n
  obtain ⟨hlow, himxi⟩ := xi_lower_bound a xi hxi n
  set μ : ℂ := (σ : ℂ) * xi n with hμdef
  have hμn : ‖μ‖ = ‖xi n‖ := by rw [hμdef, norm_mul, hσn, one_mul]
  have hImμ : |μ.im| ≤ a := by
    rcases hσ with h | h <;> simpa [hμdef, h] using himxi
  have hπ : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hΛ : m ≤ ‖μ‖ := by
    rw [hμn]
    nlinarith [mul_le_mul_of_nonneg_right hπ hmpos.le]
  have hμ0 : μ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hΛ; linarith
  have hνn : ‖2 * Complex.I * μ‖ = 2 * ‖μ‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I]; simp
  have hνpos : 0 < ‖2 * Complex.I * μ‖ := by rw [hνn]; linarith
  have hwν : indexWeight n ≤ ‖2 * Complex.I * μ‖ := by rw [hνn]; linarith
  set β : ℂ := xi n - (n : ℂ) * (Real.pi : ℂ) with hβdef
  have hβ : ‖β‖ ≤ a / indexWeight n := hxi n
  have hβ2 : ‖β‖ * indexWeight n ≤ a := (le_div_iff₀ hw).1 hβ
  have hβle : ‖β‖ ≤ 1 / 2 := by nlinarith [norm_nonneg β]
  have hβm : ‖β‖ ≤ a / m := by
    refine le_trans hβ ?_
    exact div_le_div_of_nonneg_left ha hmpos hmw
  have hμβ : μ - (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ)) = (σ : ℂ) * β := by
    rw [hμdef, hβdef]; push_cast; ring
  have hμβn : ‖μ - (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))‖ = ‖β‖ := by
    rw [hμβ, norm_mul, hσn, one_mul]
  -- the exponential comparison
  set sg : ℂ := (-1 : ℂ) ^ n with hsg
  set d : ℂ := Complex.exp (-(Complex.I * μ)) with hd
  have hsgn : ‖sg‖ = 1 := by rw [hsg, norm_zpow]; simp
  have hdsg : ‖d - sg‖ ≤ 2 * ‖β‖ := by
    have e1 : d = sg * Complex.exp (-(Complex.I * ((σ : ℂ) * β))) := by
      rw [hsg, ← exp_neg_I_pi_int σ n hσ, ← Complex.exp_add, hd]
      congr 1
      have : μ = (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ)) + (σ : ℂ) * β := by rw [← hμβ]; ring
      rw [this]; ring
    have h2 : ‖-(Complex.I * ((σ : ℂ) * β))‖ ≤ 1 := by
      rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, hσn]; simp; linarith
    have h3 := Complex.norm_exp_sub_one_le h2
    have e2 : d - sg = sg * (Complex.exp (-(Complex.I * ((σ : ℂ) * β))) - 1) := by
      rw [e1]; ring
    rw [e2, norm_mul, hsgn, one_mul]
    refine h3.trans ?_
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, hσn]; simp
  have hdn : ‖d‖ ≤ Real.exp a := by
    rw [hd, Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    have : (-(Complex.I * μ)).re = μ.im := by simp [Complex.mul_re]
    rw [this]
    exact (le_abs_self _).trans hImμ
  -- the Lipschitz bound for the double integral
  have hTlip := NlsGge.ThirdConsultation.KSPS012Support5.Tz_lip hcci hdhi ha (σ * n) hImμ
    (by rw [hμβn]; exact hβle)
  rw [hμβn] at hTlip
  set T : ℂ := NlsGge.ThirdConsultation.KSPS012Support5.Tz c dh μ with hT
  set T0 : ℂ := NlsGge.ThirdConsultation.KSPS012Support5.Tz c dh (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ)) with hT0
  have hTn : ‖T‖ ≤ ‖T0‖ + Kc * (a / m) := by
    have h1 : ‖T‖ ≤ ‖T0‖ + ‖T - T0‖ := by
      have := norm_add_le T0 (T - T0)
      rw [add_sub_cancel] at this
      linarith
    refine h1.trans ?_
    have h2 : ‖T - T0‖ ≤ Kc * ‖β‖ := hTlip
    have h3 : Kc * ‖β‖ ≤ Kc * (a / m) := mul_le_mul_of_nonneg_left hβm hKc0
    linarith
  -- the exact decomposition
  have hdec := core_decomp u w hμ0
  set Oc : ℂ := endpointOsc μ c with hOc
  have hdiff : -Complex.exp (-(2 * Complex.I * μ)) *
        endpointOsc μ (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) * uh s) * c t) -
      sg / (2 * Complex.I * μ) * P =
      -(pv1 / (2 * Complex.I * μ)) * Oc + ((d - sg) / (2 * Complex.I * μ)) * P +
        (d / (2 * Complex.I * μ)) * T := by
    rw [hdec]; ring
  -- norm estimate
  have hnorm : ‖-Complex.exp (-(2 * Complex.I * μ)) *
        endpointOsc μ (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) * uh s) * c t) -
      sg / (2 * Complex.I * μ) * P‖ ≤
      ‖pv1‖ / ‖2 * Complex.I * μ‖ * ‖Oc‖ + ‖d - sg‖ / ‖2 * Complex.I * μ‖ * ‖P‖ +
        ‖d‖ / ‖2 * Complex.I * μ‖ * ‖T‖ := by
    rw [hdiff]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_
    · rw [norm_mul, norm_neg, norm_div]
    · rw [norm_mul, norm_div]
    · rw [norm_mul, norm_div]
  set Nν : ℝ := ‖2 * Complex.I * μ‖ with hNν
  have hr : indexWeight n / Nν ≤ 1 := (div_le_one hνpos).2 hwν
  have hr0 : 0 ≤ indexWeight n / Nν := div_nonneg hw.le hνpos.le
  have hOc0 := norm_nonneg Oc
  have hP0 := norm_nonneg P
  have hT0n := norm_nonneg T
  have hpv0 := norm_nonneg pv1
  have hdsg0 := norm_nonneg (d - sg)
  have hd0 := norm_nonneg d
  -- multiply by the weight
  have hfin : indexWeight n * ‖-Complex.exp (-(2 * Complex.I * μ)) *
        endpointOsc μ (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) * uh s) * c t) -
      sg / (2 * Complex.I * μ) * P‖ ≤
      ‖pv1‖ * ‖Oc‖ + (2 * a / m) * ‖P‖ + Real.exp a * (‖T0‖ + Kc * (a / m)) := by
    refine (mul_le_mul_of_nonneg_left hnorm hw.le).trans ?_
    have e : indexWeight n * (‖pv1‖ / Nν * ‖Oc‖ + ‖d - sg‖ / Nν * ‖P‖ + ‖d‖ / Nν * ‖T‖) =
        (indexWeight n / Nν) * (‖pv1‖ * ‖Oc‖ + ‖d - sg‖ * ‖P‖ + ‖d‖ * ‖T‖) := by
      field_simp
    rw [e]
    have hB : ‖d - sg‖ * ‖P‖ ≤ (2 * a / m) * ‖P‖ := by
      refine mul_le_mul_of_nonneg_right ?_ hP0
      calc ‖d - sg‖ ≤ 2 * ‖β‖ := hdsg
        _ ≤ 2 * (a / m) := by linarith
        _ = 2 * a / m := by ring
    have hE : ‖d‖ * ‖T‖ ≤ Real.exp a * (‖T0‖ + Kc * (a / m)) :=
      mul_le_mul hdn hTn hT0n (Real.exp_pos a).le
    have hsum : ‖pv1‖ * ‖Oc‖ + ‖d - sg‖ * ‖P‖ + ‖d‖ * ‖T‖ ≤
        ‖pv1‖ * ‖Oc‖ + (2 * a / m) * ‖P‖ + Real.exp a * (‖T0‖ + Kc * (a / m)) := by linarith
    have hnn : 0 ≤ ‖pv1‖ * ‖Oc‖ + ‖d - sg‖ * ‖P‖ + ‖d‖ * ‖T‖ := by positivity
    calc (indexWeight n / Nν) * (‖pv1‖ * ‖Oc‖ + ‖d - sg‖ * ‖P‖ + ‖d‖ * ‖T‖)
        ≤ 1 * (‖pv1‖ * ‖Oc‖ + ‖d - sg‖ * ‖P‖ + ‖d‖ * ‖T‖) := mul_le_mul_of_nonneg_right hr hnn
      _ ≤ _ := by rw [one_mul]; exact hsum
  -- compare with the majorant
  have hgn : ‖pv1‖ * ‖Oc‖ + (2 * a / m) * ‖P‖ + Real.exp a * (‖T0‖ + Kc * (a / m)) =
      ‖pv1‖ * ‖endpointOsc ((σ : ℂ) * xi n) c‖ + C1 * (1 / |(n : ℝ)|) +
        Real.exp a * ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c dh
          (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))‖ := by
    rw [hC1, hOc, hμdef, hmdef.symm, hT0]
    field_simp
    ring
  have hnn : 0 ≤ indexWeight n * ‖-Complex.exp (-(2 * Complex.I * μ)) *
        endpointOsc μ (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * μ * (s : ℂ)) * uh s) * c t) -
      sg / (2 * Complex.I * μ) * P‖ := by positivity
  rw [abs_of_nonneg hnn, abs_of_nonneg (by rw [← hgn]; positivity)]
  rw [← hgn]
  exact hfin

end NlsGge.ThirdConsultation.KSPSWKB
