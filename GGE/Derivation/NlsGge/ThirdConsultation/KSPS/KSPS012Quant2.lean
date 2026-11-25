import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Support8
import NlsGge.ThirdConsultation.KSPS.KSPS003Support2
import NlsGge.ThirdConsultation.KSPSSupport.A1U01
import NlsGge.ThirdConsultation.KSPS.KSPS011Quant1
import NlsGge.ThirdConsultation.KSPS.KSPS012Quant1
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU4

/- KSPS012Q2 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPS012Quant2.lean. Pro round-15 SUPPORT (never a packet). CORE.
   Ball-uniform, finite-sum companion of KSPS012Support8.core_l2 (proof development's method):
   * core_pointwise: the per-index bound that the landed core_l2 body proves on the tail |n| ≥ ⌈2a+2⌉ (body copied,
     the final RealSqSummable step removed), with its constants written out explicitly;
   * core_tail_sum: the finite tail sums, via KSPSQ1.osc_sq_finite, KSPS012Q1.Tz_sum_le and Σ (1/|n|)² ≤ Σ' (1/|n|)²;
   * core_tail_U: one constant, chosen before u, w, ξ, F, valid for ‖u‖ ≤ Bu, ‖w‖ ≤ Bw (point value ≤ ‖ι‖‖u‖,
     ∫|u'| ≤ ‖D‖‖u‖, ∫|w| ≤ (‖w‖²+1)/2, |∫ u w| ≤ (‖u‖²+‖w‖²)/2).
   No hypothesis added; no real tsum is used except Σ' (1/|n|)² of an explicit summable nonnegative sequence. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPS012Q2
open NlsGge.ThirdConsultation.KSPSWKB

theorem core_pointwise (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) (w : PhysicalL2) (a : ℝ) (ha : 0 ≤ a)
    (xi : ℤ → ℂ) (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (n : ℤ) (hn : ((⌈2 * a + 2⌉₊ : ℕ) : ℤ) ≤ |n|) :
    indexWeight n * ‖
      -Complex.exp (-(2 * Complex.I * ((σ : ℂ) * xi n))) *
        endpointOsc ((σ : ℂ) * xi n) (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * ((σ : ℂ) * xi n) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 u) s) * coverRep38 w t) -
      (-1 : ℂ) ^ n / (2 * Complex.I * ((σ : ℂ) * xi n)) *
        ∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 u) t * coverRep38 w t‖ ≤
      ‖sobolevPointValue 1 u 1‖ * ‖endpointOsc ((σ : ℂ) * xi n) (coverRep38 w)‖ +
        (2 * a * ‖∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 u) t * coverRep38 w t‖ +
          Real.exp a * (4 * (Real.exp (2 * a) + 1) *
            (∫ s in (0 : ℝ)..1, ‖coverRep38 (physicalSobolevDerivative38 1 u) s‖) *
            (∫ t in (0 : ℝ)..1, ‖coverRep38 w t‖)) * a) * (1 / |(n : ℝ)|) +
        Real.exp a * ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz (coverRep38 w)
          (coverRep38 (physicalSobolevDerivative38 1 u)) (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))‖ := by
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
  set C1 : ℝ := 2 * a * ‖P‖ + Real.exp a * Kc * a with hC1
  set N0 : ℕ := ⌈2 * a + 2⌉₊ with hN0
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
  have hgn : ‖pv1‖ * ‖Oc‖ + (2 * a / m) * ‖P‖ + Real.exp a * (‖T0‖ + Kc * (a / m)) =
      ‖pv1‖ * ‖Oc‖ + C1 * (1 / m) + Real.exp a * ‖T0‖ := by
    rw [hC1]
    field_simp
    ring
  exact hfin.trans hgn.le

theorem sq_add3_le (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

theorem sum_sq_le_three {ι : Type*} (F : Finset ι) (x t1 t2 t3 : ι → ℝ)
    (h : ∀ n ∈ F, 0 ≤ x n ∧ x n ≤ t1 n + t2 n + t3 n)
    (T1 T2 T3 : ℝ)
    (h1 : ∑ n ∈ F, t1 n ^ 2 ≤ T1) (h2 : ∑ n ∈ F, t2 n ^ 2 ≤ T2) (h3 : ∑ n ∈ F, t3 n ^ 2 ≤ T3) :
    ∑ n ∈ F, x n ^ 2 ≤ 3 * (T1 + T2 + T3) := by
  have hp : ∀ n ∈ F, x n ^ 2 ≤ 3 * (t1 n ^ 2 + t2 n ^ 2 + t3 n ^ 2) := by
    intro n hn
    obtain ⟨h0, hle⟩ := h n hn
    exact (pow_le_pow_left₀ h0 hle 2).trans (sq_add3_le _ _ _)
  refine (Finset.sum_le_sum hp).trans ?_
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  linarith

/-- the explicit Σ' (1/|n|)² constant -/
theorem inv_sum_le (F : Finset ℤ) :
    ∑ n ∈ F, (1 / |(n : ℝ)|) ^ 2 ≤ ∑' n : ℤ, (1 / |(n : ℝ)|) ^ 2 :=
  realSqSummable_inv_abs.sum_le_tsum F (fun n _ => sq_nonneg _)

theorem inv_tsum_nonneg : 0 ≤ ∑' n : ℤ, (1 / |(n : ℝ)|) ^ 2 :=
  tsum_nonneg (fun n => sq_nonneg _)

theorem core_tail_sum (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) (w : PhysicalL2) (a : ℝ) (ha : 0 ≤ a)
    (xi : ℤ → ℂ) (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n)
    (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (F : Finset ℤ)
    (hF : ∀ n ∈ F, ((⌈2 * a + 2⌉₊ : ℕ) : ℤ) ≤ |n|) :
    ∑ n ∈ F, (indexWeight n * ‖
      -Complex.exp (-(2 * Complex.I * ((σ : ℂ) * xi n))) *
        endpointOsc ((σ : ℂ) * xi n) (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * ((σ : ℂ) * xi n) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 u) s) * coverRep38 w t) -
      (-1 : ℂ) ^ n / (2 * Complex.I * ((σ : ℂ) * xi n)) *
        ∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 u) t * coverRep38 w t‖) ^ 2 ≤
      3 * (‖sobolevPointValue 1 u 1‖ ^ 2 * (2 * (Real.exp (2 * a) + 1) * ‖w‖ ^ 2) +
        (2 * a * ‖∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 u) t * coverRep38 w t‖ +
          Real.exp a * (4 * (Real.exp (2 * a) + 1) *
            (∫ s in (0 : ℝ)..1, ‖coverRep38 (physicalSobolevDerivative38 1 u) s‖) *
            (∫ t in (0 : ℝ)..1, ‖coverRep38 w t‖)) * a) ^ 2 * (∑' n : ℤ, (1 / |(n : ℝ)|) ^ 2) +
        Real.exp a ^ 2 * ((∫ s in (0 : ℝ)..1, ‖coverRep38 (physicalSobolevDerivative38 1 u) s‖) *
          ((∫ s in (0 : ℝ)..1, ‖coverRep38 (physicalSobolevDerivative38 1 u) s‖) * ‖w‖ ^ 2))) := by
  set C1 : ℝ := 2 * a * ‖∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 u) t * coverRep38 w t‖ +
    Real.exp a * (4 * (Real.exp (2 * a) + 1) *
      (∫ s in (0 : ℝ)..1, ‖coverRep38 (physicalSobolevDerivative38 1 u) s‖) *
      (∫ t in (0 : ℝ)..1, ‖coverRep38 w t‖)) * a with hC1
  have hmem := NlsGge.ThirdConsultation.KSPSSupport.coverRep38_memLp_Icc w
  have hosc := NlsGge.ThirdConsultation.KSPSQ1.osc_sq_finite hmem a ha xi hxi σ hσ F
  rw [integral_sq_coverRep38_one] at hosc
  have hT := NlsGge.ThirdConsultation.KSPS012Q1.Tz_sum_le w (physicalSobolevDerivative38 1 u) σ hσ F
  rw [integral_sq_coverRep38_one] at hT
  refine sum_sq_le_three F _
    (fun n => ‖sobolevPointValue 1 u 1‖ * ‖endpointOsc ((σ : ℂ) * xi n) (coverRep38 w)‖)
    (fun n => C1 * (1 / |(n : ℝ)|))
    (fun n => Real.exp a * ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz (coverRep38 w)
      (coverRep38 (physicalSobolevDerivative38 1 u)) (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))‖)
    ?_ _ _ _ ?_ ?_ ?_
  · intro n hn
    exact ⟨mul_nonneg (indexWeight_pos n).le (norm_nonneg _), core_pointwise u w a ha xi hxi σ hσ n (hF n hn)⟩
  · simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hosc (by positivity)
  · simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (inv_sum_le F) (by positivity)
  · simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hT (by positivity)

theorem core_tail_U (a : ℝ) (ha : 0 ≤ a) (Bu Bw : ℝ) (hBu : 0 ≤ Bu) (hBw : 0 ≤ Bw) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) (w : PhysicalL2), ‖u‖ ≤ Bu → ‖w‖ ≤ Bw →
      ∀ (xi : ℤ → ℂ), (∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n) →
      ∀ (σ : ℤ), (σ = 1 ∨ σ = -1) → ∀ F : Finset ℤ, (∀ n ∈ F, ((⌈2 * a + 2⌉₊ : ℕ) : ℤ) ≤ |n|) →
      ∑ n ∈ F, (indexWeight n * ‖
        -Complex.exp (-(2 * Complex.I * ((σ : ℂ) * xi n))) *
          endpointOsc ((σ : ℂ) * xi n) (fun t =>
            (∫ s in t..1, Complex.exp (2 * Complex.I * ((σ : ℂ) * xi n) * (s : ℂ)) *
              coverRep38 (physicalSobolevEmbed 1 u) s) * coverRep38 w t) -
        (-1 : ℂ) ^ n / (2 * Complex.I * ((σ : ℂ) * xi n)) *
          ∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 u) t * coverRep38 w t‖) ^ 2 ≤ C := by
  have hS0 : 0 ≤ ∑' n : ℤ, (1 / |(n : ℝ)|) ^ 2 := inv_tsum_nonneg
  set I0 : ℝ := ‖iotaCLM‖ * Bu with hI0
  set D0 : ℝ := ‖derivCLM‖ * Bu with hD0
  set P0 : ℝ := (Bu ^ 2 + Bw ^ 2) / 2 with hP0
  set L0 : ℝ := (Bw ^ 2 + 1) / 2 with hL0
  set E : ℝ := Real.exp (2 * a) + 1 with hE
  have hE0 : 0 ≤ E := by positivity
  have hI00 : 0 ≤ I0 := by positivity
  have hD00 : 0 ≤ D0 := by positivity
  have hP00 : 0 ≤ P0 := by positivity
  have hL00 : 0 ≤ L0 := by positivity
  set C10 : ℝ := 2 * a * P0 + Real.exp a * (4 * E * D0 * L0) * a with hC10
  refine ⟨3 * (I0 ^ 2 * (2 * E * Bw ^ 2) + C10 ^ 2 * (∑' n : ℤ, (1 / |(n : ℝ)|) ^ 2) +
      Real.exp a ^ 2 * (D0 * (D0 * Bw ^ 2))),
    by positivity, fun u w hu hw xi hxi σ hσ F hF => ?_⟩
  refine (core_tail_sum u w a ha xi hxi σ hσ F hF).trans ?_
  -- the five explicit functionals of u, w
  have hpv : ‖sobolevPointValue 1 u 1‖ ≤ I0 :=
    (NlsGge.ThirdConsultation.KSPS003Support2.pv_sup u 1).trans
      (mul_le_mul_of_nonneg_left hu (by positivity))
  have hLd : ∫ s in (0 : ℝ)..1, ‖coverRep38 (physicalSobolevDerivative38 1 u) s‖ ≤ D0 :=
    (NlsGge.ThirdConsultation.KSPS003Support2.deriv_L1 u).trans
      (mul_le_mul_of_nonneg_left hu (by positivity))
  have hLd0 : 0 ≤ ∫ s in (0 : ℝ)..1, ‖coverRep38 (physicalSobolevDerivative38 1 u) s‖ :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _)
  have hLc : ∫ t in (0 : ℝ)..1, ‖coverRep38 w t‖ ≤ L0 := by
    refine (NlsGge.ThirdConsultation.KSPSU4.integral_norm_coverRep_le w).trans ?_
    have : ‖w‖ ^ 2 ≤ Bw ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    rw [hL0]; linarith
  have hLc0 : 0 ≤ ∫ t in (0 : ℝ)..1, ‖coverRep38 w t‖ :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => norm_nonneg _)
  have hP : ‖∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 u) t * coverRep38 w t‖ ≤ P0 := by
    refine (NlsGge.ThirdConsultation.KSPSSupport.h161_prefix_le (physicalSobolevEmbed 1 u) w
      ⟨zero_le_one, le_rfl⟩).trans ?_
    have h1 : ‖physicalSobolevEmbed 1 u‖ ≤ Bu :=
      (NlsGge.ThirdConsultation.KSPSSupport.h161_embed_norm_le 1 u).trans hu
    have h1s : ‖physicalSobolevEmbed 1 u‖ ^ 2 ≤ Bu ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h2s : ‖w‖ ^ 2 ≤ Bw ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    rw [hP0]; linarith
  have hw2 : ‖w‖ ^ 2 ≤ Bw ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
  -- monotonicity of the explicit expression
  have hC1 : 2 * a * ‖∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 u) t * coverRep38 w t‖ +
      Real.exp a * (4 * (Real.exp (2 * a) + 1) *
        (∫ s in (0 : ℝ)..1, ‖coverRep38 (physicalSobolevDerivative38 1 u) s‖) *
        (∫ t in (0 : ℝ)..1, ‖coverRep38 w t‖)) * a ≤ C10 := by
    rw [hC10]
    have hea := Real.exp_pos a
    have h4 : 4 * (Real.exp (2 * a) + 1) *
        (∫ s in (0 : ℝ)..1, ‖coverRep38 (physicalSobolevDerivative38 1 u) s‖) *
        (∫ t in (0 : ℝ)..1, ‖coverRep38 w t‖) ≤ 4 * E * D0 * L0 := by
      rw [hE]
      have h4E : 0 ≤ 4 * (Real.exp (2 * a) + 1) := by positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left hLd h4E) hLc hLc0 (by positivity)
    have h5 := mul_le_mul_of_nonneg_left h4 hea.le
    have h6 := mul_le_mul_of_nonneg_right h5 ha
    have h7 := mul_le_mul_of_nonneg_left hP (by positivity : (0 : ℝ) ≤ 2 * a)
    linarith
  have hC1n : 0 ≤ 2 * a * ‖∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 u) t * coverRep38 w t‖ +
      Real.exp a * (4 * (Real.exp (2 * a) + 1) *
        (∫ s in (0 : ℝ)..1, ‖coverRep38 (physicalSobolevDerivative38 1 u) s‖) *
        (∫ t in (0 : ℝ)..1, ‖coverRep38 w t‖)) * a := by positivity
  have t1 : ‖sobolevPointValue 1 u 1‖ ^ 2 * (2 * (Real.exp (2 * a) + 1) * ‖w‖ ^ 2) ≤
      I0 ^ 2 * (2 * E * Bw ^ 2) :=
    mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hpv 2)
      (mul_le_mul_of_nonneg_left hw2 (by positivity)) (by positivity) (by positivity)
  have t2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC1n hC1 2) hS0
  have t3 : Real.exp a ^ 2 * ((∫ s in (0 : ℝ)..1, ‖coverRep38 (physicalSobolevDerivative38 1 u) s‖) *
      ((∫ s in (0 : ℝ)..1, ‖coverRep38 (physicalSobolevDerivative38 1 u) s‖) * ‖w‖ ^ 2)) ≤
      Real.exp a ^ 2 * (D0 * (D0 * Bw ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul hLd (mul_le_mul hLd hw2 (by positivity) hD00) (by positivity) hD00
  linarith

end NlsGge.ThirdConsultation.KSPS012Q2
