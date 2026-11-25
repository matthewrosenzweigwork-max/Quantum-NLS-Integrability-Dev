import NlsGge.Atomic.G2.G2028
import NlsGge.ThirdConsultation.G2.Reparam032J
import NlsGge.ThirdConsultation.G2.Reparam032G
import NlsGge.ThirdConsultation.G2.Reparam032H
import NlsGge.ThirdConsultation.G2.Reparam032F
import NlsGge.ThirdConsultation.G2.G2073Support1
import NlsGge.ThirdConsultation.G2.G2037Host
import NlsGge.ThirdConsultation.G2.G2037Support1
import NlsGge.ThirdConsultation.G2.G2037Support2

                                                                                          
                                                                                      
                                                                                       
                                                                                            
                                                                                              
                                                                                              
                                                                                               
                                                                                     
set_option autoImplicit false
                                                                                              
-- CircleIntegrable step `hci` before the apply032 identity. Statement unchanged.

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign.G2032Homo NlsGge.GKDefinitionDesign.G2032Ellipse

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Periodic FTC for a shifted ellipse integrand: the integral over one period vanishes. -/
theorem g2037s3_periodic_ftc (ω F : ℂ → ℂ) (τ : ℂ) (e : ℝ → ℂ) (he : ContDiff ℝ 2 e)
    (hper : e (2 * Real.pi) = e 0) (hω : ∀ t : ℝ, HasDerivAt ω (F (τ + e t)) (τ + e t))
    (hF : Continuous fun t : ℝ => F (τ + e t)) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), F (τ + e t) * deriv e t = 0 := by
  have hD : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ω (τ + e s)) (F (τ + e t) * deriv e t) t := by
    intro t
    have hE : HasDerivAt e (deriv e t) t :=
      ((he.differentiable (by norm_num)) t).hasDerivAt
    have hE' : HasDerivAt (fun s : ℝ => τ + e s) (deriv e t) t := hE.const_add τ
    have h := HasDerivAt.scomp t (hω t) hE'
    rw [smul_eq_mul, mul_comm] at h
    exact h
  have hcont : Continuous fun t : ℝ => F (τ + e t) * deriv e t :=
    hF.mul (he.continuous_deriv (by norm_num))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hD t)
    (hcont.intervalIntegrable 0 (2 * Real.pi))]
  simp [hper]

/-- The ellipse has period `2π` in its parameter, so its endpoints coincide. -/
theorem g2037s3_ellF_two_pi (p q : ℂ) :
    ellF p q (2 * Real.pi) = ellF p q 0 := by
  have h := ellF_add_two_pi p q 0
  rw [zero_add] at h
  exact h

/-- M1 (ellipse proximity): the ellipse is within `‖γ‖(ρ-1)/2` of `(γ/2) cos t` for `ρ > 1`. -/
theorem g2037s3_ellF_near (γ : ℂ) (ρ : ℝ) (hρ : 1 < ρ) (t : ℝ) :
    ‖ellF (pOf γ ρ) (qOf γ ρ) t - γ / 2 * (Real.cos t : ℂ)‖ ≤ ‖γ‖ * (ρ - 1) / 2 := by
  rw [ellF_sub_cos γ ρ t, norm_mul]
  have h4 : ‖γ / 4‖ = ‖γ‖ / 4 := by
    rw [norm_div]
    norm_num
  rw [h4]
  have hρinv : ρ⁻¹ < ρ := by
    have h1 : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
    have h2 : 0 < ρ⁻¹ := inv_pos.mpr (by linarith)
    nlinarith
  have hρinv2 : 2 - ρ ≤ ρ⁻¹ := by
    have h1 : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
    have h2 : 0 < ρ⁻¹ := inv_pos.mpr (by linarith)
    nlinarith [sq_nonneg (ρ - 1)]
  have hX : ‖((ρ - 1 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) +
      ((ρ⁻¹ - 1 : ℝ) : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)‖ ≤ 2 * (ρ - 1) := by
    have e1 : ‖Complex.exp ((t : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I t
    have e2 : ‖Complex.exp (((-t : ℝ) : ℂ) * Complex.I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I (-t)
    calc ‖((ρ - 1 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) +
          ((ρ⁻¹ - 1 : ℝ) : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)‖
        ≤ ‖((ρ - 1 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I)‖ +
          ‖((ρ⁻¹ - 1 : ℝ) : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)‖ := norm_add_le _ _
      _ = |ρ - 1| + |ρ⁻¹ - 1| := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, e1, e2, mul_one, mul_one]
      _ ≤ 2 * (ρ - 1) := by
          have ha : |ρ - 1| = ρ - 1 := abs_of_nonneg (by linarith)
          have hb : |ρ⁻¹ - 1| ≤ ρ - 1 := abs_le.mpr ⟨by linarith, by linarith⟩
          linarith
  calc ‖γ‖ / 4 * ‖((ρ - 1 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) +
          ((ρ⁻¹ - 1 : ℝ) : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)‖
      ≤ ‖γ‖ / 4 * (2 * (ρ - 1)) := mul_le_mul_of_nonneg_left hX (by positivity)
    _ = ‖γ‖ * (ρ - 1) / 2 := by ring

/-- M2 (ellipse off own gap): for `ρ > 1` the ellipse point avoids the own gap segment. -/
theorem g2037s3_own_free (τ C γ : ℂ) (R ρ : ℝ) (hγ : γ ≠ 0) (hρ : 1 < ρ)
    (hw : (τ - C).re ^ 2 + (τ - C).im ^ 2 < R ^ 2)
    (hA : ‖(τ - C) + γ / 2‖ < R) (hB : ‖(τ - C) - γ / 2‖ < R) (t : ℝ) :
    τ + ellF (pOf γ ρ) (qOf γ ρ) t ∉ segment ℝ (τ - γ / 2) (τ + γ / 2) := by
  have hA' : Complex.normSq ((τ - C) + γ / 2) < R ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ((τ - C) + γ / 2)]
  have hB' : Complex.normSq ((τ - C) - γ / 2) < R ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ((τ - C) - γ / 2)]
  have h := homH_not_mem_cut τ C γ R ρ 1 t hγ hρ hw hA' hB' zero_le_one le_rfl
  rwa [homH_one τ C γ R ρ hγ hρ t] at h

/-- Points `τ + x γ/2` with `x ∈ [-1,1]` lie on the segment `[τ - γ/2, τ + γ/2]`. -/
theorem g2037s3_seg_pt (τ γ : ℂ) (x : ℝ) (h1 : -1 ≤ x) (h2 : x ≤ 1) :
    τ + (x : ℂ) * (γ / 2) ∈ segment ℝ (τ - γ / 2) (τ + γ / 2) := by
  refine ⟨(1 - x) / 2, (1 + x) / 2, by linarith, by linarith, by ring, ?_⟩
  rw [Complex.real_smul, Complex.real_smul]
  push_cast
  ring

/-- The finite product is analytic at a point off every gap segment indexed by `S`. -/
theorem g2037s3_fgd_analyticAt (u : PhysicalL2) (S : Finset ℤ) (z : ℂ)
    (hz : ∀ k ∈ S, z ∉ segment ℝ (lamMinus (realSlice u) k) (lamPlus (realSlice u) k)) :
    AnalyticAt ℂ (finiteGapDifferential u S) z := by
  have hprod : AnalyticAt ℂ (fun w : ℂ => ∏ n ∈ S,
      (lamDot (realSlice u) n - w) / standardRoot (realSlice u) n w) z := by
    apply Finset.analyticAt_fun_prod
    intro n hn
    obtain ⟨hA, hne⟩ := g2037s1_factor (realSlice u) (realSlice_mem_gkW u) n z (hz n hn)
    exact (analyticAt_const.sub analyticAt_id).div hA hne
  unfold finiteGapDifferential
  exact analyticAt_const.mul hprod

/-- Avoidance: a point of the tube of disc `n` misses every gap segment `k`, given the own gap. -/
theorem g2037s3_avoid (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ) (hg : IsolatingGeometry38 C R c N)
    (φ : PotPair) (hspec : IsolatingSpectral38 φ C R) (n k : ℤ) (z : ℂ)
    (hz : dist z (C n) < R n + c⁻¹ / 2)
    (hown : k = n → z ∉ segment ℝ (lamMinus φ n) (lamPlus φ n)) :
    z ∉ segment ℝ (lamMinus φ k) (lamPlus φ k) := by
  by_cases hkn : k = n
  · subst hkn
    exact hown rfl
  · exact g2073s1_tube_avoids C R c N hg φ hspec n k hkn z hz

/-- Conjunct (4c): zero circle period on the isolating circle of every open gap index n ∈ S. -/
theorem g2037s3_zero_period_open (u : PhysicalL2) (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔ actualGapLowerAllE02_38 u n ≠ actualGapUpperAllE02_38 u n)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hCR : IsolatingFamily38 (realSlice u) C R) (n : ℤ) (hn : n ∈ S) :
    circleIntegral (finiteGapDifferential u S) (C n) (R n) = 0 := by
  -- F2: integrability on the isolating circle, established before the apply032 identity
  have hci : CircleIntegrable (finiteGapDifferential u S) (C n) (R n) :=
    g2037s1_circleIntegrable u S C R hCR n
  obtain ⟨c, N, hg, hspec⟩ := hCR
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hg.2.2.1
  have hcpos : 0 < c⁻¹ / 2 := by
    have := inv_pos.2 hc0
    linarith
  have hφ : realSlice u ∈ gkW := realSlice_mem_gkW u
  have hne : actualGapLowerAllE02_38 u n ≠ actualGapUpperAllE02_38 u n := (hS n).1 hn
  obtain ⟨hp, hm⟩ := lamPlus_real u n
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℂ, γ = lamPlus (realSlice u) n - lamMinus (realSlice u) n :=
    ⟨_, rfl⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℂ, τ = (lamPlus (realSlice u) n + lamMinus (realSlice u) n) / 2 :=
    ⟨_, rfl⟩
  have hlp : lamPlus (realSlice u) n = τ + γ / 2 := by rw [hτdef, hγdef]; ring
  have hlm : lamMinus (realSlice u) n = τ - γ / 2 := by rw [hτdef, hγdef]; ring
  have hγ : γ ≠ 0 := by
    intro h0
    apply hne
    have h1 : lamPlus (realSlice u) n = lamMinus (realSlice u) n := by
      rw [hlp, hlm, h0]; ring
    rw [hp, hm] at h1
    exact_mod_cast h1.symm
  -- the midpoint τ lies in the isolating disc
  have hmid : τ ∈ segment ℝ (lamMinus (realSlice u) n) (lamPlus (realSlice u) n) := by
    rw [hlp, hlm]
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have hτb : dist τ (C n) < R n := mem_ball.1 ((hspec.1 n).1 hmid)
  have hw : (τ - C n).re ^ 2 + (τ - C n).im ^ 2 < R n ^ 2 := by
    have hn' : ‖τ - C n‖ < R n := by rw [← dist_eq_norm]; exact hτb
    have h1 : (τ - C n).re ^ 2 + (τ - C n).im ^ 2 = ‖τ - C n‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [h1]
    nlinarith [norm_nonneg (τ - C n)]
  have hA : ‖(τ - C n) + γ / 2‖ < R n := by
    have hlpb : dist (lamPlus (realSlice u) n) (C n) < R n :=
      mem_ball.1 ((hspec.1 n).1 (right_mem_segment ℝ _ _))
    rw [dist_eq_norm, hlp] at hlpb
    have e : (τ - C n) + γ / 2 = τ + γ / 2 - C n := by ring
    rw [e]
    exact hlpb
  have hB : ‖(τ - C n) - γ / 2‖ < R n := by
    have hlmb : dist (lamMinus (realSlice u) n) (C n) < R n :=
      mem_ball.1 ((hspec.1 n).1 (left_mem_segment ℝ _ _))
    rw [dist_eq_norm, hlm] at hlmb
    have e : (τ - C n) - γ / 2 = τ - γ / 2 - C n := by ring
    rw [e]
    exact hlmb
  -- analyticity of the integrand on the closed disc off the own gap (for apply032)
  have hzC : ∀ z ∈ Metric.closedBall (C n) (R n), dist z (C n) < R n + c⁻¹ / 2 := by
    intro z hz
    have := mem_closedBall.1 hz
    linarith
  have hf : ∀ z ∈ Metric.closedBall (C n) (R n), z ∉ segment ℝ (τ - γ / 2) (τ + γ / 2) →
      AnalyticAt ℂ (finiteGapDifferential u S) z := by
    intro z hz hzseg
    apply g2037s3_fgd_analyticAt u S z
    intro k _
    apply g2037s3_avoid C R c N hg (realSlice u) hspec n k z (hzC z hz)
    intro _
    rw [hlm, hlp]
    exact hzseg
  obtain ⟨ρ0, hρ0, hint⟩ := G2032Apply.apply032 τ (C n) γ (R n) hγ hA hB
    (finiteGapDifferential u S) hf
  obtain ⟨ρb, hρb, hball⟩ := rho_choice (τ - C n) γ (R n) hγ hA hB
  -- the local primitive from G2_028
  obtain ⟨V, hVo, hφV, -, U, hUo, hKU, -, -, hder⟩ := G2_028 u n
  have hKc : IsCompact (gapSegment (realSlice u) n) := G2028Aux.isCompact_gapSegment _ _
  obtain ⟨ε, hε, hth⟩ := hKc.exists_thickening_subset_open hUo hKU
  -- choice of ρ
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (min (ρ0 - 1) (ρb - 1)) (ε / (‖γ‖ + 1)) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min (by linarith) (by linarith)) (div_pos hε (by positivity))
  have hδ1 : δ ≤ ρ0 - 1 := by
    rw [hδdef]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ2 : δ ≤ ρb - 1 := by
    rw [hδdef]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ3 : δ * (‖γ‖ + 1) ≤ ε := by
    have h : δ ≤ ε / (‖γ‖ + 1) := by
      rw [hδdef]
      exact min_le_right _ _
    exact (le_div_iff₀ (by positivity)).1 h
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = 1 + δ := ⟨_, rfl⟩
  have hρ1 : 1 < ρ := by rw [hρdef]; linarith
  have hρ0' : ρ ≤ ρ0 := by rw [hρdef]; linarith
  have hρb' : ρ ≤ ρb := by rw [hρdef]; linarith
  have hsmall : ‖γ‖ * (ρ - 1) / 2 < ε := by
    rw [hρdef, show 1 + δ - 1 = δ by ring]
    nlinarith [norm_nonneg γ]
  -- the ellipse lies in U
  have hEU : ∀ t : ℝ, τ + ellF (pOf γ ρ) (qOf γ ρ) t ∈ U := by
    intro t
    apply hth
    rw [Metric.mem_thickening_iff]
    refine ⟨τ + (Real.cos t : ℂ) * (γ / 2), ?_, ?_⟩
    · unfold gapSegment
      rw [hlm, hlp]
      exact g2037s3_seg_pt τ γ (Real.cos t) (Real.neg_one_le_cos t) (Real.cos_le_one t)
    · rw [dist_eq_norm]
      have e : τ + ellF (pOf γ ρ) (qOf γ ρ) t - (τ + (Real.cos t : ℂ) * (γ / 2)) =
          ellF (pOf γ ρ) (qOf γ ρ) t - γ / 2 * (Real.cos t : ℂ) := by ring
      rw [e]
      exact lt_of_le_of_lt (g2037s3_ellF_near γ ρ hρ1 t) hsmall
  -- the ellipse lies in the isolating disc and off every gap segment
  have hdist : ∀ t : ℝ, dist (τ + ellF (pOf γ ρ) (qOf γ ρ) t) (C n) < R n + c⁻¹ / 2 := by
    intro t
    have h1 := hball ρ hρ1 hρb' t
    have e : τ + ellF (pOf γ ρ) (qOf γ ρ) t - C n = (τ - C n) + ellF (pOf γ ρ) (qOf γ ρ) t := by
      ring
    rw [dist_eq_norm, e]
    linarith
  have hoff : ∀ t : ℝ, ∀ k : ℤ,
      τ + ellF (pOf γ ρ) (qOf γ ρ) t ∉ segment ℝ (lamMinus (realSlice u) k) (lamPlus (realSlice u) k) := by
    intro t k
    apply g2037s3_avoid C R c N hg (realSlice u) hspec n k (τ + ellF (pOf γ ρ) (qOf γ ρ) t)
      (hdist t)
    intro _
    rw [hlm, hlp]
    exact g2037s3_own_free τ (C n) γ (R n) ρ hγ hρ1 hw hA hB t
  -- the derivative of the primitive along the ellipse
  have hderiv : ∀ t : ℝ, HasDerivAt (localLogDiscriminant n (realSlice u))
      (finiteGapDifferential u S (τ + ellF (pOf γ ρ) (qOf γ ρ) t))
      (τ + ellF (pOf γ ρ) (qOf γ ρ) t) := by
    intro t
    have hz : (realSlice u, τ + ellF (pOf γ ρ) (qOf γ ρ) t) ∈ rootDomain38 := by
      refine ⟨hφ, ?_⟩
      intro hmem
      simp only [gapSegments38, Set.mem_iUnion] at hmem
      obtain ⟨k, hk⟩ := hmem
      exact hoff t k hk
    have h := (hder (realSlice u) hφV (τ + ellF (pOf γ ρ) (qOf γ ρ) t) (hEU t) hz).2
    rw [g2037s2_deriv_eq_fgd u S hS _ hz] at h
    exact h
  have hFc : Continuous fun t : ℝ => finiteGapDifferential u S (τ + ellF (pOf γ ρ) (qOf γ ρ) t) := by
    apply continuous_iff_continuousAt.2
    intro t
    have hanal := g2037s3_fgd_analyticAt u S (τ + ellF (pOf γ ρ) (qOf γ ρ) t)
      (fun k _ => hoff t k)
    exact ContinuousAt.comp (f := fun s : ℝ => τ + ellF (pOf γ ρ) (qOf γ ρ) s)
      hanal.continuousAt (continuous_const.add (ellF_contDiff _ _).continuous).continuousAt
  have hcirc := hint ρ hρ1 hρ0'
  rw [hcirc]
  exact g2037s3_periodic_ftc (localLogDiscriminant n (realSlice u)) (finiteGapDifferential u S)
    τ (fun t : ℝ => ellF (pOf γ ρ) (qOf γ ρ) t) (ellF_contDiff _ _)
    (g2037s3_ellF_two_pi _ _) hderiv hFc

end
end NlsGge.GKDefinitionDesign
