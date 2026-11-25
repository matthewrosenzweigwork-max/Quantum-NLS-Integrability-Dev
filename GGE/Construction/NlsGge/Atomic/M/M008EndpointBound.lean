import Mathlib
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.GK38.XiSqPeriod
import NlsGge.Atomic.LIB.LIB079
import NlsGge.Atomic.M.M008Host
import NlsGge.Atomic.M.M008Loops

                                                                                                                               
                                                                                        
                                                                                                                              
                                                                                                                                   
set_option autoImplicit false
open Set Filter MeasureTheory Topology Metric
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.ThirdConsultation.MContour
noncomputable section

theorem own_endpoint_mem_omitted (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) {e : ℂ}
    (he : e ∈ segment ℝ (lamMinus φ n) (lamPlus φ n)) :
    (φ, e) ∈ a5OmittedRootDomain38 n := by
  refine ⟨hφ, fun m hmn hseg => ?_⟩
  exact Set.disjoint_left.1 ((isolating φ hφ).1 hmn.symm) (own_segment_subset_disc φ hφ n he)
    (own_segment_subset_disc φ hφ m hseg)

theorem domain_mem_rootDomain (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) {z : ℂ}
    (hz : z ∈ discU φ n \ segment ℝ (lamMinus φ n) (lamPlus φ n)) :
    (φ, z) ∈ rootDomain38 := by
  refine ⟨hφ, ?_⟩
  have := gapDiscSeg_domain_subset φ hφ n (by rw [gapDiscSeg_domain]; exact hz)
  exact this

theorem canonRoot_norm_domain (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) {z : ℂ}
    (hz : z ∈ discU φ n \ segment ℝ (lamMinus φ n) (lamPlus φ n)) :
    ‖canonRoot38 φ z‖ = 2 * ‖rootFactor38 n (φ, z)‖ * ‖a5OmittedRootProduct38 n (φ, z)‖ ∧
    ‖rootFactor38 n (φ, z)‖ ^ 2 * (Lib.piN n) ^ 2 = ‖lamMinus φ n - z‖ * ‖lamPlus φ n - z‖ := by
  have hp := domain_mem_rootDomain φ hφ n hz
  constructor
  · have := a5CanonRoot_omitted_factorization38 n (φ, z) hp
    simp only at this
    rw [this, norm_mul, norm_mul]
    simp
  · have h := rootFactor_sq38 n (φ, z) hp
    simp only at h
    have hpi : (Lib.piN n : ℝ) ≠ 0 := Lib.piN_ne_zero n
    have h2 := congrArg norm h
    rw [norm_pow, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] at h2
    have hpi2 : |Lib.piN n| ^ 2 = (Lib.piN n) ^ 2 := sq_abs _
    rw [← hpi2]
    have hpa : 0 < |Lib.piN n| := abs_pos.2 hpi
    rw [eq_div_iff (by positivity)] at h2
    exact h2

theorem omega_endpointBound_aux (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (e e' : ℂ)
    (he : e ∈ segment ℝ (lamMinus φ n) (lamPlus φ n)) (hne : e ≠ e')
    (hsym : ∀ z : ℂ, ‖lamMinus φ n - z‖ * ‖lamPlus φ n - z‖ = ‖z - e‖ * ‖z - e'‖) :
    HasEndpointBound (omega φ) (discU φ n \ segment ℝ (lamMinus φ n) (lamPlus φ n)) e := by
  have hep : (φ, e) ∈ a5OmittedRootDomain38 n := own_endpoint_mem_omitted φ hφ n he
  have hPc : ContinuousAt (fun z : ℂ => a5OmittedRootProduct38 n (φ, z)) e :=
    (AnalyticAt.comp (g := a5OmittedRootProduct38 n) (f := fun w : ℂ => (φ, w))
      (a5OmittedRoot_analytic38 n (φ, e) hep) (analyticAt_const.prod analyticAt_id)).continuousAt
  have hP0 : a5OmittedRootProduct38 n (φ, e) ≠ 0 := a5OmittedRoot_ne_zero38 n (φ, e) hep
  have hDc : ContinuousAt (deriv (discrim φ)) e :=
    ((analyticOnNhd_discrim_z φ).deriv e (mem_univ _)).continuousAt
  set M0 : ℝ := ‖a5OmittedRootProduct38 n (φ, e)‖ with hM0
  have hM0pos : 0 < M0 := norm_pos_iff.2 hP0
  obtain ⟨δ1, hδ1, hP1⟩ := Metric.continuousAt_iff.1 hPc (M0 / 2) (half_pos hM0pos)
  obtain ⟨δ2, hδ2, hD2⟩ := Metric.continuousAt_iff.1 hDc 1 one_pos
  set g : ℝ := ‖e - e'‖ / 2 with hg
  have hgpos : 0 < g := by
    have : 0 < ‖e - e'‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    rw [hg]; linarith
  set pn : ℝ := |Lib.piN n| with hpn
  have hpnpos : 0 < pn := abs_pos.2 (Lib.piN_ne_zero n)
  set m : ℝ := M0 / 2 with hm
  have hmpos : 0 < m := half_pos hM0pos
  set M : ℝ := ‖deriv (discrim φ) e‖ + 1 with hM
  have hMpos : 0 < M := by positivity
  have hsg : 0 < Real.sqrt g := Real.sqrt_pos.2 hgpos
  refine ⟨M * pn / (2 * m * Real.sqrt g), min (min δ1 δ2) g, by positivity, ?_, ?_⟩
  · exact lt_min (lt_min hδ1 hδ2) hgpos
  intro z hz hz0 hzδ
  have hzδ1 : dist z e < δ1 := lt_of_lt_of_le hzδ ((min_le_left _ _).trans (min_le_left _ _))
  have hzδ2 : dist z e < δ2 := lt_of_lt_of_le hzδ ((min_le_left _ _).trans (min_le_right _ _))
  have hzg : dist z e < g := lt_of_lt_of_le hzδ (min_le_right _ _)
  obtain ⟨hcn, hrn⟩ := canonRoot_norm_domain φ hφ n hz
  have hPz : m ≤ ‖a5OmittedRootProduct38 n (φ, z)‖ := by
    have h1 := hP1 hzδ1
    rw [dist_eq_norm] at h1
    have h2 := norm_sub_norm_le (a5OmittedRootProduct38 n (φ, e)) (a5OmittedRootProduct38 n (φ, z))
    rw [norm_sub_rev] at h2
    have : ‖a5OmittedRootProduct38 n (φ, e)‖ - ‖a5OmittedRootProduct38 n (φ, z)‖ < M0 / 2 :=
      lt_of_le_of_lt h2 h1
    rw [hm]; linarith
  have hDz : ‖deriv (discrim φ) z‖ ≤ M := by
    have h1 := hD2 hzδ2
    rw [dist_eq_norm] at h1
    have h2 := norm_sub_norm_le (deriv (discrim φ) z) (deriv (discrim φ) e)
    rw [hM]; linarith
  have hz' : ‖z - e‖ = dist z e := (dist_eq_norm z e).symm
  set d : ℝ := dist z e with hd
  have hdpos : 0 < d := hz0
  set s : ℝ := Real.sqrt d with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hdpos
  have hs2 : s ^ 2 = d := Real.sq_sqrt hdpos.le
  have hzee : g ≤ ‖z - e'‖ := by
    have h1 : ‖e - e'‖ ≤ ‖e - z‖ + ‖z - e'‖ := by
      have := norm_add_le (e - z) (z - e')
      simpa using this
    have h2 : ‖e - z‖ = d := by rw [norm_sub_rev, hz']
    rw [hg]; linarith
  -- lower bound for the rootFactor
  have hrf : s * Real.sqrt g ≤ ‖rootFactor38 n (φ, z)‖ * pn := by
    refine (sq_le_sq₀ (by positivity) (by positivity)).1 ?_
    have h1 : (‖rootFactor38 n (φ, z)‖ * pn) ^ 2 = d * ‖z - e'‖ := by
      rw [mul_pow, hpn, sq_abs, hrn, hsym z, hz']
    rw [h1, mul_pow, Real.sq_sqrt hgpos.le, hs2]
    exact mul_le_mul_of_nonneg_left hzee hdpos.le
  have hcl : 2 * m * (s * Real.sqrt g) / pn ≤ ‖canonRoot38 φ z‖ := by
    rw [hcn]
    have h1 : s * Real.sqrt g / pn ≤ ‖rootFactor38 n (φ, z)‖ := by
      rw [div_le_iff₀ hpnpos]; exact hrf
    have h2 : 2 * m * (s * Real.sqrt g / pn) ≤ 2 * ‖rootFactor38 n (φ, z)‖ * ‖a5OmittedRootProduct38 n (φ, z)‖ := by
      have h3 : m * (s * Real.sqrt g / pn) ≤ ‖a5OmittedRootProduct38 n (φ, z)‖ * ‖rootFactor38 n (φ, z)‖ :=
        mul_le_mul hPz h1 (by positivity) (norm_nonneg _)
      nlinarith [h3]
    calc 2 * m * (s * Real.sqrt g) / pn = 2 * m * (s * Real.sqrt g / pn) := by ring
      _ ≤ _ := h2
  show ‖deriv (discrim φ) z / canonRoot38 φ z‖ ≤ _
  rw [norm_div]
  calc ‖deriv (discrim φ) z‖ / ‖canonRoot38 φ z‖ ≤ M / (2 * m * (s * Real.sqrt g) / pn) :=
        div_le_div₀ hMpos.le hDz (by positivity) hcl
    _ = M * pn / (2 * m * Real.sqrt g) / s := by field_simp

/-- R4a: the square-root bound of `omega` at both endpoints of an open own gap. -/
theorem omega_endpointBound (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (hne : lamMinus φ n ≠ lamPlus φ n) :
    HasEndpointBound (omega φ) (discU φ n \ segment ℝ (lamMinus φ n) (lamPlus φ n)) (lamMinus φ n) ∧
    HasEndpointBound (omega φ) (discU φ n \ segment ℝ (lamMinus φ n) (lamPlus φ n)) (lamPlus φ n) :=
  ⟨omega_endpointBound_aux φ hφ n _ _ (left_mem_segment ℝ _ _) hne
      (fun z => by rw [norm_sub_rev z (lamMinus φ n), norm_sub_rev z (lamPlus φ n)]),
   omega_endpointBound_aux φ hφ n _ _ (right_mem_segment ℝ _ _) hne.symm
      (fun z => by rw [norm_sub_rev z (lamMinus φ n), norm_sub_rev z (lamPlus φ n), mul_comm])⟩

end
end NlsGge.ThirdConsultation.MContour
