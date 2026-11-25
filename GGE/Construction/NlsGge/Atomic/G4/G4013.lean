import Mathlib
import NlsGge.Atomic.G2.G2072
import NlsGge.Atomic.G2.G2074
import NlsGge.Atomic.G2.G2075
import NlsGge.Atomic.G2.G2019
import NlsGge.Atomic.G2.G2046
import NlsGge.ThirdConsultation.G2.G2073Support1
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.GK38.XiSqOmittedRoot
import NlsGge.GK38.StdRootBranchesProducts
import NlsGge.GK38.StdRootBranchesFactors
import NlsGge.GK38.StdRootBranchesScalar
import NlsGge.GK38.TauGamma
import NlsGge.GK38.TauGammaCircleMoments
import NlsGge.GK38.PeriodicLabellingFreeLabels
import NlsGge.GK38.PairPotential
import NlsGge.GK38.ContourAction
import NlsGge.GK38.IsolatingTopology
import NlsGge.Atomic.G4.G4NormalizedHost

                                                                                                    
                                                                                                
                                                                                                                     
                                    
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G4013 (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW)
    (lam : ℂ) (hlam : lam ∈ Metric.ball (discC φ n) (discR φ n))
    (hcut : lam ∉ gapSegment φ n) :
  canonRoot38 φ lam ≠ 0 ∧ localRoot n φ lam ≠ 0 ∧
  p6PsiNumerator38 n (sourceF n) φ lam / canonRoot38 φ lam =
    Complex.I * normalizedZeta n φ lam / localRoot n φ lam ∧
  gapContourMean n φ (normalizedZeta n φ) = 1 ∧
  (∀ z ∈ Metric.ball (discC (0 : PotPair) n) (discR (0 : PotPair) n),
    normalizedZeta n 0 z = 1) := by
  have hφW : φ ∈ sourceW := sourceFamily.V_W hφ
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφW
  have hR0 : (0 : ℝ) ≤ discR φ n := (isolating_radius_pos38 (isolating_family38 φ hgk) n).le
  have hpi : (Lib.piN n : ℂ) ≠ 0 := by exact_mod_cast Lib.piN_ne_zero n
  have hother : ∀ lam' ∈ Metric.closedBall (discC φ n) (discR φ n), ∀ k : ℤ, k ≠ n →
      lam' ∉ segment ℝ (lamMinus φ k) (lamPlus φ k) :=
    fun lam' hlam' k hk => closedBall_avoids_other_gaps φ hgk n k hk lam' hlam'
  have hnotgap : ∀ lam' ∈ Metric.closedBall (discC φ n) (discR φ n), lam' ∉ gapSegment φ n →
      lam' ∉ gapSegments38 φ := by
    intro lam' hlam' hc hmem
    simp only [gapSegments38, Set.mem_iUnion] at hmem
    obtain ⟨k, hk⟩ := hmem
    by_cases hkn : k = n
    · rw [hkn] at hk
      exact hc hk
    · exact hother lam' hlam' k hkn hk
  have hRmem : ∀ lam' ∈ Metric.closedBall (discC φ n) (discR φ n), lam' ∉ gapSegment φ n →
      (φ, lam') ∈ rootDomain38 := by
    intro lam' hlam' hc
    show φ ∈ gkW ∧ lam' ∉ gapSegments38 φ
    exact ⟨hgk, hnotgap lam' hlam' hc⟩
  have hOmem : ∀ lam' ∈ Metric.closedBall (discC φ n) (discR φ n),
      (φ, lam') ∈ a5OmittedRootDomain38 n := by
    intro lam' hlam'
    show φ ∈ gkW ∧ ∀ m : ℤ, m ≠ n → lam' ∉ segment ℝ (lamMinus φ m) (lamPlus φ m)
    exact ⟨hgk, fun m hm => hother lam' hlam' m hm⟩
  have hwfac : ∀ lam' : ℂ, localRoot n φ lam' = (Lib.piN n : ℂ) * rootFactor38 n (φ, lam') := by
    intro lam'
    unfold localRoot standardRoot rootFactor38
    dsimp only
    field_simp
  have hid : ∀ lam' ∈ Metric.closedBall (discC φ n) (discR φ n), lam' ∉ gapSegment φ n →
      p6PsiNumerator38 n (sourceF n) φ lam' / canonRoot38 φ lam' =
        Complex.I * normalizedZeta n φ lam' / localRoot n φ lam' := by
    intro lam' hlam' hc
    have hR := hRmem lam' hlam' hc
    have hO := hOmem lam' hlam'
    have hfac : canonRoot38 φ lam' =
        2 * Complex.I * rootFactor38 n (φ, lam') * a5OmittedRootProduct38 n (φ, lam') :=
      a5CanonRoot_omitted_factorization38 n (φ, lam') hR
    have hQ : a5OmittedRootProduct38 n (φ, lam') ≠ 0 := a5OmittedRoot_ne_zero38 n (φ, lam') hO
    have hRf : rootFactor38 n (φ, lam') ≠ 0 := rootFactor_ne_zero38 n (φ, lam') hR
    have hpsi : p6PsiNumerator38 n (sourceF n) φ lam' =
        -2 * Lib.omitProd n (p2Extend38 n (sourceF n φ)) lam' := rfl
    have hK : normalizedZeta n φ lam' =
        (Lib.piN n : ℂ) * Lib.omitProd n (p2Extend38 n (sourceF n φ)) lam' /
          a5OmittedRootProduct38 n (φ, lam') := rfl
    have h2 : (-2 : ℂ) = 2 * Complex.I * Complex.I := by
      linear_combination (-2 : ℂ) * Complex.I_mul_I
    rw [hpsi, hfac, hK, hwfac lam', h2]
    field_simp
    try ring
  have hsph : ∀ lam' ∈ Metric.sphere (discC φ n) (discR φ n),
      normalizedZeta n φ lam' / localRoot n φ lam' =
        -Complex.I * (p6PsiNumerator38 n (sourceF n) φ lam' / canonRoot38 φ lam') := by
    intro lam' hlam'
    have hc : lam' ∉ gapSegment φ n := sphere_avoids_own_gap φ hgk n lam' hlam'
    rw [hid lam' (Metric.sphere_subset_closedBall hlam') hc]
    linear_combination (normalizedZeta n φ lam' / localRoot n φ lam') * Complex.I_mul_I
  have hEq : Set.EqOn (fun lam' => normalizedZeta n φ lam' / localRoot n φ lam')
      (fun lam' => -Complex.I * (p6PsiNumerator38 n (sourceF n) φ lam' / canonRoot38 φ lam'))
      (Metric.sphere (discC φ n) (discR φ n)) := by
    intro lam' hlam'
    exact hsph lam' hlam'
  have hper : circleIntegral (fun lam' => p6PsiNumerator38 n (sourceF n) φ lam' / canonRoot38 φ lam')
      (discC φ n) (discR φ n) = 2 * (Real.pi : ℂ) := (G2_072 φ hφW n).2
  have hcirc : circleIntegral (fun lam' => normalizedZeta n φ lam' / localRoot n φ lam')
      (discC φ n) (discR φ n) = -Complex.I * (2 * (Real.pi : ℂ)) := by
    rw [circleIntegral.integral_congr hR0 hEq, circleIntegral.integral_const_mul, hper]
  have hgap : gapContourMean n φ (normalizedZeta n φ) = 1 := by
    unfold gapContourMean
    rw [hcirc]
    have hne : (-2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      have hpi' : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero (by norm_num) hpi') Complex.I_ne_zero
    rw [show -Complex.I * (2 * (Real.pi : ℂ)) = -2 * (Real.pi : ℂ) * Complex.I by ring]
    exact inv_mul_cancel₀ hne
  have h0W : (0 : PotPair) ∈ sourceW := by
    have h : realSlice (0 : PhysicalL2) ∈ sourceW := sourceFamily.W_real ⟨0, rfl⟩
    rwa [realSlice_zero] at h
  have hg0 : ∀ m : ℤ, gamma2 (0 : PotPair) m = 0 := fun m => by
    rw [gamma2_value38 (0 : PotPair) free_mem_gkW m, lamPlus_zero38, lamMinus_zero38]
    ring
  obtain ⟨_V0, _, h0V, _, _, _, hA0⟩ := G2_074 (0 : PotPair) h0W
  have hfree : ∀ m : ℤ, m ≠ n → normalizedRoot n m (0 : PotPair) = tauN 0 m := by
    intro m hm
    obtain ⟨A0, hfac0, _, _⟩ := hA0 (0 : PotPair) h0V n
    have h : normalizedRoot n m (0 : PotPair) = tauN 0 m + gamma2 0 m * A0 ⟨m, hm⟩ := hfac0 ⟨m, hm⟩
    rw [h, hg0 m, zero_mul, add_zero]
  have hsig : ∀ m : ℤ, m ≠ n →
      Lib.sigmaOf (p2Extend38 n (sourceF n (0 : PotPair))) m = tauN 0 m := fun m hm =>
    ((g2075_root_eq_sigma n m (0 : PotPair) hm).symm).trans (hfree m hm)
  have hzero : ∀ z ∈ Metric.ball (discC (0 : PotPair) n) (discR (0 : PotPair) n),
      normalizedZeta n 0 z = 1 := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (discC (0 : PotPair) n) (discR (0 : PotPair) n) :=
      Metric.ball_subset_closedBall hz
    have hO : ((0 : PotPair), z) ∈ a5OmittedRootDomain38 n := by
      show (0 : PotPair) ∈ gkW ∧ ∀ m : ℤ, m ≠ n → z ∉ segment ℝ (lamMinus (0 : PotPair) m) (lamPlus (0 : PotPair) m)
      exact ⟨free_mem_gkW, fun m hm => closedBall_avoids_other_gaps 0 free_mem_gkW n m hm z hz'⟩
    have hQ : a5OmittedRootProduct38 n ((0 : PotPair), z) ≠ 0 := a5OmittedRoot_ne_zero38 n _ hO
    have hfun : (fun m : ℤ => if m = n then (1 : ℂ)
        else Lib.prodFactor (Lib.sigmaOf (p2Extend38 n (sourceF n (0 : PotPair)))) z m)
        = (fun m : ℤ => a5OmittedRootFactor38 n m ((0 : PotPair), z)) := by
      funext m
      by_cases hm : m = n
      · simp [a5OmittedRootFactor38, hm]
      · have hr : rootFactor38 m ((0 : PotPair), z) = (tauN 0 m - z) / (Lib.piN m : ℂ) := by
          unfold rootFactor38
          dsimp only
          rw [hg0 m, stdRoot_degenerate38]
        show (if m = n then (1 : ℂ)
          else Lib.prodFactor (Lib.sigmaOf (p2Extend38 n (sourceF n (0 : PotPair)))) z m)
          = (if m = n then (1 : ℂ) else rootFactor38 m ((0 : PotPair), z))
        rw [if_neg hm, if_neg hm, hr]
        unfold Lib.prodFactor
        rw [hsig m hm]
    have hP : (Lib.piN n : ℂ) * Lib.omitProd n (p2Extend38 n (sourceF n (0 : PotPair))) z =
        a5OmittedRootProduct38 n ((0 : PotPair), z) := by
      unfold Lib.omitProd a5OmittedRootProduct38
      rw [← hfun, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
    show (Lib.piN n : ℂ) * Lib.omitProd n (p2Extend38 n (sourceF n (0 : PotPair))) z /
      a5OmittedRootProduct38 n ((0 : PotPair), z) = 1
    rw [hP, div_self hQ]
  have hlamc : lam ∈ Metric.closedBall (discC φ n) (discR φ n) := Metric.ball_subset_closedBall hlam
  refine ⟨canonRoot_ne_zero38 φ hgk lam (hnotgap lam hlamc hcut), ?_, hid lam hlamc hcut, hgap, hzero⟩
  rw [hwfac lam]
  exact mul_ne_zero hpi (rootFactor_ne_zero38 n (φ, lam) (hRmem lam hlamc hcut))

end
end NlsGge.GKDefinitionDesign
