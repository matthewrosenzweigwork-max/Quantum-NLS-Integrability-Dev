import Mathlib
import NlsGge.Atomic.G3.G3017
import NlsGge.Atomic.G3.G3021SegmentIdentity
import NlsGge.Atomic.G3.G3021NearBase
import NlsGge.ThirdConsultation.G2.G2073Support1
import NlsGge.Atomic.G2.G2048

                                                                                                   
                                                                                   
                                                                                                                        
                                                                                                           
                                                                                                                         
                                                                                                                             
                                                                                                                 
                                                                                                                        
                                                                                           
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section
namespace G3021N

theorem near_segment_eq (m : ℤ) (φ : PotPair) :
    segment ℝ (nearEnd m φ) (farEnd m φ) = segment ℝ (lamMinus φ m) (lamPlus φ m) := by
  rcases far_eq_or m φ with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
  · rw [h1, h2]
  · rw [h1, h2, segment_symm]

theorem near_beta_segment (n m : ℤ) (hmn : m ≠ n) (φ : PotPair) (hφ : φ ∈ sourceW)
    (hω : nearOmega m φ ≠ 0)
    (hav : ∀ t : ℝ, 0 < t → t ≤ 1 → nearSegPoint m φ t ∉ gapSegments38 φ)
    (hint : IntervalIntegrable (nearDensity n m φ) volume 0 1) :
    offDiagonalBeta n m φ =
      (antiDiscrim φ (muSeq φ m) / canonRoot38 φ (muSeq φ m)) *
        ∫ t in (0 : ℝ)..1, nearDensity n m φ t := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφ
  obtain ⟨S, hS, hode, hbeta⟩ := G3017Aux.beta_eq n m hmn φ hφ
  obtain ⟨_c, _N, _hg, hspec⟩ := isolating_family38 φ hgk
  have hτB : nearEnd m φ ∈ ball (discC φ m) (discR φ m) := near_mem_ball m φ hspec
  have hzB : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      nearEnd m φ + (t : ℂ) * (muSeq φ m - nearEnd m φ) ∈ ball (discC φ m) (discR φ m) := by
    intro t ht
    exact seg_mem (C := discC φ) (R := discR φ) m φ hspec t ht
  have hR : ∀ t : ℝ, 0 < t → t ≤ 1 →
      (φ, nearEnd m φ + (t : ℂ) * (muSeq φ m - nearEnd m φ)) ∈ rootDomain38 :=
    fun t ht ht1 => ⟨hgk, hav t ht ht1⟩
  have hμR : (φ, muSeq φ m) ∈ rootDomain38 := by
    refine ⟨hgk, ?_⟩
    have := hav 1 one_pos le_rfl
    rwa [seg_one] at this
  have hcne : canonRoot38 φ (muSeq φ m) ≠ 0 := canonRoot_ne_zero38 φ hgk _ hμR.2
  have hτ0 : perChar φ (nearEnd m φ) = 0 := near_perChar_zero m φ
  have hne : muSeq φ m ≠ nearEnd m φ := fun h => hω (by unfold nearOmega; rw [h]; ring)
  have hG : ∀ t : ℝ, 0 < t → t ≤ 1 →
      psi n φ (nearEnd m φ + (t : ℂ) * (muSeq φ m - nearEnd m φ)) /
          canonRoot38 φ (nearEnd m φ + (t : ℂ) * (muSeq φ m - nearEnd m φ)) =
        ((normalizedRoot n m φ - (nearEnd m φ + (t : ℂ) * (muSeq φ m - nearEnd m φ))) /
          standardRoot φ m (nearEnd m φ + (t : ℂ) * (muSeq φ m - nearEnd m φ))) *
          betaZeta n m φ (nearEnd m φ + (t : ℂ) * (muSeq φ m - nearEnd m φ)) := by
    intro t ht ht1
    have key := (G2_048 φ hgk (p2Extend38 n (sourceF n φ)) n m hmn _ (hR t ht ht1)).2.2.2
    rw [← normalizedRoot_eq_sigmaOf n m φ hmn] at key
    exact key
  have hI := G3021Aux.seg_ftc φ hgk (nearEnd m φ) (muSeq φ m) hne hR hτ0 S
    (fun w => ((normalizedRoot n m φ - w) / standardRoot φ m w) * betaZeta n m φ w)
    (psi n φ)
    (fun t ht => hS _ (hzB t ht)) (fun t ht => hode _ (hzB t ht)) hG hint
  have hI' : (∫ t in (0 : ℝ)..1, nearDensity n m φ t) =
      canonRoot38 φ (muSeq φ m) * S (muSeq φ m) := hI
  rw [hbeta, hI']
  field_simp

theorem near_seg_avoids (m : ℤ) (φ : PotPair) (hφ : φ ∈ sourceW)
    (hω : nearOmega m φ ≠ 0) (hμ : muSeq φ m ∉ gapSegments38 φ) :
    ∀ t : ℝ, 0 < t → t ≤ 1 → nearSegPoint m φ t ∉ gapSegments38 φ := by
  intro t ht ht1 hz
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφ
  obtain ⟨_c, _N, _hg, hspec⟩ := isolating_family38 φ hgk
  have hzB : nearSegPoint m φ t ∈ ball (discC φ m) (discR φ m) :=
    seg_mem (C := discC φ) (R := discR φ) m φ hspec t ⟨ht.le, ht1⟩
  have hnear := near_le_far m φ
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hz
  by_cases hkm : k = m
  · subst hkm
    rw [← near_segment_eq] at hk
    obtain ⟨a, b, ha, hb, hab, hzab⟩ := hk
    have hzeq : (t : ℂ) * nearOmega k φ = (b : ℂ) * (farEnd k φ - nearEnd k φ) := by
      have h1 : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
      have h2 : a • nearEnd k φ + b • farEnd k φ = nearSegPoint k φ t := hzab
      simp only [Complex.real_smul] at h2
      unfold nearSegPoint at h2
      have ha' : (a : ℂ) = 1 - b := by linear_combination h1
      rw [ha'] at h2
      linear_combination -h2
    by_cases hγ : farEnd k φ - nearEnd k φ = 0
    · rw [hγ, mul_zero] at hzeq
      rcases mul_eq_zero.1 hzeq with h | h
      · exact ht.ne' (Complex.ofReal_eq_zero.1 h)
      · exact hω h
    · set r : ℝ := b / t with hr
      have hrω : nearOmega k φ = (r : ℂ) * (farEnd k φ - nearEnd k φ) := by
        have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
        rw [hr, Complex.ofReal_div]
        field_simp
        linear_combination hzeq
      have hr0 : 0 ≤ r := div_nonneg hb ht.le
      by_cases hr1 : r ≤ 1
      · apply hμ
        refine Set.mem_iUnion.2 ⟨k, ?_⟩
        rw [← near_segment_eq]
        refine ⟨1 - r, r, by linarith, hr0, by ring, ?_⟩
        simp only [Complex.real_smul]
        push_cast
        unfold nearOmega at hrω
        linear_combination (-1 : ℂ) * hrω
      · push_neg at hr1
        have hn1 : ‖muSeq φ k - nearEnd k φ‖ = r * ‖farEnd k φ - nearEnd k φ‖ := by
          have : muSeq φ k - nearEnd k φ = (r : ℂ) * (farEnd k φ - nearEnd k φ) := hrω
          rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
        have hn2 : ‖muSeq φ k - farEnd k φ‖ = (r - 1) * ‖farEnd k φ - nearEnd k φ‖ := by
          have : muSeq φ k - farEnd k φ = ((r - 1 : ℝ) : ℂ) * (farEnd k φ - nearEnd k φ) := by
            push_cast
            unfold nearOmega at hrω
            linear_combination hrω
          rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        have hpos : 0 < ‖farEnd k φ - nearEnd k φ‖ := norm_pos_iff.2 hγ
        rw [hn1, hn2] at hnear
        nlinarith
  · exact closedBall_avoids_other_gaps φ hgk m k hkm _
      (Metric.ball_subset_closedBall hzB) hk

end G3021N
end
end NlsGge.GKDefinitionDesign
