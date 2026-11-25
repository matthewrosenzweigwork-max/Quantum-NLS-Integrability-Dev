import Mathlib
import NlsGge.Atomic.G3.G3017
import NlsGge.Atomic.G3.G3021NearBase
import NlsGge.Atomic.G3.G3021NearInitial
import NlsGge.Atomic.G3.G3021NearFinal
import NlsGge.Atomic.G3.G3021NearBeta

                                                                              
                                                                           
                                                                                                                                  
                                                                                                                     
                                                                                                                       
                         
                                                                                                                                      
                                                                                                                                       
                                                                                         
                                                                                                                                  
                                                                                                                                            
                                                                         
                                             
                                    
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38
open NlsGge.GKDefinitionDesign

namespace NlsGge.GKDefinitionDesign
noncomputable section
namespace G3021Main

theorem exists_eps (C M η : ℝ) (hC : 0 < C) (hM : 0 ≤ M) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ C * Real.sqrt ε ≤ η / 4 ∧ M * ε ≤ η / 4 := by
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (1 / 2) (min ((η / (4 * C)) ^ 2) (η / (4 * (M + 1)))) := ⟨_, rfl⟩
  have h1 : 0 < η / (4 * C) := div_pos hη (by linarith)
  have h2 : 0 < η / (4 * (M + 1)) := div_pos hη (by linarith)
  have hpos : 0 < ε := by
    rw [hε]
    exact lt_min (by norm_num) (lt_min (pow_pos h1 2) h2)
  have hle1 : ε ≤ 1 / 2 := by rw [hε]; exact min_le_left _ _
  have hle2 : ε ≤ (η / (4 * C)) ^ 2 := by
    rw [hε]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hle3 : ε ≤ η / (4 * (M + 1)) := by
    rw [hε]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨ε, hpos, by linarith, ?_, ?_⟩
  · have hs : Real.sqrt ε ≤ η / (4 * C) := by
      calc Real.sqrt ε ≤ Real.sqrt ((η / (4 * C)) ^ 2) := Real.sqrt_le_sqrt hle2
        _ = η / (4 * C) := Real.sqrt_sq h1.le
    calc C * Real.sqrt ε ≤ C * (η / (4 * C)) := mul_le_mul_of_nonneg_left hs hC.le
      _ = η / 4 := by field_simp
  · have : M * ε ≤ M * (η / (4 * (M + 1))) := mul_le_mul_of_nonneg_left hle3 hM
    have h3 : M * (η / (4 * (M + 1))) ≤ η / 4 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith

theorem seq_key (n m : ℤ) (hmn : m ≠ n) (φ0 : PotPair)
    (hφ0 : φ0 ∈ collapsedSet m \ endpointSet m) (v : ℕ → PotPair)
    (hv : Tendsto v atTop (𝓝 φ0)) :
    Tendsto (fun j => offDiagonalBeta n m (v j)) atTop (𝓝 (offDiagonalBeta n m φ0)) := by
  have hcoll : φ0 ∈ collapsedSet m := hφ0.1
  have hnot : φ0 ∉ endpointSet m := hφ0.2
  have hW0 : φ0 ∈ sourceW := hcoll.1
  have hgap0 : gamma2 φ0 m = 0 := hcoll.2
  obtain ⟨hgk, hP, hneT, hav0, hroot, hcne⟩ := G3017Aux.mu_facts m φ0 hφ0
  obtain ⟨V, hVo, hφV, hVW, hV⟩ := G3017Aux.local_ratio m φ0 hW0 hroot
  obtain ⟨ε0, hε0⟩ : ∃ ε0 : ℂ, ε0 = antiDiscrim φ0 (muSeq φ0 m) / canonRoot38 φ0 (muSeq φ0 m) :=
    ⟨_, rfl⟩
  have hβ0 : offDiagonalBeta n m φ0 = ε0 * collapsedBetaFinalSegment n m φ0 0 := by
    rw [hε0]
    exact (G3_017 n m hmn φ0 hφ0).2.2.2.1
  obtain ⟨C, d, J, hC, hd, hJ⟩ := near_initial_bound n m hmn v φ0 hcoll hnot hv
  -- the collapsed integrand is continuous, hence bounded, on [0,1]
  obtain ⟨U, hUo, hφ0U, hUgk, Cr, Rr, c, N, hg, hspecU⟩ := g2019_leaf_family φ0 hgk
  have hnv : nearEnd m φ0 = tauN φ0 m := G3021N.near_collapsed_value m φ0 hW0 hgap0
  have hgc : ContinuousOn (fun t : ℝ => betaZeta n m φ0
      (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) * (muSeq φ0 m - tauN φ0 m)) (Icc 0 1) := by
    have h : ContinuousOn (fun t : ℝ => betaZeta n m φ0 (nearSegPoint m φ0 t)) (Icc 0 1) :=
      fun t ht => (near_zeta_contAt n m hmn Cr Rr c N hg φ0 hgk (hspecU φ0 hφ0U) t ht).continuousWithinAt
    have hpt : ∀ t : ℝ, betaZeta n m φ0 (nearSegPoint m φ0 t) = betaZeta n m φ0
        (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) := by
      intro t
      unfold nearSegPoint nearOmega
      rw [hnv]
    exact (h.mul (continuousOn_const (c := muSeq φ0 m - tauN φ0 m))).congr
      (fun t _ => by simp only [Pi.mul_apply, hpt t])
  obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hgc
  obtain ⟨M, hMnn, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖betaZeta n m φ0
      (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) * (muSeq φ0 m - tauN φ0 m)‖ ≤ M :=
    ⟨max M0 0, le_max_right _ _, fun t ht => le_trans (hM0 t ht) (le_max_left _ _)⟩
  have hgint : IntervalIntegrable (fun t : ℝ => betaZeta n m φ0
      (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) * (muSeq φ0 m - tauN φ0 m)) volume 0 1 :=
    ContinuousOn.intervalIntegrable (by rw [uIcc_of_le zero_le_one]; exact hgc)
  -- the key estimate
  have claim : ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
      ‖(∫ t in (0 : ℝ)..1, nearDensity n m (v j) t) - collapsedBetaFinalSegment n m φ0 0‖ < η := by
    intro η hη
    obtain ⟨ε, hε0, hε1, hCε, hMε⟩ := exists_eps C M η hC hMnn hη
    have hεI : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε0, hε1⟩
    have hfin := near_final_tendsto n m hmn v φ0 hW0 hgap0 hv hnot ε hεI
    have hfin' := Metric.tendsto_nhds.1 hfin (η / 4) (by linarith)
    filter_upwards [hfin', eventually_ge_atTop J] with j hj hjJ
    obtain ⟨-, hintj, hbj⟩ := hJ j hjJ
    have hI1 : IntervalIntegrable (nearDensity n m (v j)) volume 0 ε :=
      hintj.mono_set (by rw [uIcc_of_le hε0.le, uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl hε1.le)
    have hI2 : IntervalIntegrable (nearDensity n m (v j)) volume ε 1 :=
      hintj.mono_set (by rw [uIcc_of_le hε1.le, uIcc_of_le zero_le_one]; exact Icc_subset_Icc hε0.le le_rfl)
    have hg1 : IntervalIntegrable (fun t : ℝ => betaZeta n m φ0
        (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) * (muSeq φ0 m - tauN φ0 m)) volume 0 ε :=
      hgint.mono_set (by rw [uIcc_of_le hε0.le, uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl hε1.le)
    have hg2 : IntervalIntegrable (fun t : ℝ => betaZeta n m φ0
        (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) * (muSeq φ0 m - tauN φ0 m)) volume ε 1 :=
      hgint.mono_set (by rw [uIcc_of_le hε1.le, uIcc_of_le zero_le_one]; exact Icc_subset_Icc hε0.le le_rfl)
    have hsplit1 := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
    have hsplit2 := intervalIntegral.integral_add_adjacent_intervals hg1 hg2
    have hF0 : collapsedBetaFinalSegment n m φ0 0 =
        (∫ t in (0 : ℝ)..ε, betaZeta n m φ0
          (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) * (muSeq φ0 m - tauN φ0 m)) +
          collapsedBetaFinalSegment n m φ0 ε := by
      unfold collapsedBetaFinalSegment
      exact hsplit2.symm
    have hA : ‖∫ t in (0 : ℝ)..ε, betaZeta n m φ0
        (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) * (muSeq φ0 m - tauN φ0 m)‖ ≤ M * ε := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := ε) (C := M)
        (f := fun t : ℝ => betaZeta n m φ0
          (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) * (muSeq φ0 m - tauN φ0 m))
        (fun t ht => by
          rw [uIoc_of_le hε0.le] at ht
          exact hM t ⟨ht.1.le, ht.2.trans hε1.le⟩)
      rw [sub_zero, abs_of_pos hε0] at h
      exact h
    have hB : ‖∫ t in (0 : ℝ)..ε, nearDensity n m (v j) t‖ ≤ η / 4 :=
      le_trans (hbj ε hεI) hCε
    have hD : ‖(∫ t in ε..(1 : ℝ), nearDensity n m (v j) t) -
        collapsedBetaFinalSegment n m φ0 ε‖ < η / 4 := by
      rw [← dist_eq_norm]
      exact hj
    rw [← hsplit1, hF0]
    have hdecomp : (∫ t in (0 : ℝ)..ε, nearDensity n m (v j) t) + (∫ t in ε..(1 : ℝ), nearDensity n m (v j) t) -
        ((∫ t in (0 : ℝ)..ε, betaZeta n m φ0
          (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) * (muSeq φ0 m - tauN φ0 m)) +
          collapsedBetaFinalSegment n m φ0 ε) =
        (∫ t in (0 : ℝ)..ε, nearDensity n m (v j) t) +
          ((∫ t in ε..(1 : ℝ), nearDensity n m (v j) t) - collapsedBetaFinalSegment n m φ0 ε) -
          (∫ t in (0 : ℝ)..ε, betaZeta n m φ0
            (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) * (muSeq φ0 m - tauN φ0 m)) := by
      ring
    rw [hdecomp]
    have t1 := norm_sub_le ((∫ t in (0 : ℝ)..ε, nearDensity n m (v j) t) +
          ((∫ t in ε..(1 : ℝ), nearDensity n m (v j) t) - collapsedBetaFinalSegment n m φ0 ε))
        (∫ t in (0 : ℝ)..ε, betaZeta n m φ0
            (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)) * (muSeq φ0 m - tauN φ0 m))
    have t2 := norm_add_le (∫ t in (0 : ℝ)..ε, nearDensity n m (v j) t)
        ((∫ t in ε..(1 : ℝ), nearDensity n m (v j) t) - collapsedBetaFinalSegment n m φ0 ε)
    linarith
  -- assemble: beta(v j) = eps0 * int_0^1 nearDensity eventually
  rw [Metric.tendsto_nhds]
  intro η hη
  have hη' : 0 < η / (‖ε0‖ + 1) := div_pos hη (by positivity)
  have hcl := claim (η / (‖ε0‖ + 1)) hη'
  have hvV : ∀ᶠ j in atTop, v j ∈ V := hv.eventually (hVo.mem_nhds hφV)
  filter_upwards [hcl, hvV, eventually_ge_atTop J] with j hcj hvj hjJ
  obtain ⟨hdj, hintj, -⟩ := hJ j hjJ
  have hWj : v j ∈ sourceW := hVW hvj
  have hωj : nearOmega m (v j) ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hd hdj)
  obtain ⟨hrd, -, -, hratio⟩ := hV (v j) hvj
  have hμj : muSeq (v j) m ∉ gapSegments38 (v j) := hrd.2
  have havj := G3021N.near_seg_avoids m (v j) hWj hωj hμj
  have hbj := G3021N.near_beta_segment n m hmn (v j) hWj hωj havj hintj
  rw [hratio, ← hε0] at hbj
  rw [dist_eq_norm, hbj, hβ0, ← mul_sub, norm_mul]
  have h1 : ‖ε0‖ * ‖(∫ t in (0 : ℝ)..1, nearDensity n m (v j) t) - collapsedBetaFinalSegment n m φ0 0‖ ≤
      ‖ε0‖ * (η / (‖ε0‖ + 1)) := mul_le_mul_of_nonneg_left hcj.le (norm_nonneg _)
  have h2 : ‖ε0‖ * (η / (‖ε0‖ + 1)) < η := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg ε0]
  linarith

end G3021Main

theorem G3_021 (n m : ℤ) (hmn : m ≠ n) (φ0 : PotPair)
    (hφ0 : φ0 ∈ collapsedSet m \ endpointSet m) :
  ContinuousAt (offDiagonalBeta n m) φ0 ∧
  ∀ v : ℕ → PotPair, (∀ j, v j ∈ sourceW) → Tendsto v atTop (𝓝 φ0) →
    Tendsto (fun j => offDiagonalBeta n m (v j)) atTop
      (𝓝 (offDiagonalBeta n m φ0)) := by
  refine ⟨?_, fun v _ hv => G3021Main.seq_key n m hmn φ0 hφ0 v hv⟩
  exact tendsto_iff_seq_tendsto.2 (fun u hu => G3021Main.seq_key n m hmn φ0 hφ0 u hu)

end
end NlsGge.GKDefinitionDesign
