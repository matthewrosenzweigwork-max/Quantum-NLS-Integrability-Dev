import Mathlib
import NlsGge.Atomic.G2.G2074
import NlsGge.GK38.TauGammaValueBounds
import NlsGge.GK38.TauGammaContourGlue
import NlsGge.GK38.IsolatingPersistence
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.XiSqLocal
import NlsGge.GK38.CountingLemmaGeometry
import NlsGge.Atomic.G4.G4NormalizedHost
import NlsGge.ThirdConsultation.G4.G4018Support1
import NlsGge.ThirdConsultation.G4.G4018Support2
import NlsGge.ThirdConsultation.G4.G4018Support3
import NlsGge.ThirdConsultation.G4.G4018Support4
import NlsGge.ThirdConsultation.G4.G4018Support5
import NlsGge.ThirdConsultation.G4.G4018Support6
import NlsGge.ThirdConsultation.G4.G4018Support7
import NlsGge.ThirdConsultation.G4.G4018Support8
import NlsGge.ThirdConsultation.G4.G4018Support9

                                                                              
                                                                                                           
                                                                                                       
                                                                                                    
                                                                                                            
                                                                                                              
                                                                                                     
                                                         
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open SummationFilter
open NlsGge.G4018Support

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G4018 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
  ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ IsOpen V ∧ V ⊆ sourceBetaW ∧
  ∃ (C : ℤ → ℂ) (R : ℤ → ℝ) (M : ℝ), 0 < M ∧
    (∀ φ ∈ V, IsolatingFamily38 φ C R) ∧
    (∀ n : ℤ, AnalyticOnNhd ℂ
      (fun p : PotPair × ℂ => normalizedZeta n p.1 p.2)
      (V ×ˢ Metric.ball (C n) (R n))) ∧
    ∀ φ ∈ V, ∀ n : ℤ, ∀ lam ∈ Metric.ball (C n) (R n),
      ‖normalizedZeta n φ lam‖ ≤ M := by
  have hφW : φ₀ ∈ sourceW := sourceFamily.V_W hφ₀
  have hgk : φ₀ ∈ gkW := sourceFamily.W_gk hφW
  obtain ⟨ρ, hρ, c, N, hgeom, hspecball⟩ :=
    fixed_family_persistence38 φ₀ (discC φ₀) (discR φ₀) (isolating_family38 φ₀ hgk)
  obtain ⟨V2, hV2o, hφV2, hV2W, B2, hB2, hA⟩ := G2_074 φ₀ hφW
  obtain ⟨V3, hV3nhds, _hV3gk, B3, hB3, h3⟩ :=
    tauGamma_common_value_bound38 discC discR isolating_selectors_admissible38 φ₀ hgk
  have hc : 1 ≤ c := hgeom.2.2.1
  have hcpos : 0 < c := by linarith
  have hc0 : c ≠ 0 := hcpos.ne'
  let V : Set PotPair := ((ball φ₀ ρ ∩ V2) ∩ interior V3) ∩ sourceBetaW
  have hVnhds : V ∈ 𝓝 φ₀ :=
    inter_mem (inter_mem (inter_mem (ball_mem_nhds φ₀ hρ) (hV2o.mem_nhds hφV2))
      (interior_mem_nhds.mpr hV3nhds)) (sourceFamily.V_open.mem_nhds hφ₀)
  have hVo : IsOpen V :=
    ((isOpen_ball.inter hV2o).inter isOpen_interior).inter sourceFamily.V_open
  have hVB : V ⊆ sourceBetaW := inter_subset_right
  have hVW : V ⊆ sourceW := fun φ hφ => hV2W hφ.1.1.2
  have hfam : ∀ φ ∈ V, IsolatingFamily38 φ (discC φ₀) (discR φ₀) := fun φ hφ =>
    ⟨c, N, hgeom, hspecball φ hφ.1.1.1⟩
  refine ⟨V, hVnhds, hVo, hVB, discC φ₀, discR φ₀,
    Real.exp (c * (Real.sqrt (B3 ^ 2 * B2) * Real.sqrt Lib.invSqSum) + c ^ 2 / 4 * B3),
    Real.exp_pos _, hfam,
    fun n => normalizedZeta_joint_analytic V hVW (discC φ₀) (discR φ₀) hfam n, ?_⟩
  intro φ hφ n lam hlam
  have hgkφ : φ ∈ gkW := sourceFamily.W_gk (hVW hφ)
  have hφV3 : φ ∈ V3 := interior_subset hφ.1.2
  have hφV2 : φ ∈ V2 := hφ.1.1.2
  have hp : (φ, lam) ∈ a5OmittedRootDomain38 n :=
    a5OwnClosedBall_omittedDomain38 φ hgkφ (discC φ₀) (discR φ₀) (hfam φ hφ) n lam
      (Metric.ball_subset_closedBall hlam)
  obtain ⟨A, hAeq, hAs, hAb⟩ := hA φ hφV2 n
  obtain ⟨-, -, hGs, -, -, hGb⟩ := h3 φ hφV3
  have hG3 : ∀ j : ℤ, ‖gamma2 φ j‖ ≤ B3 := fun j =>
    (hGs.le_tsum j (fun k _ => norm_nonneg _)).trans hGb
  have hinv : ∀ x : ℤ, (1 / |((x : ℤ) : ℝ)|) ^ 2 ≤ 1 := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have h1 : (1 : ℝ) ≤ |((x : ℤ) : ℝ)| := by
        have : (1 : ℤ) ≤ |x| := Int.one_le_abs hx
        exact_mod_cast this
      have hpos : (0 : ℝ) < |((x : ℤ) : ℝ)| := by linarith
      rw [div_pow, one_pow]
      exact (div_le_one (by positivity)).mpr (by nlinarith)
  set s : Lib.L2Seq := p2Extend38 n (sourceF n φ) with hs_def
  have hH := p2OmittedRatio_hasProd φ n s lam hp
  have hval : normalizedZeta n φ lam = p2OmittedRatio38 n ((φ, s), lam) := rfl
  rw [hval]
  refine hasProd_norm_le_exp _ _ (symmetricIcc ℤ) hH _ ?_
  intro t
  let a : ℤ → ℂ := fun j => if h : j ≠ n then A ⟨j, h⟩ else 0
  have hD5 : ∑ j ∈ t, ‖a j‖ ^ 2 ≤ B2 :=
    subtype_finset_sum_le (fun m => ‖A m‖ ^ 2) hAs (fun m => by positivity) B2 hAb
      (fun j => ‖a j‖ ^ 2) (fun j => by by_cases h : j ≠ n <;> simp [a, h]) t
  have hK : ∑ j ∈ t, ‖gamma2 φ j * a j‖ ^ 2 ≤ B3 ^ 2 * B2 := by
    calc ∑ j ∈ t, ‖gamma2 φ j * a j‖ ^ 2 ≤ ∑ j ∈ t, B3 ^ 2 * ‖a j‖ ^ 2 :=
          Finset.sum_le_sum (fun j _ => by
            rw [norm_mul, mul_pow]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hG3 j) 2)
              (sq_nonneg _))
      _ = B3 ^ 2 * ∑ j ∈ t, ‖a j‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ B3 ^ 2 * B2 := mul_le_mul_of_nonneg_left hD5 (sq_nonneg _)
  have hsum1 : ∑ j ∈ t, ‖gamma2 φ j * a j‖ * (1 / |((j - n : ℤ) : ℝ)|) ≤
      Real.sqrt (B3 ^ 2 * B2) * Real.sqrt Lib.invSqSum :=
    sum_mul_inv_abs_le n t (fun j => ‖gamma2 φ j * a j‖) (fun j => norm_nonneg _) (B3 ^ 2 * B2)
      Lib.invSqSum hK (by unfold Lib.invSqSum; exact sum_shift_sq_le n t)
      (mul_nonneg (sq_nonneg _) hB2.le)
  have conv : ∀ y : ℝ, y ≠ 0 → ∀ D G : ℝ,
      D / (c⁻¹ * |y|) + G / (4 * (c⁻¹ * |y|) ^ 2) =
        c * (D * (1 / |y|)) + c ^ 2 / 4 * (G * (1 / |y|) ^ 2) := by
    intro y hy D G
    have hy' : |y| ≠ 0 := abs_ne_zero.mpr hy
    field_simp
  have hterm : ∀ j ∈ t,
      ‖(if j = n then (1 : ℂ) else (Lib.sigmaOf s j - lam) / stdRoot38 (tauN φ j) (gamma2 φ j) lam) - 1‖ ≤
        c * (‖gamma2 φ j * a j‖ * (1 / |((j - n : ℤ) : ℝ)|)) +
          c ^ 2 / 4 * (‖gamma2 φ j‖ * (1 / |((j - n : ℤ) : ℝ)|) ^ 2) := by
    intro j _
    by_cases hj : j = n
    · subst hj
      simp
    · have hh : j ≠ n := hj
      have hσ : Lib.sigmaOf s j = tauN φ j + gamma2 φ j * a j := by
        have e1 : Lib.sigmaOf s j = normalizedRoot n j φ := by
          have hx : p2Extend38 n (sourceF n φ) j = sourceF n φ ⟨j, hh⟩ :=
            p2Extend_at38 n (sourceF n φ) ⟨j, hh⟩
          rw [hs_def]
          unfold Lib.sigmaOf normalizedRoot
          rw [dif_pos hh, hx]
          rfl
        have e2 := hAeq ⟨j, hh⟩
        simp only [a, dif_pos hh]
        rw [e1]
        exact e2
      have hpt := perterm_bound φ hgkφ (discC φ₀) (discR φ₀) c N hgeom
        (hspecball φ hφ.1.1.1) n j hj lam hlam (Lib.sigmaOf s j) (a j) hσ
      rw [if_neg hj]
      have hcv := conv ((j - n : ℤ) : ℝ) (Int.cast_ne_zero.mpr (sub_ne_zero.mpr hh))
        ‖gamma2 φ j * a j‖ ‖gamma2 φ j‖
      exact hpt.trans (le_of_eq hcv)
  calc ∑ j ∈ t, ‖(if j = n then (1 : ℂ) else (Lib.sigmaOf s j - lam) / stdRoot38 (tauN φ j) (gamma2 φ j) lam) - 1‖
      ≤ ∑ j ∈ t, (c * (‖gamma2 φ j * a j‖ * (1 / |((j - n : ℤ) : ℝ)|)) +
          c ^ 2 / 4 * (‖gamma2 φ j‖ * (1 / |((j - n : ℤ) : ℝ)|) ^ 2)) :=
        Finset.sum_le_sum hterm
    _ = c * ∑ j ∈ t, ‖gamma2 φ j * a j‖ * (1 / |((j - n : ℤ) : ℝ)|) +
          c ^ 2 / 4 * ∑ j ∈ t, ‖gamma2 φ j‖ * (1 / |((j - n : ℤ) : ℝ)|) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ c * (Real.sqrt (B3 ^ 2 * B2) * Real.sqrt Lib.invSqSum) + c ^ 2 / 4 * B3 := by
        have hG2 : ∑ j ∈ t, ‖gamma2 φ j‖ * (1 / |((j - n : ℤ) : ℝ)|) ^ 2 ≤ B3 := by
          calc ∑ j ∈ t, ‖gamma2 φ j‖ * (1 / |((j - n : ℤ) : ℝ)|) ^ 2 ≤ ∑ j ∈ t, ‖gamma2 φ j‖ :=
                Finset.sum_le_sum (fun j _ => by
                  have := hinv (j - n)
                  nlinarith [norm_nonneg (gamma2 φ j)])
            _ ≤ B3 := (hGs.sum_le_tsum t (fun j _ => norm_nonneg _)).trans hGb
        have hc2 : 0 ≤ c ^ 2 / 4 := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_left hsum1 hcpos.le)
          (mul_le_mul_of_nonneg_left hG2 hc2)

end
end NlsGge.GKDefinitionDesign
