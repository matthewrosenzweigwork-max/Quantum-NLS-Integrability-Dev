import Mathlib
import NlsGge.Atomic.G4.G4037Near
import NlsGge.ThirdConsultation.G3.G3026Support
import Armstrong.Work.RawBetaSumSpectralMass

                                                                                                    
                                                                           
                                                                                                    
                                                                                                             
                                                                                                                              
                                                                                                                             
                                                                                                           
                                                                                                              
                                                                    
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38
open scoped BigOperators

namespace NlsGge.GKDefinitionDesign
noncomputable section
namespace G4037Aux

theorem g4037_local_inverse (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ball φ0 δ ⊆ sourceW ∧
      ∀ ψ ∈ ball φ0 δ, ∀ n m : ℤ,
        ‖offDiagonalBeta n m ψ‖ ≤ C * ‖gk151BetaMass38 ψ m‖ * Lib.c3w n m := by
  obtain ⟨δ, C, hδ, hC, hsub, hb⟩ := g4037_local_nearest φ0 hφ0
  refine ⟨δ, C, hδ, hC, hsub, fun ψ hψ n m => ?_⟩
  by_cases hmn : m = n
  · subst hmn
    rw [offDiagonalBeta_diag, norm_zero]
    exact mul_nonneg (mul_nonneg hC.le (norm_nonneg _)) (Lib.c3w_nonneg m m)
  · have hψW : ψ ∈ sourceW := hsub hψ
    have hψgk : ψ ∈ gkW := sourceFamily.W_gk hψW
    have hsharp := hb ψ hψ n m hmn
    have hgeom := raw_beta_magnitude_inverse_geometry38
      (lamMinus ψ m) (lamPlus ψ m) (muSeq ψ m)
    have htau := tauN_value38 ψ hψgk m
    have hgeom' :
        Real.sqrt (‖lamPlus ψ m - lamMinus ψ m‖ +
          min ‖muSeq ψ m - lamMinus ψ m‖ ‖muSeq ψ m - lamPlus ψ m‖) *
          Real.sqrt (min ‖muSeq ψ m - lamMinus ψ m‖ ‖muSeq ψ m - lamPlus ψ m‖) ≤
        ‖lamPlus ψ m - lamMinus ψ m‖ + ‖muSeq ψ m - tauN ψ m‖ := by
      rw [htau]
      simpa only [norm_sub_rev (lamMinus ψ m) (lamPlus ψ m), add_comm] using hgeom
    have hs1 := mul_le_mul_of_nonneg_left hgeom' hC.le
    have hs2 := mul_le_mul_of_nonneg_right hs1 (Lib.c3w_nonneg n m)
    rw [norm_gk151BetaMass38]
    exact hsharp.trans (by simpa only [mul_assoc] using hs2)

end G4037Aux

theorem source_beta_inverse_distance_on_sourceBetaW
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
  ∃ V : Set PotPair,
    IsOpen V ∧ φ₀ ∈ V ∧ V ⊆ sourceBetaW ∧
    ∃ C M : ℝ, 0 < C ∧ 0 ≤ M ∧
      ∀ φ : PotPair, φ ∈ V →
        Summable (fun m : ℤ => ‖gk151BetaMass38 φ m‖^2) ∧
        (∑' m : ℤ, ‖gk151BetaMass38 φ m‖^2) ≤ M^2 ∧
        ∀ n m : ℤ,
          ‖offDiagonalBeta n m φ‖ ≤
            C * ‖gk151BetaMass38 φ m‖ * Lib.c3w n m := by
  have hφW : φ₀ ∈ sourceW := sourceFamily.V_W hφ₀
  obtain ⟨δ, C, hδ, hC, hsub, hb⟩ := G4037Aux.g4037_local_inverse φ₀ hφW
  obtain ⟨U2, hU2, _hU2gk, M0, hM0, hmass⟩ :=
    gk151BetaMass_local_l2_38 φ₀ (sourceFamily.W_gk hφW)
  refine ⟨ball φ₀ δ ∩ interior U2 ∩ sourceBetaW,
    (isOpen_ball.inter isOpen_interior).inter sourceFamily.V_open,
    ⟨⟨mem_ball_self hδ, mem_interior_iff_mem_nhds.mpr hU2⟩, hφ₀⟩, inter_subset_right,
    C, Real.sqrt M0, hC, Real.sqrt_nonneg _, ?_⟩
  intro φ hφ
  obtain ⟨hsm, hle⟩ := hmass φ (interior_subset hφ.1.2)
  refine ⟨hsm, ?_, fun n m => hb φ hφ.1.1 n m⟩
  rw [Real.sq_sqrt hM0]
  exact hle

theorem G4037
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
  ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ sourceBetaW ∧
  ∃ C : ℝ, 0 < C ∧
    ∀ φ : PotPair, φ ∈ V → ∀ n : ℤ,
      ‖Complex.exp (Complex.I * betaSum n φ)‖ ≤ C ∧
      ‖Complex.exp (-Complex.I * betaSum n φ)‖ ≤ C := by
  obtain ⟨V, hVo, hφV, hVS, C, M, hC, hM, hV⟩ :=
    source_beta_inverse_distance_on_sourceBetaW φ₀ hφ₀
  refine ⟨V, hVo.mem_nhds hφV, hVS,
    Real.exp (C * Real.sqrt Lib.invSqSum * M), Real.exp_pos _, fun φ hφ n => ?_⟩
  obtain ⟨hs, htsum, hb⟩ := hV φ hφ
  have hspec : spectralNorm φ ≤ M := by
    unfold spectralNorm
    exact Real.sqrt_le_iff.mpr ⟨hM, htsum⟩
  obtain ⟨hsum, _, hrow⟩ := row_bounds hC φ hs hspec hb n
  have hHas := hasSum_offDiagonalBeta_betaSum n φ (hVS hφ)
  have hnorm : ‖betaSum n φ‖ ≤ C * Real.sqrt Lib.invSqSum * M := by
    have h1 : ‖betaSum n φ‖ ≤ ∑' m : ℤ, ‖offDiagonalBeta n m φ‖ := by
      rw [← hHas.tsum_eq]
      exact norm_tsum_le_tsum_norm hsum
    exact h1.trans hrow
  have hre : |(betaSum n φ).im| ≤ C * Real.sqrt Lib.invSqSum * M :=
    (Complex.abs_im_le_norm _).trans hnorm
  constructor
  · rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have : (Complex.I * betaSum n φ).re = -(betaSum n φ).im := by simp
    rw [this]
    exact (neg_le_abs _).trans hre
  · rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have : (-Complex.I * betaSum n φ).re = (betaSum n φ).im := by simp
    rw [this]
    exact (le_abs_self _).trans hre

end
end NlsGge.GKDefinitionDesign
