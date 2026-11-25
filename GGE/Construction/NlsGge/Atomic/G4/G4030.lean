import Mathlib
import NlsGge.Atomic.G4.G4030Reg
import NlsGge.Atomic.G4.G4048
import NlsGge.Atomic.G4.G4019
import NlsGge.Atomic.G4.G4021

                                                                                                    
                                                                           
                                                                                                                                        
                                                                                                                        
                                                                                                                                  
                                                                                                                                     
                                                                                                           
                                                                                                                           
                                                                                                    
                                                        
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38
open scoped BigOperators

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G4030
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
  ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ sourceBetaW ∧
  ∃ C : ℝ, 0 < C ∧
    ∀ φ : PotPair, φ ∈ V → ∀ n s : ℤ,
      (s = 1 ∨ s = -1) →
        ‖Complex.exp ((s : ℂ) *
          (regularEtaIntegral n φ + constantEtaCorrection n φ))‖ ≤ C := by
  obtain ⟨V1, hV1n, _hV1o, hV1B, Cc, R, r, ε, M, hε, hM, hfam, hrR, hcol, hder⟩ :=
    G4019 φ₀ hφ₀
  obtain ⟨V2, hV2n, hV2B, C2, hC2, h2⟩ := G4021 φ₀ hφ₀
  have hφ1 : φ₀ ∈ V1 := mem_of_mem_nhds hV1n
  obtain ⟨c, N, hg, _hs⟩ := hfam φ₀ hφ1
  obtain ⟨Rm, hRm0, hRm⟩ := g2019_radius_bound Cc R c N hg
  have hVS : V1 ∩ V2 ⊆ sourceBetaW := inter_subset_left.trans hV1B
  have hrle : ∀ n : ℤ, r n ≤ R n := fun n => by
    have := hrR n
    linarith [this.1, this.2]
  have hreg := G4030Aux.g4030_regular_bound (V1 ∩ V2) hVS Cc R r M hM.le hrle
    (fun φ hφ => hfam φ hφ.1) (fun φ hφ => hcol φ hφ.1) (fun φ hφ => hder φ hφ.1)
  have hL : NormalizedZetaGapBound (V1 ∩ V2) C2 := by
    refine ⟨hC2.le, inter_subset_right.trans hV2B, fun φ hφ n => ?_⟩
    have hgk : φ ∈ gkW := sourceFamily.W_gk (sourceFamily.V_W (hVS hφ))
    exact (h2 φ hφ.2 n).1 (tauN φ n) (g4036_tau_mem φ hgk n)
  obtain ⟨Cd, hCd, hconst⟩ := G4048 (V1 ∩ V2) C2 hL
  -- uniform size of the gap and of the Dirichlet offset
  have hsize : ∀ φ ∈ V1 ∩ V2, ∀ n : ℤ,
      ‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖ ≤ 4 * Rm := by
    intro φ hφ n
    have hgk : φ ∈ gkW := sourceFamily.W_gk (sourceFamily.V_W (hVS hφ))
    obtain ⟨hgap, hmu⟩ := hcol φ hφ.1 n
    have hlm : lamMinus φ n ∈ Metric.ball (Cc n) (r n) := hgap (left_mem_segment ℝ _ _)
    have hlp : lamPlus φ n ∈ Metric.ball (Cc n) (r n) := hgap (right_mem_segment ℝ _ _)
    have hτ : tauN φ n ∈ Metric.ball (Cc n) (r n) := hgap (g4036_tau_mem φ hgk n)
    have h1 : ‖lamPlus φ n - lamMinus φ n‖ ≤ 2 * r n := by
      rw [← dist_eq_norm]
      have := dist_triangle_right (lamPlus φ n) (lamMinus φ n) (Cc n)
      rw [Metric.mem_ball] at hlm hlp
      linarith
    have h2' : ‖muSeq φ n - tauN φ n‖ ≤ 2 * r n := by
      rw [← dist_eq_norm]
      have := dist_triangle_right (muSeq φ n) (tauN φ n) (Cc n)
      rw [Metric.mem_ball] at hmu hτ
      linarith
    have := hRm n
    have := hrle n
    linarith
  refine ⟨V1 ∩ V2, inter_mem hV1n hV2n, hVS,
    Real.exp ((Real.pi / 2) * M * (4 * Rm) + Cd * C2 * (4 * Rm)), Real.exp_pos _,
    fun φ hφ n s hs => ?_⟩
  have h1 := hreg φ hφ n
  have h2'' := hconst φ hφ n
  have hsz := hsize φ hφ n
  have hRM : ‖regularEtaIntegral n φ‖ ≤ (Real.pi / 2) * M * (4 * Rm) :=
    h1.trans (mul_le_mul_of_nonneg_left hsz (mul_nonneg (by positivity) hM.le))
  have hCO : ‖constantEtaCorrection n φ‖ ≤ Cd * C2 * (4 * Rm) :=
    h2''.trans (mul_le_mul_of_nonneg_left hsz (mul_nonneg hCd.le hC2.le))
  have hx : ‖regularEtaIntegral n φ + constantEtaCorrection n φ‖ ≤
      (Real.pi / 2) * M * (4 * Rm) + Cd * C2 * (4 * Rm) :=
    (norm_add_le _ _).trans (add_le_add hRM hCO)
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc ((s : ℂ) * (regularEtaIntegral n φ + constantEtaCorrection n φ)).re
      ≤ ‖(s : ℂ) * (regularEtaIntegral n φ + constantEtaCorrection n φ)‖ := Complex.re_le_norm _
    _ = ‖regularEtaIntegral n φ + constantEtaCorrection n φ‖ := by
        rcases hs with rfl | rfl
        · simp
        · rw [Int.cast_neg, Int.cast_one, neg_one_mul, norm_neg]
    _ ≤ _ := hx

end
end NlsGge.GKDefinitionDesign
