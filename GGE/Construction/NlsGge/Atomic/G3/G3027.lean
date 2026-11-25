import Mathlib
import NlsGge.ThirdConsultation.G3.G3026Support

                                                                                      
                                                                           
                                                                                                                           
                                                                                                                               
                                                                                                                             
                                                                                                                                 
                                                                         
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G3_027 :
  ∃ U : Set PotPair, IsOpen U ∧ range realSlice ⊆ U ∧ U ⊆ sourceBetaW ∧
    (∀ n : ℤ, TendstoLocallyUniformlyOn (betaPartialSum n) (betaSum n) atTop U) ∧
    ∀ φ0 ∈ U, ∃ V : Set PotPair, ∃ C M : ℝ,
      IsOpen V ∧ φ0 ∈ V ∧ V ⊆ U ∧ 0 < C ∧ 0 ≤ M ∧
      (∀ φ ∈ V, Summable (fun m : ℤ => ‖gk151BetaMass38 φ m‖^2) ∧
        spectralNorm φ ≤ M ∧ ∀ n m : ℤ,
          ‖offDiagonalBeta n m φ‖ ≤ C*‖gk151BetaMass38 φ m‖*Lib.c3w n m) ∧
      ∀ n : ℤ,
        Tendsto (fixedIndexReciprocalTail n) atTop (𝓝 0) ∧
        ∀ R : ℕ, ∀ φ ∈ V,
          Summable (fun m : ℤ => if (R : ℝ) < |(m : ℝ)|
            then ‖offDiagonalBeta n m φ‖ else 0) ∧
          (∑' m : ℤ, if (R : ℝ) < |(m : ℝ)|
            then ‖offDiagonalBeta n m φ‖ else 0) ≤ C*M*fixedIndexReciprocalTail n R ∧
          ‖betaSum n φ-betaPartialSum n R φ‖ ≤ C*M*fixedIndexReciprocalTail n R := by
  obtain ⟨U, hUo, hUr, hUsub, hloc⟩ := betaLocalData
  have hmain : ∀ φ0 ∈ U, ∃ V : Set PotPair, ∃ C M : ℝ,
      IsOpen V ∧ φ0 ∈ V ∧ V ⊆ U ∧ 0 < C ∧ 0 ≤ M ∧
      (∀ φ ∈ V, Summable (fun m : ℤ => ‖gk151BetaMass38 φ m‖^2) ∧
        spectralNorm φ ≤ M ∧ ∀ n m : ℤ,
          ‖offDiagonalBeta n m φ‖ ≤ C*‖gk151BetaMass38 φ m‖*Lib.c3w n m) ∧
      ∀ n : ℤ,
        Tendsto (fixedIndexReciprocalTail n) atTop (𝓝 0) ∧
        ∀ R : ℕ, ∀ φ ∈ V,
          Summable (fun m : ℤ => if (R : ℝ) < |(m : ℝ)|
            then ‖offDiagonalBeta n m φ‖ else 0) ∧
          (∑' m : ℤ, if (R : ℝ) < |(m : ℝ)|
            then ‖offDiagonalBeta n m φ‖ else 0) ≤ C*M*fixedIndexReciprocalTail n R ∧
          ‖betaSum n φ-betaPartialSum n R φ‖ ≤ C*M*fixedIndexReciprocalTail n R := by
    intro φ0 hφ0
    obtain ⟨V, C, M, hVo, hφ0V, hVU, hC, hM, hV⟩ := hloc φ0 hφ0
    refine ⟨V, C, M, hVo, hφ0V, hVU, hC, hM, hV, fun n => ⟨tendsto_fixedIndexReciprocalTail n, ?_⟩⟩
    intro R φ hφ
    obtain ⟨hs, hspec, hb⟩ := hV φ hφ
    obtain ⟨hsum, hbound⟩ := tail_bounds hC n R φ hs hspec (fun m => hb n m)
    refine ⟨hsum, hbound, ?_⟩
    have hHas := hasSum_offDiagonalBeta_betaSum n φ (hUsub (hVU hφ))
    rw [sub_betaPartialSum_eq n R φ hHas]
    have hnorm : ∀ m : ℤ, ‖(if (R : ℝ) < |(m : ℝ)| then offDiagonalBeta n m φ else 0)‖ =
        if (R : ℝ) < |(m : ℝ)| then ‖offDiagonalBeta n m φ‖ else 0 := fun m => by
      split_ifs <;> simp
    calc ‖∑' m : ℤ, if (R : ℝ) < |(m : ℝ)| then offDiagonalBeta n m φ else 0‖
        ≤ ∑' m : ℤ, ‖(if (R : ℝ) < |(m : ℝ)| then offDiagonalBeta n m φ else 0)‖ :=
          norm_tsum_le_tsum_norm (hsum.congr (fun m => (hnorm m).symm))
      _ = ∑' m : ℤ, if (R : ℝ) < |(m : ℝ)| then ‖offDiagonalBeta n m φ‖ else 0 :=
          tsum_congr hnorm
      _ ≤ C*M*fixedIndexReciprocalTail n R := hbound
  refine ⟨U, hUo, hUr, hUsub, ?_, hmain⟩
  intro n
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε φ0 hφ0
  obtain ⟨V, C, M, hVo, hφ0V, hVU, hC, hM, hVprop, hn⟩ := hmain φ0 hφ0
  obtain ⟨hT, hR⟩ := hn n
  refine ⟨V, mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hφ0V), ?_⟩
  have hlim : Tendsto (fun R : ℕ => C*M*fixedIndexReciprocalTail n R) atTop (𝓝 0) := by
    simpa using hT.const_mul (C*M)
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with R hR' φ hφ
  rw [dist_eq_norm]
  exact lt_of_le_of_lt (hR R φ hφ).2.2 hR'

end
end NlsGge.GKDefinitionDesign
