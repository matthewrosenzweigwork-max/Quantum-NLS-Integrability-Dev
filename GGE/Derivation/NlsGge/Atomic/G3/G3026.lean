import Mathlib
import NlsGge.ThirdConsultation.G3.G3026Support

/- G3_026 PRODUCTION01 (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/Atomic/G3/G3026.lean, namespace NlsGge.GKDefinitionDesign.
   Head VERBATIM from followup8 STATEMENTS/G3.md (the G3-026 block; byte-identical in followup7 = round 9; no later round).
   Route: neighbourhood data `betaLocalData` (G3_011 inverse-distance bound on Winverse, intersected with sourceBetaW, local ℓ² bound
   from gk151BetaMass_local_l2_38), Cauchy-Schwarz `row_bounds` (Lib.c3_cs), and the bridge `hasSum_offDiagonalBeta_betaSum`
   (subtype sum over {m // m ≠ n} of beta_spec to HasSum over ℤ with zero diagonal).  No hypothesis beyond the head. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G3_026 :
  ∃ U : Set PotPair, IsOpen U ∧ range realSlice ⊆ U ∧ U ⊆ sourceBetaW ∧
    ∀ φ0 ∈ U, ∃ V : Set PotPair, ∃ C M : ℝ,
      IsOpen V ∧ φ0 ∈ V ∧ V ⊆ U ∧ 0 < C ∧ 0 ≤ M ∧
      ∀ φ ∈ V,
        Summable (fun m : ℤ => ‖gk151BetaMass38 φ m‖^2) ∧ spectralNorm φ ≤ M ∧
        (∀ n m : ℤ,
          ‖offDiagonalBeta n m φ‖ ≤ C*‖gk151BetaMass38 φ m‖*Lib.c3w n m) ∧
        ∀ n : ℤ,
          Summable (fun m : ℤ => ‖offDiagonalBeta n m φ‖) ∧
          HasSum (fun m : ℤ => offDiagonalBeta n m φ) (betaSum n φ) ∧
          (∑' m : ℤ, ‖offDiagonalBeta n m φ‖) ≤
            C*Real.sqrt Lib.invSqSum*spectralNorm φ ∧
          (∑' m : ℤ, ‖offDiagonalBeta n m φ‖) ≤ C*Real.sqrt Lib.invSqSum*M := by
  obtain ⟨U, hUo, hUr, hUsub, hloc⟩ := betaLocalData
  refine ⟨U, hUo, hUr, hUsub, fun φ0 hφ0 => ?_⟩
  obtain ⟨V, C, M, hVo, hφ0V, hVU, hC, hM, hV⟩ := hloc φ0 hφ0
  refine ⟨V, C, M, hVo, hφ0V, hVU, hC, hM, fun φ hφ => ?_⟩
  obtain ⟨hs, hspec, hb⟩ := hV φ hφ
  refine ⟨hs, hspec, hb, fun n => ?_⟩
  obtain ⟨hsum, ht1, ht2⟩ := row_bounds hC φ hs hspec hb n
  exact ⟨hsum, hasSum_offDiagonalBeta_betaSum n φ (hUsub (hVU hφ)), ht1, ht2⟩

end
end NlsGge.GKDefinitionDesign
