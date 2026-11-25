import Mathlib
import NlsGge.Atomic.G3.G3031
import NlsGge.Atomic.G3.G3023
import NlsGge.Atomic.G4.G4011
import NlsGge.Atomic.G4.G4037
import NlsGge.ThirdConsultation.G3.G3026Support
import NlsGge.ThirdConsultation.G3.G3026Host
import NlsGge.ThirdConsultation.G3.G3028Host
import NlsGge.ThirdConsultation.G3.G3003Host
import NlsGge.Atomic.X.X006
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic

/- G3-031 ALL-DOMAIN SUPPORT G3031All (proof development, AUTHOR; not semantically reviewed by its author; not accepted).
   Target NlsGge/Atomic/G3/G3031All.lean, namespace NlsGge.GKDefinitionDesign.  Supporting module, NOT a packet head.
   Content: `AnalyticOnNhd ℂ (betaSum n) sourceBetaW` natively, i.e. G3_031's analyticity conclusion on ALL of sourceBetaW
   (landed G3_031 only gives it on U = Winverse ∩ sourceBetaW).
   Route (Decision 13: no analytic anchor; gkSourceBeta_analytic38 / gk151BetaAmbient_analytic38 / sourceFamily.XY_analytic /
   gk16_same_family_scalar_models_analytic38 / any X-006 analyticity field is NOT used; `sourceFamily.beta_spec` is used only through
   the landed bridge `hasSum_offDiagonalBeta_betaSum`, which is summability/sum identity data):
   (1) local data at EVERY φ0 ∈ sourceBetaW from the landed full-domain estimate `source_beta_inverse_distance_on_sourceBetaW`
       (G4-037, Pro round 12 §5.3); `spectralNorm φ ≤ M` from `∑' ‖mass‖² ≤ M²` as in G4037 (Real.sqrt_le_iff).
   (2) tail bounds `tail_bounds` and `sub_betaPartialSum_eq` (landed G3026Support) + `tendsto_fixedIndexReciprocalTail`
       give TendstoLocallyUniformlyOn (betaPartialSum n) (betaSum n) atTop sourceBetaW, exactly as the end of G3_027 but on sourceBetaW.
   (3) partial sums analytic on sourceW ⊇ sourceBetaW: landed `G3031Aux.analyticOnNhd_betaPartialSum` (G3_023 per term).
   (4) landed G4-011 `analyticOnNhd_of_locally_uniform_limit` on the open set sourceBetaW (sourceFamily.V_open). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section
namespace G3031AllAux

/-- Local data of the G3_027 shape at every point of `sourceBetaW`. -/
theorem betaLocalDataAll (φ0 : PotPair) (hφ0 : φ0 ∈ sourceBetaW) :
    ∃ V : Set PotPair, ∃ C M : ℝ,
      IsOpen V ∧ φ0 ∈ V ∧ V ⊆ sourceBetaW ∧ 0 < C ∧ 0 ≤ M ∧
      ∀ φ ∈ V,
        Summable (fun m : ℤ => ‖gk151BetaMass38 φ m‖^2) ∧ spectralNorm φ ≤ M ∧
        ∀ n m : ℤ,
          ‖offDiagonalBeta n m φ‖ ≤ C*‖gk151BetaMass38 φ m‖*Lib.c3w n m := by
  obtain ⟨V, hVo, hφ0V, hVS, C, M, hC, hM, hV⟩ :=
    source_beta_inverse_distance_on_sourceBetaW φ0 hφ0
  refine ⟨V, C, M, hVo, hφ0V, hVS, hC, hM, fun φ hφ => ?_⟩
  obtain ⟨hs, htsum, hb⟩ := hV φ hφ
  refine ⟨hs, ?_, hb⟩
  unfold spectralNorm
  exact Real.sqrt_le_iff.mpr ⟨hM, htsum⟩

/-- Locally uniform convergence of the partial sums on all of `sourceBetaW`. -/
theorem tendstoLocallyUniformlyOn_betaPartialSum (n : ℤ) :
    TendstoLocallyUniformlyOn (betaPartialSum n) (betaSum n) atTop sourceBetaW := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε φ0 hφ0
  obtain ⟨V, C, M, hVo, hφ0V, hVS, hC, hM, hV⟩ := betaLocalDataAll φ0 hφ0
  refine ⟨V, mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hφ0V), ?_⟩
  have hlim : Tendsto (fun R : ℕ => C*M*fixedIndexReciprocalTail n R) atTop (𝓝 0) := by
    simpa using (tendsto_fixedIndexReciprocalTail n).const_mul (C*M)
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with R hR' φ hφ
  rw [dist_eq_norm]
  obtain ⟨hs, hspec, hb⟩ := hV φ hφ
  obtain ⟨hsum, hbound⟩ := tail_bounds hC n R φ hs hspec (fun m => hb n m)
  have hHas := hasSum_offDiagonalBeta_betaSum n φ (hVS hφ)
  have hnorm : ∀ m : ℤ, ‖(if (R : ℝ) < |(m : ℝ)| then offDiagonalBeta n m φ else 0)‖ =
      if (R : ℝ) < |(m : ℝ)| then ‖offDiagonalBeta n m φ‖ else 0 := fun m => by
    split_ifs <;> simp
  have hle : ‖betaSum n φ - betaPartialSum n R φ‖ ≤ C*M*fixedIndexReciprocalTail n R := by
    rw [sub_betaPartialSum_eq n R φ hHas]
    calc ‖∑' m : ℤ, if (R : ℝ) < |(m : ℝ)| then offDiagonalBeta n m φ else 0‖
        ≤ ∑' m : ℤ, ‖(if (R : ℝ) < |(m : ℝ)| then offDiagonalBeta n m φ else 0)‖ :=
          norm_tsum_le_tsum_norm (hsum.congr (fun m => (hnorm m).symm))
      _ = ∑' m : ℤ, if (R : ℝ) < |(m : ℝ)| then ‖offDiagonalBeta n m φ‖ else 0 :=
          tsum_congr hnorm
      _ ≤ C*M*fixedIndexReciprocalTail n R := hbound
  exact lt_of_le_of_lt hle hR'

end G3031AllAux

theorem betaSum_analyticOnNhd_sourceBetaW (n : ℤ) :
    AnalyticOnNhd ℂ (betaSum n) sourceBetaW :=
  NlsGge.Atomic.G4.analyticOnNhd_of_locally_uniform_limit sourceFamily.V_open
    (f := betaPartialSum n) (g := betaSum n)
    (fun R => (G3031Aux.analyticOnNhd_betaPartialSum n R).mono
      (fun _ hφ => sourceFamily.V_W hφ))
    (G3031AllAux.tendstoLocallyUniformlyOn_betaPartialSum n)

end
end NlsGge.GKDefinitionDesign
