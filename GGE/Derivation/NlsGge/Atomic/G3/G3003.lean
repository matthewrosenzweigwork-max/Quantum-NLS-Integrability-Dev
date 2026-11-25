import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G2.G2072Host
import NlsGge.ThirdConsultation.G3.G3SourcePathHost
import NlsGge.ThirdConsultation.G3.G3003Host
import Armstrong.Frozen.RawBeta.gkBetaSourceWellDefined38
import Armstrong.Frozen.RawBetaAnalytic.gkSourceBeta38
import Armstrong.Work.RawBetaSum

/- G3_003 PRODUCTION01 (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/Atomic/G3/G3003.lean, namespace NlsGge.GKDefinitionDesign.
   Head VERBATIM from followup7 STATEMENTS/G3.md:68-77 (no later round changes G3-003).
   Proof: offDiagonalBeta n m = gk151BetaAmbient38 = (m != n) frozen gkSourceBeta38 (RawBetaSum.gk151BetaAmbient_eq_source38), which is
   Classical.choose of the frozen gkBetaSourceWellDefined38 value; GKSourceBetaValue38 gives HasGKImproperPathIntegral38 for EVERY
   rooted path (this includes the branch-endpoint case, the anchor's own clause).  Conjunct 3: uniqueness of limits along the
   (non-trivial) filter nhdsWithin (0,0) of the open triangle, then k = 0.  No hypothesis beyond the head. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem offDiagonalBeta_eq_source (n m : ℤ) (hmn : m ≠ n) (φ : SourcePotential) :
    offDiagonalBeta n m φ.1 =
      gkSourceBeta38 sourceW sourceFamily.W_open sourceFamily.W_real
        sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
        sourceFamily.F_period n m hmn φ :=
  gk151BetaAmbient_eq_source38 sourceW sourceFamily.W_open sourceFamily.W_real
    sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
    sourceFamily.F_period n m hmn φ

theorem offDiagonalBeta_pathValue (n m : ℤ) (hmn : m ≠ n) (φ : SourcePotential)
    (p : SourcePath m φ) :
    HasGKImproperPathIntegral38 n m sourceF (sourceGK φ) p (offDiagonalBeta n m φ.1) := by
  have hspec := Classical.choose_spec
    ((gkBetaSourceWellDefined38 sourceW sourceFamily.W_open sourceFamily.W_real
      sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
      sourceFamily.F_period n φ.1 φ.2 m hmn).1)
  rw [offDiagonalBeta_eq_source n m hmn φ]
  obtain ⟨_, _, hall⟩ := hspec.1
  exact hall p

theorem triangleFilter_neBot :
    (nhdsWithin ((0 : ℝ), (0 : ℝ))
      {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot]
  have h0 : Tendsto (fun t : ℝ => (t, t)) (nhds 0) (nhds ((0 : ℝ), (0 : ℝ))) :=
    (continuous_id.prodMk continuous_id).tendsto' 0 _ rfl
  refine mem_closure_of_tendsto (h0.mono_left nhdsWithin_le_nhds : Tendsto (fun t : ℝ => (t, t))
    (nhdsWithin 0 (Ioi 0)) (nhds ((0 : ℝ), (0 : ℝ)))) ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
  exact ⟨ht.1, ht.1, by linarith [ht.2]⟩

theorem G3_003 (n m : ℤ) (hmn : m ≠ n) (φ : SourcePotential)
    (p q : SourcePath m φ) :
  HasGKImproperPathIntegral38 n m sourceF (sourceGK φ) p (offDiagonalBeta n m φ.1) ∧
  HasGKImproperPathIntegral38 n m sourceF (sourceGK φ) q (offDiagonalBeta n m φ.1) ∧
  ∀ a b : ℂ,
    HasGKImproperPathIntegral38 n m sourceF (sourceGK φ) p a →
    HasGKImproperPathIntegral38 n m sourceF (sourceGK φ) q b →
    a = b ∧ ∃ k : ℤ, a-b = (k : ℂ)*abelianPeriod38 m φ.1 (psi n φ.1) := by
  have hp := offDiagonalBeta_pathValue n m hmn φ p
  have hq := offDiagonalBeta_pathValue n m hmn φ q
  refine ⟨hp, hq, fun a b ha hb => ?_⟩
  have := triangleFilter_neBot
  have hab : a = b := by
    rw [tendsto_nhds_unique ha.2 hp.2, tendsto_nhds_unique hb.2 hq.2]
  exact ⟨hab, 0, by simp [hab]⟩

end
end NlsGge.GKDefinitionDesign
