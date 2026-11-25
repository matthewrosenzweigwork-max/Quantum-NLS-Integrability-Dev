import NlsGge.Measure.ActualSourceCMFiniteScoreEvaluationPrerequisiteV1
import NlsGge.Sobolev.WeightedHilbert

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace NlsGge.Measure

/-- The difference of two actual source score partials is the same score
applied to the actual weighted projection onto the intervening modes. -/
theorem actualSourceCMFiniteScorePartial_shell_v1
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c))
    (N M : ℕ) (hNM : N ≤ M) :
    (fun z : ℤ → ℂ => actualSourceCMFiniteScorePartial c x M z -
      actualSourceCMFiniteScorePartial c x N z) =
      actualSourceCMFiniteScorePartial c
        (NlsGge.Pilot.weightedProjection (NlsGge.Pilot.cmModeWeight c)
          (NlsGge.Pilot.symmetricModes M \ NlsGge.Pilot.symmetricModes N)
          (show NlsGge.Pilot.WeightedHilbert
            (NlsGge.Pilot.cmModeWeight c) from x)) M := by
  classical
  let S := NlsGge.Pilot.symmetricModes M \ NlsGge.Pilot.symmetricModes N
  let xS : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c) :=
    NlsGge.Pilot.weightedProjection (NlsGge.Pilot.cmModeWeight c) S
      (show NlsGge.Pilot.WeightedHilbert (NlsGge.Pilot.cmModeWeight c) from x)
  have hsub : NlsGge.Pilot.symmetricModes N ⊆ NlsGge.Pilot.symmetricModes M := by
    intro n hn
    simp only [NlsGge.Pilot.symmetricModes, Finset.mem_Icc] at hn ⊢
    exact ⟨le_trans (by omega) hn.1, le_trans hn.2 (by omega)⟩
  have hSsub : S ⊆ NlsGge.Pilot.symmetricModes M := Finset.sdiff_subset
  funext z
  rw [actualSourceCMFiniteScorePartial_eq_coordinate_sum_v1 c x M,
    actualSourceCMFiniteScorePartial_eq_coordinate_sum_v1 c x N,
    actualSourceCMFiniteScorePartial_eq_coordinate_sum_v1 c xS M]
  change (∑ n ∈ NlsGge.Pilot.symmetricModes M,
      NlsGge.Pilot.cmModeWeight c n *
        inner ℝ ((show NlsGge.Pilot.WeightedHilbert
          (NlsGge.Pilot.cmModeWeight c) from x) n) (z n)) -
    ∑ n ∈ NlsGge.Pilot.symmetricModes N,
      NlsGge.Pilot.cmModeWeight c n *
        inner ℝ ((show NlsGge.Pilot.WeightedHilbert
          (NlsGge.Pilot.cmModeWeight c) from x) n) (z n) =
    ∑ n ∈ NlsGge.Pilot.symmetricModes M,
      NlsGge.Pilot.cmModeWeight c n *
        inner ℝ ((show NlsGge.Pilot.WeightedHilbert
          (NlsGge.Pilot.cmModeWeight c) from xS) n) (z n)
  have hleft :
      (∑ n ∈ NlsGge.Pilot.symmetricModes M,
        NlsGge.Pilot.cmModeWeight c n *
          inner ℝ ((show NlsGge.Pilot.WeightedHilbert
            (NlsGge.Pilot.cmModeWeight c) from x) n) (z n)) -
      ∑ n ∈ NlsGge.Pilot.symmetricModes N,
        NlsGge.Pilot.cmModeWeight c n *
          inner ℝ ((show NlsGge.Pilot.WeightedHilbert
            (NlsGge.Pilot.cmModeWeight c) from x) n) (z n) =
      ∑ n ∈ S, NlsGge.Pilot.cmModeWeight c n *
        inner ℝ ((show NlsGge.Pilot.WeightedHilbert
          (NlsGge.Pilot.cmModeWeight c) from x) n) (z n) := by
    rw [← Finset.sum_sdiff hsub]
    simp only [S]
    ring
  have hright :
      (∑ n ∈ NlsGge.Pilot.symmetricModes M,
        NlsGge.Pilot.cmModeWeight c n *
          inner ℝ ((show NlsGge.Pilot.WeightedHilbert
            (NlsGge.Pilot.cmModeWeight c) from xS) n) (z n)) =
      ∑ n ∈ S, NlsGge.Pilot.cmModeWeight c n *
        inner ℝ ((show NlsGge.Pilot.WeightedHilbert
          (NlsGge.Pilot.cmModeWeight c) from x) n) (z n) := by
    rw [← Finset.sum_sdiff hSsub]
    have htail :
        (∑ n ∈ NlsGge.Pilot.symmetricModes M \ S,
          NlsGge.Pilot.cmModeWeight c n *
            inner ℝ ((show NlsGge.Pilot.WeightedHilbert
              (NlsGge.Pilot.cmModeWeight c) from xS) n) (z n)) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp only [Finset.mem_sdiff] at hn
      simp [xS, NlsGge.Pilot.weightedProjection_apply, hn.2]
    rw [htail, zero_add]
    apply Finset.sum_congr rfl
    intro n hn
    simp [xS, NlsGge.Pilot.weightedProjection_apply, hn]
  rw [hleft, hright]

end NlsGge.Measure
