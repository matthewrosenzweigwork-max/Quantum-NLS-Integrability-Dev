import NlsGge.Measure.ActualSourceCMFiniteScoreL2CauchyContractV1
import NlsGge.Measure.ActualSourceCMFiniteScoreCoordinateBridgeV2
import NlsGge.Measure.WeightedModes
import NlsGge.Sobolev.CMWeightComparison

set_option autoImplicit false
noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace NlsGge.Measure

set_option backward.isDefEq.respectTransparency false in
theorem actualSourceCMFiniteScoreFunctional_modeEvaluation_v1
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c))
    (n : ℤ) (z : ℂ) :
    actualSourceCMFiniteScoreFunctional c x (fullWeightedModeMap c 0 n z) =
      NlsGge.Pilot.cmModeWeight c n * inner ℝ
        ((show NlsGge.Pilot.WeightedHilbert
          (NlsGge.Pilot.cmModeWeight c) from x) n) z := by
  let Jx := NlsGge.Pilot.cmToFullWeightedHilbert c 0 (by norm_num) x
  have hcoordinate :=
    actualSourceCMFiniteScore_mode_inner_coordinate_v2 c x n z
  have hpair : inner ℝ Jx (fullWeightedModeMap c 0 n z) =
      NlsGge.Pilot.sourceRate c n * inner ℝ z
        ((show NlsGge.Pilot.WeightedHilbert
          (NlsGge.Pilot.cmModeWeight c) from x) n) := by
    calc
      inner ℝ Jx (fullWeightedModeMap c 0 n z) =
          inner ℝ (fullWeightedModeMap c 0 n z) Jx := real_inner_comm _ _
      _ = _ := hcoordinate
  change (2 : ℝ) * inner ℝ Jx (fullWeightedModeMap c 0 n z) = _
  rw [hpair]
  simp only [NlsGge.Pilot.cmModeWeight]
  rw [real_inner_comm z]
  ring

theorem actualSourceCMFiniteScorePartial_eq_coordinate_sum_v1
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c))
    (N : ℕ) :
    actualSourceCMFiniteScorePartial c x N =
      fun z : ℤ → ℂ =>
        ∑ n ∈ NlsGge.Pilot.symmetricModes N,
          NlsGge.Pilot.cmModeWeight c n * inner ℝ
            ((show NlsGge.Pilot.WeightedHilbert
              (NlsGge.Pilot.cmModeWeight c) from x) n) (z n) := by
  funext z
  change (actualSourceCMFiniteScoreFunctional c x)
      (fullWeightedSequencePartial c 0 N z) = _
  rw [fullWeightedSequencePartial_eq_sumModeMaps]
  calc
    actualSourceCMFiniteScoreFunctional c x
        (∑ n ∈ NlsGge.Pilot.symmetricModes N,
          fullWeightedModeMap c 0 n (z n)) =
      ∑ n ∈ NlsGge.Pilot.symmetricModes N,
        actualSourceCMFiniteScoreFunctional c x
          (fullWeightedModeMap c 0 n (z n)) := by
            exact map_sum (actualSourceCMFiniteScoreFunctional c x) _ _
    _ = ∑ n ∈ NlsGge.Pilot.symmetricModes N,
        NlsGge.Pilot.cmModeWeight c n * inner ℝ
          ((show NlsGge.Pilot.WeightedHilbert
            (NlsGge.Pilot.cmModeWeight c) from x) n) (z n) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact actualSourceCMFiniteScoreFunctional_modeEvaluation_v1 c x n (z n)

end NlsGge.Measure
