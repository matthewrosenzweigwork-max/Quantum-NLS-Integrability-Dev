import Mathlib
import NlsGge.Atomic.G5.G5010
import NlsGge.Atomic.G5.G5012
import NlsGge.Atomic.G5.G5012Sup2
import NlsGge.Atomic.G5.G5012Sup3

/- G5-013 PRODUCTION02 (proof development; tactic fix of g5013_proj_sub after root chain probe G5CHAIN_MAINPROBE02:
   PhysicalL2 has no StarAddMonoid instance, so star additivity goes through landed star_add_lp / star_smul_lp; AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5013.lean.
   Head `G5013` verbatim from STATEMENTS/G5.md (followup12; round 14, cluster 5). No lexical edits.
   Route (GK-17.3 p. 95; Pro round 14 "G5012/013"): by the G5-012 adjoint identity, (A* - id) b_j = gradient(coordinate j) - b_j;
   by Sup3 and Sup2 this is (+-1/sqrt 2) * projection(grad X_n - basis+) (or Y). The projection estimate
   ||proj v|| <= sqrt 2 * pairGradientNorm v (Sup1) bounds it by the G5-010 l2 errors, separately for true and false coordinates. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation (finiteGap)
open NlsGge.ThirdConsultation.G5017Support1

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5013_proj_sub (v w : PotPair) :
    pairGradientProjection (v - w) = pairGradientProjection v - pairGradientProjection w := by
  unfold pairGradientProjection
  have h : star (v.1 - w.1) = star v.1 - star w.1 := by
    conv_lhs => rw [sub_eq_add_neg, ← neg_one_smul ℂ w.1, star_add_lp, star_smul_lp, map_neg, map_one,
      neg_one_smul]
    abel
  rw [Prod.fst_sub, Prod.snd_sub, h]
  abel

theorem g5013_bound (r : ℝ) (hr : |r| = 1 / Real.sqrt 2) (v : PotPair) :
    ‖r • pairGradientProjection v‖ ^ 2 ≤ pairGradientNorm v ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, hr]
  have h := norm_pairGradientProjection_le v
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : 1 / Real.sqrt 2 * ‖pairGradientProjection v‖ ≤ pairGradientNorm v := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hs]
    linarith [mul_comm (Real.sqrt 2) (pairGradientNorm v)]
  have h0 : 0 ≤ 1 / Real.sqrt 2 * ‖pairGradientProjection v‖ := by positivity
  nlinarith

theorem g5013_abs : |(1 / Real.sqrt 2 : ℝ)| = 1 / Real.sqrt 2 ∧
    |(-1 / Real.sqrt 2 : ℝ)| = 1 / Real.sqrt 2 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · exact abs_of_pos (by positivity)
  · rw [abs_div, abs_neg, abs_one, abs_of_pos hs]

theorem G5013 (u : PhysicalL2) (hu : finiteGap u) :
  Summable (fun j : Bool × ℤ =>
    ‖(jacobianAdjoint u - ContinuousLinearMap.id ℝ PhysicalL2)
      (physicalFourierBasis j)‖^2) := by
  obtain ⟨hX, hY, -⟩ := G5010 u hu
  have sX := g5006_sq hX
  have sY := g5006_sq hY
  have hle : ∀ j : Bool × ℤ,
      ‖(jacobianAdjoint u - ContinuousLinearMap.id ℝ PhysicalL2) (physicalFourierBasis j)‖ ^ 2 ≤
        (if j.1 then
          pairGradientNorm (pairGradient (cartesianX j.2) (realSlice u) - fourierRealBasisPlus j.2) ^ 2
        else
          pairGradientNorm (pairGradient (cartesianY j.2) (realSlice u) - fourierRealBasisMinus j.2) ^ 2) := by
    rintro ⟨b, n⟩
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, G5012.2.2 u (b, n),
      gradient_physicalCoordinate]
    obtain ⟨hp, hm⟩ := physicalFourierBasis_projection n
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← hm, ← smul_sub, ← g5013_proj_sub]
      exact g5013_bound _ g5013_abs.2 _
    · simp only [↓reduceIte]
      rw [← hp, ← smul_sub, ← g5013_proj_sub]
      exact g5013_bound _ g5013_abs.1 _
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hle ?_
  refine (summable_prod_of_nonneg (fun j => ?_)).mpr ⟨fun b => ?_, Summable.of_finite⟩
  · show 0 ≤ (if j.1 then _ else _)
    split_ifs <;> positivity
  · cases b
    · simpa using sY
    · simpa using sX

end
end NlsGge.GKDefinitionDesign
