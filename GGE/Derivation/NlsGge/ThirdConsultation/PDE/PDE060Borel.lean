import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14Action

/- PDE060B PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target
   NlsGge/ThirdConsultation/PDE/PDE060Borel.lean, namespace NlsGge.ThirdConsultation.PDE. Support for PDE-060
   (no packet increment): the second conjunct actionNormBorel = comap actionCoe actionProductBorel, from separability of
   lp¹(ℤ) taken as an explicit hypothesis `hsep` (proof development LP1Separable, in progress).
   (comap ≤ borel) actionCoe J n = J n / w_n is continuous into the product topology (|f n| ≤ ‖f‖ in lp¹).
   (borel ≤ comap) the cone is second countable (subtype of a separable metric space), so every open set is a countable
   union of balls with dense centres and rational radii; each ball {J | ‖J - x‖ < r} is
   actionCoe⁻¹' {y | Σ' ofReal |w_n y_n - x_n| < ofReal r}, a measurable set of the product σ-algebra, which is the
   product Borel σ-algebra (Pi.borelSpace, ℤ countable). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Metric
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GKDefinitionDesign
namespace NlsGge.ThirdConsultation.PDE

theorem lp1_coord_continuous (n : ℤ) :
    Continuous (fun f : WeightedActionSpace => f n) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) (fun f g => ?_)).continuous
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  have h := lp.norm_apply_le_norm (by norm_num : (1 : ENNReal) ≠ 0) (f - g) n
  rwa [lp.coeFn_sub, Pi.sub_apply] at h

theorem actionCoe_continuous : Continuous actionCoe := by
  refine continuous_pi (fun n => ?_)
  show Continuous (fun I : PositiveActionSpace => I.val n / actionWeight n)
  exact ((lp1_coord_continuous n).comp continuous_subtype_val).div_const _

theorem actionCoe_mul (J : PositiveActionSpace) (n : ℤ) :
    actionWeight n * actionCoe J n = J.val n := by
  show actionWeight n * (J.val n / actionWeight n) = J.val n
  have h : actionWeight n ≠ 0 := (sobolevModeWeight_pos 1 n).ne'
  field_simp

/-- Each norm ball of the cone is a coordinate preimage of a product-measurable set. -/
theorem ball_eq_preimage (x : PositiveActionSpace) (r : ℝ) :
    ball x r = actionCoe ⁻¹' {y : ℤ → ℝ |
      (∑' n : ℤ, ENNReal.ofReal |actionWeight n * y n - x.val n|) < ENNReal.ofReal r} := by
  ext J
  simp only [mem_ball, Set.mem_preimage, Set.mem_setOf_eq]
  have hd : dist J x = ‖J.val - x.val‖ := by rw [Subtype.dist_eq, dist_eq_norm]
  have hs := lp.hasSum_norm (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal) (J.val - x.val)
  simp only [ENNReal.toReal_one, Real.rpow_one] at hs
  have he : (∑' n : ℤ, ENNReal.ofReal |actionWeight n * actionCoe J n - x.val n|) =
      ENNReal.ofReal ‖J.val - x.val‖ := by
    rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) hs.summable]
    refine tsum_congr (fun n => ?_)
    rw [actionCoe_mul, lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs]
  rw [hd, he]
  constructor
  · intro h
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (norm_nonneg _) h)).2 h
  · intro h
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).1 h

theorem actionNormBorel_eq_comap
    (hsep : TopologicalSpace.SeparableSpace (lp (fun _ : ℤ => ℝ) 1)) :
    actionNormBorel = MeasurableSpace.comap actionCoe actionProductBorel := by
  have hprod : actionProductBorel = (inferInstance : MeasurableSpace (ℤ → ℝ)) :=
    (BorelSpace.measurable_eq (α := ℤ → ℝ)).symm
  apply le_antisymm
  · -- every norm-open set is coordinate measurable
    unfold actionNormBorel
    refine MeasurableSpace.generateFrom_le (fun U hU0 => ?_)
    have hU : IsOpen U := hU0
    haveI := hsep
    obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense PositiveActionSpace
    set S : Set (PositiveActionSpace × ℚ) :=
      {p | p.1 ∈ D ∧ (0 : ℝ) < p.2 ∧ ball p.1 (p.2 : ℝ) ⊆ U} with hS
    have hSc : S.Countable :=
      Set.Countable.mono (fun p hp => Set.mem_prod.2 ⟨hp.1, Set.mem_univ p.2⟩)
        (hDc.prod (Set.countable_univ : (Set.univ : Set ℚ).Countable))
    have hUeq : U = ⋃ p ∈ S, ball p.1 (p.2 : ℝ) := by
      ext x
      simp only [Set.mem_iUnion, exists_prop]
      constructor
      · intro hx
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
        obtain ⟨q, hq0, hq⟩ := exists_rat_btwn (by positivity : (0 : ℝ) < ε / 2)
        obtain ⟨d, hdx, hdD⟩ := Metric.dense_iff.1 hD x q hq0
        refine ⟨(d, q), ⟨hdD, hq0, fun y hy => hball ?_⟩, ?_⟩
        · rw [mem_ball] at hy hdx ⊢
          have := dist_triangle y d x
          linarith
        · rw [mem_ball, dist_comm]; exact hdx
      · rintro ⟨p, hp, hxp⟩
        exact hp.2.2 hxp
    rw [hUeq]
    refine MeasurableSet.biUnion hSc (fun p _ => ?_)
    rw [ball_eq_preimage]
    refine ⟨_, ?_, rfl⟩
    rw [hprod]
    refine measurableSet_lt (Measurable.ennreal_tsum (fun n => ?_)) measurable_const
    exact ((((measurable_pi_apply n).const_mul _).sub_const _).abs).ennreal_ofReal
  · -- actionCoe is continuous, so coordinate sets are norm-Borel
    rw [MeasurableSpace.comap_le_iff_le_map]
    unfold actionProductBorel actionNormBorel
    refine MeasurableSpace.generateFrom_le (fun V hV => ?_)
    exact MeasurableSpace.measurableSet_generateFrom (hV.preimage actionCoe_continuous)

end NlsGge.ThirdConsultation.PDE
