import Mathlib
import NlsGge.ThirdConsultation.PDE.PDE060Borel
import NlsGge.ThirdConsultation.PDE.LP1Separable
import NlsGge.Atomic.G6.G6034
import LiebLiniger.FixedPeriod.Atomic.ALLS.TransCPrepK3Rate

/-! # Trunk C PREPARATORY (K4): product-Borel measurability of zero extensions from `ℓ¹₊`

Author: Claude Opus 5.5 (preparatory author P3).  NOT self-reviewed, NOT accepted, NOT approved,
NOT rooted.  Namespace `NlsGge.ALLS.TransCPrep`; every name carries the prefix `prep_`.
Unweighted mirror of `PDE060Cone.positiveActionCone_eq/_measurableSet` and
`PDE060Borel.ball_eq_preimage/actionNormBorel_eq_comap` (+ `PDE061Core.measurable_omega_of`):
here the cone carries the plain `ℓ¹` metric and the coordinate map has no weight division.
`ℤ → ℝ` carries its instance (product = Borel) σ-algebra throughout.

Binders / conclusions (one line each):
* `prep_l1Cone_eq` : `ℓ¹₊ = {I ≥ 0} ∩ ⋃_{C : ℕ} ⋂_{s : Finset ℤ} {Σ_{n∈s} I n ≤ C}`.
* `prep_l1Cone_measurableSet` : `ℓ¹₊` is a measurable subset of `ℤ → ℝ`.
* `prep_coe J` : for `J : PositiveActionSpace` (nonnegative elements of `lp ℝ 1` on `ℤ`), its
  underlying sequence `n ↦ J n` (no weight).
* `prep_toPos I hI` : for `I ∈ ℓ¹₊`, the same sequence as an element of `PositiveActionSpace`;
  `prep_coe_toPos` : `prep_coe (prep_toPos I hI) = I`.
* `prep_coe_mem J` : `prep_coe J ∈ ℓ¹₊`.
* `prep_coe_continuous` : `prep_coe` is continuous into the product topology.
* `prep_dist_eq J K` / `prep_summable_abs_sub J K` : `dist J K = Σ' |J n − K n|`, and this family is
  summable (so the `tsum` is genuine).
* `prep_ball_eq_preimage x r` : the `ℓ¹` ball of radius `r` about `x` in the cone is the
  `prep_coe`-preimage of `{y | Σ' ofReal |y n − x n| < ofReal r}` (extended-real sum).
* `prep_borel_eq_comap` : the Borel σ-algebra of `PositiveActionSpace` equals the comap of the
  product σ-algebra of `ℤ → ℝ` along `prep_coe` (uses the existing separability of `lp ℝ 1`).
* `prep_continuous_of_l1 f hf` : if `f : (ℤ → ℝ) → ℝ` is ε–δ `ℓ¹`-continuous at every point of
  `ℓ¹₊` (hypothesis `hf`, C-MAIN item 3 shape), then `J ↦ f (prep_coe J)` is continuous on
  `PositiveActionSpace`.
* `prep_measurable_zeroExt f hf` : under the same `hf`, the zero extension
  `I ↦ if I ∈ ℓ¹₊ then f I else 0` is measurable on `ℤ → ℝ`.
* `prep_measurable_omegaOfRate rate n hrate` : under the `ℓ²₊`-continuity hypothesis `hrate` of
  K3, the candidate `prep_omegaOfRate rate n` (already zero off `ℓ¹₊`) is measurable. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Topology Metric
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.PDE

namespace NlsGge.ALLS.TransCPrep

theorem prep_l1Cone_eq :
    prep_l1Cone =
      {I : ℤ → ℝ | ∀ n : ℤ, 0 ≤ I n} ∩
        ⋃ C : ℕ, ⋂ s : Finset ℤ, {I : ℤ → ℝ | ∑ n ∈ s, I n ≤ C} := by
  ext I
  simp only [prep_l1Cone, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter]
  constructor
  · rintro ⟨h0, hs⟩
    exact ⟨h0, ⌈∑' n : ℤ, I n⌉₊, fun s =>
      (hs.sum_le_tsum s (fun n _ => h0 n)).trans (Nat.le_ceil _)⟩
  · rintro ⟨h0, C, hC⟩
    exact ⟨h0, summable_of_sum_le h0 hC⟩

theorem prep_l1Cone_measurableSet : MeasurableSet prep_l1Cone := by
  rw [prep_l1Cone_eq]
  refine MeasurableSet.inter ?_ ?_
  · have : {I : ℤ → ℝ | ∀ n : ℤ, 0 ≤ I n} = ⋂ n : ℤ, {I : ℤ → ℝ | 0 ≤ I n} := by
      ext I; simp
    rw [this]
    exact MeasurableSet.iInter (fun n => measurableSet_le measurable_const (measurable_pi_apply n))
  · refine MeasurableSet.iUnion (fun C => MeasurableSet.iInter (fun s => ?_))
    exact measurableSet_le (Finset.measurable_sum s (fun n _ => measurable_pi_apply n))
      measurable_const

/-- Underlying (unweighted) sequence of a cone point. -/
def prep_coe (J : PositiveActionSpace) : ℤ → ℝ := fun n => J.val n

/-- A point of `ℓ¹₊` as a cone point. -/
def prep_toPos (I : ℤ → ℝ) (hI : I ∈ prep_l1Cone) : PositiveActionSpace :=
  ⟨⟨I, memℓp_gen (hI.2.congr (fun n => by
      rw [ENNReal.toReal_one, Real.rpow_one, Real.norm_of_nonneg (hI.1 n)]))⟩, hI.1⟩

theorem prep_coe_toPos (I : ℤ → ℝ) (hI : I ∈ prep_l1Cone) : prep_coe (prep_toPos I hI) = I :=
  rfl

theorem prep_coe_mem (J : PositiveActionSpace) :
    (∀ k, 0 ≤ prep_coe J k) ∧ Summable (prep_coe J) :=
  ⟨J.2, Summable.of_norm (f := prep_coe J) (G6034Aux.hasSum_norm_one J.val).summable⟩

theorem prep_coe_continuous : Continuous prep_coe :=
  continuous_pi (fun n => (lp1_coord_continuous n).comp continuous_subtype_val)

theorem prep_summable_abs_sub (J K : PositiveActionSpace) :
    Summable (fun n => |prep_coe J n - prep_coe K n|) := by
  refine (G6034Aux.hasSum_norm_one (J.val - K.val)).summable.congr (fun n => ?_)
  rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs]
  rfl

theorem prep_dist_eq (J K : PositiveActionSpace) :
    dist J K = ∑' n, |prep_coe J n - prep_coe K n| := by
  rw [Subtype.dist_eq, dist_eq_norm, ← (G6034Aux.hasSum_norm_one (J.val - K.val)).tsum_eq]
  refine tsum_congr (fun n => ?_)
  rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs]
  rfl

theorem prep_ball_eq_preimage (x : PositiveActionSpace) (r : ℝ) :
    ball x r = prep_coe ⁻¹' {y : ℤ → ℝ |
      (∑' n : ℤ, ENNReal.ofReal |y n - prep_coe x n|) < ENNReal.ofReal r} := by
  ext J
  simp only [mem_ball, Set.mem_preimage, Set.mem_setOf_eq]
  have he : (∑' n : ℤ, ENNReal.ofReal |prep_coe J n - prep_coe x n|) =
      ENNReal.ofReal (dist J x) := by
    rw [prep_dist_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => abs_nonneg _)
      (prep_summable_abs_sub J x)]
  rw [he]
  constructor
  · intro h
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt dist_nonneg h)).2 h
  · intro h
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).1 h

/-- Norm-Borel σ-algebra of the cone = coordinate comap of the product σ-algebra. -/
theorem prep_borel_eq_comap :
    borel PositiveActionSpace =
      MeasurableSpace.comap prep_coe (inferInstance : MeasurableSpace (ℤ → ℝ)) := by
  apply le_antisymm
  · refine MeasurableSpace.generateFrom_le (fun U hU0 => ?_)
    have hU : IsOpen U := hU0
    haveI := lp_one_int_real_separableSpace
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
    rw [prep_ball_eq_preimage]
    refine ⟨_, ?_, rfl⟩
    refine measurableSet_lt (Measurable.ennreal_tsum (fun n => ?_)) measurable_const
    exact (((measurable_pi_apply n).sub_const _).abs).ennreal_ofReal
  · rw [MeasurableSpace.comap_le_iff_le_map]
    have hprod : (inferInstance : MeasurableSpace (ℤ → ℝ)) = borel (ℤ → ℝ) :=
      BorelSpace.measurable_eq
    rw [hprod]
    refine MeasurableSpace.generateFrom_le (fun V hV => ?_)
    exact MeasurableSpace.measurableSet_generateFrom (hV.preimage prep_coe_continuous)

theorem prep_continuous_of_l1 (f : (ℤ → ℝ) → ℝ)
    (hf : ∀ I : ℤ → ℝ, ((∀ k, 0 ≤ I k) ∧ Summable I) →
      ∀ ε > 0, ∃ δ > 0, ∀ J : ℤ → ℝ, ((∀ k, 0 ≤ J k) ∧ Summable J) →
        ∑' k, |J k - I k| < δ → |f J - f I| < ε) :
    Continuous (fun J : PositiveActionSpace => f (prep_coe J)) := by
  rw [Metric.continuous_iff]
  intro J ε hε
  obtain ⟨δ, hδ, h⟩ := hf (prep_coe J) (prep_coe_mem J) ε hε
  refine ⟨δ, hδ, fun K hK => ?_⟩
  rw [prep_dist_eq] at hK
  rw [Real.dist_eq]
  exact h (prep_coe K) (prep_coe_mem K) hK

open scoped Classical in
/-- **Measurability of the zero extension** of an `ℓ¹₊`-continuous function. -/
theorem prep_measurable_zeroExt (f : (ℤ → ℝ) → ℝ)
    (hf : ∀ I : ℤ → ℝ, ((∀ k, 0 ≤ I k) ∧ Summable I) →
      ∀ ε > 0, ∃ δ > 0, ∀ J : ℤ → ℝ, ((∀ k, 0 ≤ J k) ∧ Summable J) →
        ∑' k, |J k - I k| < δ → |f J - f I| < ε) :
    Measurable (fun I : ℤ → ℝ => if I ∈ prep_l1Cone then f I else 0) := by
  intro B hB
  have hgm : MeasurableSet[borel PositiveActionSpace]
      ((fun J : PositiveActionSpace => f (prep_coe J)) ⁻¹' B) := by
    letI : MeasurableSpace PositiveActionSpace := borel _
    haveI : BorelSpace PositiveActionSpace := ⟨rfl⟩
    exact (prep_continuous_of_l1 f hf).measurable hB
  rw [prep_borel_eq_comap] at hgm
  obtain ⟨T, hT, hTeq⟩ := hgm
  have hset : (fun I : ℤ → ℝ => if I ∈ prep_l1Cone then f I else 0) ⁻¹' B =
      (prep_l1Cone ∩ T) ∪ (prep_l1Coneᶜ ∩ {_I | (0 : ℝ) ∈ B}) := by
    ext I
    by_cases hI : I ∈ prep_l1Cone
    · rw [Set.mem_preimage, if_pos hI]
      have key := Set.ext_iff.1 hTeq (prep_toPos I hI)
      simp only [Set.mem_preimage, prep_coe_toPos] at key
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq, hI,
        not_true_eq_false, false_and, or_false, true_and]
      exact key.symm
    · rw [Set.mem_preimage, if_neg hI]
      simp [hI]
  rw [hset]
  exact (prep_l1Cone_measurableSet.inter hT).union
    (prep_l1Cone_measurableSet.compl.inter (MeasurableSet.const _))

/-- The K3 rate candidate is measurable on `ℤ → ℝ`. -/
theorem prep_measurable_omegaOfRate (rate : ℤ → (ℤ → ℝ) → ℝ) (n : ℤ)
    (hrate : ∀ q : ℤ → ℝ, ((∀ k, 0 ≤ q k) ∧ Summable (fun k => q k ^ 2)) →
      ∀ ε > 0, ∃ δ > 0, ∀ p : ℤ → ℝ, ((∀ k, 0 ≤ p k) ∧ Summable (fun k => p k ^ 2)) →
        ∑' k, (p k - q k) ^ 2 < δ → |rate n p - rate n q| < ε) :
    Measurable (prep_omegaOfRate rate n) := by
  classical
  have h := prep_measurable_zeroExt (prep_omegaOfRate rate n)
    (prep_omegaOfRate_continuous rate n hrate)
  convert h using 1
  funext I
  by_cases hI : I ∈ prep_l1Cone
  · rw [if_pos hI]
  · rw [if_neg hI, prep_omegaOfRate_of_not_mem rate n I hI]

end NlsGge.ALLS.TransCPrep
