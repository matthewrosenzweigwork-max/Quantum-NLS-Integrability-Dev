import Mathlib
import NlsGge.Atomic.F.F022
import NlsGge.Birkhoff.F07MassMoment38
import NlsGge.Birkhoff.F05Identity38
import NlsGge.Hierarchy.FiniteOrderGaussianTail38

/- F-023 PRODUCTION01 (proof development landing kit; HELD). Source: proof development/F023_PROOF03.lean.txt (author proof development; independent review proof development/REVIEW_F023_01.md), identical except this header and the removed #check/#print axioms lines. Target NlsGge/Atomic/F/F023.lean. Hosts tiltProduct/lowerQuadratic/gammaPrime verbatim from DEFINITIONS/F.lean.md; imports F022 (lowerChargeSymbol, ratePrime, f022). -/
set_option autoImplicit false

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.F

def tiltProduct (m : ℕ) (β : ℕ → ℝ) (δ : ℝ) : ℝ :=
  ∏' n : ℤ, ratePrime m β δ n / finiteHierarchyRate38 m β n

def lowerQuadratic (m : ℕ) (y : SobolevHilbert ((m - 1 : ℕ) : ℝ)) : ℝ :=
  ∑' n : ℤ, lowerChargeSymbol m n *
    ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y) n‖ ^ 2

def gammaPrime (m : ℕ) (β : ℕ → ℝ) (δ : ℝ) :
    Measure (SobolevHilbert ((m - 1 : ℕ) : ℝ)) :=
  ((countableComplexGaussian (ratePrime m β δ)).map (gaussianRealization38 m)).map
    (FinvH38 m)

namespace F023Aux

theorem L_nonneg (m : ℕ) (n : ℤ) : 0 ≤ lowerChargeSymbol m n := by
  unfold lowerChargeSymbol
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

theorem L_neg (m : ℕ) (n : ℤ) : lowerChargeSymbol m (-n) = lowerChargeSymbol m n := by
  unfold lowerChargeSymbol
  rw [Int.cast_neg, mul_neg]
  exact Even.neg_pow ⟨_, by ring⟩ _

theorem w_eq (m : ℕ) (n : ℤ) :
    sobolevModeWeight ((m - 1 : ℕ) : ℝ) n = (1 + (n : ℝ) ^ 2) ^ (m - 1) := by
  have hj : japaneseBracket n ^ 2 = 1 + (n : ℝ) ^ 2 := by
    unfold japaneseBracket
    exact Real.sq_sqrt (by positivity)
  unfold sobolevModeWeight
  rw [show (2 * ((m - 1 : ℕ) : ℝ)) = ((2 * (m - 1) : ℕ) : ℝ) by push_cast; ring]
  change japaneseBracket n ^ ((2 * (m - 1) : ℕ) : ℝ) = _
  rw [Real.rpow_natCast, pow_mul, hj]

theorem L_le_w (m : ℕ) (n : ℤ) :
    lowerChargeSymbol m n ≤ (2 * Real.pi) ^ (2 * (m - 1)) * sobolevModeWeight ((m - 1 : ℕ) : ℝ) n := by
  rw [w_eq]
  unfold lowerChargeSymbol
  have e : (2 * Real.pi * (n : ℝ)) ^ (2 * (m - 1)) =
      (2 * Real.pi) ^ (2 * (m - 1)) * ((n : ℝ) ^ 2) ^ (m - 1) := by ring
  rw [e]
  gcongr
  linarith

theorem coord_cont (r : ℝ) (n : ℤ) :
    Continuous (fun y : SobolevHilbert r =>
      (show WeightedHilbert (sobolevModeWeight r) from y) n) := by
  have hev : Continuous (fun f : lp (fun _ : ℤ => ℂ) 2 => f n) := by
    refine (LipschitzWith.of_dist_le_mul (K := 1) fun x y => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    have := lp.norm_apply_le_norm (p := (2 : ℝ≥0∞)) (by norm_num) (x - y) n
    simpa using this
  have h1 : Continuous (fun y : SobolevHilbert r =>
      weightedIsometry (sobolevModeWeight r) (show WeightedHilbert (sobolevModeWeight r) from y)) :=
    (weightedIsometry (sobolevModeWeight r)).continuous
  have key : ∀ y : SobolevHilbert r, (show WeightedHilbert (sobolevModeWeight r) from y) n =
      (Real.sqrt (sobolevModeWeight r n) : ℂ)⁻¹ *
        (weightedIsometry (sobolevModeWeight r) (show WeightedHilbert (sobolevModeWeight r) from y)) n := by
    intro y
    rw [weightedIsometry_apply]
    unfold weightedCoordinates
    have := weightSqrt_ne_zero (sobolevModeWeight r) n
    field_simp
  exact (continuous_const.mul (hev.comp h1)).congr (fun y => (key y).symm)

theorem summable_all (m : ℕ) (y : SobolevHilbert ((m - 1 : ℕ) : ℝ)) :
    Summable (fun n : ℤ => lowerChargeSymbol m n *
      ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y) n‖ ^ 2) := by
  have hs := (weightedHilbert_hasSum (sobolevModeWeight ((m - 1 : ℕ) : ℝ))
    (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y)).summable
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (L_nonneg m n) (sq_nonneg _))
    (fun n => ?_) (hs.mul_left ((2 * Real.pi) ^ (2 * (m - 1))))
  calc lowerChargeSymbol m n * ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y) n‖ ^ 2
      ≤ ((2 * Real.pi) ^ (2 * (m - 1)) * sobolevModeWeight ((m - 1 : ℕ) : ℝ) n) *
          ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y) n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (L_le_w m n) (sq_nonneg _)
    _ = _ := by ring

theorem measurable_lowerQuadratic (m : ℕ) : Measurable (lowerQuadratic m) := by
  refine measurable_of_tendsto_metrizable
    (f := fun N : ℕ => fun y : SobolevHilbert ((m - 1 : ℕ) : ℝ) =>
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, lowerChargeSymbol m n *
        ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y) n‖ ^ 2)
    (fun N => ?_) ?_
  · exact (continuous_finset_sum _ (fun n _ =>
      continuous_const.mul ((coord_cont _ n).norm.pow 2))).measurable
  · rw [tendsto_pi_nhds]
    intro y
    exact tendsto_sum_Icc38 (summable_all m y).hasSum

theorem map_withDensity_comp {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    (μ : Measure α) (Φ : α → γ) (h : γ → ℝ≥0∞) (hΦ : Measurable Φ) (hh : Measurable h) :
    (μ.withDensity (fun z => h (Φ z))).map Φ = (μ.map Φ).withDensity h := by
  ext s hs
  rw [Measure.map_apply hΦ hs, withDensity_apply _ (hΦ hs), withDensity_apply _ hs,
    Measure.restrict_map hΦ hs, lintegral_map hh hΦ]

theorem lowerQuadratic_Phi (m : ℕ) (z : ℤ → ℂ)
    (hz : Summable (fun n : ℤ => sobolevModeWeight ((m - 1 : ℕ) : ℝ) n * ‖z n‖ ^ 2)) :
    lowerQuadratic m (FinvH38 m (gaussianRealization38 m z)) =
      ∑' n : ℤ, lowerChargeSymbol m n * ‖z n‖ ^ 2 := by
  have hco : ∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from
      FinvH38 m (gaussianRealization38 m z)) n = -(z (-n)) := by
    intro n
    rw [coeff_FinvH38]
    have := seqRealization_apply38 (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) z hz (-n)
    exact congrArg Neg.neg this
  unfold lowerQuadratic
  simp_rw [hco, norm_neg]
  rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => lowerChargeSymbol m n * ‖z n‖ ^ 2)]
  exact tsum_congr (fun n => by simp [L_neg])

end F023Aux

open F023Aux in
theorem f023 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) (δ : ℝ)
    (hδ : 0 < δ) (hδβ : δ < β (m - 1)) :
    0 < tiltProduct m β δ ∧
    HasProd (fun n : ℤ => ratePrime m β δ n / finiteHierarchyRate38 m β n)
      (tiltProduct m β δ) ∧
    (∀ᵐ z ∂gammaM38 m β,
      Summable (fun n : ℤ => lowerChargeSymbol m n * ‖z n‖ ^ 2)) ∧
    countableComplexGaussian (ratePrime m β δ) =
      (gammaM38 m β).withDensity (fun z : ℤ → ℂ => ENNReal.ofReal
        (tiltProduct m β δ * Real.exp
          (δ * ∑' n : ℤ, lowerChargeSymbol m n * ‖z n‖ ^ 2))) ∧
    (∀ y : SobolevHilbert ((m - 1 : ℕ) : ℝ),
      Summable (fun n : ℤ => lowerChargeSymbol m n *
        ‖(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y) n‖ ^ 2)) ∧
    gammaPrime m β δ = (gammaFM38 m β).withDensity
      (fun y => ENNReal.ofReal
        (tiltProduct m β δ * Real.exp (δ * lowerQuadratic m y))) := by
  have hb0 : 0 < β 0 := hβ 0 (Nat.zero_le m)
  have hbm : 0 < β m := hβ m le_rfl
  obtain ⟨hratio, hprime, hsumL⟩ := f022 m hm β hβ δ hδ hδβ
  have hq : ∀ n : ℤ, 0 < finiteHierarchyRate38 m β n := fun n => rate_pos m β hβ _
  have hq' : ∀ n : ℤ, 0 < ratePrime m β δ n := fun n => (hprime n).1
  have hle : ∀ n : ℤ, ratePrime m β δ n ≤ finiteHierarchyRate38 m β n := fun n => by
    unfold ratePrime; nlinarith [mul_nonneg hδ.le (L_nonneg m n)]
  have hsum : Summable (fun n : ℤ => (finiteHierarchyRate38 m β n - ratePrime m β δ n) /
      finiteHierarchyRate38 m β n) :=
    (hsumL.mul_left δ).congr (fun n => by unfold ratePrime; ring)
  obtain ⟨d, hd0, hd⟩ := hasProd_ratio38 (finiteHierarchyRate38 m β) (ratePrime m β δ) hq' hle
    (1 - δ / β (m - 1)) (by linarith [hratio]) (fun n => (hprime n).2.2.2) hsum
  have hdt : tiltProduct m β δ = d := hd.tprod_eq
  have haeL : ∀ᵐ z ∂gammaM38 m β, Summable (fun n : ℤ => lowerChargeSymbol m n * ‖z n‖ ^ 2) :=
    ae_sequenceSummable _ _ hq (L_nonneg m) hsumL
  have htilt := countableGaussian_tilt38 (finiteHierarchyRate38 m β) (ratePrime m β δ) hq' hle hsum
    d hd0 hd
  have hc : ∀ n : ℤ, 0 ≤ finiteHierarchyRate38 m β n - ratePrime m β δ n := fun n => by
    linarith [hle n]
  have hρ : gaussTiltDensity38 (fun n => finiteHierarchyRate38 m β n - ratePrime m β δ n) d
      =ᵐ[gammaM38 m β] fun z => ENNReal.ofReal
        (tiltProduct m β δ * Real.exp (δ * ∑' n : ℤ, lowerChargeSymbol m n * ‖z n‖ ^ 2)) := by
    filter_upwards [haeL] with z hz
    have hs' : Summable (fun n : ℤ => (finiteHierarchyRate38 m β n - ratePrime m β δ n) * ‖z n‖ ^ 2) :=
      (hz.mul_left δ).congr (fun n => by unfold ratePrime; ring)
    rw [gaussTiltDensity_eq38 _ hc d z hs', hdt]
    have e : ∑' n : ℤ, (finiteHierarchyRate38 m β n - ratePrime m β δ n) * ‖z n‖ ^ 2 =
        δ * ∑' n : ℤ, lowerChargeSymbol m n * ‖z n‖ ^ 2 := by
      rw [← tsum_mul_left]
      exact tsum_congr (fun n => by unfold ratePrime; ring)
    rw [e, ← ENNReal.ofReal_mul hd0.le]
  have hdens : countableComplexGaussian (ratePrime m β δ) = (gammaM38 m β).withDensity
      (fun z : ℤ → ℂ => ENNReal.ofReal
        (tiltProduct m β δ * Real.exp (δ * ∑' n : ℤ, lowerChargeSymbol m n * ‖z n‖ ^ 2))) := by
    rw [htilt]
    exact withDensity_congr_ae hρ
  refine ⟨hdt ▸ hd0, hdt ▸ hd, haeL, hdens, summable_all m, ?_⟩
  -- transport through Phi
  set Φ : (ℤ → ℂ) → SobolevHilbert ((m - 1 : ℕ) : ℝ) :=
    fun z => FinvH38 m (gaussianRealization38 m z) with hΦdef
  have hΦ : Measurable Φ :=
    (continuous_FinvH38 m).measurable.comp measurable_gaussianRealization38
  have hF : gammaFM38 m β = (gammaM38 m β).map Φ := by
    unfold gammaFM38
    rw [Measure.map_map (continuous_FinvH38 m).measurable measurable_gaussianRealization38]
    rfl
  have hP : gammaPrime m β δ = (countableComplexGaussian (ratePrime m β δ)).map Φ := by
    unfold gammaPrime
    rw [Measure.map_map (continuous_FinvH38 m).measurable measurable_gaussianRealization38]
    rfl
  set h : SobolevHilbert ((m - 1 : ℕ) : ℝ) → ℝ≥0∞ := fun y => ENNReal.ofReal
    (tiltProduct m β δ * Real.exp (δ * lowerQuadratic m y)) with hh
  have hhm : Measurable h :=
    (((measurable_lowerQuadratic m).const_mul δ |> Real.measurable_exp.comp).const_mul
      (tiltProduct m β δ)).ennreal_ofReal
  have hae : (fun z : ℤ → ℂ => ENNReal.ofReal
        (tiltProduct m β δ * Real.exp (δ * ∑' n : ℤ, lowerChargeSymbol m n * ‖z n‖ ^ 2)))
      =ᵐ[gammaM38 m β] fun z => h (Φ z) := by
    filter_upwards [ae_summable38 hm (fun i hi => (hβ i hi).le) hb0 hbm] with z hz
    simp only [hh, hΦdef]
    rw [lowerQuadratic_Phi m z hz]
  rw [hP, hdens, hF, withDensity_congr_ae hae]
  exact map_withDensity_comp (gammaM38 m β) Φ h hΦ hhm

end NlsGge.ThirdConsultation.F
