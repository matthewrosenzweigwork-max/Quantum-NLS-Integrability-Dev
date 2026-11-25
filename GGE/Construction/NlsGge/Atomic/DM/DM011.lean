import NlsGge.Atomic.DM.DM010
import NlsGge.Atomic.LIB.LIB038
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Lp.lpHolder

set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace NlsGge.Atomic.DM011
open NlsGge.Schur NlsGge.Atomic.Interval
open NlsGge.Atomic.LIB031 NlsGge.Atomic.LIB036 NlsGge.Atomic.LIB037

private def dm011FrequencyDistance
    (bc : ZSBoundaryCondition) (lam : ℂ) : ℝ :=
  Metric.infDist lam (NlsGge.Atomic.DM010.dmSourceFrequencySet bc)

private theorem dm011_sourceFrequencySet_nonempty
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic) :
    (NlsGge.Atomic.DM010.dmSourceFrequencySet bc).Nonempty := by
  rcases hbc with hperiodic | hantiperiodic
  · subst bc
    rw [NlsGge.Atomic.DM010.dm_sourceFrequencySet_eq_parityFrequencySet
      .periodic (Or.inl rfl)]
    exact ⟨(0 : ℂ), ⟨⟨0, by norm_num [NlsGge.Atomic.DM010.dmFrequencySet]⟩,
      by simp⟩⟩
  · subst bc
    rw [NlsGge.Atomic.DM010.dm_sourceFrequencySet_eq_parityFrequencySet
      .antiperiodic (Or.inr rfl)]
    exact ⟨(1 : ℂ), ⟨⟨1, by norm_num [NlsGge.Atomic.DM010.dmFrequencySet]⟩,
      by simp⟩⟩

private theorem dm011_frequencyDistance_ge_abs_im
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (lam : ℂ) :
    |lam.im| ≤ dm011FrequencyDistance bc lam := by
  rw [dm011FrequencyDistance]
  apply (Metric.le_infDist (dm011_sourceFrequencySet_nonempty bc hbc)).2
  intro z hz
  rcases hz with ⟨i, rfl⟩
  have him : ((freeFrequency bc i : ℂ)).im = 0 := by simp
  calc
    |lam.im| = |(lam - (freeFrequency bc i : ℂ)).im| := by simp [him]
    _ ≤ ‖lam - (freeFrequency bc i : ℂ)‖ := Complex.abs_im_le_norm _
    _ = dist lam (freeFrequency bc i : ℂ) := by rw [dist_eq_norm]

private theorem dm011_scaledDenominator_norm_lower
    (bc : ZSBoundaryCondition) (lam : ℂ)
    (hδ : 0 < dm011FrequencyDistance bc lam)
    (i : FreeIndex bc) :
    Real.pi * dm011FrequencyDistance bc lam ≤
      ‖(Real.pi : ℂ) * lam - freeEigenvalue bc i‖ := by
  have hfreq : (freeFrequency bc i : ℂ) ∈
      NlsGge.Atomic.DM010.dmSourceFrequencySet bc := ⟨i, rfl⟩
  have hdist : Metric.infDist lam
      (NlsGge.Atomic.DM010.dmSourceFrequencySet bc) ≤
        dist lam (freeFrequency bc i : ℂ) :=
    Metric.infDist_le_dist_of_mem (x := lam) hfreq
  rw [dist_eq_norm] at hdist
  have hscale :
      ‖(Real.pi : ℂ) * lam - freeEigenvalue bc i‖ =
        Real.pi * ‖lam - (freeFrequency bc i : ℂ)‖ := by
    rw [freeEigenvalue]
    rw [show (Real.pi : ℂ) * lam -
        (freeFrequency bc i : ℂ) * (Real.pi : ℂ) =
          (Real.pi : ℂ) * (lam - (freeFrequency bc i : ℂ)) by ring]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    Real.pi * dm011FrequencyDistance bc lam ≤
        Real.pi * ‖lam - (freeFrequency bc i : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hdist Real.pi_pos.le
    _ = ‖(Real.pi : ℂ) * lam - freeEigenvalue bc i‖ := hscale.symm

private theorem dm011_freeCoefficient_norm_le
    (bc : ZSBoundaryCondition) (lam : ℂ)
    (hδ : 0 < dm011FrequencyDistance bc lam)
    (i : FreeIndex bc) :
    ‖(((Real.pi : ℂ) * lam - freeEigenvalue bc i)⁻¹)‖ ≤
      (Real.pi * dm011FrequencyDistance bc lam)⁻¹ := by
  have hden := dm011_scaledDenominator_norm_lower bc lam hδ i
  have hδπ : 0 < Real.pi * dm011FrequencyDistance bc lam :=
    mul_pos Real.pi_pos hδ
  have hdenpos : 0 < ‖(Real.pi : ℂ) * lam - freeEigenvalue bc i‖ :=
    lt_of_lt_of_le hδπ hden
  rw [norm_inv]
  exact (inv_le_inv₀ hdenpos hδπ).2 hden

private def dm011FreeDiagonal
    (bc : ZSBoundaryCondition) (lam : ℂ)
    (hδ : 0 < dm011FrequencyDistance bc lam) :
    NlsGge.Atomic.LIB037.FreeSquare bc →L[ℂ]
      NlsGge.Atomic.LIB037.FreeSquare bc :=
  lp.mapCLM 2
    (fun i => (((Real.pi : ℂ) * lam - freeEigenvalue bc i)⁻¹) •
      ContinuousLinearMap.id ℂ ℂ)
    (inv_nonneg.mpr (mul_nonneg Real.pi_pos.le hδ.le))
    (by
      intro i
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using
        dm011_freeCoefficient_norm_le bc lam hδ i)

private def dm011FreeResolventDiagonal
    (bc : ZSBoundaryCondition) (lam : ℂ)
    (hδ : 0 < dm011FrequencyDistance bc lam) :
    SourcePairL2 →L[ℂ] SourcePairL2 :=
  (freeZSBasis bc).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((dm011FreeDiagonal bc lam hδ).comp
      (freeZSBasis bc).repr.toContinuousLinearEquiv.toContinuousLinearMap)

private theorem dm011_freeResolventDiagonal_repr
    (bc : ZSBoundaryCondition) (lam : ℂ)
    (hδ : 0 < dm011FrequencyDistance bc lam)
    (f : SourcePairL2) (i : FreeIndex bc) :
    (freeZSBasis bc).repr (dm011FreeResolventDiagonal bc lam hδ f) i =
      (((Real.pi : ℂ) * lam - freeEigenvalue bc i)⁻¹) *
        (freeZSBasis bc).repr f i := by
  change (freeZSBasis bc).repr ((freeZSBasis bc).repr.symm
    (dm011FreeDiagonal bc lam hδ ((freeZSBasis bc).repr f))) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

private theorem dm011_freeResolventDiagonal_norm_le
    (bc : ZSBoundaryCondition) (lam : ℂ)
    (hδ : 0 < dm011FrequencyDistance bc lam) :
    ‖dm011FreeResolventDiagonal bc lam hδ‖ ≤
      (Real.pi * dm011FrequencyDistance bc lam)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (inv_nonneg.mpr (mul_nonneg Real.pi_pos.le hδ.le))
  intro f
  change ‖(freeZSBasis bc).repr.symm
      (dm011FreeDiagonal bc lam hδ ((freeZSBasis bc).repr f))‖ ≤
    (Real.pi * dm011FrequencyDistance bc lam)⁻¹ * ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  have hdiag := (dm011FreeDiagonal bc lam hδ).le_of_opNorm_le
    (lp.norm_mapCLM_le 2 _ _ _) ((freeZSBasis bc).repr f)
  simpa only [LinearIsometryEquiv.norm_map] using hdiag

private theorem dm011_freeResolventDiagonal_eq_of_coefficients
    (bc : ZSBoundaryCondition) (lam : ℂ)
    (hδ : 0 < dm011FrequencyDistance bc lam)
    (R0 : SourcePairL2 →L[ℂ] SourcePairL2)
    (hcoeff : ∀ f : SourcePairL2, ∀ i : FreeIndex bc,
      (freeZSBasis bc).repr (R0 f) i =
        (((Real.pi : ℂ) * lam - freeEigenvalue bc i)⁻¹) *
          (freeZSBasis bc).repr f i) :
    R0 = dm011FreeResolventDiagonal bc lam hδ := by
  apply ContinuousLinearMap.ext
  intro f
  apply (freeZSBasis bc).repr.injective
  ext i
  rw [hcoeff f i, dm011_freeResolventDiagonal_repr bc lam hδ f i]

private theorem dm011_freeResolvent_norm_of_coefficients
    (bc : ZSBoundaryCondition) (lam : ℂ)
    (R0 : SourcePairL2 →L[ℂ] SourcePairL2)
    (hδ : 0 < dm011FrequencyDistance bc lam)
    (hcoeff : ∀ f : SourcePairL2, ∀ i : FreeIndex bc,
      (freeZSBasis bc).repr (R0 f) i =
        (((Real.pi : ℂ) * lam - freeEigenvalue bc i)⁻¹) *
          (freeZSBasis bc).repr f i) :
    ‖R0‖ ≤ (Real.pi * dm011FrequencyDistance bc lam)⁻¹ := by
  calc
    ‖R0‖ = ‖dm011FreeResolventDiagonal bc lam hδ‖ := by
      rw [dm011_freeResolventDiagonal_eq_of_coefficients bc lam hδ R0 hcoeff]
    _ ≤ (Real.pi * dm011FrequencyDistance bc lam)⁻¹ :=
      dm011_freeResolventDiagonal_norm_le bc lam hδ


/- Private actual potential-after-free map and sharp norm scaling. -/
private abbrev dm011SourcePairL2 := NlsGge.Schur.SourcePairL2
private abbrev dm011H1Pair := NlsGge.Atomic.Interval.H1Pair
private abbrev dm011ContinuousPair :=
  C(Icc (0 : ℝ) 1, NlsGge.Atomic.LIB031.PointPair)

private def dm011FreeH1Lift
    (bc : NlsGge.Atomic.Interval.ZSBoundaryCondition)
    (R0 : dm011SourcePairL2 →L[ℂ] dm011SourcePairL2)
    (hR0 : ∀ f : dm011SourcePairL2,
      R0 f ∈ (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain)
    (f : dm011SourcePairL2) : dm011H1Pair :=
  NlsGge.Atomic.LIB033.domainLift
    (⟨R0 f, hR0 f⟩ : NlsGge.Atomic.LIB033.zsDomain bc)

private lemma dm011FreeH1Lift_add
    (bc : NlsGge.Atomic.Interval.ZSBoundaryCondition)
    (R0 : dm011SourcePairL2 →L[ℂ] dm011SourcePairL2)
    (hR0 : ∀ f : dm011SourcePairL2,
      R0 f ∈ (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain)
    (f g : dm011SourcePairL2) :
    dm011FreeH1Lift bc R0 hR0 (f + g) =
      NlsGge.Atomic.LIB033.h1PairAdd
        (dm011FreeH1Lift bc R0 hR0 f) (dm011FreeH1Lift bc R0 hR0 g) := by
  apply NlsGge.Atomic.LIB033.h1PairValue_injective
  simp [dm011FreeH1Lift, NlsGge.Atomic.LIB033.domainLift_value,
    NlsGge.Atomic.LIB033.h1PairValue_add, map_add]

private lemma dm011FreeH1Lift_smul
    (bc : NlsGge.Atomic.Interval.ZSBoundaryCondition)
    (R0 : dm011SourcePairL2 →L[ℂ] dm011SourcePairL2)
    (hR0 : ∀ f : dm011SourcePairL2,
      R0 f ∈ (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain)
    (c : ℂ) (f : dm011SourcePairL2) :
    dm011FreeH1Lift bc R0 hR0 (c • f) =
      NlsGge.Atomic.LIB033.h1PairSmul c (dm011FreeH1Lift bc R0 hR0 f) := by
  apply NlsGge.Atomic.LIB033.h1PairValue_injective
  simp [dm011FreeH1Lift, NlsGge.Atomic.LIB033.domainLift_value,
    NlsGge.Atomic.LIB033.h1PairValue_smul, map_smul]

private def dm011PotentialTimesFreeLinear
    (bc : NlsGge.Atomic.Interval.ZSBoundaryCondition)
    (φ : dm011SourcePairL2)
    (R0 : dm011SourcePairL2 →L[ℂ] dm011SourcePairL2)
    (hR0 : ∀ f : dm011SourcePairL2,
      R0 f ∈ (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain) :
    dm011SourcePairL2 →ₗ[ℂ] dm011SourcePairL2 where
  toFun f := NlsGge.Atomic.LIB032.potentialProduct φ
    (dm011FreeH1Lift bc R0 hR0 f)
  map_add' f g := by
    rw [dm011FreeH1Lift_add, NlsGge.Atomic.LIB038.potentialProduct_add]
  map_smul' c f := by
    rw [dm011FreeH1Lift_smul, NlsGge.Atomic.LIB038.potentialProduct_smul]
    rfl

private lemma dm011PotentialTimesFreeLinear_bound
    (bc : NlsGge.Atomic.Interval.ZSBoundaryCondition)
    (φ : dm011SourcePairL2)
    (R0 : dm011SourcePairL2 →L[ℂ] dm011SourcePairL2)
    (hR0 : ∀ f : dm011SourcePairL2,
      R0 f ∈ (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain)
    (T0 : dm011SourcePairL2 →L[ℂ] dm011ContinuousPair)
    (hT0 : ∀ f : dm011SourcePairL2,
      T0 f = NlsGge.Atomic.LIB031.pairRepresentative
        (dm011FreeH1Lift bc R0 hR0 f))
    (C : ℝ) (hTnorm : ‖T0‖ ≤ C) (f : dm011SourcePairL2) :
    ‖dm011PotentialTimesFreeLinear bc φ R0 hR0 f‖ ≤
      (‖φ‖ * C) * ‖f‖ := by
  calc
    _ ≤ ‖φ‖ * ‖NlsGge.Atomic.LIB031.pairRepresentative
        (dm011FreeH1Lift bc R0 hR0 f)‖ :=
      NlsGge.Atomic.LIB032.potentialProduct_norm_le φ _
    _ = ‖φ‖ * ‖T0 f‖ := by rw [hT0 f]
    _ ≤ ‖φ‖ * (C * ‖f‖) :=
      mul_le_mul_of_nonneg_left
        (calc
          ‖T0 f‖ ≤ ‖T0‖ * ‖f‖ := T0.le_opNorm f
          _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_right hTnorm (norm_nonneg f))
        (norm_nonneg φ)
    _ = (‖φ‖ * C) * ‖f‖ := by ring

private def dm011PotentialTimesFree
    (bc : NlsGge.Atomic.Interval.ZSBoundaryCondition)
    (φ : dm011SourcePairL2)
    (R0 : dm011SourcePairL2 →L[ℂ] dm011SourcePairL2)
    (hR0 : ∀ f : dm011SourcePairL2,
      R0 f ∈ (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain)
    (T0 : dm011SourcePairL2 →L[ℂ] dm011ContinuousPair)
    (hT0 : ∀ f : dm011SourcePairL2,
      T0 f = NlsGge.Atomic.LIB031.pairRepresentative
        (dm011FreeH1Lift bc R0 hR0 f))
    (C : ℝ) (hC : 0 ≤ C) (hTnorm : ‖T0‖ ≤ C) :
    dm011SourcePairL2 →L[ℂ] dm011SourcePairL2 :=
  (dm011PotentialTimesFreeLinear bc φ R0 hR0).mkContinuous
    (‖φ‖ * C)
    (dm011PotentialTimesFreeLinear_bound bc φ R0 hR0 T0 hT0 C hTnorm)

private theorem dm011PotentialTimesFree_norm_le
    (bc : NlsGge.Atomic.Interval.ZSBoundaryCondition)
    (φ : dm011SourcePairL2)
    (R0 : dm011SourcePairL2 →L[ℂ] dm011SourcePairL2)
    (hR0 : ∀ f : dm011SourcePairL2,
      R0 f ∈ (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain)
    (T0 : dm011SourcePairL2 →L[ℂ] dm011ContinuousPair)
    (hT0 : ∀ f : dm011SourcePairL2,
      T0 f = NlsGge.Atomic.LIB031.pairRepresentative
        (dm011FreeH1Lift bc R0 hR0 f))
    (C : ℝ) (hC : 0 ≤ C) (hTnorm : ‖T0‖ ≤ C) :
    ‖dm011PotentialTimesFree bc φ R0 hR0 T0 hT0 C hC hTnorm‖ ≤ ‖φ‖ * C := by
  exact LinearMap.mkContinuous_norm_le _
    (mul_nonneg (norm_nonneg φ) hC)
    (dm011PotentialTimesFreeLinear_bound bc φ R0 hR0 T0 hT0 C hTnorm)

private lemma dm011_scaledPotential_norm (v : NlsGge.Atomic.DM001.PiPairL2) :
    ‖NlsGge.Atomic.DM001.scaledPotential v‖ = Real.pi * ‖v‖ := by
  rw [NlsGge.Atomic.DM001.scaledPotential, norm_smul,
    NlsGge.Atomic.DM001.unitaryRescalePair.norm_map]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

private theorem dm011PotentialTimesFree_scaled_norm_le
    (bc : NlsGge.Atomic.Interval.ZSBoundaryCondition)
    (v : NlsGge.Atomic.DM001.PiPairL2)
    (R0 : dm011SourcePairL2 →L[ℂ] dm011SourcePairL2)
    (hR0 : ∀ f : dm011SourcePairL2,
      R0 f ∈ (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain)
    (T0 : dm011SourcePairL2 →L[ℂ] dm011ContinuousPair)
    (hT0 : ∀ f : dm011SourcePairL2,
      T0 f = NlsGge.Atomic.LIB031.pairRepresentative
        (dm011FreeH1Lift bc R0 hR0 f))
    (a : ℝ) (ha : 0 ≤ a)
    (hTnorm : ‖T0‖ ≤ Real.sqrt a / Real.pi) :
    ‖dm011PotentialTimesFree bc (NlsGge.Atomic.DM001.scaledPotential v)
      R0 hR0 T0 hT0 (Real.sqrt a / Real.pi)
      (div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le) hTnorm‖ ≤
      ‖v‖ * Real.sqrt a := by
  calc
    _ ≤ ‖NlsGge.Atomic.DM001.scaledPotential v‖ * (Real.sqrt a / Real.pi) :=
      dm011PotentialTimesFree_norm_le _ _ _ _ _ _ _ _ _
    _ = ‖v‖ * Real.sqrt a := by
      rw [dm011_scaledPotential_norm]
      field_simp [Real.pi_ne_zero]



private lemma dm011_nearby_le_three_over_abs_t (x t : ℝ) (ht : 1 ≤ |t|) :
    NlsGge.Atomic.DM010.dmNearbySum x t ≤ 3 / |t| := by
  have htpos : 0 < |t| := lt_of_lt_of_le zero_lt_one ht
  have ht2 : |t| ≤ t ^ 2 := by
    calc
      |t| = |t| * 1 := by ring
      _ ≤ |t| * |t| := mul_le_mul_of_nonneg_left ht (abs_nonneg t)
      _ = |t| ^ 2 := by ring
      _ = t ^ 2 := sq_abs t
  unfold NlsGge.Atomic.DM010.dmNearbySum
  calc
    _ ≤ ∑ τ ∈ Finset.Icc (-1 : ℤ) 1, 1 / |t| := by
      apply Finset.sum_le_sum
      intro τ hτ
      apply one_div_le_one_div_of_le htpos
      nlinarith [sq_nonneg (x - (τ : ℝ)), ht2]
    _ = 3 / |t| := by
      simp only [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
      norm_num
      rw [div_eq_mul_inv]

private theorem dm011_sourceEnergy_le_nine_over_abs_t
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : NlsGge.Atomic.DM010.dmLambda n x t ∉
      NlsGge.Atomic.DM010.dmSourceFrequencySet bc)
    (ht : 1 ≤ |t|) :
    NlsGge.Atomic.DM010.dmLatticeSum bc
      (NlsGge.Atomic.DM010.dmLambda n x t) ≤ 9 / |t| := by
  have hscalar : NlsGge.Atomic.DM010.dmLambda n x t ∉
      Set.range (fun k : NlsGge.Atomic.DM010.DMFrequency bc => (k.val : ℂ)) := by
    rw [← NlsGge.Atomic.DM010.dm_sourceFrequencySet_eq_parityFrequencySet bc hbc]
    exact «hλ»
  have hsum : Summable
      (NlsGge.Atomic.DM010.dmLatticeTerm bc
        (NlsGge.Atomic.DM010.dmLambda n x t)) :=
    NlsGge.Atomic.DM010.dm_resolvent_lattice_summable bc hbc n x t hx hscalar
  have hnear := dm011_nearby_le_three_over_abs_t x t ht
  have htail : NlsGge.Atomic.DM010.dmTailProfile t = |t|⁻¹ := by
    simp [NlsGge.Atomic.DM010.dmTailProfile, ht]
  have hmajorant :=
    NlsGge.Atomic.DM010.dm_resolvent_lattice_sum_le bc hbc n x t hx hscalar
  rw [htail] at hmajorant
  calc
    _ ≤ NlsGge.Atomic.DM010.dmNearbySum x t + 6 * |t|⁻¹ := hmajorant
    _ ≤ 3 / |t| + 6 * |t|⁻¹ := add_le_add hnear le_rfl
    _ = 9 / |t| := by ring

private def dm011ActualPerturbation
    (bc : ZSBoundaryCondition)
    (v : NlsGge.Atomic.DM001.PiPairL2)
    (R0 : NlsGge.Schur.SourcePairL2 →L[ℂ] NlsGge.Schur.SourcePairL2)
    (hR0 : ∀ f : NlsGge.Schur.SourcePairL2,
      R0 f ∈ (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain)
    (T0 : NlsGge.Schur.SourcePairL2 →L[ℂ]
      C(Icc (0 : ℝ) 1, NlsGge.Atomic.LIB031.PointPair))
    (hT0 : ∀ f : NlsGge.Schur.SourcePairL2,
      T0 f = NlsGge.Atomic.LIB031.pairRepresentative
        (dm011FreeH1Lift bc R0 hR0 f))
    (a : ℝ) (ha : 0 ≤ a)
    (hTnorm : ‖T0‖ ≤ Real.sqrt a / Real.pi) :
    NlsGge.Schur.SourcePairL2 →L[ℂ] NlsGge.Schur.SourcePairL2 :=
  dm011PotentialTimesFree bc (NlsGge.Atomic.DM001.scaledPotential v)
    R0 hR0 T0 hT0 (Real.sqrt a / Real.pi)
    (div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le) hTnorm

private theorem dm011_actualPerturbation_norm_le_half
    (bc : ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (v : NlsGge.Atomic.DM001.PiPairL2)
    (n : ℤ) (x t : ℝ) (hx : -1 ≤ x ∧ x ≤ 1)
    («hλ» : NlsGge.Atomic.DM010.dmLambda n x t ∉
      NlsGge.Atomic.DM010.dmSourceFrequencySet bc)
    (hlarge : 1 + 14 * ‖v‖ ≤ Real.sqrt |t|
    )
    (R0 : NlsGge.Schur.SourcePairL2 →L[ℂ] NlsGge.Schur.SourcePairL2)
    (hR0 : ∀ f : NlsGge.Schur.SourcePairL2,
      R0 f ∈ (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain)
    (T0 : NlsGge.Schur.SourcePairL2 →L[ℂ]
      C(Icc (0 : ℝ) 1, NlsGge.Atomic.LIB031.PointPair))
    (hT0 : ∀ f : NlsGge.Schur.SourcePairL2,
      T0 f = NlsGge.Atomic.LIB031.pairRepresentative
        (dm011FreeH1Lift bc R0 hR0 f))
    (hTnorm : ‖T0‖ ≤
      Real.sqrt (NlsGge.Atomic.DM010.dmLatticeSum bc
        (NlsGge.Atomic.DM010.dmLambda n x t)) / Real.pi) :
    ‖dm011ActualPerturbation bc v R0 hR0 T0 hT0
      (NlsGge.Atomic.DM010.dmLatticeSum bc
        (NlsGge.Atomic.DM010.dmLambda n x t))
      (by
        unfold NlsGge.Atomic.DM010.dmLatticeSum
        exact tsum_nonneg (fun k =>
          NlsGge.Atomic.DM010.dm_latticeTerm_nonneg bc
            (NlsGge.Atomic.DM010.dmLambda n x t) k)) hTnorm‖ ≤ 1 / 2 := by
  let a := NlsGge.Atomic.DM010.dmLatticeSum bc
    (NlsGge.Atomic.DM010.dmLambda n x t)
  have hq : 0 ≤ ‖v‖ := norm_nonneg _
  have hroot1 : 1 ≤ Real.sqrt |t| := by linarith
  have hrootSq : (1 : ℝ) ^ 2 ≤ (Real.sqrt |t|) ^ 2 :=
    (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (Real.sqrt_nonneg _)).2 hroot1
  have ht : 1 ≤ |t| := by
    simpa only [one_pow, Real.sq_sqrt (abs_nonneg t)] using hrootSq
  have ha : 0 ≤ a := by
    dsimp [a]
    unfold NlsGge.Atomic.DM010.dmLatticeSum
    exact tsum_nonneg (fun k =>
      NlsGge.Atomic.DM010.dm_latticeTerm_nonneg bc
        (NlsGge.Atomic.DM010.dmLambda n x t) k)
  have henergy := dm011_sourceEnergy_le_nine_over_abs_t bc hbc n x t hx «hλ» ht
  have hrootpos : 0 < Real.sqrt |t| := by positivity
  have hrootbound : Real.sqrt a ≤ 3 / Real.sqrt |t| := by
    have hratio : (3 / Real.sqrt |t|) ^ 2 = 9 / |t| := by
      rw [div_pow, Real.sq_sqrt (abs_nonneg t)]
      ring
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt ha, hratio]
    exact henergy
  have hKnorm :
      ‖dm011ActualPerturbation bc v R0 hR0 T0 hT0 a ha hTnorm‖ ≤
        ‖v‖ * Real.sqrt a := by
    simpa only [dm011ActualPerturbation] using
      dm011PotentialTimesFree_scaled_norm_le bc v R0 hR0 T0 hT0 a ha hTnorm
  have hKhalf :
      ‖dm011ActualPerturbation bc v R0 hR0 T0 hT0 a ha hTnorm‖ ≤ 1 / 2 := by
    calc
      _ ≤ ‖v‖ * Real.sqrt a := hKnorm
      _ ≤ ‖v‖ * (3 / Real.sqrt |t|) :=
        mul_le_mul_of_nonneg_left hrootbound hq
      _ = (3 * ‖v‖) / Real.sqrt |t| := by ring
      _ ≤ 1 / 2 := (div_le_iff₀ hrootpos).2 (by linarith [hlarge, hq])
  simpa [a, dm011ActualPerturbation] using hKhalf

private theorem dm011_neumann_radius_of_half
    (K : NlsGge.Schur.SourcePairL2 →L[ℂ] NlsGge.Schur.SourcePairL2)
    (hKhalf : ‖K‖ ≤ (1 / 2 : ℝ)) : ‖K‖ < 1 :=
  lt_of_le_of_lt hKhalf (by norm_num)

private def dm011NeumannInverse
    (K : NlsGge.Schur.SourcePairL2 →L[ℂ] NlsGge.Schur.SourcePairL2)
    (hK : ‖K‖ < 1) : NlsGge.Schur.SourcePairL2 →L[ℂ] NlsGge.Schur.SourcePairL2 :=
  ↑((Units.oneSub K hK)⁻¹)

private theorem dm011Neumann_hasSum
    (K : NlsGge.Schur.SourcePairL2 →L[ℂ] NlsGge.Schur.SourcePairL2)
    (hK : ‖K‖ < 1) :
    HasSum (fun j : ℕ => K ^ j) (dm011NeumannInverse K hK) := by
  have hgeom : Summable (fun j : ℕ => K ^ j) :=
    summable_geometric_of_norm_lt_one hK
  simpa [dm011NeumannInverse, Units.oneSub] using hgeom.hasSum

private theorem dm011NeumannRightInverse
    (K : NlsGge.Schur.SourcePairL2 →L[ℂ] NlsGge.Schur.SourcePairL2)
    (hK : ‖K‖ < 1) :
    (1 - K) * dm011NeumannInverse K hK = 1 :=
  (Units.oneSub K hK).val_inv

private theorem dm011NeumannLeftInverse
    (K : NlsGge.Schur.SourcePairL2 →L[ℂ] NlsGge.Schur.SourcePairL2)
    (hK : ‖K‖ < 1) :
    dm011NeumannInverse K hK * (1 - K) = 1 :=
  (Units.oneSub K hK).inv_val

private theorem dm011_actualNeumann_norm_le_two
    (K : NlsGge.Schur.SourcePairL2 →L[ℂ] NlsGge.Schur.SourcePairL2)
    (hK : ‖K‖ < 1) (hKhalf : ‖K‖ ≤ (1 / 2 : ℝ)) :
    ‖dm011NeumannInverse K hK‖ ≤ 2 := by
  have hhas : HasSum (fun j : ℕ => K ^ j) (dm011NeumannInverse K hK) :=
    dm011Neumann_hasSum K hK
  have hN' : dm011NeumannInverse K hK = ∑' j : ℕ, K ^ j := hhas.tsum_eq.symm
  rw [hN']
  have hid : ‖(1 : NlsGge.Schur.SourcePairL2 →L[ℂ] NlsGge.Schur.SourcePairL2)‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ NlsGge.Schur.SourcePairL2‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le (𝕜 := ℂ)
      (E := NlsGge.Schur.SourcePairL2)
  calc
    _ ≤ ‖(1 : NlsGge.Schur.SourcePairL2 →L[ℂ] NlsGge.Schur.SourcePairL2)‖ -
        1 + (1 - ‖K‖)⁻¹ := tsum_geometric_le_of_norm_lt_one K hK
    _ ≤ (1 - ‖K‖)⁻¹ := by nlinarith [hid]
    _ ≤ (1 / 2 : ℝ)⁻¹ := by
      have hdenpos : 0 < 1 - ‖K‖ := by linarith
      apply (inv_le_inv₀ hdenpos (by norm_num : (0 : ℝ) < 1 / 2)).2
      linarith
    _ = 2 := by norm_num

private lemma dm011NeumannRightApply
    (K : NlsGge.Schur.SourcePairL2 →L[ℂ] NlsGge.Schur.SourcePairL2)
    (hK : ‖K‖ < 1) (f : NlsGge.Schur.SourcePairL2) :
    dm011NeumannInverse K hK f - K (dm011NeumannInverse K hK f) = f := by
  have h := congrArg
    (fun S : NlsGge.Schur.SourcePairL2 →L[ℂ] NlsGge.Schur.SourcePairL2 => S f)
    (dm011NeumannRightInverse K hK)
  exact h

private lemma dm011NeumannLeftApply
    (K : NlsGge.Schur.SourcePairL2 →L[ℂ] NlsGge.Schur.SourcePairL2)
    (hK : ‖K‖ < 1) (f : NlsGge.Schur.SourcePairL2) :
    dm011NeumannInverse K hK (f - K f) = f := by
  have h := congrArg
    (fun S : NlsGge.Schur.SourcePairL2 →L[ℂ] NlsGge.Schur.SourcePairL2 => S f)
    (dm011NeumannLeftInverse K hK)
  exact h

private lemma dm011ActualAction_split
    (φ : NlsGge.Schur.SourcePairL2)
    (bc : NlsGge.Atomic.Interval.ZSBoundaryCondition)
    (u : NlsGge.Atomic.LIB033.zsDomain bc) :
    NlsGge.Atomic.LIB033.zsRealization φ bc u =
      NlsGge.Atomic.LIB033.zsRealization 0 bc u +
        NlsGge.Atomic.LIB032.potentialProduct φ
          (NlsGge.Atomic.LIB033.domainLift u) := by
  change NlsGge.Atomic.Interval.zsApply φ
      (NlsGge.Atomic.LIB033.domainLift u) =
    NlsGge.Atomic.Interval.zsApply 0
      (NlsGge.Atomic.LIB033.domainLift u) +
      NlsGge.Atomic.LIB032.potentialProduct φ
        (NlsGge.Atomic.LIB033.domainLift u)
  exact NlsGge.Atomic.LIB038.zsApply_eq_free_add φ
    (NlsGge.Atomic.LIB033.domainLift u)

private theorem dm011_actual_perturbation_assembly
    (bc : ZSBoundaryCondition)
    (v : NlsGge.Atomic.DM001.PiPairL2)
    (z : ℂ) (a δ : ℝ)
    (ha : 0 ≤ a) (hδ : 0 < δ)
    (R0 : SourcePairL2 →L[ℂ] SourcePairL2)
    (T0 : SourcePairL2 →L[ℂ] dm011ContinuousPair)
    (hR0 : ∀ f : SourcePairL2,
      R0 f ∈ (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain)
    (hfreeRight : ∀ f : SourcePairL2,
      z • R0 f - NlsGge.Atomic.LIB033.zsRealization 0 bc
        ⟨R0 f, hR0 f⟩ = f)
    (hfreeLeft : ∀ u : (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain,
      R0 (z • (u : SourcePairL2) -
        NlsGge.Atomic.LIB033.zsRealization 0 bc u) = u)
    (hT0 : ∀ f : SourcePairL2,
      T0 f = NlsGge.Atomic.LIB031.pairRepresentative
        (NlsGge.Atomic.LIB033.domainLift
          (⟨R0 f, hR0 f⟩ : NlsGge.Atomic.LIB033.zsDomain bc)))
    (hR0norm : ‖R0‖ ≤ (Real.pi * δ)⁻¹)
    (hT0norm : ‖T0‖ ≤ Real.sqrt a / Real.pi)
    (hKhalf : ‖dm011ActualPerturbation bc v R0 hR0 T0 hT0 a ha hT0norm‖ ≤
      (1 / 2 : ℝ)) :
    ∃ (R : SourcePairL2 →L[ℂ] SourcePairL2)
      (T : SourcePairL2 →L[ℂ] dm011ContinuousPair)
      (hR : ∀ f : SourcePairL2,
        R f ∈ (NlsGge.Atomic.LIB033.zsRealization
          (NlsGge.Atomic.DM001.scaledPotential v) bc).domain),
      (∀ f : SourcePairL2,
        z • R f - NlsGge.Atomic.LIB033.zsRealization
          (NlsGge.Atomic.DM001.scaledPotential v) bc ⟨R f, hR f⟩ = f) ∧
      (∀ u : (NlsGge.Atomic.LIB033.zsRealization
          (NlsGge.Atomic.DM001.scaledPotential v) bc).domain,
        R (z • (u : SourcePairL2) -
          NlsGge.Atomic.LIB033.zsRealization
            (NlsGge.Atomic.DM001.scaledPotential v) bc u) = u) ∧
      (∀ f : SourcePairL2,
        T f = NlsGge.Atomic.LIB031.pairRepresentative
          (NlsGge.Atomic.LIB033.domainLift
            (⟨R f, hR f⟩ : NlsGge.Atomic.LIB033.zsDomain bc))) ∧
      ‖R‖ ≤ 2 * (Real.pi * δ)⁻¹ ∧
      ‖T‖ ≤ 2 * Real.sqrt a / Real.pi := by
  let φ := NlsGge.Atomic.DM001.scaledPotential v
  let K := dm011ActualPerturbation bc v R0 hR0 T0 hT0 a ha hT0norm
  have hK : ‖K‖ < 1 := dm011_neumann_radius_of_half K hKhalf
  let N := dm011NeumannInverse K hK
  let R := R0.comp N
  let T := T0.comp N
  let hR : ∀ f : SourcePairL2,
      R f ∈ (NlsGge.Atomic.LIB033.zsRealization φ bc).domain := by
    intro f
    change R0 (N f) ∈ (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain
    exact hR0 (N f)
  have hNnorm : ‖N‖ ≤ 2 := by
    change ‖dm011NeumannInverse K hK‖ ≤ 2
    exact dm011_actualNeumann_norm_le_two K hK hKhalf
  refine ⟨R, T, hR, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    let u0 : NlsGge.Atomic.LIB033.zsDomain bc :=
      ⟨R0 (N f), hR0 (N f)⟩
    have hfree : z • R0 (N f) -
        NlsGge.Atomic.LIB033.zsRealization 0 bc u0 = N f := by
      exact hfreeRight (N f)
    have hpot : K (N f) = NlsGge.Atomic.LIB032.potentialProduct φ
        (NlsGge.Atomic.LIB033.domainLift u0) := by
      change NlsGge.Atomic.LIB032.potentialProduct φ
          (dm011FreeH1Lift bc R0 hR0 (N f)) = _
      rfl
    change z • R0 (N f) - NlsGge.Atomic.LIB033.zsRealization φ bc u0 = f
    calc
      _ = z • R0 (N f) -
          (NlsGge.Atomic.LIB033.zsRealization 0 bc u0 +
            NlsGge.Atomic.LIB032.potentialProduct φ
              (NlsGge.Atomic.LIB033.domainLift u0)) := by
        rw [dm011ActualAction_split φ bc u0]
      _ = (z • R0 (N f) -
            NlsGge.Atomic.LIB033.zsRealization 0 bc u0) - K (N f) := by
        rw [← hpot]
        abel
      _ = N f - K (N f) := by rw [hfree]
      _ = f := dm011NeumannRightApply K hK f
  · intro u
    have hu0 : (u : SourcePairL2) ∈ NlsGge.Atomic.LIB033.zsDomain bc := by
      change (u : SourcePairL2) ∈
        (NlsGge.Atomic.LIB033.zsRealization φ bc).domain
      exact u.property
    let u0 : NlsGge.Atomic.LIB033.zsDomain bc :=
      ⟨(u : SourcePairL2), hu0⟩
    have hsub : u0 = u := by
      apply Subtype.ext
      rfl
    let g := z • (u0 : SourcePairL2) -
      NlsGge.Atomic.LIB033.zsRealization 0 bc u0
    have hfree : R0 g = (u0 : SourcePairL2) := by
      exact hfreeLeft u0
    have hlift : dm011FreeH1Lift bc R0 hR0 g =
        NlsGge.Atomic.LIB033.domainLift u0 := by
      apply NlsGge.Atomic.LIB033.h1PairValue_injective
      simp [dm011FreeH1Lift, g, hfree]
    have hpot : K g = NlsGge.Atomic.LIB032.potentialProduct φ
        (NlsGge.Atomic.LIB033.domainLift u0) := by
      change NlsGge.Atomic.LIB032.potentialProduct φ
        (dm011FreeH1Lift bc R0 hR0 g) = _
      rw [hlift]
    have hfactor : z • (u : SourcePairL2) -
        NlsGge.Atomic.LIB033.zsRealization φ bc u = g - K g := by
      rw [← hsub]
      change z • (u0 : SourcePairL2) -
        NlsGge.Atomic.LIB033.zsRealization φ bc u0 = g - K g
      rw [dm011ActualAction_split φ bc u0, hpot]
      dsimp [g]
      abel
    change R0 (N (z • (u : SourcePairL2) -
      NlsGge.Atomic.LIB033.zsRealization φ bc u)) = (u : SourcePairL2)
    rw [hfactor, dm011NeumannLeftApply K hK g]
    simpa [hsub] using hfree
  · intro f
    change T0 (N f) = NlsGge.Atomic.LIB031.pairRepresentative
      (NlsGge.Atomic.LIB033.domainLift
        (⟨R0 (N f), hR0 (N f)⟩ : NlsGge.Atomic.LIB033.zsDomain bc))
    exact hT0 (N f)
  · calc
      ‖R‖ ≤ ‖R0‖ * ‖N‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (Real.pi * δ)⁻¹ * ‖N‖ :=
        mul_le_mul_of_nonneg_right hR0norm (norm_nonneg _)
      _ ≤ (Real.pi * δ)⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left hNnorm (by positivity)
      _ = 2 * (Real.pi * δ)⁻¹ := by ring
  · calc
      ‖T‖ ≤ ‖T0‖ * ‖N‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (Real.sqrt a / Real.pi) * ‖N‖ :=
        mul_le_mul_of_nonneg_right hT0norm (norm_nonneg _)
      _ ≤ (Real.sqrt a / Real.pi) * 2 :=
        mul_le_mul_of_nonneg_left hNnorm (by positivity)
      _ = 2 * Real.sqrt a / Real.pi := by ring

/-- The exact two equations above build the project's concrete predicate. -/
private theorem dm011_assembly_hasBoundedResolvent
    (bc : ZSBoundaryCondition)
    (φ : NlsGge.Schur.SourcePairL2)
    (z : ℂ)
    (R : SourcePairL2 →L[ℂ] SourcePairL2)
    (hR : ∀ f : SourcePairL2,
      R f ∈ (NlsGge.Atomic.LIB033.zsRealization φ bc).domain)
    (hright : ∀ f : SourcePairL2,
      z • R f - NlsGge.Atomic.LIB033.zsRealization φ bc ⟨R f, hR f⟩ = f)
    (hleft : ∀ u : (NlsGge.Atomic.LIB033.zsRealization φ bc).domain,
      R (z • (u : SourcePairL2) -
        NlsGge.Atomic.LIB033.zsRealization φ bc u) = u) :
    NlsGge.Atomic.LIB038.HasBoundedResolvent
      (NlsGge.Atomic.LIB033.zsRealization φ bc) z :=
  ⟨R, (fun f => ⟨hR f, hright f⟩), hleft⟩

theorem dm_resolvent_large_imaginary
    (bc : NlsGge.Atomic.Interval.ZSBoundaryCondition)
    (hbc : bc = .periodic ∨ bc = .antiperiodic)
    (v : NlsGge.Atomic.DM001.PiPairL2)
    (lam : ℂ)
    (hlarge : (1 + 14 * ‖v‖) ^ 2 ≤ |lam.im|) :
    let φ : NlsGge.Atomic.DM001.UnitPairL2 :=
      NlsGge.Atomic.DM001.scaledPotential v
    let z : ℂ := (Real.pi : ℂ) * lam
    let A : NlsGge.Schur.SourcePairL2 →ₗ.[ℂ] NlsGge.Schur.SourcePairL2 :=
      NlsGge.Atomic.LIB033.zsRealization φ bc
    let a : ℝ := NlsGge.Atomic.DM010.dmLatticeSum bc lam
    let δ : ℝ := Metric.infDist lam
      (NlsGge.Atomic.DM010.dmSourceFrequencySet bc)
    ∃ (R : NlsGge.Schur.SourcePairL2 →L[ℂ] NlsGge.Schur.SourcePairL2)
      (T : NlsGge.Schur.SourcePairL2 →L[ℂ]
        ContinuousMap (Set.Icc (0 : ℝ) 1) NlsGge.Atomic.LIB031.PointPair)
      (hR : ∀ f : NlsGge.Schur.SourcePairL2, R f ∈ A.domain),
      (∀ f, z • R f - A ⟨R f, hR f⟩ = f) ∧
      (∀ u : A.domain, R (z • (u : NlsGge.Schur.SourcePairL2) - A u) = u) ∧
      (∀ f, T f = NlsGge.Atomic.LIB031.pairRepresentative
        (NlsGge.Atomic.LIB033.domainLift
          (⟨R f, hR f⟩ : NlsGge.Atomic.LIB033.zsDomain bc)) ) ∧
      NlsGge.Atomic.LIB038.HasBoundedResolvent A z ∧
      0 < δ ∧
      ‖R‖ ≤ 2 / (Real.pi * δ) ∧
      ‖T‖ ≤ 2 * Real.sqrt a / Real.pi := by
  let n : ℤ := ⌊lam.re⌋
  let x : ℝ := lam.re - (n : ℝ)
  let t : ℝ := lam.im
  let φ : NlsGge.Atomic.DM001.UnitPairL2 :=
    NlsGge.Atomic.DM001.scaledPotential v
  let z : ℂ := (Real.pi : ℂ) * lam
  let a : ℝ := NlsGge.Atomic.DM010.dmLatticeSum bc lam
  let δ : ℝ := dm011FrequencyDistance bc lam

  have hnle : (n : ℝ) ≤ lam.re := by
    dsimp [n]
    exact Int.floor_le _
  have hlt : lam.re < (n : ℝ) + 1 := by
    dsimp [n]
    exact Int.lt_floor_add_one _
  have hx : -1 ≤ x ∧ x ≤ 1 := by
    constructor <;> dsimp [x] <;> linarith
  have hdecomp : NlsGge.Atomic.DM010.dmLambda n x t = lam := by
    apply Complex.ext <;>
      simp [NlsGge.Atomic.DM010.dmLambda, x, t] <;> ring

  have hbase : (1 : ℝ) ≤ (1 + 14 * ‖v‖) ^ 2 := by
    have hq : 0 ≤ ‖v‖ := norm_nonneg v
    nlinarith [sq_nonneg (14 * ‖v‖)]
  have himlarge : (1 : ℝ) ≤ |lam.im| := hbase.trans hlarge
  have himne : lam.im ≠ 0 := by
    intro him0
    rw [him0] at himlarge
    norm_num at himlarge
  have hnotpole : lam ∉ NlsGge.Atomic.DM010.dmSourceFrequencySet bc := by
    change lam ∉ Set.range (fun i : FreeIndex bc => (freeFrequency bc i : ℂ))
    rintro ⟨i, rfl⟩
    apply himne
    simp
  have hnotpoleSector : NlsGge.Atomic.DM010.dmLambda n x t ∉
      NlsGge.Atomic.DM010.dmSourceFrequencySet bc := by
    rw [hdecomp]
    exact hnotpole

  have himlargeSqrt : 1 + 14 * ‖v‖ ≤ Real.sqrt |t| := by
    apply Real.le_sqrt_of_sq_le
    simpa [t] using hlarge
  have hδpos : 0 < δ := by
    have hδlower := dm011_frequencyDistance_ge_abs_im bc hbc lam
    dsimp [δ]
    exact lt_of_lt_of_le zero_lt_one (himlarge.trans hδlower)

  obtain ⟨R0, T0, hR0, hcoeffSector, _hactionSector,
      hfreeRightSector, hfreeLeftSector, hT0Sector, hT0normSector⟩ :=
    NlsGge.Atomic.DM010.dm_free_resolvent_realization
      bc hbc n x t hx hnotpoleSector

  have hcoeff : ∀ f : SourcePairL2, ∀ i : FreeIndex bc,
      (freeZSBasis bc).repr (R0 f) i =
        (((Real.pi : ℂ) * lam - freeEigenvalue bc i)⁻¹) *
          (freeZSBasis bc).repr f i := by
    intro f i
    simpa [hdecomp] using hcoeffSector f i
  have hR0norm : ‖R0‖ ≤ (Real.pi * δ)⁻¹ := by
    apply dm011_freeResolvent_norm_of_coefficients bc lam R0
      (by simpa [δ] using hδpos) hcoeff

  have hfreeRight : ∀ f : SourcePairL2,
      z • R0 f - NlsGge.Atomic.LIB033.zsRealization 0 bc
        ⟨R0 f, hR0 f⟩ = f := by
    intro f
    simpa [z, hdecomp] using hfreeRightSector f
  have hfreeLeft : ∀ u : (NlsGge.Atomic.LIB033.zsRealization 0 bc).domain,
      R0 (z • (u : SourcePairL2) -
        NlsGge.Atomic.LIB033.zsRealization 0 bc u) = u := by
    intro u
    simpa [z, hdecomp] using hfreeLeftSector u
  have hT0 : ∀ f : SourcePairL2,
      T0 f = NlsGge.Atomic.LIB031.pairRepresentative
        (NlsGge.Atomic.LIB033.domainLift
          (⟨R0 f, hR0 f⟩ : NlsGge.Atomic.LIB033.zsDomain bc)) :=
    hT0Sector
  have hT0norm : ‖T0‖ ≤ Real.sqrt a / Real.pi := by
    simpa [a, hdecomp] using hT0normSector
  have ha : 0 ≤ a := by
    dsimp [a, NlsGge.Atomic.DM010.dmLatticeSum]
    exact tsum_nonneg (fun k =>
      NlsGge.Atomic.DM010.dm_latticeTerm_nonneg bc lam k)

  have hKhalfSector := dm011_actualPerturbation_norm_le_half
    bc hbc v n x t hx hnotpoleSector himlargeSqrt
    R0 hR0 T0 hT0 hT0normSector
  have hKhalf :
      ‖dm011ActualPerturbation bc v R0 hR0 T0 hT0 a ha hT0norm‖ ≤ 1 / 2 := by
    simpa [a, hdecomp] using hKhalfSector

  obtain ⟨R, T, hR, hright, hleft, hrep, hRnorm, hTnorm⟩ :=
    dm011_actual_perturbation_assembly
      bc v z a δ ha hδpos R0 T0 hR0 hfreeRight hfreeLeft hT0
      hR0norm hT0norm hKhalf

  dsimp only
  refine ⟨R, T, hR, hright, hleft, hrep, ?_, ?_, ?_, ?_⟩
  · exact dm011_assembly_hasBoundedResolvent
      bc (NlsGge.Atomic.DM001.scaledPotential v) z R hR hright hleft
  · simpa [δ, dm011FrequencyDistance] using hδpos
  · simpa [δ, dm011FrequencyDistance, div_eq_mul_inv] using hRnorm
  · simpa [a] using hTnorm
end NlsGge.Atomic.DM011
