import NlsGge.Hierarchy.A01Spectral38
import NlsGge.Spectral.ActualFirstMomentE02_38
import NlsGge.Hierarchy.RiccatiUnitPeriodIntervalToPhysicalHaar

/-! # S01 (translation equivariance), part b: Φ-free momentum/Fourier identity

For a smooth period-one `U` the momentum `P(U) = Im ∫₀¹ Ū U'` equals `2π Σ n |û_n|²`
(Parseval for the inner product, `fourierBasis`), and a physical field in every `H^m` has a smooth
periodic representative. Together with the accepted first-moment identity
(`actualFirstMoment_eq_sum_E02_38`, `actualFirstMoment_eq_neg_momentum_E02_38`) this gives
`Σ 2πn I_n(u) = -2π Σ n |û_n|²` for finite-gap smooth fields.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations MeasureTheory
open scoped ContDiff

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

theorem periodicDerivComplex_S01_38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) :
    Function.Periodic (deriv U) 1 := by
  have := NlsGge.HierarchyRiccati.periodic_iteratedDeriv_of_contDiff U hU hper 1
  simpa [iteratedDeriv_one] using this

/-- Parseval for the momentum of a smooth period-one field: `P(U) = Σ 2π n |û_n|²`. -/
theorem momentum_hasSum38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) :
    HasSum (fun n : ℤ => 2 * Real.pi * (n : ℝ) * ‖smoothFourier38 U hU hper n‖ ^ 2)
      (momentumE02_38 U) := by
  have hdc : Continuous (deriv U) := hU.continuous_deriv (by simp)
  have hdp := periodicDerivComplex_S01_38 U hU hper
  set F := riccatiSmoothPeriodicLiftContinuousMapRecovery30First U hU.continuous hper with hF
  set G := riccatiSmoothPeriodicLiftContinuousMapRecovery30First (deriv U) hdc hdp with hG
  set fL : Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) :=
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ F with hfL
  set gL : Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) :=
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ G with hgL
  -- Parseval for the inner product
  have hP := (fourierBasis (T := (1 : ℝ))).hasSum_inner_mul_inner fL gL
  have hcoef : ∀ (v : Lp ℂ 2 (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ)))) (i : ℤ),
      inner ℂ ((fourierBasis (T := (1 : ℝ))) i) v = fourierCoeff v i := fun v i =>
    (HilbertBasis.repr_apply_apply _ v i).symm.trans (fourierBasis_repr v i)
  have hgcoef : ∀ i : ℤ, fourierCoeff gL i = fourierMultiplier i * fourierCoeff fL i := by
    intro i
    have h1 := physicalFourier_liftContinuousMap_eq_fourierCoeffOnRecovery30First
      (deriv U) hdc hdp i
    have h2 := physicalFourier_liftContinuousMap_eq_fourierCoeffOnRecovery30First
      U hU.continuous hper i
    have h3 := riccatiFourierCoeffOn_deriv_periodOneRecovery29 U hU hper i
    have e1 : fourierCoeff gL i = fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (deriv U) i := h1
    have e2 : fourierCoeff fL i = fourierCoeffOn (by norm_num : (0 : ℝ) < 1) U i := h2
    rw [e1, e2, h3]
  have hterm : ∀ i : ℤ, (inner ℂ fL ((fourierBasis (T := (1 : ℝ))) i) *
      inner ℂ ((fourierBasis (T := (1 : ℝ))) i) gL).im =
      2 * Real.pi * (i : ℝ) * ‖smoothFourier38 U hU hper i‖ ^ 2 := by
    intro i
    have e1 : inner ℂ fL ((fourierBasis (T := (1 : ℝ))) i) = (starRingEnd ℂ) (fourierCoeff fL i) := by
      rw [← hcoef fL i]
      exact (inner_conj_symm _ _).symm
    have e2 : inner ℂ ((fourierBasis (T := (1 : ℝ))) i) gL =
        fourierMultiplier i * fourierCoeff fL i := by
      rw [hcoef gL i, hgcoef]
    have hs : smoothFourier38 U hU hper i = fourierCoeff fL i := rfl
    rw [e1, e2, hs]
    set c := fourierCoeff fL i
    have : (starRingEnd ℂ) c * (fourierMultiplier i * c) =
        (((2 * Real.pi * (i : ℝ) * ‖c‖ ^ 2 : ℝ) : ℂ)) * Complex.I := by
      unfold fourierMultiplier
      have h := Complex.conj_mul' c
      push_cast
      calc (starRingEnd ℂ) c * (2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * c)
          = 2 * (Real.pi : ℂ) * Complex.I * (i : ℂ) * ((starRingEnd ℂ) c * c) := by ring
        _ = _ := by rw [h]; ring
    rw [this, Complex.mul_I_im, Complex.ofReal_re]
  have hJ : inner ℂ fL gL = ∫ x in (0 : ℝ)..1, star (U x) * deriv U x := by
    rw [L2.inner_def]
    have hfae := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
      (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) F
    have hgae := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
      (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) G
    have h1 : ∫ a, inner ℂ (fL a) (gL a) ∂(AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) =
        ∫ a : PhysicalCircle, inner ℂ (F a) (G a) ∂spatialMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [hfae, hgae] with a ha hb
      rw [ha, hb]
    rw [h1, ← NlsGge.HierarchyRiccati.unitIntervalIntegral_lift_eq_spatialHaar (fun a : PhysicalCircle => inner ℂ (F a) (G a))]
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    have ht' : t ∈ Set.Ioc (0 : ℝ) (0 + 1) := by simpa using ht
    have hFt : F (t : PhysicalCircle) = U t := AddCircle.liftIoc_coe_apply ht'
    have hGt : G (t : PhysicalCircle) = deriv U t := AddCircle.liftIoc_coe_apply (f := deriv U) ht'
    simp only [hFt, hGt, RCLike.inner_apply]
    simp [mul_comm]
  have hIm := hP.mapL Complex.imCLM
  rw [hJ] at hIm
  have hIm' : HasSum (fun n : ℤ => 2 * Real.pi * (n : ℝ) * ‖smoothFourier38 U hU hper n‖ ^ 2)
      (Complex.imCLM (∫ x in (0 : ℝ)..1, star (U x) * deriv U x)) := by
    refine hIm.congr_fun (fun n => ?_)
    rw [← hterm n]
    rfl
  exact hIm'


theorem exists_Ioc_rep38 (y : PhysicalCircle) :
    ∃ t ∈ Set.Ioc (0 : ℝ) 1, (t : PhysicalCircle) = y := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  refine ⟨toIocMod one_pos 0 x, by simpa using toIocMod_mem_Ioc one_pos 0 x, ?_⟩
  rw [← self_sub_toIocDiv_zsmul one_pos 0 x]
  simp

/-- A physical field in every `H^m` has a smooth period-one representative `U`
whose `L²` class (`smoothL2_38`) is the field. -/
theorem exists_smooth_rep38 (u : PhysicalL2)
    (hall : ∀ m : ℕ, SobolevSquareSummable (m : ℝ) (physicalFourier u)) :
    ∃ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      smoothL2_38 U hU hper = u := by
  have hu1 : SobolevSquareSummable 1 (physicalFourier u) := by simpa using hall 1
  set C := NlsGge.Analysis.physicalH1Continuous u hu1 with hC
  set U : ℝ → ℂ := fun y => C (y : PhysicalCircle) with hUdef
  have hser : ∀ y : ℝ, U y = ∑' n : ℤ, fourierRealTerm n (physicalFourier u n) y := by
    intro y
    have h := (NlsGge.Analysis.physicalH1Continuous_hasSum u hu1).mapL
      (ContinuousMap.evalCLM ℂ (y : PhysicalCircle))
    change HasSum (fun n : ℤ => fourierRealTerm n (physicalFourier u n) y) (C (y : PhysicalCircle)) at h
    exact h.tsum_eq.symm
  have hU : ContDiff ℝ ∞ U := by
    have hfun : U = fun y : ℝ => ∑' n : ℤ, fourierRealTerm n (physicalFourier u n) y :=
      funext hser
    rw [hfun]
    exact contDiff_tsum (fun n => contDiff_fourierRealTerm n (physicalFourier u n))
      (fun k _ => (summable_sobolev_amplitude k (physicalFourier u)
        (hall (k + 1))).mul_left ((2 * Real.pi) ^ k))
      (fun k n y _ => norm_iteratedFDeriv_fourierRealTerm_le n (physicalFourier u n) k y)
  have hper : Function.Periodic U 1 := by
    intro y
    simp only [hUdef, AddCircle.coe_add_period]
  refine ⟨U, hU, hper, ?_⟩
  have hF : riccatiSmoothPeriodicLiftContinuousMapRecovery30First U hU.continuous hper = C := by
    ext y
    obtain ⟨t, ht, rfl⟩ := exists_Ioc_rep38 y
    have ht' : t ∈ Set.Ioc (0 : ℝ) (0 + 1) := by simpa using ht
    simp only [riccatiSmoothPeriodicLiftContinuousMapRecovery30First, ContinuousMap.coe_mk]
    rw [AddCircle.liftIoc_coe_apply ht']
  unfold smoothL2_38
  rw [hF]
  exact NlsGge.Analysis.physicalH1Continuous_toLp u hu1


/-- S01.01-.02 in Fourier form: for a field in every `H^m` with finitely many open gaps,
`Σ 2πn I_n(u) = -Σ 2πn |û_n|²` (the first spectral moment is `-P(u)`, and `P(u) = Σ 2πn |û_n|²`). -/
theorem actualFirstMoment_fourier38 (u : PhysicalL2)
    (hall : ∀ m : ℕ, SobolevSquareSummable (m : ℝ) (physicalFourier u))
    (hfin : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite) :
    Summable (fun n : ℤ => 2 * Real.pi * (n : ℝ) * ‖physicalFourier u n‖ ^ 2) ∧
    Summable (fun n : ℤ => 2 * Real.pi * (n : ℝ) * actualGapActionAllE02_38 u n) ∧
    ∑' n : ℤ, 2 * Real.pi * (n : ℝ) * actualGapActionAllE02_38 u n =
      -∑' n : ℤ, 2 * Real.pi * (n : ℝ) * ‖physicalFourier u n‖ ^ 2 := by
  obtain ⟨U, hU, hper, hUu⟩ := exists_smooth_rep38 u hall
  subst hUu
  have hu1 : SobolevSquareSummable 1 (physicalFourier (smoothL2_38 U hU hper)) := by
    simpa using hall 1
  have hae := smoothL2_38_cover_ae U hU hper
  obtain ⟨-, h1s, h1⟩ := actualFirstMoment_eq_sum_E02_38 _ hu1 hfin
  obtain ⟨-, h2⟩ := actualFirstMoment_eq_neg_momentum_E02_38 _ hu1 U hU hper hae
  have h3 := momentum_hasSum38 U hU hper
  have h3' : HasSum (fun n : ℤ => 2 * Real.pi * (n : ℝ) *
      ‖physicalFourier (smoothL2_38 U hU hper) n‖ ^ 2) (momentumE02_38 U) := h3
  refine ⟨h3'.summable, h1s, ?_⟩
  rw [h3'.tsum_eq, ← h1, h2]

end NlsGge.Birkhoff
