import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.ThirdConsultation.M.PeriodicGN036A

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.MPeriodicGN

theorem jb_sq (n : ℤ) : japaneseBracket n ^ 2 = 1 + (n : ℝ) ^ 2 := by
  unfold japaneseBracket
  rw [Real.sq_sqrt (by positivity)]

theorem modeWeight_eq (m : ℕ) (n : ℤ) :
    sobolevModeWeight (m : ℝ) n = (1 + (n : ℝ) ^ 2) ^ m := by
  unfold sobolevModeWeight
  have he : 2 * (m : ℝ) = ((2 * m : ℕ) : ℝ) := by push_cast; ring
  rw [he]
  change japaneseBracket n ^ ((2 * m : ℕ) : ℝ) = _
  rw [Real.rpow_natCast, pow_mul, jb_sq]

theorem ord_norm_sq (m : ℕ) (u : PhysicalSobolev38 (m : ℝ)) :
    ‖ordinarySobolevCarrier38 m u‖ ^ 2 = ‖u‖ ^ 2 := by
  have hu : ‖u‖ = ‖physicalSobolevFourierEquiv38 (m : ℝ) u‖ :=
    ((physicalSobolevFourierEquiv38 (m : ℝ)).norm_map u).symm
  rw [hu]
  set x := physicalSobolevFourierEquiv38 (m : ℝ) u with hx
  set a := carrierCoe38 (m : ℝ) x with ha
  have h1 : ‖x‖ ^ 2 = ∑' n : ℤ, sobolevModeWeight (m : ℝ) n * ‖a n‖ ^ 2 :=
    weightedHilbert_norm_sq (sobolevModeWeight (m : ℝ))
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x)
  have h2 : ‖ordinarySobolevCarrier38 m u‖ ^ 2 =
      ∑' n : ℤ, sobolevModeWeight (m : ℝ) n * ‖-a (-n)‖ ^ 2 :=
    weightedHilbert_norm_sq (sobolevModeWeight (m : ℝ))
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from ordinarySobolevCarrier38 m u)
  rw [h2, h1]
  rw [← (Equiv.neg ℤ).tsum_eq (fun n => sobolevModeWeight (m : ℝ) n * ‖a n‖ ^ 2)]
  refine tsum_congr (fun n => ?_)
  simp only [Equiv.neg_apply, norm_neg]
  have : sobolevModeWeight (m : ℝ) (-n) = sobolevModeWeight (m : ℝ) n := by
    simp [sobolevModeWeight, japaneseBracket]
  rw [this]

theorem ord_norm (m : ℕ) (u : PhysicalSobolev38 (m : ℝ)) :
    ‖ordinarySobolevCarrier38 m u‖ = ‖u‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (ord_norm_sq m u)

/-- Coordinate of the ordinary Sobolev carrier. -/
def ordCoord (m : ℕ) (u : PhysicalSobolev38 (m : ℝ)) (n : ℤ) : ℂ :=
  (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from ordinarySobolevCarrier38 m u) n

theorem hasSum_weighted (m : ℕ) (u : PhysicalSobolev38 (m : ℝ)) :
    HasSum (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ m * ‖ordCoord m u n‖ ^ 2) (‖u‖ ^ 2) := by
  have h : HasSum (fun n : ℤ => sobolevModeWeight (m : ℝ) n * ‖ordCoord m u n‖ ^ 2)
      (‖ordinarySobolevCarrier38 m u‖ ^ 2) :=
    weightedHilbert_hasSum (sobolevModeWeight (m : ℝ))
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from ordinarySobolevCarrier38 m u)
  rw [ord_norm] at h
  simpa only [modeWeight_eq] using h

theorem hasSum_phys (m : ℕ) (u : PhysicalSobolev38 (m : ℝ)) :
    HasSum (fun n : ℤ => ‖ordCoord m u n‖ ^ 2)
      (‖riccatiSobolevIteratedDerivativeL2CLMRecovery30First m 0 (Nat.zero_le m)
        (ordinarySobolevCarrier38 m u)‖ ^ 2) := by
  have h := hasSum_physicalFourier_sq
    (riccatiSobolevIteratedDerivativeL2CLMRecovery30First m 0 (Nat.zero_le m)
      (ordinarySobolevCarrier38 m u))
  have e : ∀ n, physicalFourier
      (riccatiSobolevIteratedDerivativeL2CLMRecovery30First m 0 (Nat.zero_le m)
        (ordinarySobolevCarrier38 m u)) n = ordCoord m u n := by
    intro n
    rw [riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier]
    unfold riccatiSobolevJetCoefficientL2Recovery28Second ordCoord
    rw [pow_zero, one_mul]
  simpa only [e] using h


local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

theorem cont_rep_coord (m i : ℕ) (h : i + 1 ≤ m) (x : SobolevHilbert (m : ℝ)) :
    ∃ y : SobolevHilbert 1,
      riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth m i h x =
        physicalH1CanonicalContinuousRepresentativeCLM y ∧
      ∀ n, (show WeightedHilbert (sobolevModeWeight (1 : ℝ)) from y) n =
        riccatiSobolevJetCoefficientL2Recovery28Second m i x n := by
  refine ⟨_, rfl, fun n => rfl⟩

theorem sup_le_sum (m i : ℕ) (h : i + 1 ≤ m) (x : SobolevHilbert (m : ℝ)) :
    ‖riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth m i h x‖ ≤
      ∑' n : ℤ, ‖riccatiSobolevJetCoefficientL2Recovery28Second m i x n‖ := by
  obtain ⟨y, hy, hcoord⟩ := cont_rep_coord m i h x
  rw [hy, physicalH1CanonicalContinuousRepresentativeCLM_apply]
  have hu := physicalH1CarrierToL2AfterAcceptedCoordinate_sobolevSquareSummable y
  have hs := NlsGge.Analysis.physicalH1_absolute_fourier_summable
    (physicalH1CarrierToL2AfterAcceptedCoordinate y) hu
  unfold physicalH1CarrierContinuousAfterAcceptedCoordinate
  calc ‖NlsGge.Analysis.physicalH1Continuous (physicalH1CarrierToL2AfterAcceptedCoordinate y) hu‖
      ≤ ∑' p : ℤ, ‖physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate y) p •
          fourier (T := (1 : ℝ)) p‖ :=
        norm_tsum_le_tsum_norm (by simpa only [norm_smul, fourier_norm, mul_one] using hs)
    _ = ∑' p : ℤ, ‖physicalFourier (physicalH1CarrierToL2AfterAcceptedCoordinate y) p‖ := by
        simp only [norm_smul, fourier_norm, mul_one]
    _ = ∑' p : ℤ, ‖riccatiSobolevJetCoefficientL2Recovery28Second m i x p‖ := by
        refine tsum_congr (fun p => ?_)
        rw [physicalH1CarrierToL2AfterAcceptedCoordinate_fourier, hcoord]

theorem coef_norm (m i : ℕ) (u : PhysicalSobolev38 (m : ℝ)) (n : ℤ) :
    ‖riccatiSobolevJetCoefficientL2Recovery28Second m i (ordinarySobolevCarrier38 m u) n‖ =
      (2 * Real.pi) ^ i * (|(n : ℝ)| ^ i * ‖ordCoord m u n‖) := by
  unfold riccatiSobolevJetCoefficientL2Recovery28Second
  rw [norm_mul, norm_pow, norm_fourierMultiplier, mul_pow, mul_assoc]
  rfl

theorem rpow_sq_half {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : (x ^ 2) ^ (a / 2) = x ^ a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1; push_cast; ring

theorem rpow_sq_swap {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : (x ^ a) ^ 2 = (x ^ 2) ^ a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1; push_cast; ring

theorem GN_sup (m i : ℕ) (hi : i < m) (u : PhysicalSobolev38 (m : ℝ)) :
    ‖riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth m i (by omega)
        (ordinarySobolevCarrier38 m u)‖ ≤
      2 ^ (i + 3) * (2 * Real.pi) ^ i *
        (‖u‖ ^ (((i : ℝ) + 1 / 2) / m) *
          ‖riccatiSobolevIteratedDerivativeL2CLMRecovery30First m 0 (Nat.zero_le m)
            (ordinarySobolevCarrier38 m u)‖ ^ (1 - ((i : ℝ) + 1 / 2) / m)) := by
  set φn := ‖riccatiSobolevIteratedDerivativeL2CLMRecovery30First m 0 (Nat.zero_le m)
            (ordinarySobolevCarrier38 m u)‖ with hφ
  obtain ⟨hsum, hle⟩ := int_sum_bound m i hi (fun n => ‖ordCoord m u n‖)
    (fun n => norm_nonneg _) (φn ^ 2) (‖u‖ ^ 2) (hasSum_phys m u) (hasSum_weighted m u)
  rw [rpow_sq_half (norm_nonneg _), rpow_sq_half (norm_nonneg _)] at hle
  refine (sup_le_sum m i (by omega) _).trans ?_
  rw [tsum_congr (coef_norm m i u), tsum_mul_left]
  have hp : 0 ≤ (2 * Real.pi) ^ i := by positivity
  calc (2 * Real.pi) ^ i * ∑' n : ℤ, |(n : ℝ)| ^ i * ‖ordCoord m u n‖
      ≤ (2 * Real.pi) ^ i * (2 ^ (i + 3) * (φn ^ (1 - ((i : ℝ) + 1 / 2) / m) *
          ‖u‖ ^ (((i : ℝ) + 1 / 2) / m))) := mul_le_mul_of_nonneg_left hle hp
    _ = _ := by ring

theorem GN_deriv (m j : ℕ) (hj : j ≤ m) (hm0 : 0 < m) (u : PhysicalSobolev38 (m : ℝ))
    (v : PhysicalSobolev38 (j : ℝ))
    (hv : physicalSobolevFourierEquiv38 (j : ℝ) v =
      carrierIncl38 (Nat.cast_le.mpr hj : (j : ℝ) ≤ (m : ℝ))
        (physicalSobolevFourierEquiv38 (m : ℝ) u)) :
    ‖physicalSobolevDerivative38 j v‖ ≤
      (2 * Real.pi) ^ j *
        (‖u‖ ^ ((j : ℝ) / m) *
          ‖riccatiSobolevIteratedDerivativeL2CLMRecovery30First m 0 (Nat.zero_le m)
            (ordinarySobolevCarrier38 m u)‖ ^ (1 - (j : ℝ) / m)) := by
  set φn := ‖riccatiSobolevIteratedDerivativeL2CLMRecovery30First m 0 (Nat.zero_le m)
            (ordinarySobolevCarrier38 m u)‖ with hφ
  have hcoord : ∀ n, ordCoord j v n = ordCoord m u n := by
    intro n
    have h1 : ordCoord j v n = -(carrierCoe38 (j : ℝ) (physicalSobolevFourierEquiv38 (j : ℝ) v) (-n)) := rfl
    have h2 : ordCoord m u n = -(carrierCoe38 (m : ℝ) (physicalSobolevFourierEquiv38 (m : ℝ) u) (-n)) := rfl
    rw [h1, h2, hv, carrierCoe38_incl38]
  have hD : HasSum (fun n : ℤ => ((2 * Real.pi) ^ j * |(n : ℝ)| ^ j) ^ 2 * ‖ordCoord m u n‖ ^ 2)
      (‖physicalSobolevDerivative38 j v‖ ^ 2) := by
    have h := hasSum_physicalFourier_sq (physicalSobolevDerivative38 j v)
    have e : ∀ n : ℤ, ‖physicalFourier (physicalSobolevDerivative38 j v) n‖ ^ 2 =
        ((2 * Real.pi) ^ j * |(n : ℝ)| ^ j) ^ 2 * ‖ordCoord m u n‖ ^ 2 := by
      intro n
      have hn : ‖(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))‖ = 2 * Real.pi * |(n : ℝ)| :=
        norm_fourierMultiplier n
      have hc : ‖physicalFourier (physicalSobolevEmbed j v) n‖ = ‖ordCoord m u n‖ := by
        rw [← hcoord n, ← ordinarySobolevCarrier38_fourier j v n]; rfl
      rw [physicalSobolevDerivative38_fourier j v n, norm_mul, norm_pow, hn, hc, mul_pow, mul_pow]
    have : (fun n : ℤ => ‖physicalFourier (physicalSobolevDerivative38 j v) n‖ ^ 2) =
        fun n : ℤ => ((2 * Real.pi) ^ j * |(n : ℝ)| ^ j) ^ 2 * ‖ordCoord m u n‖ ^ 2 := funext e
    rw [this] at h
    exact h
  obtain ⟨hs, hle⟩ := holder_bound m j hj hm0 (fun n => ‖ordCoord m u n‖ ^ 2)
    (fun n => sq_nonneg _) (φn ^ 2) (‖u‖ ^ 2) (hasSum_phys m u) (hasSum_weighted m u)
  have hmaj : Summable (fun n : ℤ => ((2 * Real.pi) ^ j) ^ 2 *
      ((1 + (n : ℝ) ^ 2) ^ j * ‖ordCoord m u n‖ ^ 2)) := hs.mul_left _
  have hterm : ∀ n : ℤ, ((2 * Real.pi) ^ j * |(n : ℝ)| ^ j) ^ 2 * ‖ordCoord m u n‖ ^ 2 ≤
      ((2 * Real.pi) ^ j) ^ 2 * ((1 + (n : ℝ) ^ 2) ^ j * ‖ordCoord m u n‖ ^ 2) := by
    intro n
    have h1 : (|(n : ℝ)| ^ j) ^ 2 ≤ (1 + (n : ℝ) ^ 2) ^ j := by
      calc (|(n : ℝ)| ^ j) ^ 2 = (|(n : ℝ)| ^ 2) ^ j := by ring
        _ = ((n : ℝ) ^ 2) ^ j := by rw [sq_abs]
        _ ≤ (1 + (n : ℝ) ^ 2) ^ j := pow_le_pow_left₀ (sq_nonneg _) (by linarith) j
    calc ((2 * Real.pi) ^ j * |(n : ℝ)| ^ j) ^ 2 * ‖ordCoord m u n‖ ^ 2
        = ((2 * Real.pi) ^ j) ^ 2 * ((|(n : ℝ)| ^ j) ^ 2 * ‖ordCoord m u n‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)) (sq_nonneg _)
  have hD2 : ‖physicalSobolevDerivative38 j v‖ ^ 2 ≤ ((2 * Real.pi) ^ j) ^ 2 *
      (‖u‖ ^ 2) ^ ((j : ℝ) / m) * (φn ^ 2) ^ (1 - (j : ℝ) / m) := by
    rw [← hD.tsum_eq]
    refine (hD.summable.tsum_le_tsum hterm hmaj).trans ?_
    rw [tsum_mul_left, mul_assoc]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  have e : ((2 * Real.pi) ^ j * (‖u‖ ^ ((j : ℝ) / m) * φn ^ (1 - (j : ℝ) / m))) ^ 2 =
      ((2 * Real.pi) ^ j) ^ 2 * ((‖u‖ ^ ((j : ℝ) / m)) ^ 2 * (φn ^ (1 - (j : ℝ) / m)) ^ 2) := by
    ring
  rw [e, rpow_sq_swap (norm_nonneg _), rpow_sq_swap (norm_nonneg _)]
  calc _ ≤ _ := hD2
    _ = _ := by ring

end NlsGge.ThirdConsultation.MPeriodicGN
