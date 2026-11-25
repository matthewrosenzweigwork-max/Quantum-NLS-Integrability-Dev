import NlsGge.Sobolev.FiniteFourier

/-! Actual periodic representatives and the genuine Hilbert-space Fourier transform. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Real

namespace NlsGge.Pilot

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- The real-line representative of the finite field; derivatives are taken here. -/
def planeReal (N : ℕ) (z : FourierPlane N) (x : ℝ) : ℂ :=
  planeField N z (x : PhysicalCircle)

theorem planeReal_periodic (N : ℕ) (z : FourierPlane N) :
    Function.Periodic (planeReal N z) 1 := by
  intro x
  simp only [planeReal, AddCircle.coe_add_period]

theorem contDiff_planeReal (N : ℕ) (z : FourierPlane N) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (planeReal N z) := by
  unfold planeReal planeField
  simp only [fourier_coe_apply]
  apply ContDiff.sum
  intro i _
  apply contDiff_const.mul
  apply ContDiff.cexp
  apply ContDiff.div_const
  exact contDiff_const.mul Complex.ofRealCLM.contDiff

/-- Differentiation of Fourier coordinates, with the physical period-one multiplier. -/
def derivativePlane (N : ℕ) (z : FourierPlane N) : FourierPlane N :=
  fun i => z i * (2 * π * Complex.I * (modeIndex N i : ℂ))

theorem hasDerivAt_planeReal (N : ℕ) (z : FourierPlane N) (x : ℝ) :
    HasDerivAt (planeReal N z) (planeReal N (derivativePlane N z) x) x := by
  unfold planeReal planeField derivativePlane
  convert HasDerivAt.sum (u := Finset.univ)
    (fun i _ => (hasDerivAt_fourier (1 : ℝ) (modeIndex N i) x).const_mul (z i)) using 1
  · funext y
    simp only [Finset.sum_apply]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Complex.ofReal_one, div_one]
    ring

/-- Ordinary Fourier analysis is a linear isometric equivalence onto genuine l2. -/
def physicalFourierL2 : PhysicalL2 ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  (fourierBasis (T := (1 : ℝ))).repr

theorem physicalFourierL2_apply (u : PhysicalL2) (n : ℤ) :
    physicalFourierL2 u n = physicalFourier u n :=
  fourierBasis_repr u n

theorem physicalFourierL2_norm (u : PhysicalL2) :
    ‖physicalFourierL2 u‖ = ‖u‖ :=
  physicalFourierL2.norm_map u

theorem hasSum_physicalFourier_sq (u : PhysicalL2) :
    HasSum (fun n : ℤ => ‖physicalFourier u n‖ ^ 2) (‖u‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (physicalFourierL2 u)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, physicalFourierL2_apply,
    physicalFourierL2_norm] using h

theorem summable_physicalFourier_sq (u : PhysicalL2) :
    Summable (fun n : ℤ => ‖physicalFourier u n‖ ^ 2) :=
  (hasSum_physicalFourier_sq u).summable

theorem planeL2_eq_sum (N : ℕ) (z : FourierPlane N) :
    planeL2 N z = ∑ i : Fin (2 * N + 1), z i • fourierLp 2 (modeIndex N i) := by
  have h : planeContinuous N z =
      ∑ i : Fin (2 * N + 1), z i • (fourier (T := (1 : ℝ)) (modeIndex N i)) := by
    ext x
    simp [planeContinuous, planeField, smul_eq_mul]
  unfold planeL2
  rw [h, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (ContinuousMap.toLp 2 spatialMeasure ℂ).map_smul (z i) (fourier (modeIndex N i))

theorem planeL2_norm_sq (N : ℕ) (z : FourierPlane N) :
    ‖planeL2 N z‖ ^ 2 = ∑ i : Fin (2 * N + 1), ‖z i‖ ^ 2 := by
  have hs : ‖∑ i : Fin (2 * N + 1),
      z i • fourierLp (T := (1 : ℝ)) 2 (modeIndex N i)‖ ^ 2 =
      ∑ i : Fin (2 * N + 1), ‖z i‖ ^ 2 := by
    have h := ((orthonormal_fourier (T := (1 : ℝ))).comp
      (modeIndex N) (modeIndex_injective N)).inner_sum z z Finset.univ
    simp only [Function.comp_apply] at h
    rw [inner_self_eq_norm_sq_to_K] at h
    simp only [RCLike.conj_mul] at h
    exact_mod_cast h
  rw [planeL2_eq_sum]
  exact hs

/-- Weighted coordinates in ordinary l2, rather than a norm on all sequences. -/
def weightedCoordinates (w : ℤ → ℝ) (x : ℤ → ℂ) (n : ℤ) : ℂ :=
  (Real.sqrt (w n) : ℂ) * x n

theorem weightedCoordinates_norm_sq (w : ℤ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (x : ℤ → ℂ) (n : ℤ) :
    ‖weightedCoordinates w x n‖ ^ 2 = w n * ‖x n‖ ^ 2 := by
  simp only [weightedCoordinates, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hw n)]

theorem weightedCoordinates_mem_l2_iff (w : ℤ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (x : ℤ → ℂ) :
    Memℓp (weightedCoordinates w x) 2 ↔
      Summable (fun n : ℤ => w n * ‖x n‖ ^ 2) := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, weightedCoordinates_norm_sq w hw x]

/-- A concrete weighted square-summable sequence realized in mathlib's l2. -/
def weightedL2Element (w : ℤ → ℝ) (hw : ∀ n, 0 ≤ w n) (x : ℤ → ℂ)
    (hx : Summable (fun n : ℤ => w n * ‖x n‖ ^ 2)) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨weightedCoordinates w x, (weightedCoordinates_mem_l2_iff w hw x).2 hx⟩

theorem weightedL2Element_hasSum (w : ℤ → ℝ) (hw : ∀ n, 0 ≤ w n) (x : ℤ → ℂ)
    (hx : Summable (fun n : ℤ => w n * ‖x n‖ ^ 2)) :
    HasSum (fun n : ℤ => w n * ‖x n‖ ^ 2) (‖weightedL2Element w hw x hx‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num)
    (weightedL2Element w hw x hx)
  change HasSum (fun n : ℤ => ‖weightedCoordinates w x n‖ ^ (2 : ℝ≥0∞).toReal)
    (‖weightedL2Element w hw x hx‖ ^ (2 : ℝ≥0∞).toReal) at h
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    weightedCoordinates_norm_sq w hw x] using h

theorem weightedL2Element_norm_sq (w : ℤ → ℝ) (hw : ∀ n, 0 ≤ w n) (x : ℤ → ℂ)
    (hx : Summable (fun n : ℤ => w n * ‖x n‖ ^ 2)) :
    ‖weightedL2Element w hw x hx‖ ^ 2 = ∑' n : ℤ, w n * ‖x n‖ ^ 2 :=
  (weightedL2Element_hasSum w hw x hx).tsum_eq.symm

theorem weightedCoordinates_injective (w : ℤ → ℝ) (hw : ∀ n, 0 < w n) :
    Function.Injective (weightedCoordinates w) := by
  intro x y h
  funext n
  have hn := congrFun h n
  exact mul_left_cancel₀ (by exact_mod_cast (Real.sqrt_pos.2 (hw n)).ne') hn


theorem deriv_planeReal (N : ℕ) (z : FourierPlane N) :
    deriv (planeReal N z) = planeReal N (derivativePlane N z) := by
  funext x
  exact (hasDerivAt_planeReal N z x).deriv

theorem iteratedDeriv_planeReal (N : ℕ) (z : FourierPlane N) (k : ℕ) :
    iteratedDeriv k (planeReal N z) = planeReal N ((derivativePlane N)^[k] z) := by
  induction k with
  | zero => simp only [iteratedDeriv_zero, Function.iterate_zero, id_eq]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, deriv_planeReal, Function.iterate_succ_apply']

theorem planeField_reflectPlane (N : ℕ) (z : FourierPlane N) (x : PhysicalCircle) :
    planeField N (reflectPlane N z) x = -planeField N z (-x) := by
  classical
  unfold planeField reflectPlane
  calc
    (∑ i : Fin (2 * N + 1), -z (reflectMode N i) * fourier (modeIndex N i) x) =
        ∑ i : Fin (2 * N + 1), -z i * fourier (-modeIndex N i) x := by
      apply Fintype.sum_bijective (reflectMode N) (reflectMode_involutive N).bijective
      intro i
      rw [modeIndex_reflect, neg_neg]
    _ = -(∑ i : Fin (2 * N + 1), z i * fourier (modeIndex N i) (-x)) := by
      simp only [fourier_apply, zsmul_neg, neg_zsmul, neg_mul,
        Finset.sum_neg_distrib]

theorem japaneseBracket_one_le (n : ℤ) : 1 ≤ japaneseBracket n := by
  unfold japaneseBracket
  exact Real.one_le_sqrt.2 (by nlinarith [sq_nonneg (n : ℝ)])

theorem japaneseBracket_pos (n : ℤ) : 0 < japaneseBracket n :=
  lt_of_lt_of_le zero_lt_one (japaneseBracket_one_le n)

theorem sobolevSquareSummable_restrict (r t : ℝ) (hrt : r ≤ t) (x : ℤ → ℂ)
    (hx : SobolevSquareSummable t x) : SobolevSquareSummable r x := by
  apply Summable.of_nonneg_of_le (fun n =>
    mul_nonneg (Real.rpow_nonneg (japaneseBracket_pos n).le _) (sq_nonneg _))
    (fun n => ?_) hx
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (japaneseBracket_one_le n) (by linarith))
    (sq_nonneg _)

theorem weightedSquareSummable_restrict (a : ℤ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (s t : ℝ) (hst : s ≤ t) (x : ℤ → ℂ)
    (hx : WeightedSquareSummable a s x) : WeightedSquareSummable a t x := by
  apply Summable.of_nonneg_of_le (fun n =>
    mul_nonneg (mul_nonneg (ha n) (Real.rpow_nonneg (japaneseBracket_pos n).le _))
      (sq_nonneg _)) (fun n => ?_) hx
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (japaneseBracket_one_le n) (by linarith)) (ha n)

theorem summable_weighted_planeField (N : ℕ) (z : FourierPlane N) (w : ℤ → ℝ) :
    Summable (fun n : ℤ => w n * ‖physicalFourier (planeField N z) n‖ ^ 2) := by
  classical
  apply summable_of_ne_finset_zero
    (s := Finset.univ.image (modeIndex N))
  intro n hn
  have hout : n < -(N : ℤ) ∨ (N : ℤ) < n := by
    by_contra h
    have hb : -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ) := by omega
    obtain ⟨i, hi⟩ := modeIndex_covers N n hb.1 hb.2
    exact hn (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)
  simp [physicalFourier_planeField_outside N z n hout]

theorem sobolevSquareSummable_planeField (N : ℕ) (z : FourierPlane N) (r : ℝ) :
    SobolevSquareSummable r (physicalFourier (planeField N z)) :=
  summable_weighted_planeField N z (fun n => Real.rpow (japaneseBracket n) (2 * r))

theorem weightedSquareSummable_planeField (N : ℕ) (z : FourierPlane N)
    (a : ℤ → ℝ) (s : ℝ) :
    WeightedSquareSummable a s (physicalFourier (planeField N z)) :=
  summable_weighted_planeField N z (fun n => a n * Real.rpow (japaneseBracket n) (-2 * s))

def physicalSobolevL2 (r : ℝ) (u : PhysicalL2)
    (hu : SobolevSquareSummable r (physicalFourier u)) : lp (fun _ : ℤ => ℂ) 2 :=
  weightedL2Element (fun n => Real.rpow (japaneseBracket n) (2 * r))
    (fun n => (Real.rpow_pos_of_pos (japaneseBracket_pos n) _).le)
    (physicalFourier u) hu

theorem physicalSobolevL2_norm_sq (r : ℝ) (u : PhysicalL2)
    (hu : SobolevSquareSummable r (physicalFourier u)) :
    ‖physicalSobolevL2 r u hu‖ ^ 2 =
      ∑' n : ℤ, Real.rpow (japaneseBracket n) (2 * r) * ‖physicalFourier u n‖ ^ 2 :=
  weightedL2Element_norm_sq _ _ _ hu

def squareReflection (x : lp (fun _ : ℤ => ℂ) 2) : lp (fun _ : ℤ => ℂ) 2 := by
  refine ⟨fun n => -x (-n), ?_⟩
  apply memℓp_gen
  have hs := (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa only [norm_neg, Function.comp_apply] using!
    ((Equiv.neg ℤ).summable_iff).2 hs

def squareReflectionLinearEquiv :
    lp (fun _ : ℤ => ℂ) 2 ≃ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2 where
  toFun := squareReflection
  invFun := squareReflection
  left_inv x := by
    apply lp.ext
    funext n
    simp only [squareReflection, neg_neg]
  right_inv x := by
    apply lp.ext
    funext n
    simp only [squareReflection, neg_neg]
  map_add' x y := by
    apply lp.ext
    funext n
    simp only [squareReflection, lp.coeFn_add, Pi.add_apply, neg_add]
  map_smul' c x := by
    apply lp.ext
    funext n
    simp only [squareReflection, lp.coeFn_smul, Pi.smul_apply, smul_neg, RingHom.id_apply]

theorem squareReflection_norm (x : lp (fun _ : ℤ => ℂ) 2) : ‖squareReflection x‖ = ‖x‖ := by
  have hx := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) x
  have hr := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (squareReflection x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hx hr
  have hsum : (∑' n : ℤ, ‖squareReflection x n‖ ^ 2) = ∑' n : ℤ, ‖x n‖ ^ 2 := by
    simp only [squareReflection, norm_neg]
    exact tsum_comp_neg (fun n : ℤ => ‖x n‖ ^ 2)
  rw [hsum, ← hx] at hr
  nlinarith [norm_nonneg (squareReflection x), norm_nonneg x]

def squareReflectionIsometry :
    lp (fun _ : ℤ => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 where
  __ := squareReflectionLinearEquiv
  norm_map' := squareReflection_norm

/-- The actual source minus-reflected physical Fourier convention on L2. -/
def reflectedFourierL2 : PhysicalL2 ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  physicalFourierL2.trans squareReflectionIsometry

theorem reflectedFourierL2_apply (u : PhysicalL2) (n : ℤ) :
    reflectedFourierL2 u n = reflectedFourier u n := by
  change -physicalFourierL2 u (-n) = reflectedFourier u n
  rw [physicalFourierL2_apply]
  rfl

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

theorem continuous_planeL2 (N : ℕ) : Continuous (planeL2 N) := by
  letI : ContinuousAdd PhysicalL2 := inferInstance
  letI : ContinuousSMul ℂ PhysicalL2 := inferInstance
  have hterm (i : Fin (2 * N + 1)) :
      Continuous (fun z : FourierPlane N =>
        z i • (fourierLp 2 (modeIndex N i) : PhysicalL2)) :=
    (continuous_apply i).smul continuous_const
  have hsum : Continuous (fun z : FourierPlane N =>
      (∑ i : Fin (2 * N + 1),
        z i • (fourierLp 2 (modeIndex N i) : PhysicalL2))) :=
    continuous_finsetSum Finset.univ (fun i _ => hterm i)
  have h : planeL2 N = fun z : FourierPlane N =>
      ∑ i : Fin (2 * N + 1), z i • (fourierLp 2 (modeIndex N i) : PhysicalL2) := by
    funext z
    exact planeL2_eq_sum N z
  rw [h]
  exact hsum

theorem measurable_planeL2 [MeasurableSpace PhysicalL2] [BorelSpace PhysicalL2]
    (N : ℕ) : Measurable (planeL2 N) :=
  (continuous_planeL2 N).measurable

end NlsGge.Pilot
