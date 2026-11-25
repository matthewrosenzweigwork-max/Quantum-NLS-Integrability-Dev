import NlsGge.Atomic.LIB.LIB034
import NlsGge.Atomic.LIB.LIB008
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Compact inclusion of the genuine interval H1 graph with no boundary condition.
The doubled-circle volume graph is connected explicitly to the normalized Haar
Fourier carrier before applying the accepted compact sequence inclusion. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology Classical

namespace NlsGge.Atomic.LIB035
open NlsGge.Schur NlsGge.Atomic.LIB034 NlsGge.Atomic.LIB001 NlsGge.Atomic.LIB002
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff

local instance : IsProbabilityMeasure spectralHaar := by
  dsimp only [spectralHaar]
  infer_instance

lemma haar_le_volume : spectralHaar ≤ (volume : Measure SpectralCircle) := by
  intro s
  rw [spectral_volume_eq_two_smul, Measure.smul_apply, smul_eq_mul]
  exact le_mul_of_one_le_left (by positivity) (by norm_num)

/-- The actual identity on representative functions, from volume to probability Haar. -/
def toHaar : PeriodTwoL2 →L[ℝ] SpectralScalarL2 :=
  Lp.LpToLpOfMeasureLeSMul (c := (1 : ℝ≥0∞)) (by simp)
    (by simpa only [one_smul] using haar_le_volume)

/-- The reverse actual measure-change map; continuity follows from volume=2*Haar. -/
def toVolume : SpectralScalarL2 →L[ℝ] PeriodTwoL2 :=
  Lp.LpToLpOfMeasureLeSMul (c := (2 : ℝ≥0∞)) (by simp)
    spectral_volume_eq_two_smul.le

lemma toHaar_ae (u : PeriodTwoL2) : toHaar u =ᵐ[spectralHaar] (fun z => u z) :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ u

lemma toVolume_ae (u : SpectralScalarL2) :
    toVolume u =ᵐ[(volume : Measure SpectralCircle)] (fun z => u z) :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ u

set_option backward.isDefEq.respectTransparency false in
lemma toHaar_norm_le (u : PeriodTwoL2) : ‖toHaar u‖ ≤ ‖u‖ := by
  have h : ‖toHaar‖ ≤ 1 := by
    simpa only [toHaar, ENNReal.toReal_one, Real.one_rpow] using
      Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := (2 : ℝ≥0∞))
        (c := (1 : ℝ≥0∞)) (μ := spectralHaar) (ν := (volume : Measure SpectralCircle))
        (by simp) (by simpa only [one_smul] using haar_le_volume)
  calc
    _ ≤ ‖toHaar‖ * ‖u‖ := toHaar.le_opNorm u
    _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := one_mul _

lemma haar_ae_to_volume {u v : SpectralCircle → ℂ} (h : u =ᵐ[spectralHaar] v) :
    u =ᵐ[(volume : Measure SpectralCircle)] v := by
  rw [spectral_volume_eq_two_smul]
  exact Measure.ae_smul_measure h (2 : ℝ≥0∞)

lemma volume_ae_to_haar {u v : SpectralCircle → ℂ}
    (h : u =ᵐ[(volume : Measure SpectralCircle)] v) : u =ᵐ[spectralHaar] v :=
  (Measure.absolutelyContinuous_of_le haar_le_volume).ae_eq h

@[simp] lemma toVolume_toHaar (u : PeriodTwoL2) : toVolume (toHaar u) = u := by
  apply Lp.ext
  filter_upwards [toVolume_ae (toHaar u), haar_ae_to_volume (toHaar_ae u)] with z hv hh
  exact hv.trans hh

@[simp] lemma toHaar_toVolume (u : SpectralScalarL2) : toHaar (toVolume u) = u := by
  apply Lp.ext
  filter_upwards [toHaar_ae (toVolume u), volume_ae_to_haar (toVolume_ae u)] with z hh hv
  exact hh.trans hv

lemma circle_integral_volume (F : SpectralCircle → ℂ) :
    (∫ z, F z ∂(volume : Measure SpectralCircle)) = (2 : ℂ) * ∫ z, F z ∂spectralHaar := by
  rw [spectral_volume_eq_two_smul, integral_smul_measure]
  simp [Complex.real_smul]

/-- The literal pairing normalization, proved on the actual L2 classes. -/
lemma inner_volume_toHaar (u v : PeriodTwoL2) :
    inner ℂ u v = (2 : ℂ) * inner ℂ (toHaar u) (toHaar v) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = (2 : ℂ) * ∫ z : SpectralCircle, inner ℂ (u z) (v z) ∂spectralHaar :=
      circle_integral_volume _
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [toHaar_ae u, toHaar_ae v] with z hu hv
      rw [hu, hv]

lemma toHaar_periodicTest (ψ : SmoothPeriodicTest (2 : ℝ)) :
    toHaar (periodicTestL2 ψ) = ψ.toL2 := by
  apply Lp.ext
  have hv := volume_ae_to_haar
    (ContinuousMap.coeFn_toLp (p := 2) (μ := (volume : Measure SpectralCircle)) (𝕜 := ℂ) ψ.toContinuousMap)
  have hh := ContinuousMap.coeFn_toLp (p := 2) (μ := spectralHaar) (𝕜 := ℂ) ψ.toContinuousMap
  filter_upwards [toHaar_ae (periodicTestL2 ψ), hv, hh] with z hp hvz hhz
  exact hp.trans (hvz.trans hhz.symm)

set_option backward.isDefEq.respectTransparency false in
/-- Every independent complex smooth periodic test is transported, with no new regularity premise. -/
lemma periodic_graph_toHaar_weak (f : PeriodicH1Two) :
    HasWeakDerivativeL2 (2 : ℝ) 1 (toHaar f.val.fst) (toHaar f.val.snd) := by
  intro ψ
  have h := f.property ψ
  change inner ℂ (periodicTestL2 (SmoothPeriodicTest.iterated ψ 1)) f.val.fst =
    -inner ℂ (periodicTestL2 ψ) f.val.snd at h
  rw [inner_volume_toHaar, inner_volume_toHaar,
    toHaar_periodicTest, toHaar_periodicTest] at h
  change inner ℂ (SmoothPeriodicTest.iterated ψ 1).toL2 (toHaar f.val.fst) =
    (-1 : ℂ) ^ 1 * inner ℂ ψ.toL2 (toHaar f.val.snd)
  simp only [pow_one, neg_one_mul]
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  simpa only [mul_neg] using h

/-- The actual value and derivative projections of the periodic weak graph. -/
def periodicValue : PeriodicH1Two →L[ℂ] PeriodTwoL2 :=
  (WithLp.fstL 2 ℂ PeriodTwoL2 PeriodTwoL2).comp periodicH1Graph.subtypeL

def periodicDerivative : PeriodicH1Two →L[ℂ] PeriodTwoL2 :=
  (WithLp.sndL 2 ℂ PeriodTwoL2 PeriodTwoL2).comp periodicH1Graph.subtypeL

def periodicFourierValue : PeriodicH1Two →L[ℝ] lp (fun _ : ℤ => ℂ) 2 :=
  ((normalizedFourierL2 (2 : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
    (toHaar.comp (periodicValue.restrictScalars ℝ))

def periodicFourierDerivative : PeriodicH1Two →L[ℝ] lp (fun _ : ℤ => ℂ) 2 :=
  ((normalizedFourierL2 (2 : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
    (toHaar.comp (periodicDerivative.restrictScalars ℝ))

lemma lp2_hasSum (u : lp (fun _ : ℤ => ℂ) 2) :
    HasSum (fun n : ℤ => ‖u n‖ ^ 2) (‖u‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) u

set_option backward.isDefEq.respectTransparency false in
lemma periodicFourier_derivative (f : PeriodicH1Two) (n : ℤ) :
    periodicFourierDerivative f n =
      fourierMultiplier 2 n * periodicFourierValue f n := by
  change normalizedFourierL2 (2 : ℝ) (toHaar f.val.snd) n =
    fourierMultiplier 2 n * normalizedFourierL2 (2 : ℝ) (toHaar f.val.fst) n
  rw [normalizedFourierL2_apply, normalizedFourierL2_apply]
  simpa only [pow_one] using weakDerivative_fourierCoeff (periodic_graph_toHaar_weak f) n

lemma multiplier_two_norm_sq (n : ℤ) :
    ‖fourierMultiplier 2 n‖ ^ 2 = Real.pi ^ 2 * (n : ℝ) ^ 2 := by
  have he : fourierMultiplier 2 n = (Real.pi : ℂ) * Complex.I * (n : ℂ) := by
    unfold NlsGge.Atomic.LIB002.fourierMultiplier
    norm_num only [Complex.ofReal_ofNat]
    ring
  rw [he, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I,
    Complex.norm_intCast, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one,
    mul_pow, sq_abs]

lemma modeWeight_one (n : ℤ) : sobolevModeWeight 1 n = 1 + (n : ℝ) ^ 2 := by
  change (Real.sqrt (1 + (n : ℝ) ^ 2)) ^ (2 * (1 : ℝ)) = _
  rw [mul_one, Real.rpow_two]
  exact Real.sq_sqrt (by positivity)

lemma periodicFourier_term_le (f : PeriodicH1Two) (n : ℤ) :
    sobolevModeWeight 1 n * ‖periodicFourierValue f n‖ ^ 2 ≤
      ‖periodicFourierValue f n‖ ^ 2 + ‖periodicFourierDerivative f n‖ ^ 2 := by
  rw [modeWeight_one, periodicFourier_derivative, norm_mul, mul_pow,
    multiplier_two_norm_sq]
  have hp : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hnon : 0 ≤ (n : ℝ) ^ 2 * ‖periodicFourierValue f n‖ ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h := le_mul_of_one_le_left hnon hp
  nlinarith only [h]

lemma periodicFourier_summable (f : PeriodicH1Two) :
    Summable (fun n : ℤ => sobolevModeWeight 1 n * ‖periodicFourierValue f n‖ ^ 2) :=
  Summable.of_nonneg_of_le
    (fun n => mul_nonneg (sobolevModeWeight_pos 1 n).le (sq_nonneg _))
    (periodicFourier_term_le f)
    ((lp2_hasSum (periodicFourierValue f)).summable.add
      (lp2_hasSum (periodicFourierDerivative f)).summable)

lemma periodicFourier_mem (f : PeriodicH1Two) :
    (fun n => periodicFourierValue f n) ∈ seqSobolev38 1 := by
  apply (mem_seqSobolev38_iff 1 _).2
  exact periodicFourier_summable f

/-- Weighted membership is proved from the weak derivative, before making the carrier. -/
def periodicFourierH1Value (f : PeriodicH1Two) : SobolevCarrier38 1 :=
  carrierMk38 1 (fun n => periodicFourierValue f n) (periodicFourier_mem f)

@[simp] lemma periodicFourierH1Value_coeff (f : PeriodicH1Two) (n : ℤ) :
    carrierCoe38 1 (periodicFourierH1Value f) n = periodicFourierValue f n := rfl

set_option backward.isDefEq.respectTransparency false in
lemma periodicFourierH1Value_norm_sq_le (f : PeriodicH1Two) :
    ‖periodicFourierH1Value f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have hs := carrier_hasSum_norm_sq38 1 (periodicFourierH1Value f)
  have ht := (lp2_hasSum (periodicFourierValue f)).add
    (lp2_hasSum (periodicFourierDerivative f))
  have hsum : ‖periodicFourierH1Value f‖ ^ 2 ≤
      ‖periodicFourierValue f‖ ^ 2 + ‖periodicFourierDerivative f‖ ^ 2 :=
    hasSum_le (periodicFourier_term_le f) hs ht
  have hv : ‖periodicFourierValue f‖ ≤ ‖f.val.fst‖ := by
    change ‖normalizedFourierL2 (2 : ℝ) (toHaar f.val.fst)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact toHaar_norm_le _
  have hd : ‖periodicFourierDerivative f‖ ≤ ‖f.val.snd‖ := by
    change ‖normalizedFourierL2 (2 : ℝ) (toHaar f.val.snd)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact toHaar_norm_le _
  rw [periodicH1Two_norm_sq]
  exact hsum.trans (add_le_add (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2 hv)
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.2 hd))

lemma periodicFourierH1Value_norm_le (f : PeriodicH1Two) :
    ‖periodicFourierH1Value f‖ ≤ ‖f‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (periodicFourierH1Value_norm_sq_le f)

/-- The bounded real-linear Fourier map into the genuine weighted Hilbert carrier. -/
def periodicFourierH1 : PeriodicH1Two →L[ℝ] SobolevCarrier38 1 :=
  LinearMap.mkContinuous
    { toFun := periodicFourierH1Value
      map_add' := by
        intro f g
        apply carrierExt38
        funext n
        change periodicFourierValue (f + g) n = periodicFourierValue f n + periodicFourierValue g n
        rw [map_add]
        rfl
      map_smul' := by
        intro c f
        apply carrierExt38
        funext n
        change periodicFourierValue (c • f) n = c • periodicFourierValue f n
        rw [map_smul]
        rfl }
    1 (fun f => by
      change ‖periodicFourierH1Value f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using periodicFourierH1Value_norm_le f)

/-- The actual unweighted sequence of a coherent h0 vector. -/
def h0ToLpValue (x : SobolevCarrier38 0) : lp (fun _ : ℤ => ℂ) 2 :=
  seqToLp38 (carrierCoe38 0 x) (carrierCoe38_mem 0 x)

@[simp] lemma h0ToLpValue_apply (x : SobolevCarrier38 0) (n : ℤ) :
    h0ToLpValue x n = carrierCoe38 0 x n := rfl

lemma h0ToLpValue_norm (x : SobolevCarrier38 0) : ‖h0ToLpValue x‖ = ‖x‖ := by
  have hw (n : ℤ) : sobolevModeWeight 0 n = 1 := by
    change (japaneseBracket n) ^ (2 * (0 : ℝ)) = 1
    rw [mul_zero, Real.rpow_zero]
  have hz : HasSum (fun n : ℤ => ‖carrierCoe38 0 x n‖ ^ 2) (‖x‖ ^ 2) := by
    simpa only [hw, one_mul] using
      carrier_hasSum_norm_sq38 0 x
  have h : ‖h0ToLpValue x‖ ^ 2 = ‖x‖ ^ 2 :=
    (lp2_hasSum (h0ToLpValue x)).unique hz
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The actual bounded coefficient identity h0→ℓ2, with no physical-space identification. -/
def h0ToLp : SobolevCarrier38 0 →L[ℝ] lp (fun _ : ℤ => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := h0ToLpValue
      map_add' := by intro x y; apply lp.ext; rfl
      map_smul' := by intro c x; apply lp.ext; rfl }
    1 (fun x => by
      change ‖h0ToLpValue x‖ ≤ 1 * ‖x‖
      simp only [one_mul, h0ToLpValue_norm, le_refl])

@[simp] lemma h0ToLp_apply (x : SobolevCarrier38 0) (n : ℤ) :
    h0ToLp x n = carrierCoe38 0 x n := rfl

/-- Reconstruction goes through the actual normalized Haar Fourier inverse and actual measure change. -/
def h0ToVolume : SobolevCarrier38 0 →L[ℝ] PeriodTwoL2 :=
  toVolume.comp
    (((normalizedFourierL2 (2 : ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
      h0ToLp)

lemma h0_inclusion_fourier (f : PeriodicH1Two) :
    h0ToLp (NlsGge.Atomic.LIB008.sobolevSequenceInclusion 1 0 (by norm_num)
      (periodicFourierH1 f)) = periodicFourierValue f := by
  apply lp.ext
  funext n
  change carrierCoe38 0 (NlsGge.Atomic.LIB008.sobolevSequenceInclusion 1 0 (by norm_num)
    (periodicFourierH1 f)) n = periodicFourierValue f n
  rw [NlsGge.Atomic.LIB008.sobolevSequenceInclusion_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma periodic_reconstruction (f : PeriodicH1Two) :
    h0ToVolume (NlsGge.Atomic.LIB008.sobolevSequenceInclusion 1 0 (by norm_num)
      (periodicFourierH1 f)) = periodicValue f := by
  change toVolume ((normalizedFourierL2 (2 : ℝ)).symm
    (h0ToLp (NlsGge.Atomic.LIB008.sobolevSequenceInclusion 1 0 _
      (periodicFourierH1 f)))) = periodicValue f
  rw [h0_inclusion_fourier]
  change toVolume ((normalizedFourierL2 (2 : ℝ)).symm
    (normalizedFourierL2 (2 : ℝ) (toHaar (periodicValue f)))) = periodicValue f
  rw [LinearIsometryEquiv.symm_apply_apply, toVolume_toHaar]

/-- Compactness on the literal periodic weak graph, via the proved Fourier factorization. -/
theorem periodicValue_compact : IsCompactOperator periodicValue := by
  have h := ((NlsGge.Atomic.LIB008.sobolevSequenceInclusion_compact
    (s := 1) (t := 0) (by norm_num)).comp_clm periodicFourierH1).clm_comp h0ToVolume
  have heq : (h0ToVolume ∘ NlsGge.Atomic.LIB008.sobolevSequenceInclusion 1 0 (by norm_num) ∘
      periodicFourierH1) = periodicValue := funext periodic_reconstruction
  rwa [heq] at h

/-- The literal scalar value inclusion on the genuine normed interval H1 graph. -/
def intervalScalarInclusion : IntervalH1 →L[ℂ] SourceIntervalL2 :=
  (WithLp.fstL 2 ℂ SourceIntervalL2 SourceIntervalL2).comp intervalH1Graph.subtypeL

@[simp] lemma intervalScalarInclusion_apply (f : IntervalH1) :
    intervalScalarInclusion f = f.val.fst := rfl

lemma intervalScalar_factorization (f : IntervalH1) :
    restrictL2 (periodicValue (intervalH1Reflect f)) = intervalScalarInclusion f :=
  intervalH1Reflect_restrict_value f

/-- No boundary condition occurs: every interval weak-H1 vector is reflected and restricted. -/
theorem intervalScalarInclusion_compact : IsCompactOperator intervalScalarInclusion := by
  have h := (periodicValue_compact.comp_clm intervalH1Reflect).clm_comp restrictL2
  have heq : (restrictL2 ∘ periodicValue ∘ intervalH1Reflect) = intervalScalarInclusion :=
    funext intervalScalar_factorization
  rwa [heq] at h

abbrev IntervalPairH1 := PiLp 2 (fun _ : Bool => IntervalH1)

/-- Actual bounded insertion into one of the source Bool components (true is upper). -/
def pairInsert (b : Bool) : SourceIntervalL2 →L[ℂ] SourcePairL2 :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Bool => SourceIntervalL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Bool => SourceIntervalL2) b)

/-- The actual pair inclusion, assembled from the two scalar value maps. -/
def intervalH1ToL2 : IntervalPairH1 →L[ℂ] SourcePairL2 :=
  (pairInsert true).comp (intervalScalarInclusion.comp (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Bool => IntervalH1) true)) +
  (pairInsert false).comp (intervalScalarInclusion.comp (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Bool => IntervalH1) false))

@[simp] lemma intervalH1ToL2_apply (f : IntervalPairH1) (b : Bool) :
    intervalH1ToL2 f b = (f b).val.fst := by
  cases b <;> simp [intervalH1ToL2, pairInsert]

/-- H1([0,1];C²)→L2([0,1];C²) is compact, without any boundary condition. -/
theorem interval_h1_l2_compact : IsCompactOperator intervalH1ToL2 := by
  have ht := (intervalScalarInclusion_compact.comp_clm
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Bool => IntervalH1) true)).clm_comp (pairInsert true)
  have hf := (intervalScalarInclusion_compact.comp_clm
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Bool => IntervalH1) false)).clm_comp (pairInsert false)
  exact ht.add hf

/-- Every literal source H1 pair occurs in this domain, component by component. -/
def intervalPairOfLiteral (f : NlsGge.Atomic.Interval.H1Pair) : IntervalPairH1 :=
  WithLp.toLp 2 (fun b => intervalH1OfLiteral (f b))

@[simp] lemma intervalPairOfLiteral_value (f : NlsGge.Atomic.Interval.H1Pair) :
    intervalH1ToL2 (intervalPairOfLiteral f) = NlsGge.Atomic.Interval.h1PairValue f := by
  apply PiLp.ext
  intro b
  rw [intervalH1ToL2_apply]
  rfl

/-- The carrier is exactly all literal weak-H1 pairs, not a boundary subspace. -/
def intervalPairLiteralEquiv : NlsGge.Atomic.Interval.H1Pair ≃ IntervalPairH1 where
  toFun := intervalPairOfLiteral
  invFun f b := intervalH1ToLiteral (f b)
  left_inv f := by funext b; exact intervalH1Equiv.left_inv (f b)
  right_inv f := by apply PiLp.ext; intro b; exact intervalH1Equiv.right_inv (f b)

lemma intervalScalarInclusion_norm_le (f : IntervalH1) :
    ‖intervalScalarInclusion f‖ ≤ ‖f‖ :=
  WithLp.norm_fst_le SourceIntervalL2 f.val

lemma intervalH1ToL2_norm_le (f : IntervalPairH1) : ‖intervalH1ToL2 f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro b _
  rw [intervalH1ToL2_apply]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (intervalScalarInclusion_norm_le (f b))

lemma intervalH1ToL2_opNorm_le : ‖intervalH1ToL2‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (fun f => by simpa only [one_mul] using intervalH1ToL2_norm_le f)

lemma intervalPairOfLiteral_energy (f : NlsGge.Atomic.Interval.H1Pair) :
    ‖intervalPairOfLiteral f‖ ^ 2 =
      ∑ b : Bool, (‖(f b).value‖ ^ 2 + ‖(f b).derivative‖ ^ 2) := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro b _
  exact intervalH1OfLiteral_norm_sq (f b)

end NlsGge.Atomic.LIB035
