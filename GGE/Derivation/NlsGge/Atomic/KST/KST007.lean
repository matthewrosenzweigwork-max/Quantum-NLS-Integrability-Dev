import NlsGge.Atomic.KST.KST006
import NlsGge.Analysis.ComplexHilbertSchmidtUnitaryTransport

/-!
# Positive Fourier majorants for the full KST Q operator

Kappeler--Serier--Topalov (2009), equations (16)--(21), pp.2080--2081.
The potential is an arbitrary physical period-one L2 pair; the operators act
on the full normalized doubled L2 space. Convolution construction is adapted
locally from the checked KST006 proof. All integer labels and the whole closed
spectral strip are retained. Later Lemma2.2 decay constants are separate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory NlsGge.Atomic.KST002 NlsGge.Atomic.KST003
  NlsGge.Atomic.KST004 NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.NLS38
open scoped ENNReal InnerProduct InnerProductSpace

namespace NlsGge.Atomic.KST007

/-- Actual Fourier coordinates on the full period-two source scalar space. -/
def spectralCoeff (f : SpectralScalarL2) (k : ℤ) : ℂ :=
  (fourierBasis (T := (2 : ℝ))).repr f k

/-- Actual lifted coefficients of an arbitrary physical L2 potential. -/
def potentialCoeff (φ : PhysicalPairLp) (b : Bool) (k : ℤ) : ℂ :=
  fourierCoeff (naturalPhysicalCoverL2 (φ b)) k

/-- The literal maximum of the four source Fourier magnitudes. -/
def majorantCoeff (φ : PhysicalPairLp) (k : ℤ) : ℝ :=
  max (max ‖potentialCoeff φ true k‖ ‖potentialCoeff φ true (-k)‖)
      (max ‖potentialCoeff φ false k‖ ‖potentialCoeff φ false (-k)‖)

theorem majorant_even (φ : PhysicalPairLp) : Function.Even (majorantCoeff φ) := by
  intro k
  simp only [majorantCoeff, neg_neg]
  rw [max_comm ‖potentialCoeff φ true (-k)‖, max_comm ‖potentialCoeff φ false (-k)‖]

theorem majorant_nonneg (φ : PhysicalPairLp) (k : ℤ) : 0 ≤ majorantCoeff φ k :=
  (norm_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem potentialCoeff_norm_le_majorant (φ : PhysicalPairLp) (b : Bool) (k : ℤ) :
    ‖potentialCoeff φ b k‖ ≤ majorantCoeff φ k := by
  cases b
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_left _ _).trans (le_max_left _ _)

theorem majorant_odd_eq_zero (φ : PhysicalPairLp) (k : ℤ) (hk : k % 2 ≠ 0) :
    majorantCoeff φ k = 0 := by
  have hk' : (-k) % 2 ≠ 0 := by omega
  simp [majorantCoeff, potentialCoeff, naturalPhysicalCoverL2_fourier_odd _ k hk,
    naturalPhysicalCoverL2_fourier_odd _ (-k) hk']

private def potentialLp (φ : PhysicalPairLp) (b : Bool) : lp (fun _ : ℤ => ℂ) 2 :=
  (fourierBasis (T := (2 : ℝ))).repr (naturalPhysicalCoverL2 (φ b))

private lemma potentialLp_apply (φ : PhysicalPairLp) (b : Bool) (k : ℤ) :
    potentialLp φ b k = potentialCoeff φ b k := fourierBasis_repr _ _

private lemma potentialLp_norm (φ : PhysicalPairLp) (b : Bool) :
    ‖potentialLp φ b‖ = ‖φ b‖ := by
  simp [potentialLp, naturalPhysicalCoverL2.norm_map]

private lemma lp_sq {ι : Type*} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    (x : lp (fun _ : ι => 𝕜) 2) : ‖x‖ ^ 2 = ∑' k, ‖x k‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x)

private lemma potential_sq_summable (φ : PhysicalPairLp) (b : Bool) :
    Summable (fun k : ℤ => ‖potentialCoeff φ b k‖ ^ 2) := by
  simpa only [potentialLp_apply, ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp (potentialLp φ b)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

private lemma max_sq_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max a b ^ 2 ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

private def fourEnergy (φ : PhysicalPairLp) (k : ℤ) : ℝ :=
  (‖potentialCoeff φ true k‖ ^ 2 + ‖potentialCoeff φ true (-k)‖ ^ 2) +
    (‖potentialCoeff φ false k‖ ^ 2 + ‖potentialCoeff φ false (-k)‖ ^ 2)

private lemma fourEnergy_summable (φ : PhysicalPairLp) : Summable (fourEnergy φ) :=
  ((potential_sq_summable φ true).add
    ((potential_sq_summable φ true).comp_injective neg_injective)).add
      ((potential_sq_summable φ false).add
        ((potential_sq_summable φ false).comp_injective neg_injective))

private lemma majorant_sq_le_four (φ : PhysicalPairLp) (k : ℤ) :
    majorantCoeff φ k ^ 2 ≤ fourEnergy φ k := by
  have hu := max_sq_le ‖potentialCoeff φ true k‖ ‖potentialCoeff φ true (-k)‖
    (norm_nonneg _) (norm_nonneg _)
  have hl := max_sq_le ‖potentialCoeff φ false k‖ ‖potentialCoeff φ false (-k)‖
    (norm_nonneg _) (norm_nonneg _)
  have h := max_sq_le
    (max ‖potentialCoeff φ true k‖ ‖potentialCoeff φ true (-k)‖)
    (max ‖potentialCoeff φ false k‖ ‖potentialCoeff φ false (-k)‖)
    (le_trans (norm_nonneg _) (le_max_left _ _))
    (le_trans (norm_nonneg _) (le_max_left _ _))
  exact h.trans (add_le_add hu hl)

private lemma majorant_sq_summable (φ : PhysicalPairLp) :
    Summable (fun k : ℤ => majorantCoeff φ k ^ 2) :=
  Summable.of_nonneg_of_le (fun k => sq_nonneg _) (majorant_sq_le_four φ)
    (fourEnergy_summable φ)

/-- The actual real square-summable maximum sequence, constructed from Parseval. -/
def majorantSequence (φ : PhysicalPairLp) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨majorantCoeff φ, memℓp_gen ((majorant_sq_summable φ).congr (fun k => by
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
      abs_of_nonneg (majorant_nonneg φ k)]))⟩

theorem majorantSequence_apply (φ : PhysicalPairLp) (k : ℤ) :
    majorantSequence φ k = majorantCoeff φ k := rfl

private def complexMajorant (φ : PhysicalPairLp) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨fun k => (majorantCoeff φ k : ℂ), memℓp_gen ((majorant_sq_summable φ).congr
    (fun k => by simp [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (majorant_nonneg φ k)]))⟩

private lemma complexMajorant_norm (φ : PhysicalPairLp) :
    ‖complexMajorant φ‖ = ‖majorantSequence φ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [lp_sq, lp_sq]
  apply tsum_congr
  intro k
  simp [complexMajorant, majorantSequence, Complex.norm_real]

/-- Actual Fourier synthesis of the majorant on the doubled scalar circle. -/
def majorantFunction (φ : PhysicalPairLp) : SpectralScalarL2 :=
  (fourierBasis (T := (2 : ℝ))).repr.symm (complexMajorant φ)

theorem majorantFunction_coeff (φ : PhysicalPairLp) (k : ℤ) :
    spectralCoeff (majorantFunction φ) k = (majorantCoeff φ k : ℂ) := by
  simp [spectralCoeff, majorantFunction, complexMajorant]

theorem majorantFunction_norm (φ : PhysicalPairLp) :
    ‖majorantFunction φ‖ = ‖majorantSequence φ‖ := by
  exact ((fourierBasis (T := (2 : ℝ))).repr.symm.norm_map _).trans
    (complexMajorant_norm φ)


private lemma potential_sq_tsum (φ : PhysicalPairLp) (b : Bool) :
    (∑' k : ℤ, ‖potentialCoeff φ b k‖ ^ 2) = ‖φ b‖ ^ 2 := by
  rw [← potentialLp_norm φ b, lp_sq]
  exact tsum_congr fun k => by rw [potentialLp_apply]

private lemma fourEnergy_tsum (φ : PhysicalPairLp) :
    (∑' k : ℤ, fourEnergy φ k) = 2 * ‖φ‖ ^ 2 := by
  have ht := potential_sq_summable φ true
  have hf := potential_sq_summable φ false
  have ht' := ht.comp_injective (i := fun k : ℤ => -k) neg_injective
  have hf' := hf.comp_injective (i := fun k : ℤ => -k) neg_injective
  dsimp only [Function.comp_def] at ht' hf'
  have hneg (b : Bool) : (∑' k : ℤ, ‖potentialCoeff φ b (-k)‖ ^ 2) =
      ∑' k : ℤ, ‖potentialCoeff φ b k‖ ^ 2 :=
    (Equiv.neg ℤ).tsum_eq (fun k => ‖potentialCoeff φ b k‖ ^ 2)
  simp only [fourEnergy]
  rw [(ht.add ht').tsum_add (hf.add hf'), ht.tsum_add ht', hf.tsum_add hf',
    hneg true, hneg false,
    potential_sq_tsum, potential_sq_tsum]
  have hp := PiLp.norm_sq_eq_of_L2 (fun _ : Bool => PhysicalL2) φ
  simp only [Fintype.sum_bool] at hp
  nlinarith

/-- The source constants for the actual physical Euclidean pair norm. -/
theorem majorant_norm_bounds (φ : PhysicalPairLp) :
    (1 / 2 : ℝ) * ‖φ‖ ≤ ‖majorantSequence φ‖ ∧
      ‖majorantSequence φ‖ ≤ 2 * ‖φ‖ := by
  have hsq : ‖majorantSequence φ‖ ^ 2 = ∑' k : ℤ, majorantCoeff φ k ^ 2 := by
    rw [lp_sq]
    apply tsum_congr
    intro k
    simp [majorantSequence, Real.norm_eq_abs, abs_of_nonneg (majorant_nonneg φ k)]
  have hup : ‖majorantSequence φ‖ ^ 2 ≤ 2 * ‖φ‖ ^ 2 := by
    rw [hsq, ← fourEnergy_tsum φ]
    exact (majorant_sq_summable φ).tsum_le_tsum (majorant_sq_le_four φ)
      (fourEnergy_summable φ)
  have hc (b : Bool) : ‖φ b‖ ^ 2 ≤ ‖majorantSequence φ‖ ^ 2 := by
    rw [← potential_sq_tsum φ b, hsq]
    apply (potential_sq_summable φ b).tsum_le_tsum _ (majorant_sq_summable φ)
    intro k
    exact (sq_le_sq₀ (norm_nonneg _) (majorant_nonneg φ k)).mpr
      (potentialCoeff_norm_le_majorant φ b k)
  have hp := PiLp.norm_sq_eq_of_L2 (fun _ : Bool => PhysicalL2) φ
  simp only [Fintype.sum_bool] at hp
  constructor <;> nlinarith [hc true, hc false, norm_nonneg φ,
    norm_nonneg (majorantSequence φ)]

private abbrev CSeq := lp (fun _ : ℤ => ℂ) 2

private def weightedCoefficients (d : CSeq) (f : SpectralScalarL2) (j : ℤ) : ℂ :=
  d j * spectralCoeff f j

private lemma coeff_sq_summable (x : CSeq) : Summable (fun k : ℤ => ‖x k‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

private lemma weighted_isL1 (d : CSeq) (f : SpectralScalarL2) :
    IsL1 (weightedCoefficients d f) := by
  have hp : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]; norm_num
  simpa [IsL1, weightedCoefficients, spectralCoeff, norm_mul] using
    (lp.summable_mul hp d ((fourierBasis (T := (2 : ℝ))).repr f))

private lemma weighted_l1_bound (d : CSeq) (f : SpectralScalarL2) :
    l1 (weightedCoefficients d f) ≤ ‖d‖ * ‖f‖ := by
  have hp : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]; norm_num
  have h := lp.tsum_mul_le_mul_norm' hp d ((fourierBasis (T := (2 : ℝ))).repr f)
  simpa [l1, weightedCoefficients, spectralCoeff, norm_mul] using h

private def outputLp (a d : CSeq) (f : SpectralScalarL2) : CSeq :=
  ⟨conv (weightedCoefficients d f) a,
    memℓp_gen (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (summable_sq_conv (weighted_isL1 d f) (coeff_sq_summable a)).1)⟩

private lemma outputLp_norm_le (a d : CSeq) (f : SpectralScalarL2) :
    ‖outputLp a d f‖ ≤ (‖a‖ * ‖d‖) * ‖f‖ := by
  have hy := (summable_sq_conv (weighted_isL1 d f) (coeff_sq_summable a)).2
  have hout : ‖outputLp a d f‖ ^ 2 ≤ l1 (weightedCoefficients d f) ^ 2 * ‖a‖ ^ 2 := by
    rw [lp_sq]
    change (∑' k : ℤ, ‖conv (weightedCoefficients d f) a k‖ ^ 2) ≤ _
    rw [lp_sq]
    exact hy
  have hsq : l1 (weightedCoefficients d f) ^ 2 ≤ (‖d‖ * ‖f‖) ^ 2 :=
    (sq_le_sq₀ (tsum_nonneg fun k => norm_nonneg _) (by positivity)).mpr
      (weighted_l1_bound d f)
  have h := hout.trans (mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖a‖))
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  convert h using 1 <;> ring

private def coefficientLinear (a d : CSeq) :
    SpectralScalarL2 →ₗ[ℂ] SpectralScalarL2 where
  toFun f := (fourierBasis (T := (2 : ℝ))).repr.symm (outputLp a d f)
  map_add' f g := by
    apply (fourierBasis (T := (2 : ℝ))).repr.injective
    simp only [map_add, LinearIsometryEquiv.apply_symm_apply]
    apply lp.ext
    funext k
    have hlin : weightedCoefficients d (f + g) =
        weightedCoefficients d f + weightedCoefficients d g := by
      funext j
      simp [weightedCoefficients, spectralCoeff, map_add, mul_add]
    change conv (weightedCoefficients d (f + g)) a k =
      conv (weightedCoefficients d f) a k + conv (weightedCoefficients d g) a k
    rw [hlin]
    exact congrFun (conv_add_left_of_summable
      (fun j => summable_conv_term_l2 (weighted_isL1 d f) (coeff_sq_summable a) j)
      (fun j => summable_conv_term_l2 (weighted_isL1 d g) (coeff_sq_summable a) j)) k
  map_smul' c f := by
    apply (fourierBasis (T := (2 : ℝ))).repr.injective
    simp only [map_smul, LinearIsometryEquiv.apply_symm_apply]
    apply lp.ext
    funext k
    have hlin : weightedCoefficients d (c • f) = c • weightedCoefficients d f := by
      funext j
      simp [weightedCoefficients, spectralCoeff, map_smul]
      ring
    change conv (weightedCoefficients d (c • f)) a k = c • conv (weightedCoefficients d f) a k
    rw [hlin]
    exact congrFun (conv_smul_left c _ _) k

private def coefficientOperator (a d : CSeq) :
    SpectralScalarL2 →L[ℂ] SpectralScalarL2 :=
  (coefficientLinear a d).mkContinuous (‖a‖ * ‖d‖) (fun f => by
    change ‖(fourierBasis (T := (2 : ℝ))).repr.symm (outputLp a d f)‖ ≤ _
    rw [(fourierBasis (T := (2 : ℝ))).repr.symm.norm_map]
    exact outputLp_norm_le a d f)

private lemma coefficientOperator_norm_le (a d : CSeq) :
    ‖coefficientOperator a d‖ ≤ ‖a‖ * ‖d‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

private lemma coefficientOperator_coeff (a d : CSeq) (f : SpectralScalarL2) (l : ℤ) :
    spectralCoeff (coefficientOperator a d f) l =
      ∑' j : ℤ, a (l - j) * (d j * spectralCoeff f j) := by
  rw [coefficientOperator, LinearMap.mkContinuous_apply]
  change ((fourierBasis (T := (2 : ℝ))).repr
    ((fourierBasis (T := (2 : ℝ))).repr.symm (outputLp a d f))) l = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change conv (weightedCoefficients d f) a l = _
  unfold conv weightedCoefficients
  exact tsum_congr fun j => mul_comm _ _

private lemma coefficientOperator_coeff_summable (a d : CSeq)
    (f : SpectralScalarL2) (l : ℤ) :
    Summable (fun j : ℤ => ‖a (l - j) * (d j * spectralCoeff f j)‖) := by
  refine (summable_norm_conv_term_l2 (weighted_isL1 d f) (coeff_sq_summable a) l).congr ?_
  intro j
  simp only [weightedCoefficients, mul_comm]

/-- The exact positive reciprocal coefficient, zero on the removed resonance. -/
def reciprocalDistance (n k : ℤ) : ℝ :=
  if k = n then 0 else 1 / (Int.natAbs (n - k) : ℝ)

private lemma reciprocalDistance_eq (n k : ℤ) :
    reciprocalDistance n k = 1 / (Int.natAbs (k - n) : ℝ) := by
  by_cases h : k = n
  · simp [reciprocalDistance, h]
  · simp [reciprocalDistance, h, abs_sub_comm]

private lemma reciprocalDistance_nonneg (n k : ℤ) : 0 ≤ reciprocalDistance n k := by
  rw [reciprocalDistance_eq]; positivity

private lemma reciprocalDistance_sq_summable (n : ℤ) :
    Summable (fun k : ℤ => reciprocalDistance n k ^ 2) := by
  have hbase0 : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
  have hbase : Summable (fun k : ℤ => 1 / (k.natAbs : ℝ) ^ 2) := by
    convert hbase0 using 1 <;> simp [Nat.cast_natAbs, Int.cast_abs, abs_pow]
  have hshift := (Equiv.addRight (-n)).summable_iff.mpr hbase
  refine hshift.congr fun k => ?_
  simp [reciprocalDistance_eq, sub_eq_add_neg, div_pow]

private lemma reciprocalDistance_sq_sum_le (n : ℤ) :
    (∑' k : ℤ, reciprocalDistance n k ^ 2) ≤ 4 := by
  have he : (fun k : ℤ => reciprocalDistance n k ^ 2) =
      fun k : ℤ => 1 / (Int.natAbs (k - n) : ℝ) ^ 2 := by
    funext k
    simp [reciprocalDistance_eq, div_pow]
  rw [he]
  exact lattice_reciprocal_sq_bound n

private def flipSeq (x : CSeq) : CSeq :=
  ⟨fun k => x (-k), memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Function.comp_def] using
      (coeff_sq_summable x).comp_injective (i := fun k : ℤ => -k) neg_injective)⟩

private lemma flipSeq_norm (x : CSeq) : ‖flipSeq x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [lp_sq, lp_sq]
  exact (Equiv.neg ℤ).tsum_eq (fun k => ‖x k‖ ^ 2)

private def distanceLp (n : ℤ) : CSeq :=
  ⟨fun k => (reciprocalDistance n k : ℂ), memℓp_gen
    ((reciprocalDistance_sq_summable n).congr fun k => by
      simp [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (reciprocalDistance_nonneg n k)])⟩

private lemma distanceLp_norm_le_two (n : ℤ) : ‖distanceLp n‖ ≤ 2 := by
  have he : ‖distanceLp n‖ ^ 2 = ∑' k : ℤ, reciprocalDistance n k ^ 2 := by
    rw [lp_sq]
    apply tsum_congr
    intro k
    simp [distanceLp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (reciprocalDistance_nonneg n k)]
  have hb := reciprocalDistance_sq_sum_le n
  rw [← he] at hb
  nlinarith [norm_nonneg (distanceLp n)]

private def signedDistanceLp (n : ℤ) (upper : Bool) : CSeq :=
  if upper then distanceLp n else flipSeq (distanceLp n)

private lemma signedDistanceLp_apply (n : ℤ) (upper : Bool) (j : ℤ) :
    signedDistanceLp n upper j =
      (reciprocalDistance n (if upper then j else -j) : ℂ) := by
  cases upper <;> rfl

private lemma signedDistanceLp_norm_le_two (n : ℤ) (upper : Bool) :
    ‖signedDistanceLp n upper‖ ≤ 2 := by
  cases upper
  · simpa [signedDistanceLp, flipSeq_norm] using distanceLp_norm_le_two n
  · exact distanceLp_norm_le_two n

/-- The actual positive full-lattice scalar matrix. Upper/lower input labels
are respectively j and -j, with no parity restriction. -/
def positiveKernel (φ : PhysicalPairLp) (n : ℤ) (upper : Bool) (l j : ℤ) : ℝ :=
  majorantCoeff φ (l - j) * reciprocalDistance n (if upper then j else -j)

/-- The bounded positive convolution-resolvent block, genuinely constructed in L2. -/
def positiveBlock (φ : PhysicalPairLp) (n : ℤ) (upper : Bool) :
    SpectralScalarL2 →L[ℂ] SpectralScalarL2 :=
  coefficientOperator (complexMajorant φ) (signedDistanceLp n upper)

private lemma positiveKernel_cast (φ : PhysicalPairLp) (n : ℤ)
    (upper : Bool) (l j : ℤ) :
    (positiveKernel φ n upper l j : ℂ) =
      complexMajorant φ (l - j) * signedDistanceLp n upper j := by
  simp only [positiveKernel, Complex.ofReal_mul, signedDistanceLp_apply]
  rfl

/-- Absolute convergence and the literal coefficient formula of X_n^±. -/
theorem positiveBlock_coeff (φ : PhysicalPairLp) (n : ℤ) (upper : Bool)
    (f : SpectralScalarL2) (l : ℤ) :
    Summable (fun j : ℤ => ‖(positiveKernel φ n upper l j : ℂ) * spectralCoeff f j‖) ∧
    spectralCoeff (positiveBlock φ n upper f) l =
      ∑' j : ℤ, (positiveKernel φ n upper l j : ℂ) * spectralCoeff f j := by
  constructor
  · simpa only [positiveKernel_cast, mul_assoc] using
      coefficientOperator_coeff_summable (complexMajorant φ) (signedDistanceLp n upper) f l
  · simpa only [positiveBlock, positiveKernel_cast, mul_assoc] using
      coefficientOperator_coeff (complexMajorant φ) (signedDistanceLp n upper) f l

/-- The source bound, uniform for every signed integer n. -/
theorem norm_positiveBlock_le (φ : PhysicalPairLp) (n : ℤ) (upper : Bool) :
    ‖positiveBlock φ n upper‖ ≤ 2 * ‖majorantSequence φ‖ := by
  calc
    ‖positiveBlock φ n upper‖ ≤ ‖complexMajorant φ‖ * ‖signedDistanceLp n upper‖ :=
      coefficientOperator_norm_le _ _
    _ ≤ ‖complexMajorant φ‖ * 2 :=
      mul_le_mul_of_nonneg_left (signedDistanceLp_norm_le_two n upper) (norm_nonneg _)
    _ = 2 * ‖majorantSequence φ‖ := by rw [complexMajorant_norm]; ring

private lemma spectralCoeff_basis (j k : ℤ) :
    spectralCoeff (spectralBasis j) k = if k = j then 1 else 0 := by
  have hv : (fourierBasis (T := (2 : ℝ))) j = spectralBasis j := by
    simp [spectralBasis]
  have h := congrArg (fun x : CSeq => x k)
    ((fourierBasis (T := (2 : ℝ))).repr_self j)
  simpa only [spectralCoeff, hv, lp.single_apply, Pi.single_apply, eq_comm] using h

/-- The actual nonnegative positive-block entries. -/
theorem positiveBlock_matrix (φ : PhysicalPairLp) (n : ℤ) (upper : Bool) (l j : ℤ) :
    spectralCoeff (positiveBlock φ n upper (spectralBasis j)) l =
      (positiveKernel φ n upper l j : ℂ) := by
  rw [(positiveBlock_coeff φ n upper (spectralBasis j) l).2]
  simp only [spectralCoeff_basis, mul_ite, mul_one, mul_zero]
  simp

private lemma positiveKernel_nonneg (φ : PhysicalPairLp) (n : ℤ)
    (upper : Bool) (l j : ℤ) : 0 ≤ positiveKernel φ n upper l j :=
  mul_nonneg (majorant_nonneg φ _) (reciprocalDistance_nonneg n _)

/-- The literal positive scalar product kernel, before any real norm is taken. -/
def positiveProductKernel (φ : PhysicalPairLp) (n : ℤ) (upper : Bool)
    (l j : ℤ) : ℝ :=
  ∑' k : ℤ, positiveKernel φ n upper l k * positiveKernel φ n (!upper) k j

/-- The positive matrix product is a genuinely summable real series. -/
theorem positiveProductKernel_summable (φ : PhysicalPairLp) (n : ℤ)
    (upper : Bool) (l j : ℤ) :
    Summable (fun k : ℤ =>
      positiveKernel φ n upper l k * positiveKernel φ n (!upper) k j) := by
  have h := (positiveBlock_coeff φ n upper
    (positiveBlock φ n (!upper) (spectralBasis j)) l).1
  simpa only [positiveBlock_matrix, ← Complex.ofReal_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (positiveKernel_nonneg φ n upper l _)
        (positiveKernel_nonneg φ n (!upper) _ j))] using h

/-- The actual bounded scalar product has the positive product-kernel entries. -/
theorem positiveProduct_matrix (φ : PhysicalPairLp) (n : ℤ)
    (upper : Bool) (l j : ℤ) :
    spectralCoeff
      (((positiveBlock φ n upper).comp (positiveBlock φ n (!upper)))
        (spectralBasis j)) l = (positiveProductKernel φ n upper l j : ℂ) := by
  rw [ContinuousLinearMap.comp_apply,
    (positiveBlock_coeff φ n upper
      (positiveBlock φ n (!upper) (spectralBasis j)) l).2]
  simp only [positiveBlock_matrix, ← Complex.ofReal_mul]
  exact ((Complex.ofRealCLM).map_tsum
    (positiveProductKernel_summable φ n upper l j)).symm

private def shiftedMajorant (φ : PhysicalPairLp) (j : ℤ) : CSeq :=
  ⟨fun k => complexMajorant φ (k + j), memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Function.comp_def] using
      (coeff_sq_summable (complexMajorant φ)).comp_injective
        (i := fun k : ℤ => k + j) (by intro a b h; exact add_right_cancel h))⟩

private lemma majorantCoeff_le_norm (φ : PhysicalPairLp) (k : ℤ) :
    majorantCoeff φ k ≤ ‖majorantSequence φ‖ := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (majorantSequence φ) k
  simpa only [majorantSequence_apply, Real.norm_eq_abs,
    abs_of_nonneg (majorant_nonneg φ k)] using h

private lemma weightedMajorant_summable (φ : PhysicalPairLp) (n j : ℤ) :
    Summable (fun k : ℤ => majorantCoeff φ (k + j) * reciprocalDistance n k) := by
  have hp : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]; norm_num
  have h := lp.summable_mul hp (shiftedMajorant φ j) (distanceLp n)
  refine h.congr fun k => ?_
  change ‖(majorantCoeff φ (k + j) : ℂ)‖ * ‖(reciprocalDistance n k : ℂ)‖ = _
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (majorant_nonneg φ (k + j)),
    abs_of_nonneg (reciprocalDistance_nonneg n k)]

private lemma sourceInner_summable (φ : PhysicalPairLp) (n j : ℤ)
    (outputIndex : ℤ → ℤ) :
    Summable (fun k : ℤ => majorantCoeff φ (outputIndex k) *
      majorantCoeff φ (k + j) * reciprocalDistance n k) := by
  have h := weightedMajorant_summable φ n j
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg
      (mul_nonneg (majorant_nonneg φ _) (majorant_nonneg φ _))
      (reciprocalDistance_nonneg n k)) (fun k => ?_)
    (h.mul_left ‖majorantSequence φ‖)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right (majorantCoeff_le_norm φ (outputIndex k))
    (mul_nonneg (majorant_nonneg φ _) (reciprocalDistance_nonneg n k))

private lemma sourceInner_plus_summable (φ : PhysicalPairLp) (n l j : ℤ) :
    Summable (fun k : ℤ => majorantCoeff φ (l + k) *
      majorantCoeff φ (k + j) * reciprocalDistance n k) :=
  sourceInner_summable φ n j (fun k => l + k)

private lemma sourceInner_minus_summable (φ : PhysicalPairLp) (n l j : ℤ) :
    Summable (fun k : ℤ => majorantCoeff φ (l - k) *
      majorantCoeff φ (k + j) * reciprocalDistance n k) :=
  sourceInner_summable φ n j (fun k => l - k)

/-- The exact unreflected lower-product kernel used by the next source estimate. -/
theorem positiveProductKernel_minus_plus (φ : PhysicalPairLp) (n l j : ℤ) :
    positiveProductKernel φ n false l j = reciprocalDistance n j *
      ∑' k : ℤ, majorantCoeff φ (l + k) * majorantCoeff φ (k + j) *
        reciprocalDistance n k := by
  unfold positiveProductKernel
  rw [← (Equiv.neg ℤ).tsum_eq]
  simp only [positiveKernel, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
    Equiv.neg_apply, neg_neg, sub_neg_eq_add]
  rw [← (sourceInner_plus_summable φ n l j).tsum_mul_left (reciprocalDistance n j)]
  apply tsum_congr
  intro k
  have he : majorantCoeff φ (-k - j) = majorantCoeff φ (k + j) := by
    rw [show -k - j = -(k + j) by ring, majorant_even]
  rw [he]
  ring

/-- The exact reflected upper-product kernel retains raw input `-j`. -/
theorem positiveProductKernel_plus_minus_reflected
    (φ : PhysicalPairLp) (n l j : ℤ) :
    positiveProductKernel φ n true l (-j) = reciprocalDistance n j *
      ∑' k : ℤ, majorantCoeff φ (l - k) * majorantCoeff φ (k + j) *
        reciprocalDistance n k := by
  unfold positiveProductKernel
  simp only [positiveKernel, ↓reduceIte, Bool.not_true,
    Bool.false_eq_true, neg_neg, sub_neg_eq_add]
  rw [← (sourceInner_minus_summable φ n l j).tsum_mul_left (reciprocalDistance n j)]
  apply tsum_congr
  intro k
  ring

private def scalarBasis : HilbertBasis ℤ ℂ SpectralScalarL2 :=
  fourierBasis (T := (2 : ℝ))

private lemma scalarBasis_apply (k : ℤ) : scalarBasis k = spectralBasis k := by
  exact congrFun (coe_fourierBasis (T := (2 : ℝ))) k

private lemma scalarBasis_repr (f : SpectralScalarL2) (k : ℤ) :
    scalarBasis.repr f k = spectralCoeff f k := rfl

/-- The actual inclusion of one full scalar component into the doubled pair. -/
def scalarIn (b : Bool) : SpectralScalarL2 →L[ℂ] KSTPairL2 :=
  ({ toLinearMap :=
      ((WithLp.linearEquiv 2 ℂ (Bool → SpectralScalarL2)).symm.toLinearMap).comp
        (LinearMap.single ℂ (fun _ : Bool => SpectralScalarL2) b)
     norm_map' := fun f => PiLp.norm_single 2 (fun _ : Bool => SpectralScalarL2) b f } :
      SpectralScalarL2 →ₗᵢ[ℂ] KSTPairL2).toContinuousLinearMap

/-- The actual component projection on the doubled pair. -/
def scalarOut (b : Bool) : KSTPairL2 →L[ℂ] SpectralScalarL2 :=
  PiLp.proj 2 (fun _ : Bool => SpectralScalarL2) b

private lemma scalarIn_apply (b : Bool) (f : SpectralScalarL2) :
    scalarIn b f = PiLp.single 2 b f := rfl

private lemma scalarOut_apply (b : Bool) (f : KSTPairL2) :
    scalarOut b f = f b := rfl

/-- The true off-diagonal block extracted from the accepted full Q operator. -/
def qBlock (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) :
    SpectralScalarL2 →L[ℂ] SpectralScalarL2 :=
  (scalarOut upper).comp
    ((KST006.qOperator φ n z hz).comp (scalarIn (!upper)))

/-- Both scalar coefficient laws preserve the lower block's reflected index. -/
theorem qBlock_coeff (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool)
    (f : SpectralScalarL2) (l : ℤ) :
    spectralCoeff (qBlock φ n z hz upper f) l =
      ∑' j : ℤ, potentialCoeff φ upper (l - j) *
        (complementaryResolventCoeff n z (if upper then j else -j) *
          spectralCoeff f j) := by
  cases upper
  · simpa only [qBlock, ContinuousLinearMap.comp_apply, scalarOut_apply,
      scalarIn_apply, Bool.not_false, PiLp.single_eq_same, spectralCoeff,
      potentialCoeff, Bool.false_eq_true, ↓reduceIte] using
      KST006.qOperator_lower_coeff φ n z hz (scalarIn true f) l
  · simpa only [qBlock, ContinuousLinearMap.comp_apply, scalarOut_apply,
      scalarIn_apply, Bool.not_true, PiLp.single_eq_same, spectralCoeff,
      potentialCoeff, ↓reduceIte] using
      KST006.qOperator_upper_coeff φ n z hz (scalarIn false f) l

private lemma qBlock_matrix (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) (l j : ℤ) :
    spectralCoeff (qBlock φ n z hz upper (spectralBasis j)) l =
      potentialCoeff φ upper (l - j) *
        complementaryResolventCoeff n z (if upper then j else -j) := by
  rw [qBlock_coeff]
  simp only [spectralCoeff_basis, mul_ite, mul_one, mul_zero]
  simp

/-- Actual scalar matrix entries are bounded by the source positive matrices. -/
theorem qBlock_matrix_majorant (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) (l j : ℤ) :
    ‖spectralCoeff (qBlock φ n z hz upper (spectralBasis j)) l‖ ≤
      positiveKernel φ n upper l j := by
  rw [qBlock_matrix, norm_mul]
  exact mul_le_mul (potentialCoeff_norm_le_majorant φ upper (l - j))
    (by simpa only [reciprocalDistance_eq] using
      complementaryResolventCoeff_bound n (if upper then j else -j) z hz)
    (norm_nonneg _) (majorant_nonneg φ _)

private lemma qBlock_term_bound (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) (l k : ℤ) (c : ℂ) :
    ‖potentialCoeff φ upper (l - k) *
      (complementaryResolventCoeff n z (if upper then k else -k) * c)‖ ≤
      positiveKernel φ n upper l k * ‖c‖ := by
  simp only [norm_mul]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg c)
  exact mul_le_mul (potentialCoeff_norm_le_majorant φ upper (l - k))
    (by simpa only [reciprocalDistance_eq] using
      complementaryResolventCoeff_bound n (if upper then k else -k) z hz)
    (norm_nonneg _) (majorant_nonneg φ _)

/-- The squared complex blocks are dominated by their actual positive products. -/
theorem qBlock_product_matrix_majorant (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) (l j : ℤ) :
    ‖spectralCoeff
      (((qBlock φ n z hz upper).comp (qBlock φ n z hz (!upper)))
        (spectralBasis j)) l‖ ≤ positiveProductKernel φ n upper l j := by
  have hb (k : ℤ) :
      ‖potentialCoeff φ upper (l - k) *
        (complementaryResolventCoeff n z (if upper then k else -k) *
          spectralCoeff (qBlock φ n z hz (!upper) (spectralBasis j)) k)‖ ≤
        positiveKernel φ n upper l k * positiveKernel φ n (!upper) k j :=
    (qBlock_term_bound φ n z hz upper l k _).trans
      (mul_le_mul_of_nonneg_left (qBlock_matrix_majorant φ n z hz (!upper) k j)
        (positiveKernel_nonneg φ n upper l k))
  have hsum : Summable (fun k : ℤ =>
      ‖potentialCoeff φ upper (l - k) *
        (complementaryResolventCoeff n z (if upper then k else -k) *
          spectralCoeff (qBlock φ n z hz (!upper) (spectralBasis j)) k)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
      (positiveProductKernel_summable φ n upper l j)
  rw [ContinuousLinearMap.comp_apply, qBlock_coeff]
  exact (norm_tsum_le_tsum_norm hsum).trans
    (hsum.tsum_le_tsum hb (positiveProductKernel_summable φ n upper l j))

private lemma majorant_sq_tsum (φ : PhysicalPairLp) :
    (∑' k : ℤ, majorantCoeff φ k ^ 2) = ‖majorantSequence φ‖ ^ 2 := by
  rw [lp_sq]
  apply tsum_congr
  intro k
  simp only [majorantSequence_apply, Real.norm_eq_abs, sq_abs]

private lemma positiveBlock_column_energy (φ : PhysicalPairLp) (n : ℤ)
    (upper : Bool) (j : ℤ) :
    ‖positiveBlock φ n upper (spectralBasis j)‖ ^ 2 =
      ‖majorantSequence φ‖ ^ 2 *
        reciprocalDistance n (if upper then j else -j) ^ 2 := by
  rw [← scalarBasis.repr.norm_map
    (positiveBlock φ n upper (spectralBasis j)), lp_sq]
  change (∑' l : ℤ, ‖spectralCoeff
    (positiveBlock φ n upper (spectralBasis j)) l‖ ^ 2) = _
  simp only [positiveBlock_matrix, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    positiveKernel, mul_pow]
  rw [tsum_mul_right]
  congr 1
  have h := (Equiv.addRight (-j)).tsum_eq (fun k => majorantCoeff φ k ^ 2)
  simpa only [Equiv.coe_addRight, sub_eq_add_neg, majorant_sq_tsum] using h

private lemma positiveBlock_columns_summable (φ : PhysicalPairLp) (n : ℤ)
    (upper : Bool) :
    Summable (fun j : ℤ => ‖positiveBlock φ n upper (spectralBasis j)‖ ^ 2) := by
  simp_rw [positiveBlock_column_energy]
  apply Summable.mul_left
  cases upper
  · simpa only [Bool.false_eq_true, ↓reduceIte, Function.comp_def] using
      (reciprocalDistance_sq_summable n).comp_injective
        (i := fun j : ℤ => -j) neg_injective
  · exact reciprocalDistance_sq_summable n

/-- Every positive block is genuinely complex Hilbert--Schmidt, for all labels. -/
theorem positiveBlock_isComplexHilbertSchmidt (φ : PhysicalPairLp) (n : ℤ)
    (upper : Bool) : IsComplexHilbertSchmidt (positiveBlock φ n upper) := by
  apply isComplexHilbertSchmidt_of_summable_basis scalarBasis
  simpa only [scalarBasis_apply] using
    positiveBlock_columns_summable φ n upper

private lemma scalar_comp_isComplexHilbertSchmidt
    (S T : SpectralScalarL2 →L[ℂ] SpectralScalarL2)
    (hT : IsComplexHilbertSchmidt T) : IsComplexHilbertSchmidt (S.comp T) := by
  let b := scalarBasis
  have ht := summable_basis_of_isComplexHilbertSchmidt b hT
  apply isComplexHilbertSchmidt_of_summable_basis b
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => ?_)
    (ht.mul_left (‖S‖ ^ 2))
  change ‖S (T (b j))‖ ^ 2 ≤ ‖S‖ ^ 2 * ‖T (b j)‖ ^ 2
  rw [← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (S.le_opNorm _)

private lemma positiveProductKernel_nonneg (φ : PhysicalPairLp) (n : ℤ)
    (upper : Bool) (l j : ℤ) : 0 ≤ positiveProductKernel φ n upper l j :=
  tsum_nonneg fun k => mul_nonneg (positiveKernel_nonneg φ n upper l k)
    (positiveKernel_nonneg φ n (!upper) k j)

private lemma blockProduct_energy_le (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) :
    complexHilbertSchmidtEnergy
      ((qBlock φ n z hz upper).comp (qBlock φ n z hz (!upper))) ≤
    complexHilbertSchmidtEnergy
      ((positiveBlock φ n upper).comp (positiveBlock φ n (!upper))) := by
  rw [complexHilbertSchmidtEnergy_eq_matrix _
      scalarBasis scalarBasis,
    complexHilbertSchmidtEnergy_eq_matrix _
      scalarBasis scalarBasis]
  apply ENNReal.tsum_le_tsum
  intro j
  apply ENNReal.tsum_le_tsum
  intro l
  apply ENNReal.ofReal_le_ofReal
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
  rw [← scalarBasis.repr_apply_apply, ← scalarBasis.repr_apply_apply]
  simp only [scalarBasis_repr, scalarBasis_apply]
  rw [positiveProduct_matrix, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (positiveProductKernel_nonneg φ n upper l j)]
  exact qBlock_product_matrix_majorant φ n z hz upper l j

/-- Finiteness is transferred in extended nonnegative energy before norm comparison. -/
theorem blockProduct_hs_comparison (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) :
    IsComplexHilbertSchmidt
      ((positiveBlock φ n upper).comp (positiveBlock φ n (!upper))) ∧
    IsComplexHilbertSchmidt
      ((qBlock φ n z hz upper).comp (qBlock φ n z hz (!upper))) ∧
    complexHilbertSchmidtNorm
      ((qBlock φ n z hz upper).comp (qBlock φ n z hz (!upper))) ≤
    complexHilbertSchmidtNorm
      ((positiveBlock φ n upper).comp (positiveBlock φ n (!upper))) := by
  have hp := scalar_comp_isComplexHilbertSchmidt (positiveBlock φ n upper)
    (positiveBlock φ n (!upper)) (positiveBlock_isComplexHilbertSchmidt φ n (!upper))
  have he := blockProduct_energy_le φ n z hz upper
  have hq : IsComplexHilbertSchmidt
      ((qBlock φ n z hz upper).comp (qBlock φ n z hz (!upper))) :=
    ne_of_lt (lt_of_le_of_lt he (lt_top_iff_ne_top.mpr hp))
  exact ⟨hp, hq, Real.sqrt_le_sqrt (ENNReal.toReal_mono hp he)⟩

private def flipLinear : CSeq →ₗ[ℂ] CSeq where
  toFun := flipSeq
  map_add' f g := by
    apply lp.ext
    funext k
    rfl
  map_smul' c f := by
    apply lp.ext
    funext k
    rfl

private def flipIsometry : CSeq ≃ₗᵢ[ℂ] CSeq where
  toLinearEquiv :=
    { toLinearMap := flipLinear
      invFun := flipSeq
      left_inv := fun f => by
        apply lp.ext
        funext k
        change f (- -k) = f k
        rw [neg_neg]
      right_inv := fun f => by
        apply lp.ext
        funext k
        change f (- -k) = f k
        rw [neg_neg] }
  norm_map' := flipSeq_norm

private def scalarReflection : SpectralScalarL2 ≃ₗᵢ[ℂ] SpectralScalarL2 :=
  (scalarBasis.repr.trans flipIsometry).trans
    scalarBasis.repr.symm

private lemma scalarReflection_coeff (f : SpectralScalarL2) (k : ℤ) :
    spectralCoeff (scalarReflection f) k = spectralCoeff f (-k) := by
  change (scalarBasis.repr
    (scalarBasis.repr.symm
      (flipSeq (scalarBasis.repr f)))) k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

private lemma scalarReflection_involutive (f : SpectralScalarL2) :
    scalarReflection (scalarReflection f) = f := by
  apply scalarBasis.repr.injective
  apply lp.ext
  funext k
  change spectralCoeff (scalarReflection (scalarReflection f)) k = spectralCoeff f k
  rw [scalarReflection_coeff, scalarReflection_coeff, neg_neg]

private lemma scalarReflection_symm_apply (f : SpectralScalarL2) :
    scalarReflection.symm f = scalarReflection f := by
  apply scalarReflection.injective
  rw [LinearIsometryEquiv.apply_symm_apply, scalarReflection_involutive]

private lemma scalarReflection_positive (φ : PhysicalPairLp) (n : ℤ)
    (upper : Bool) (f : SpectralScalarL2) :
    scalarReflection (positiveBlock φ n upper f) =
      positiveBlock φ n (!upper) (scalarReflection f) := by
  apply scalarBasis.repr.injective
  apply lp.ext
  funext l
  change spectralCoeff (scalarReflection (positiveBlock φ n upper f)) l =
    spectralCoeff (positiveBlock φ n (!upper) (scalarReflection f)) l
  rw [scalarReflection_coeff, (positiveBlock_coeff φ n upper f (-l)).2,
    (positiveBlock_coeff φ n (!upper) (scalarReflection f) l).2]
  simp_rw [scalarReflection_coeff]
  rw [← (Equiv.neg ℤ).tsum_eq (fun j : ℤ =>
    (positiveKernel φ n (!upper) l j : ℂ) * spectralCoeff f (-j))]
  apply tsum_congr
  intro j
  have he : majorantCoeff φ (-l - j) = majorantCoeff φ (l + j) := by
    rw [show -l - j = -(l + j) by ring, majorant_even]
  cases upper <;> simp [positiveKernel, he, sub_neg_eq_add]

private lemma positiveProduct_reflection (φ : PhysicalPairLp) (n : ℤ) :
    transportComplexOperator
      ((positiveBlock φ n false).comp (positiveBlock φ n true))
      scalarReflection scalarReflection =
      (positiveBlock φ n true).comp (positiveBlock φ n false) := by
  apply ContinuousLinearMap.ext
  intro f
  change scalarReflection
    (positiveBlock φ n false (positiveBlock φ n true (scalarReflection.symm f))) = _
  rw [scalarReflection_symm_apply, scalarReflection_positive,
    scalarReflection_positive, scalarReflection_involutive]
  rfl

/-- The two source positive products are unitarily conjugate by Fourier reflection. -/
theorem positiveProduct_hsNorm_eq (φ : PhysicalPairLp) (n : ℤ) :
    complexHilbertSchmidtNorm
      ((positiveBlock φ n false).comp (positiveBlock φ n true)) =
    complexHilbertSchmidtNorm
      ((positiveBlock φ n true).comp (positiveBlock φ n false)) := by
  rw [← positiveProduct_reflection]
  exact (complexHilbertSchmidtNorm_unitaryTransport _ scalarReflection
    scalarReflection).symm

private lemma qOperator_component (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (f : KSTPairL2) (b : Bool) :
    KST006.qOperator φ n z hz f b = qBlock φ n z hz b (f (!b)) := by
  apply scalarBasis.repr.injective
  apply lp.ext
  funext l
  change scalarBasis.repr (KST006.qOperator φ n z hz f b) l =
    spectralCoeff (qBlock φ n z hz b (f (!b))) l
  rw [qBlock_coeff]
  cases b
  · exact KST006.qOperator_lower_coeff φ n z hz f l
  · exact KST006.qOperator_upper_coeff φ n z hz f l

/-- The square of the full operator is exactly diagonal in its true scalar blocks. -/
theorem qOperator_sq_apply (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (f : KSTPairL2) :
    (KST006.qOperator φ n z hz).comp (KST006.qOperator φ n z hz) f =
      WithLp.toLp 2 (fun b =>
        ((qBlock φ n z hz b).comp (qBlock φ n z hz (!b))) (f b)) := by
  apply PiLp.ext
  intro b
  change KST006.qOperator φ n z hz (KST006.qOperator φ n z hz f) b = _
  rw [qOperator_component, qOperator_component]
  simp only [Bool.not_not, ContinuousLinearMap.comp_apply, PiLp.toLp_apply]

private def fullPairVector (i : Bool × ℤ) : KSTPairL2 :=
  PiLp.single 2 i.1 (scalarBasis i.2)

private lemma fullPairVector_orthonormal : Orthonormal ℂ fullPairVector := by
  classical
  have hs (j k : ℤ) : inner ℂ (scalarBasis j) (scalarBasis k) =
      if j = k then 1 else 0 :=
    orthonormal_iff_ite.mp scalarBasis.orthonormal j k
  rw [orthonormal_iff_ite]
  rintro ⟨b, j⟩ ⟨c, k⟩
  cases b <;> cases c <;> simp [fullPairVector, PiLp.inner_apply, hs]

private lemma fullPairVector_orthogonal_eq_bot :
    (Submodule.span ℂ (Set.range fullPairVector))ᗮ = ⊥ := by
  classical
  apply le_antisymm
  · intro f hf
    change f = 0
    have hi (b : Bool) (j : ℤ) :
        inner ℂ (scalarBasis j) (f b) = 0 := by
      have h := (Submodule.mem_orthogonal
        (Submodule.span ℂ (Set.range fullPairVector)) f).mp hf
        (fullPairVector (b, j)) (Submodule.subset_span (Set.mem_range_self (b, j)))
      cases b <;> simpa [fullPairVector, PiLp.inner_apply, Fintype.sum_bool] using h
    apply PiLp.ext
    intro b
    apply scalarBasis.repr.injective
    apply lp.ext
    funext j
    rw [HilbertBasis.repr_apply_apply, hi b j]
    simp
  · exact bot_le

private def fullPairBasis : HilbertBasis (Bool × ℤ) ℂ KSTPairL2 :=
  HilbertBasis.mkOfOrthogonalEqBot fullPairVector_orthonormal
    fullPairVector_orthogonal_eq_bot

private lemma qOperator_sq_single (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (b : Bool) (f : SpectralScalarL2) :
    (KST006.qOperator φ n z hz).comp (KST006.qOperator φ n z hz)
      (PiLp.single 2 b f) =
    PiLp.single 2 b
      (((qBlock φ n z hz b).comp (qBlock φ n z hz (!b))) f) := by
  rw [qOperator_sq_apply]
  apply PiLp.ext
  intro c
  by_cases h : c = b
  · subst c; simp
  · simp [h]

private lemma qOperator_sq_energy (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) :
    complexHilbertSchmidtEnergy
      ((KST006.qOperator φ n z hz).comp (KST006.qOperator φ n z hz)) =
    complexHilbertSchmidtEnergy
      ((qBlock φ n z hz true).comp (qBlock φ n z hz false)) +
    complexHilbertSchmidtEnergy
      ((qBlock φ n z hz false).comp (qBlock φ n z hz true)) := by
  rw [complexHilbertSchmidtEnergy_eq_basis _ fullPairBasis,
    complexHilbertSchmidtEnergy_eq_basis _ scalarBasis,
    complexHilbertSchmidtEnergy_eq_basis _ scalarBasis]
  simp only [fullPairBasis, HilbertBasis.coe_mkOfOrthogonalEqBot, fullPairVector,
    qOperator_sq_single, PiLp.norm_single]
  rw [ENNReal.tsum_prod']
  simp only [tsum_fintype, Fintype.sum_bool, Bool.not_true, Bool.not_false]

private lemma positiveProduct_energy_eq (φ : PhysicalPairLp) (n : ℤ) :
    complexHilbertSchmidtEnergy
      ((positiveBlock φ n false).comp (positiveBlock φ n true)) =
    complexHilbertSchmidtEnergy
      ((positiveBlock φ n true).comp (positiveBlock φ n false)) := by
  rw [← positiveProduct_reflection]
  exact (complexHilbertSchmidtEnergy_unitaryTransport _ scalarReflection
    scalarReflection).symm

/-- The source factor-two bound on the full doubled pair, throughout the closed strip. -/
theorem qOperator_sq_hs_majorant (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) :
    IsComplexHilbertSchmidt
      ((KST006.qOperator φ n z hz).comp (KST006.qOperator φ n z hz)) ∧
    complexHilbertSchmidtNorm
      ((KST006.qOperator φ n z hz).comp (KST006.qOperator φ n z hz)) ≤
      2 * complexHilbertSchmidtNorm
        ((positiveBlock φ n false).comp (positiveBlock φ n true)) := by
  let A := complexHilbertSchmidtEnergy
    ((positiveBlock φ n false).comp (positiveBlock φ n true))
  have hA : A ≠ ∞ := (blockProduct_hs_comparison φ n z hz false).1
  have he : complexHilbertSchmidtEnergy
      ((KST006.qOperator φ n z hz).comp (KST006.qOperator φ n z hz)) ≤ A + A := by
    rw [qOperator_sq_energy]
    have hp := blockProduct_energy_le φ n z hz true
    have hm := blockProduct_energy_le φ n z hz false
    simp only [Bool.not_true] at hp
    simp only [Bool.not_false] at hm
    rw [← positiveProduct_energy_eq φ n] at hp
    exact add_le_add hp hm
  have hAA : A + A ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hA, hA⟩
  have hq : IsComplexHilbertSchmidt
      ((KST006.qOperator φ n z hz).comp (KST006.qOperator φ n z hz)) :=
    ne_of_lt (lt_of_le_of_lt he (lt_top_iff_ne_top.mpr hAA))
  refine ⟨hq, ?_⟩
  have hr := ENNReal.toReal_mono hAA he
  rw [ENNReal.toReal_add hA hA] at hr
  change Real.sqrt _ ≤ 2 * Real.sqrt A.toReal
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt (ENNReal.toReal_nonneg (a := A)),
    ENNReal.toReal_nonneg (a := A)]

end NlsGge.Atomic.KST007
