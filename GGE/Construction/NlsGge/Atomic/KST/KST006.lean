import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST004
import NlsGge.Atomic.KST.KST005
import NlsGge.NLS38.SeqConv38a
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic

/-!
# The bounded complementary Q-equation operator

The potential is the actual period-one `L²` pair, lifted to the full
period-two source circle.  The operator is constructed on Fourier
coefficients from the source convolution formulas.  Each resolvent-weighted
input is first proved to be in `ℓ¹`, and Young's `ℓ¹ * ℓ² → ℓ²` estimate then
constructs the output.  No multiplication operator on `L²` is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory
open NlsGge.Atomic.KST003
open NlsGge.Atomic.KST004
open NlsGge.Atomic.KST002
open NlsGge.Analysis
open NlsGge.Pilot
open NlsGge.Schur
open NlsGge.NLS38
open scoped ENNReal

namespace NlsGge.Atomic.KST006

/-- Fourier coordinates of one actual period-one potential after its genuine
double-cover lift. Odd doubled-period modes are retained (and vanish by the
proved cover theorem), so the coefficient family lives on the full source
spectrum. -/
private def potentialCoefficients (φ : PhysicalPairLp) (b : Bool) :
    lp (fun _ : ℤ => ℂ) 2 :=
  (fourierBasis (T := (2 : ℝ))).repr (naturalPhysicalCoverL2 (φ b))

private theorem potentialCoefficients_norm (φ : PhysicalPairLp) (b : Bool) :
    ‖potentialCoefficients φ b‖ = ‖φ b‖ := by
  simp [potentialCoefficients, naturalPhysicalCoverL2.norm_map]

private theorem potentialCoefficients_apply (φ : PhysicalPairLp) (b : Bool) (k : ℤ) :
    potentialCoefficients φ b k =
      fourierCoeff (naturalPhysicalCoverL2 (φ b)) k := by
  exact fourierBasis_repr _ _

private def sourceCoefficients (f : SpectralScalarL2) : lp (fun _ : ℤ => ℂ) 2 :=
  (fourierBasis (T := (2 : ℝ))).repr f

private theorem sourceCoefficients_norm (f : SpectralScalarL2) :
    ‖sourceCoefficients f‖ = ‖f‖ := by
  exact (fourierBasis (T := (2 : ℝ))).repr.norm_map f

private theorem lp_two_norm_sq (f : lp (fun _ : ℤ => ℂ) 2) :
    ‖f‖ ^ 2 = ∑' k : ℤ, ‖f k‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) f)

/-- Translate the reciprocal-square p-series to any integer center.  The zero
term is totalized to zero, exactly as in the KST complementary coefficient. -/
private theorem shiftedReciprocalSqSummable (c : ℤ) :
    Summable (fun k : ℤ => if k = c then 0 else
      1 / (Int.natAbs (k - c) : ℝ) ^ 2) := by
  have hbase0 : Summable (fun d : ℤ => 1 / (d : ℝ) ^ 2) := by
    exact (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  have hbase : Summable (fun d : ℤ =>
      1 / (Int.natAbs d : ℝ) ^ 2) := by
    convert hbase0 using 1 <;> simp [Nat.cast_natAbs, Int.cast_abs, abs_pow]
  have hshift := (Equiv.addRight (-c)).summable_iff.mpr hbase
  have heq : (fun k : ℤ => if k = c then 0 else
      1 / (Int.natAbs (k - c) : ℝ) ^ 2) =
      fun k : ℤ => 1 / (Int.natAbs (k - c) : ℝ) ^ 2 := by
    funext k
    by_cases hk : k = c
    · simp [hk]
    · simp [hk]
  rw [heq]
  have hshiftNat : Summable (fun k : ℤ =>
      1 / (Int.natAbs (k - c) : ℝ) ^ 2) := by
    have hshiftNat' : Summable (fun k : ℤ =>
        1 / (Int.natAbs (k + -c) : ℝ) ^ 2) := by
      exact hshift.congr fun k => by rfl
    exact hshiftNat'.congr fun k => by
      rw [show k + -c = k - c by omega]
  exact hshiftNat

/-- The multiplier coefficients, with the raw upper `m` and lower `-m`
source-label convention of (12b,c). -/
private def qResolventCoeff (n : ℤ) (z : ℂ)
    (upper : Bool) (m : ℤ) : ℂ :=
  complementaryResolventCoeff n z (if upper then m else -m)

private def qResolventCenter (n : ℤ) (upper : Bool) : ℤ :=
  if upper then n else -n

private theorem qResolventCoeff_bound (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) (m : ℤ) :
    ‖qResolventCoeff n z upper m‖ ≤
      1 / (Int.natAbs (m - qResolventCenter n upper) : ℝ) := by
  have h := complementaryResolventCoeff_bound n
    (if upper then m else -m) z hz
  cases upper with
  | false =>
      have hindex : Int.natAbs (-m - n) = Int.natAbs (m - (-n)) := by
        rw [show -m - n = -(m - (-n)) by ring, Int.natAbs_neg]
      simpa [qResolventCoeff, qResolventCenter, hindex] using h
  | true =>
      simpa [qResolventCoeff, qResolventCenter] using h

private theorem qResolventCoeff_sq_bound (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) (m : ℤ) :
    ‖qResolventCoeff n z upper m‖ ^ 2 ≤
      if m = qResolventCenter n upper then 0 else
        1 / (Int.natAbs (m - qResolventCenter n upper) : ℝ) ^ 2 := by
  by_cases hm : m = qResolventCenter n upper
  · subst m
    cases upper <;>
      simp [qResolventCoeff, qResolventCenter, complementaryResolventCoeff]
  · have hb := qResolventCoeff_bound n z hz upper m
    have hd : 0 < (Int.natAbs (m - qResolventCenter n upper) : ℝ) := by
      exact_mod_cast Int.natAbs_pos.mpr (sub_ne_zero.mpr hm)
    have hnonneg : 0 ≤ 1 / (Int.natAbs (m - qResolventCenter n upper) : ℝ) := by
      positivity
    have hsq := (sq_le_sq₀ (norm_nonneg _) hnonneg).2 hb
    simpa [hm, one_div, div_pow] using hsq

private theorem qResolvent_sq_summable (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) :
    Summable (fun m : ℤ => ‖qResolventCoeff n z upper m‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun m => sq_nonneg _) (qResolventCoeff_sq_bound n z hz upper)
  exact shiftedReciprocalSqSummable (qResolventCenter n upper)

private theorem qResolvent_sq_sum_le_four (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) :
    ∑' m : ℤ, ‖qResolventCoeff n z upper m‖ ^ 2 ≤ 4 := by
  have hsum := qResolvent_sq_summable n z hz upper
  have hmajor := shiftedReciprocalSqSummable (qResolventCenter n upper)
  have hle : ∀ m : ℤ, ‖qResolventCoeff n z upper m‖ ^ 2 ≤
      (if m = qResolventCenter n upper then 0 else
        1 / (Int.natAbs (m - qResolventCenter n upper) : ℝ) ^ 2) :=
    qResolventCoeff_sq_bound n z hz upper
  have htsum := hsum.tsum_le_tsum hle hmajor
  have hKST := lattice_reciprocal_sq_bound_contract (qResolventCenter n upper)
  have hmajor_eq : (fun m : ℤ =>
      (if m = qResolventCenter n upper then 0 else
        1 / (Int.natAbs (m - qResolventCenter n upper) : ℝ) ^ 2)) =
      fun m : ℤ =>
        (if m ≠ qResolventCenter n upper then
          1 / (Int.natAbs (m - qResolventCenter n upper) : ℝ) ^ 2 else 0) := by
    funext m
    by_cases hm : m = qResolventCenter n upper <;> simp [hm]
  rw [hmajor_eq] at htsum
  exact le_trans htsum hKST

private def qResolventLp (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨qResolventCoeff n z upper,
    memℓp_gen (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        qResolvent_sq_summable n z hz upper)⟩

private theorem qResolventLp_norm_le_two (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) : ‖qResolventLp n z hz upper‖ ≤ 2 := by
  have hnorm := lp_two_norm_sq (qResolventLp n z hz upper)
  have hsum := qResolvent_sq_sum_le_four n z hz upper
  have hsum' : ∑' k : ℤ, ‖(qResolventLp n z hz upper) k‖ ^ 2 ≤ 4 := by
    simpa [qResolventLp] using hsum
  rw [← hnorm] at hsum'
  have hnonneg : 0 ≤ ‖qResolventLp n z hz upper‖ := norm_nonneg _
  nlinarith

private def resolventWeightedCoefficients (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) (f : SpectralScalarL2) : ℤ → ℂ :=
  fun m => qResolventCoeff n z upper m * sourceCoefficients f m

private theorem resolventWeightedCoefficients_isL1 (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) (f : SpectralScalarL2) :
    IsL1 (resolventWeightedCoefficients n z hz upper f) := by
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hs := lp.summable_mul hpq (qResolventLp n z hz upper) (sourceCoefficients f)
  simpa [IsL1, resolventWeightedCoefficients, qResolventLp,
    sourceCoefficients, norm_mul] using hs

private theorem resolventWeightedCoefficients_l1_bound (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) (f : SpectralScalarL2) :
    l1 (resolventWeightedCoefficients n z hz upper f) ≤ 2 * ‖f‖ := by
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := lp.tsum_mul_le_mul_norm' hpq
    (qResolventLp n z hz upper) (sourceCoefficients f)
  calc
    l1 (resolventWeightedCoefficients n z hz upper f) =
        ∑' m : ℤ, ‖qResolventCoeff n z upper m‖ * ‖sourceCoefficients f m‖ := by
          simp [l1, resolventWeightedCoefficients, norm_mul]
    _ ≤ ‖qResolventLp n z hz upper‖ * ‖sourceCoefficients f‖ := h
    _ ≤ 2 * ‖f‖ := by
      rw [sourceCoefficients_norm]
      exact mul_le_mul_of_nonneg_right
        (qResolventLp_norm_le_two n z hz upper) (norm_nonneg _)

private def qScalarCoefficientFunction (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) (f : SpectralScalarL2) : ℤ → ℂ :=
  conv (resolventWeightedCoefficients n z hz upper f)
    (fun k => potentialCoefficients φ upper k)

private theorem qScalarCoefficientFunction_sq_summable (φ : PhysicalPairLp)
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (upper : Bool)
    (f : SpectralScalarL2) :
    Summable (fun k : ℤ =>
      ‖qScalarCoefficientFunction φ n z hz upper f k‖ ^ 2) := by
  have ha : Summable (fun k : ℤ => ‖potentialCoefficients φ upper k‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (potentialCoefficients φ upper)).summable
  exact (summable_sq_conv
    (resolventWeightedCoefficients_isL1 n z hz upper f) ha).1

private def qScalarOutputCoefficients (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) (f : SpectralScalarL2) :
    lp (fun _ : ℤ => ℂ) 2 :=
  ⟨qScalarCoefficientFunction φ n z hz upper f,
    memℓp_gen (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        qScalarCoefficientFunction_sq_summable φ n z hz upper f)⟩

private theorem qScalarOutputCoefficients_norm_le (φ : PhysicalPairLp)
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (upper : Bool)
    (f : SpectralScalarL2) :
    ‖qScalarOutputCoefficients φ n z hz upper f‖ ≤
      2 * ‖φ upper‖ * ‖f‖ := by
  have hYoung := (summable_sq_conv
    (resolventWeightedCoefficients_isL1 n z hz upper f)
      (by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num)
            (potentialCoefficients φ upper)).summable)).2
  have hout : ‖qScalarOutputCoefficients φ n z hz upper f‖ ^ 2 ≤
      l1 (resolventWeightedCoefficients n z hz upper f) ^ 2 *
        ‖potentialCoefficients φ upper‖ ^ 2 := by
    calc
      ‖qScalarOutputCoefficients φ n z hz upper f‖ ^ 2 =
          ∑' k : ℤ, ‖qScalarCoefficientFunction φ n z hz upper f k‖ ^ 2 := by
            simpa [qScalarOutputCoefficients] using
              lp_two_norm_sq (qScalarOutputCoefficients φ n z hz upper f)
      _ ≤ l1 (resolventWeightedCoefficients n z hz upper f) ^ 2 *
          ∑' k : ℤ, ‖potentialCoefficients φ upper k‖ ^ 2 := by
            simpa [qScalarCoefficientFunction] using hYoung
      _ = l1 (resolventWeightedCoefficients n z hz upper f) ^ 2 *
          ‖potentialCoefficients φ upper‖ ^ 2 := by
            rw [← lp_two_norm_sq]
  have hl1 := resolventWeightedCoefficients_l1_bound n z hz upper f
  have hpotnorm := potentialCoefficients_norm φ upper
  have hnonneg : 0 ≤ 2 * ‖φ upper‖ * ‖f‖ := by positivity
  have hsq : (‖qScalarOutputCoefficients φ n z hz upper f‖) ^ 2 ≤
      (2 * ‖φ upper‖ * ‖f‖) ^ 2 := by
    calc
      _ ≤ l1 (resolventWeightedCoefficients n z hz upper f) ^ 2 *
          ‖potentialCoefficients φ upper‖ ^ 2 := hout
      _ ≤ (2 * ‖f‖) ^ 2 * ‖φ upper‖ ^ 2 := by
        rw [hpotnorm]
        have hl1nonneg : 0 ≤ l1 (resolventWeightedCoefficients n z hz upper f) :=
          tsum_nonneg fun m => norm_nonneg _
        have hsq : l1 (resolventWeightedCoefficients n z hz upper f) ^ 2 ≤
            (2 * ‖f‖) ^ 2 :=
          (sq_le_sq₀ hl1nonneg (by positivity)).2
            (resolventWeightedCoefficients_l1_bound n z hz upper f)
        exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = (2 * ‖φ upper‖ * ‖f‖) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) hnonneg).1 hsq

private def qScalarOutputLinear (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) :
    SpectralScalarL2 →ₗ[ℂ] SpectralScalarL2 where
  toFun f := (fourierBasis (T := (2 : ℝ))).repr.symm
    (qScalarOutputCoefficients φ n z hz upper f)
  map_add' f g := by
    apply (fourierBasis (T := (2 : ℝ))).repr.injective
    simp only [map_add, LinearIsometryEquiv.apply_symm_apply]
    apply lp.ext
    funext k
    have hf : IsL1 (resolventWeightedCoefficients n z hz upper f) :=
      resolventWeightedCoefficients_isL1 n z hz upper f
    have hg : IsL1 (resolventWeightedCoefficients n z hz upper g) :=
      resolventWeightedCoefficients_isL1 n z hz upper g
    have ha : Summable (fun j : ℤ => ‖potentialCoefficients φ upper j‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num)
          (potentialCoefficients φ upper)).summable
    have hslice (u : SpectralScalarL2) :
        ∀ k : ℤ, Summable (fun j : ℤ =>
          resolventWeightedCoefficients n z hz upper u j *
            potentialCoefficients φ upper (k - j)) := by
      intro k
      exact summable_conv_term_l2
        (resolventWeightedCoefficients_isL1 n z hz upper u) ha k
    have hlin (j : ℤ) :
        resolventWeightedCoefficients n z hz upper (f + g) j =
          resolventWeightedCoefficients n z hz upper f j +
            resolventWeightedCoefficients n z hz upper g j := by
      simp [resolventWeightedCoefficients, sourceCoefficients, map_add]
      ring
    change qScalarCoefficientFunction φ n z hz upper (f + g) k =
      qScalarCoefficientFunction φ n z hz upper f k +
        qScalarCoefficientFunction φ n z hz upper g k
    unfold qScalarCoefficientFunction
    rw [show resolventWeightedCoefficients n z hz upper (f + g) =
        resolventWeightedCoefficients n z hz upper f +
          resolventWeightedCoefficients n z hz upper g from funext hlin]
    exact congrFun
      (conv_add_left_of_summable (fun j => hslice f j) (fun j => hslice g j)) k
  map_smul' c f := by
    apply (fourierBasis (T := (2 : ℝ))).repr.injective
    simp only [map_smul, LinearIsometryEquiv.apply_symm_apply]
    apply lp.ext
    funext k
    have hlin (j : ℤ) :
        resolventWeightedCoefficients n z hz upper (c • f) j =
          c • resolventWeightedCoefficients n z hz upper f j := by
      simp [resolventWeightedCoefficients, sourceCoefficients, map_smul]
      ring
    change qScalarCoefficientFunction φ n z hz upper (c • f) k =
      c • qScalarCoefficientFunction φ n z hz upper f k
    unfold qScalarCoefficientFunction
    rw [show resolventWeightedCoefficients n z hz upper (c • f) =
        c • resolventWeightedCoefficients n z hz upper f from funext hlin]
    exact congrFun (conv_smul_left c _ _) k

private theorem qScalarOutputLinear_norm_le (φ : PhysicalPairLp)
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) (upper : Bool)
    (f : SpectralScalarL2) :
    ‖qScalarOutputLinear φ n z hz upper f‖ ≤
      2 * ‖φ upper‖ * ‖f‖ := by
  change ‖(fourierBasis (T := (2 : ℝ))).repr.symm
      (qScalarOutputCoefficients φ n z hz upper f)‖ ≤ _
  rw [(fourierBasis (T := (2 : ℝ))).repr.symm.norm_map]
  exact qScalarOutputCoefficients_norm_le φ n z hz upper f

private def qOperatorLinear (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) : KSTPairL2 →ₗ[ℂ] KSTPairL2 where
  toFun f := WithLp.toLp 2 (fun b =>
    if b then qScalarOutputLinear φ n z hz true (f false)
    else qScalarOutputLinear φ n z hz false (f true))
  map_add' f g := by
    apply PiLp.ext
    intro b
    cases b
    · exact map_add (qScalarOutputLinear φ n z hz false) (f true) (g true)
    · exact map_add (qScalarOutputLinear φ n z hz true) (f false) (g false)
  map_smul' c f := by
    apply PiLp.ext
    intro b
    cases b
    · exact map_smul (qScalarOutputLinear φ n z hz false) c (f true)
    · exact map_smul (qScalarOutputLinear φ n z hz true) c (f false)

private theorem qOperatorLinear_norm_le (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (f : KSTPairL2) :
    ‖qOperatorLinear φ n z hz f‖ ≤ 2 * ‖φ‖ * ‖f‖ := by
  have hupper := qScalarOutputLinear_norm_le φ n z hz true (f false)
  have hlower := qScalarOutputLinear_norm_le φ n z hz false (f true)
  have hφu : 0 ≤ ‖φ true‖ := norm_nonneg _
  have hφl : 0 ≤ ‖φ false‖ := norm_nonneg _
  have hfu : 0 ≤ ‖f true‖ := norm_nonneg _
  have hfl : 0 ≤ ‖f false‖ := norm_nonneg _
  have hphi : ‖φ‖ ^ 2 = ‖φ true‖ ^ 2 + ‖φ false‖ ^ 2 := by
    simpa only [Fintype.sum_bool] using
      (PiLp.norm_sq_eq_of_L2 (fun _ : Bool => PhysicalL2) φ)
  have hinput : ‖f‖ ^ 2 = ‖f true‖ ^ 2 + ‖f false‖ ^ 2 := by
    simpa only [Fintype.sum_bool] using
      (PiLp.norm_sq_eq_of_L2 (fun _ : Bool => SpectralScalarL2) f)
  have houtput : ‖qOperatorLinear φ n z hz f‖ ^ 2 =
      ‖qOperatorLinear φ n z hz f true‖ ^ 2 +
        ‖qOperatorLinear φ n z hz f false‖ ^ 2 := by
    simpa only [Fintype.sum_bool] using
      (PiLp.norm_sq_eq_of_L2 (fun _ : Bool => SpectralScalarL2)
        (qOperatorLinear φ n z hz f))
  have hUpperSq : ‖qOperatorLinear φ n z hz f true‖ ^ 2 ≤
      (2 * ‖φ true‖ * ‖f false‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hupper
  have hLowerSq : ‖qOperatorLinear φ n z hz f false‖ ^ 2 ≤
      (2 * ‖φ false‖ * ‖f true‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hlower
  have hdot :
      (‖φ true‖ * ‖f false‖) ^ 2 + (‖φ false‖ * ‖f true‖) ^ 2 ≤
        (‖φ true‖ ^ 2 + ‖φ false‖ ^ 2) *
          (‖f true‖ ^ 2 + ‖f false‖ ^ 2) := by
    nlinarith [sq_nonneg (‖φ true‖ * ‖f true‖ -
        ‖φ false‖ * ‖f false‖)]
  have hsquare : ‖qOperatorLinear φ n z hz f‖ ^ 2 ≤
      (2 * ‖φ‖ * ‖f‖) ^ 2 := by
    calc
      ‖qOperatorLinear φ n z hz f‖ ^ 2 =
          ‖qOperatorLinear φ n z hz f true‖ ^ 2 +
            ‖qOperatorLinear φ n z hz f false‖ ^ 2 := houtput
      _ ≤ (2 * ‖φ true‖ * ‖f false‖) ^ 2 +
          (2 * ‖φ false‖ * ‖f true‖) ^ 2 := add_le_add hUpperSq hLowerSq
      _ ≤ 4 * (‖φ true‖ ^ 2 + ‖φ false‖ ^ 2) *
          (‖f true‖ ^ 2 + ‖f false‖ ^ 2) := by nlinarith [hdot]
      _ = (2 * ‖φ‖ * ‖f‖) ^ 2 := by rw [← hphi, ← hinput]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsquare

/-- The actual bounded KST Q-equation operator on the full doubled source
pair space. Its two coefficient components are exactly formulas (12b,c). -/
noncomputable def qOperator (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) : KSTPairL2 →L[ℂ] KSTPairL2 :=
  (qOperatorLinear φ n z hz).mkContinuous (2 * ‖φ‖)
    (qOperatorLinear_norm_le φ n z hz)

/-- The source upper convolution formula (12b), in the actual Fourier basis
coordinates of the full period-two output and input. -/
theorem qOperator_upper_coeff (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (f : KSTPairL2) (l : ℤ) :
    (fourierBasis (T := (2 : ℝ))).repr (qOperator φ n z hz f true) l =
      ∑' m : ℤ,
        fourierCoeff (naturalPhysicalCoverL2 (φ true)) (l - m) *
          (complementaryResolventCoeff n z m *
            (fourierBasis (T := (2 : ℝ))).repr (f false) m) := by
  rw [qOperator, LinearMap.mkContinuous_apply]
  change (fourierBasis (T := (2 : ℝ))).repr
    (qScalarOutputLinear φ n z hz true (f false)) l = _
  change ((fourierBasis (T := (2 : ℝ))).repr
      ((fourierBasis (T := (2 : ℝ))).repr.symm
        (qScalarOutputCoefficients φ n z hz true (f false)))) l = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change qScalarOutputCoefficients φ n z hz true (f false) l = _
  change qScalarCoefficientFunction φ n z hz true (f false) l = _
  unfold qScalarCoefficientFunction resolventWeightedCoefficients qResolventCoeff conv
  apply tsum_congr
  intro m
  simp only [potentialCoefficients_apply, sourceCoefficients]
  simp <;> ring

/-- The source lower convolution formula (12c), retaining its reflected
resolvent index `-m`. -/
theorem qOperator_lower_coeff (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (f : KSTPairL2) (l : ℤ) :
    (fourierBasis (T := (2 : ℝ))).repr (qOperator φ n z hz f false) l =
      ∑' m : ℤ,
        fourierCoeff (naturalPhysicalCoverL2 (φ false)) (l - m) *
          (complementaryResolventCoeff n z (-m) *
            (fourierBasis (T := (2 : ℝ))).repr (f true) m) := by
  rw [qOperator, LinearMap.mkContinuous_apply]
  change (fourierBasis (T := (2 : ℝ))).repr
    (qScalarOutputLinear φ n z hz false (f true)) l = _
  change ((fourierBasis (T := (2 : ℝ))).repr
      ((fourierBasis (T := (2 : ℝ))).repr.symm
        (qScalarOutputCoefficients φ n z hz false (f true)))) l = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change qScalarOutputCoefficients φ n z hz false (f true) l = _
  change qScalarCoefficientFunction φ n z hz false (f true) l = _
  unfold qScalarCoefficientFunction resolventWeightedCoefficients qResolventCoeff conv
  apply tsum_congr
  intro m
  simp only [potentialCoefficients_apply, sourceCoefficients]
  simp <;> ring

/-- The source KST estimate: the full-space Q-equation operator is bounded
uniformly throughout the closed spectral strip. -/
theorem norm_qOperator_le (φ : PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) : ‖qOperator φ n z hz‖ ≤ 2 * ‖φ‖ := by
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

end NlsGge.Atomic.KST006
