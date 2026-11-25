import Mathlib
import NlsGge.ThirdConsultation.M.M028Host
import NlsGge.ThirdConsultation.M.MW1Power
import NlsGge.ThirdConsultation.M.MRound11Sector
import NlsGge.ThirdConsultation.M.MRound11Paths
import NlsGge.Atomic.M.M021
import NlsGge.Atomic.M.M022
import NlsGge.Atomic.KST.KST016

/-!
# MSchurBound: shared supports for M-027 / M-028 (proof development, AUTHOR; not self-reviewed)

Weighted bounds on the Schur path terms from the landed M-022 square bound `T_squared_bound`:

* iteration `shiftedPairNorm ((T^2)^m g) <= q^m shiftedPairNorm g`, `q = 4 ||phi||_w^2 / <n>`;
* extraction of the resonant coefficient: `w(2n) |<e_out, g>| <= shiftedPairNorm g`;
* the shifted norm of `V e_in` is the weighted component norm `componentNorm w phi plus`;
* the even path terms and the even remainder bound (the M-028 core).

Every `HasSum` is proved before it is used; `tsum_of_norm_bounded` needs no summability of the series itself.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace NlsGge.ThirdConsultation.MTwoModeB

open NlsGge.ThirdConsultation.MTwoMode NlsGge.Atomic.M.M054 NlsGge.Atomic.KST003

/-! ### weights -/

theorem weight_even (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w) (k : ℤ) :
    w (-k) = w k := by
  obtain ⟨v, _, hve, _, hwv⟩ := hw
  rw [hwv, hwv, hve]
  unfold indexWeight
  rw [Int.cast_neg, abs_neg]

theorem one_le_weight (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w) (k : ℤ) :
    1 ≤ w k :=
  (NlsGge.ThirdConsultation.MTwoModeW.one_le_indexWeight k).trans
    (NlsGge.ThirdConsultation.MTwoModeW.indexWeight_le_of_oneDerivative w hw k)

theorem weight_pos (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w) (k : ℤ) :
    0 < w k :=
  lt_of_lt_of_le one_pos (one_le_weight w hw k)

theorem le_of_sq_le_sq' (x N : ℝ) (hN : 0 ≤ N) (h : x ^ 2 ≤ N ^ 2) : x ≤ N := by
  by_contra hc
  push_neg at hc
  nlinarith [mul_pos (sub_pos.2 hc) (by linarith : 0 < x + N)]

/-! ### component energies -/

def compEnergy (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair) (plus : Bool) : ℝ≥0∞ :=
  ∑' k : ℤ, ENNReal.ofReal (w k ^ 2 * ‖fourierPotential φ plus k‖ ^ 2)

theorem componentNorm_eq (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair) (plus : Bool) :
    NlsGge.ThirdConsultation.M.componentNorm w φ plus = Real.sqrt (compEnergy w φ plus).toReal :=
  rfl

theorem potentialEnergy_split (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair) :
    potentialCoefficientEnergy w φ = compEnergy w φ true + compEnergy w φ false := by
  rw [potentialCoefficientEnergy_eq, add_comm]
  rfl

theorem compEnergy_ne_top (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair)
    (h : potentialCoefficientEnergy w φ ≠ ⊤) (plus : Bool) : compEnergy w φ plus ≠ ⊤ := by
  rw [potentialEnergy_split] at h
  cases plus
  · exact fun h' => h (by rw [h', add_top])
  · exact fun h' => h (by rw [h', top_add])

theorem compEnergy_summable (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair) (plus : Bool)
    (h : compEnergy w φ plus ≠ ⊤) :
    Summable fun k : ℤ => w k ^ 2 * ‖fourierPotential φ plus k‖ ^ 2 :=
  NlsGge.ThirdConsultation.MTwoMode.Real21.summable_of_ofReal_tsum_ne_top _
    (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)) h

theorem compEnergy_toReal (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair) (plus : Bool)
    (h : compEnergy w φ plus ≠ ⊤) :
    (compEnergy w φ plus).toReal = ∑' k : ℤ, w k ^ 2 * ‖fourierPotential φ plus k‖ ^ 2 := by
  unfold compEnergy
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (compEnergy_summable w φ plus h),
    ENNReal.toReal_ofReal (tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _))]

theorem potentialNorm_sq (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair)
    (h : potentialCoefficientEnergy w φ ≠ ⊤) :
    potentialCoefficientNorm w φ ^ 2 =
      NlsGge.ThirdConsultation.M.componentNorm w φ true ^ 2 +
        NlsGge.ThirdConsultation.M.componentNorm w φ false ^ 2 := by
  unfold potentialCoefficientNorm
  rw [componentNorm_eq, componentNorm_eq, Real.sq_sqrt ENNReal.toReal_nonneg,
    Real.sq_sqrt ENNReal.toReal_nonneg, Real.sq_sqrt ENNReal.toReal_nonneg,
    potentialEnergy_split, ENNReal.toReal_add (compEnergy_ne_top w φ h true)
      (compEnergy_ne_top w φ h false)]

/-! ### iteration of the M-022 square bound -/

theorem iter_w (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair) (hφ : potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ) (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (g : KSTPairL2) (hg : shiftedPairEnergy w n false (coefficientPair g) ≠ ⊤) (m : ℕ) :
    shiftedPairEnergy w n false
        (coefficientPair ((((ambientT φ n lam hlam) ^ 2) ^ m) g)) ≠ ⊤ ∧
      shiftedPairNorm w n false
        (coefficientPair ((((ambientT φ n lam hlam) ^ 2) ^ m) g)) ≤
        (4 * potentialCoefficientNorm w φ ^ 2 / indexWeight n) ^ m *
          shiftedPairNorm w n false (coefficientPair g) := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have h := NlsGge.ThirdConsultation.M.T_squared_bound w hw φ hφ n lam hlam
      ((((ambientT φ n lam hlam) ^ 2) ^ m) g) ih1
    have e : (((ambientT φ n lam hlam) ^ 2) ^ (m + 1)) g =
        T φ n lam hlam (T φ n lam hlam ((((ambientT φ n lam hlam) ^ 2) ^ m) g)) := by
      rw [pow_succ', ContinuousLinearMap.mul_apply, sq, ContinuousLinearMap.mul_apply]
      rfl
    rw [e]
    refine ⟨h.1, h.2.trans ?_⟩
    have hq : 0 ≤ 4 * potentialCoefficientNorm w φ ^ 2 / indexWeight n :=
      div_nonneg (by positivity) (NlsGge.ThirdConsultation.MTwoModeW.indexWeight_pos n).le
    calc (4 * potentialCoefficientNorm w φ ^ 2 / indexWeight n) *
          shiftedPairNorm w n false
            (coefficientPair ((((ambientT φ n lam hlam) ^ 2) ^ m) g))
        ≤ (4 * potentialCoefficientNorm w φ ^ 2 / indexWeight n) *
            ((4 * potentialCoefficientNorm w φ ^ 2 / indexWeight n) ^ m *
              shiftedPairNorm w n false (coefficientPair g)) :=
          mul_le_mul_of_nonneg_left ih2 hq
      _ = (4 * potentialCoefficientNorm w φ ^ 2 / indexWeight n) ^ (m + 1) *
            shiftedPairNorm w n false (coefficientPair g) := by ring

/-! ### extraction of the resonant coefficient -/

theorem sq_term_le (w : ℤ → ℝ) (n : ℤ) (f : CoefficientPair)
    (hf : shiftedPairEnergy w n false f ≠ ⊤) (k : ℤ) :
    w (k + -n) ^ 2 * ‖f true k‖ ^ 2 + w (k - -n) ^ 2 * ‖f false k‖ ^ 2 ≤
      shiftedPairNorm w n false f ^ 2 := by
  have h1 : ENNReal.ofReal (w (k + -n) ^ 2 * ‖f true k‖ ^ 2 + w (k - -n) ^ 2 * ‖f false k‖ ^ 2) ≤
      shiftedPairEnergy w n false f := by
    change _ ≤ ∑' k : ℤ, ENNReal.ofReal
      (w (k + -n) ^ 2 * ‖f true k‖ ^ 2 + w (k - -n) ^ 2 * ‖f false k‖ ^ 2)
    exact ENNReal.le_tsum (f := fun k : ℤ => ENNReal.ofReal
      (w (k + -n) ^ 2 * ‖f true k‖ ^ 2 + w (k - -n) ^ 2 * ‖f false k‖ ^ 2)) k
  rw [ENNReal.ofReal_le_iff_le_toReal hf] at h1
  unfold shiftedPairNorm
  rwa [Real.sq_sqrt ENNReal.toReal_nonneg]

theorem coeff_false_le (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (n : ℤ) (g : KSTPairL2) (hg : shiftedPairEnergy w n false (coefficientPair g) ≠ ⊤) :
    w (2 * n) * ‖coefficientPair g false n‖ ≤ shiftedPairNorm w n false (coefficientPair g) := by
  have h := sq_term_le w n (coefficientPair g) hg n
  have hw2 : n - -n = 2 * n := by ring
  rw [hw2] at h
  refine le_of_sq_le_sq' _ _ (Real.sqrt_nonneg _) ?_
  have h0 : 0 ≤ w (n + -n) ^ 2 * ‖coefficientPair g true n‖ ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [mul_pow]
  linarith

theorem coeff_true_le (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (n : ℤ) (g : KSTPairL2) (hg : shiftedPairEnergy w n false (coefficientPair g) ≠ ⊤) :
    w (2 * n) * ‖coefficientPair g true (-n)‖ ≤ shiftedPairNorm w n false (coefficientPair g) := by
  have h := sq_term_le w n (coefficientPair g) hg (-n)
  have hw2 : w (-n + -n) = w (2 * n) := by
    rw [show -n + -n = -(2 * n) by ring, weight_even w hw]
  rw [hw2] at h
  refine le_of_sq_le_sq' _ _ (Real.sqrt_nonneg _) ?_
  have h0 : 0 ≤ w (-n - -n) ^ 2 * ‖coefficientPair g false (-n)‖ ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [mul_pow]
  linarith

theorem inner_frame_false (n : ℤ) (g : KSTPairL2) :
    inner ℂ (schurFrame n false : KSTPairL2) g = coefficientPair g false n := by
  have e : (schurFrame n false : KSTPairL2) = PiLp.single 2 false (NlsGge.Schur.spectralBasis n) := rfl
  rw [e, NlsGge.Atomic.KST016.inner_single_left,
    ← NlsGge.ThirdConsultation.MTwoModeSupp.fourierCoeff_eq_inner]
  rfl

theorem inner_frame_true (n : ℤ) (g : KSTPairL2) :
    inner ℂ (schurFrame n true : KSTPairL2) g = coefficientPair g true (-n) := by
  have e : (schurFrame n true : KSTPairL2) = PiLp.single 2 true (NlsGge.Schur.spectralBasis (-n)) := rfl
  rw [e, NlsGge.Atomic.KST016.inner_single_left,
    ← NlsGge.ThirdConsultation.MTwoModeSupp.fourierCoeff_eq_inner]
  rfl

theorem inner_frame_false_le (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (n : ℤ) (g : KSTPairL2) (hg : shiftedPairEnergy w n false (coefficientPair g) ≠ ⊤) :
    w (2 * n) * ‖inner ℂ (schurFrame n false : KSTPairL2) g‖ ≤
      shiftedPairNorm w n false (coefficientPair g) := by
  rw [inner_frame_false]
  exact coeff_false_le w hw n g hg

theorem inner_frame_true_le (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (n : ℤ) (g : KSTPairL2) (hg : shiftedPairEnergy w n false (coefficientPair g) ≠ ⊤) :
    w (2 * n) * ‖inner ℂ (schurFrame n true : KSTPairL2) g‖ ≤
      shiftedPairNorm w n false (coefficientPair g) := by
  rw [inner_frame_true]
  exact coeff_true_le w hw n g hg

/-! ### the shifted norm of `V e` -/

theorem V_upper_eq (φ : NlsGge.GK38.PotPair) (n : ℤ) :
    NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n (schurFrame n true : KSTPairL2) =
      (PiLp.single 2 false (NlsGge.Schur.fourierMultiplier (-n)
        (NlsGge.Analysis.naturalPhysicalCoverL2 φ.2)) : KSTPairL2) := by
  have h := orthonormal_iff_ite.mp (kstPnFrame_orthonormal n)
  have huu : inner ℂ (kstPnUpper n) (kstPnUpper n) = 1 := by simpa [kstPnFrame] using h true true
  have hlu : inner ℂ (kstPnLower n) (kstPnUpper n) = 0 := by simpa [kstPnFrame] using h false true
  have hu : (schurFrame n true : KSTPairL2) = kstPnUpper n := rfl
  rw [hu, NlsGge.Atomic.KST016.pot_apply, huu, hlu, zero_smul, one_smul, zero_add]
  rfl

theorem V_lower_eq (φ : NlsGge.GK38.PotPair) (n : ℤ) :
    NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n (schurFrame n false : KSTPairL2) =
      (PiLp.single 2 true (NlsGge.Schur.fourierMultiplier n
        (NlsGge.Analysis.naturalPhysicalCoverL2 φ.1)) : KSTPairL2) := by
  have h := orthonormal_iff_ite.mp (kstPnFrame_orthonormal n)
  have hll : inner ℂ (kstPnLower n) (kstPnLower n) = 1 := by simpa [kstPnFrame] using h false false
  have hul : inner ℂ (kstPnUpper n) (kstPnLower n) = 0 := by simpa [kstPnFrame] using h true false
  have hl : (schurFrame n false : KSTPairL2) = kstPnLower n := rfl
  rw [hl, NlsGge.Atomic.KST016.pot_apply, hll, hul, zero_smul, one_smul, add_zero]
  rfl

theorem fm_coeff (F : NlsGge.Schur.SpectralScalarL2) (s k : ℤ) :
    _root_.fourierCoeff (NlsGge.Schur.fourierMultiplier s F) k = _root_.fourierCoeff F (k - s) := by
  rw [NlsGge.ThirdConsultation.MTwoModeSupp.fourierCoeff_eq_inner,
    NlsGge.Atomic.KST016.inner_basis_mul]

theorem V_upper_coeff_true (φ : NlsGge.GK38.PotPair) (n k : ℤ) :
    coefficientPair (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
      (schurFrame n true : KSTPairL2)) true k = 0 := by
  rw [V_upper_eq]
  change _root_.fourierCoeff (0 : NlsGge.Schur.SpectralScalarL2) k = 0
  rw [NlsGge.ThirdConsultation.MTwoModeSupp.fourierCoeff_eq_inner, inner_zero_right]

theorem V_upper_coeff_false (φ : NlsGge.GK38.PotPair) (n k : ℤ) :
    coefficientPair (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
      (schurFrame n true : KSTPairL2)) false k = fourierPotential φ true (k + n) := by
  rw [V_upper_eq]
  change _root_.fourierCoeff (NlsGge.Schur.fourierMultiplier (-n)
    (NlsGge.Analysis.naturalPhysicalCoverL2 φ.2)) k = _
  rw [fm_coeff, sub_neg_eq_add]
  rfl

theorem V_lower_coeff_false (φ : NlsGge.GK38.PotPair) (n k : ℤ) :
    coefficientPair (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
      (schurFrame n false : KSTPairL2)) false k = 0 := by
  rw [V_lower_eq]
  change _root_.fourierCoeff (0 : NlsGge.Schur.SpectralScalarL2) k = 0
  rw [NlsGge.ThirdConsultation.MTwoModeSupp.fourierCoeff_eq_inner, inner_zero_right]

theorem V_lower_coeff_true (φ : NlsGge.GK38.PotPair) (n k : ℤ) :
    coefficientPair (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
      (schurFrame n false : KSTPairL2)) true k = fourierPotential φ false (k - n) := by
  rw [V_lower_eq]
  change _root_.fourierCoeff (NlsGge.Schur.fourierMultiplier n
    (NlsGge.Analysis.naturalPhysicalCoverL2 φ.1)) k = _
  rw [fm_coeff]
  rfl

theorem shifted_V_upper (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair) (n : ℤ) :
    shiftedPairEnergy w n false (coefficientPair
      (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
        (schurFrame n true : KSTPairL2))) = compEnergy w φ true := by
  change ∑' k : ℤ, ENNReal.ofReal (w (k + -n) ^ 2 * ‖coefficientPair
      (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
        (schurFrame n true : KSTPairL2)) true k‖ ^ 2 +
      w (k - -n) ^ 2 * ‖coefficientPair
      (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
        (schurFrame n true : KSTPairL2)) false k‖ ^ 2) = _
  have e : ∀ k : ℤ, w (k + -n) ^ 2 * ‖coefficientPair
      (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
        (schurFrame n true : KSTPairL2)) true k‖ ^ 2 +
      w (k - -n) ^ 2 * ‖coefficientPair
      (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
        (schurFrame n true : KSTPairL2)) false k‖ ^ 2 =
      w (k + n) ^ 2 * ‖fourierPotential φ true (k + n)‖ ^ 2 := by
    intro k
    rw [V_upper_coeff_true, V_upper_coeff_false, sub_neg_eq_add]
    simp
  rw [tsum_congr fun k => congrArg ENNReal.ofReal (e k)]
  exact (Equiv.addRight n).tsum_eq
    (fun j : ℤ => ENNReal.ofReal (w j ^ 2 * ‖fourierPotential φ true j‖ ^ 2))

theorem shifted_V_lower (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair) (n : ℤ) :
    shiftedPairEnergy w n false (coefficientPair
      (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
        (schurFrame n false : KSTPairL2))) = compEnergy w φ false := by
  change ∑' k : ℤ, ENNReal.ofReal (w (k + -n) ^ 2 * ‖coefficientPair
      (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
        (schurFrame n false : KSTPairL2)) true k‖ ^ 2 +
      w (k - -n) ^ 2 * ‖coefficientPair
      (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
        (schurFrame n false : KSTPairL2)) false k‖ ^ 2) = _
  have e : ∀ k : ℤ, w (k + -n) ^ 2 * ‖coefficientPair
      (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
        (schurFrame n false : KSTPairL2)) true k‖ ^ 2 +
      w (k - -n) ^ 2 * ‖coefficientPair
      (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
        (schurFrame n false : KSTPairL2)) false k‖ ^ 2 =
      w (k - n) ^ 2 * ‖fourierPotential φ false (k - n)‖ ^ 2 := by
    intro k
    rw [V_lower_coeff_true, V_lower_coeff_false, ← sub_eq_add_neg]
    simp
  rw [tsum_congr fun k => congrArg ENNReal.ofReal (e k)]
  exact (Equiv.subRight n).tsum_eq
    (fun j : ℤ => ENNReal.ofReal (w j ^ 2 * ‖fourierPotential φ false j‖ ^ 2))

theorem shifted_norm_V_upper (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair) (n : ℤ) :
    shiftedPairNorm w n false (coefficientPair
      (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
        (schurFrame n true : KSTPairL2))) = NlsGge.ThirdConsultation.M.componentNorm w φ true := by
  unfold shiftedPairNorm
  rw [shifted_V_upper]
  rfl

theorem shifted_norm_V_lower (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair) (n : ℤ) :
    shiftedPairNorm w n false (coefficientPair
      (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
        (schurFrame n false : KSTPairL2))) = NlsGge.ThirdConsultation.M.componentNorm w φ false := by
  unfold shiftedPairNorm
  rw [shifted_V_lower]
  rfl

/-! ### the even path terms and the even remainder -/

theorem even_term_le (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair) (hφ : potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ) (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (plus : Bool) (j : ℕ) :
    w (2 * n) * ‖schurPathTerm φ n lam hlam (2 * j + 2)
        (if plus then false else true) (if plus then true else false)‖ ≤
      (4 * potentialCoefficientNorm w φ ^ 2 / indexWeight n) ^ (j + 1) *
        NlsGge.ThirdConsultation.M.componentNorm w φ plus := by
  have e : 2 * j + 2 = 2 * (j + 1) := by ring
  cases plus
  · -- minus: output frame `true`, input frame `false`
    have hK : shiftedPairEnergy w n false (coefficientPair
        (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
          (schurFrame n false : KSTPairL2))) ≠ ⊤ := by
      rw [shifted_V_lower]
      exact compEnergy_ne_top w φ hφ false
    obtain ⟨h1, h2⟩ := iter_w w hw φ hφ n lam hlam _ hK (j + 1)
    have h3 := inner_frame_true_le w hw n _ h1
    have h4 : schurPathTerm φ n lam hlam (2 * j + 2) true false =
        inner ℂ (schurFrame n true : KSTPairL2)
          ((((ambientT φ n lam hlam) ^ 2) ^ (j + 1))
            (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
              (schurFrame n false : KSTPairL2))) := by
      unfold schurPathTerm
      rw [e, pow_mul]
    change w (2 * n) * ‖schurPathTerm φ n lam hlam (2 * j + 2) true false‖ ≤ _
    rw [h4]
    refine h3.trans (h2.trans ?_)
    rw [shifted_norm_V_lower]
  · -- plus: output frame `false`, input frame `true`
    have hK : shiftedPairEnergy w n false (coefficientPair
        (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
          (schurFrame n true : KSTPairL2))) ≠ ⊤ := by
      rw [shifted_V_upper]
      exact compEnergy_ne_top w φ hφ true
    obtain ⟨h1, h2⟩ := iter_w w hw φ hφ n lam hlam _ hK (j + 1)
    have h3 := inner_frame_false_le w hw n _ h1
    have h4 : schurPathTerm φ n lam hlam (2 * j + 2) false true =
        inner ℂ (schurFrame n false : KSTPairL2)
          ((((ambientT φ n lam hlam) ^ 2) ^ (j + 1))
            (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
              (schurFrame n true : KSTPairL2))) := by
      unfold schurPathTerm
      rw [e, pow_mul]
    change w (2 * n) * ‖schurPathTerm φ n lam hlam (2 * j + 2) false true‖ ≤ _
    rw [h4]
    refine h3.trans (h2.trans ?_)
    rw [shifted_norm_V_upper]

theorem tsum_geom_bound (f : ℕ → ℂ) (q K W : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2)
    (hK : 0 ≤ K) (hW : 0 < W) (h : ∀ j : ℕ, W * ‖f j‖ ≤ q ^ (j + 1) * K) :
    W * ‖∑' j : ℕ, f j‖ ≤ 2 * q * K := by
  have hq1 : q < 1 := by linarith
  have hHas : HasSum (fun j : ℕ => (q * K / W) * q ^ j) ((q * K / W) * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left _
  have hpt : ∀ j : ℕ, ‖f j‖ ≤ (q * K / W) * q ^ j := by
    intro j
    have h1 := h j
    have h2 : ‖f j‖ ≤ q ^ (j + 1) * K / W := by
      rw [le_div_iff₀ hW]
      linarith
    calc ‖f j‖ ≤ q ^ (j + 1) * K / W := h2
      _ = (q * K / W) * q ^ j := by ring
  have hn := tsum_of_norm_bounded hHas hpt
  have hinv : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hqK : 0 ≤ q * K / W := by positivity
  calc W * ‖∑' j : ℕ, f j‖ ≤ W * ((q * K / W) * (1 - q)⁻¹) :=
        mul_le_mul_of_nonneg_left hn hW.le
    _ = q * K * (1 - q)⁻¹ := by field_simp
    _ ≤ q * K * 2 := mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 2 * q * K := by ring

theorem even_remainder_bound (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair) (hφ : potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ) (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hthreshold : 8 * potentialCoefficientNorm w φ ^ 2 ≤ indexWeight n) (plus : Bool) :
    w (2 * n) * ‖schurEvenRemainder φ n lam hlam plus‖ ≤
      8 * potentialCoefficientNorm w φ ^ 2 *
        NlsGge.ThirdConsultation.M.componentNorm w φ plus / indexWeight n := by
  have hρ : 0 < indexWeight n := NlsGge.ThirdConsultation.MTwoModeW.indexWeight_pos n
  have hq0 : 0 ≤ 4 * potentialCoefficientNorm w φ ^ 2 / indexWeight n :=
    div_nonneg (by positivity) hρ.le
  have hq : 4 * potentialCoefficientNorm w φ ^ 2 / indexWeight n ≤ 1 / 2 := by
    rw [div_le_iff₀ hρ]
    linarith
  have hK : 0 ≤ NlsGge.ThirdConsultation.M.componentNorm w φ plus := Real.sqrt_nonneg _
  have hW : 0 < w (2 * n) := weight_pos w hw _
  have key := tsum_geom_bound
    (fun j : ℕ => schurPathTerm φ n lam hlam (2 * j + 2)
      (if plus then false else true) (if plus then true else false))
    (4 * potentialCoefficientNorm w φ ^ 2 / indexWeight n)
    (NlsGge.ThirdConsultation.M.componentNorm w φ plus) (w (2 * n)) hq0 hq hK hW
    (fun j => even_term_le w hw φ hφ n lam hlam plus j)
  have hE : schurEvenRemainder φ n lam hlam plus =
      ∑' j : ℕ, schurPathTerm φ n lam hlam (2 * j + 2)
        (if plus then false else true) (if plus then true else false) := by
    cases plus <;> rfl
  rw [hE]
  refine key.trans (le_of_eq ?_)
  ring

end NlsGge.ThirdConsultation.MTwoModeB

end
