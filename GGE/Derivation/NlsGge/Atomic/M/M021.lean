import NlsGge.ThirdConsultation.M.M021Host
import NlsGge.ThirdConsultation.M.M021Comp

/-!
# M-021 production (proof development, author; not self-reviewed)

Section-8 declarations of Pro rounds 7-8 (M-021): the kernel identity for the
pair operator. Target `NlsGge/Atomic/M/M021.lean` after landing (namespace
NlsGge.ThirdConsultation.MTwoMode, as M-020).
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Schur
open NlsGge.Analysis
open NlsGge.Atomic.KST003 NlsGge.Atomic.KST004
open NlsGge.ThirdConsultation.MTwoMode.Comp21

namespace NlsGge.ThirdConsultation.MTwoMode
noncomputable section

/-- The coefficient kernel of the pair operator `T`, componentwise. The identity
is an unconditional tsum identity, inherited from the production coefficient
formulas `qOperator_upper_coeff` and `qOperator_lower_coeff` (no summability
hypothesis is added). -/
theorem Tcoeff_eq_kernel
    (φ : PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (f : KSTPairL2) (b : Bool) (k : ℤ) :
  Tcoeff φ n lam hlam f b k =
    ∑' l : ℤ, potentialCoefficientPair φ b (k-l) *
      (NlsGge.Atomic.KST004.complementaryResolventCoeff
        n lam (if b then l else -l) * coefficientPair f (!b) l) := by
  cases b
  · have h := NlsGge.Atomic.KST006.qOperator_lower_coeff
      (WithLp.toLp 2 (fun b : Bool => if b then φ.1 else φ.2)) n lam hlam f k
    have hr : ∀ (g : SpectralScalarL2) (j : ℤ),
        (fourierBasis (T := (2 : ℝ))).repr g j = fourierCoeff g j :=
      fun g j => fourierBasis_repr g j
    simp only [hr] at h
    simp only [Tcoeff, T, coefficientPair, potentialCoefficientPair]
    rw [h]
    simp
  · have h := NlsGge.Atomic.KST006.qOperator_upper_coeff
      (WithLp.toLp 2 (fun b : Bool => if b then φ.1 else φ.2)) n lam hlam f k
    have hr : ∀ (g : SpectralScalarL2) (j : ℤ),
        (fourierBasis (T := (2 : ℝ))).repr g j = fourierCoeff g j :=
      fun g j => fourierBasis_repr g j
    simp only [hr] at h
    simp only [Tcoeff, T, coefficientPair, potentialCoefficientPair]
    rw [h]
    simp


theorem tsum_ofReal_add_split (X Y : ℤ → ℝ) (hX : ∀ k, 0 ≤ X k) (hY : ∀ k, 0 ≤ Y k) :
    ∑' k : ℤ, ENNReal.ofReal (X k + Y k) =
      (∑' k : ℤ, ENNReal.ofReal (X k)) + ∑' k : ℤ, ENNReal.ofReal (Y k) := by
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun k => ENNReal.ofReal_add (hX k) (hY k)

theorem ennreal_mix (Pa Pb Ea Eb : ℝ≥0∞) :
    4 * Pa * Eb + 4 * Pb * Ea ≤ 4 * (Pa + Pb) * (Ea + Eb) := by
  have key : 4 * (Pa + Pb) * (Ea + Eb) =
      (4 * Pa * Eb + 4 * Pb * Ea) + (4 * Pa * Ea + 4 * Pb * Eb) := by ring
  rw [key]
  exact le_self_add

theorem potentialCoefficientEnergy_eq (w : ℤ → ℝ) (φ : PotPair) :
    potentialCoefficientEnergy w φ =
      (∑' k : ℤ, ENNReal.ofReal (w k ^ 2 * ‖potentialCoefficientPair φ true k‖ ^ 2)) +
        ∑' k : ℤ, ENNReal.ofReal (w k ^ 2 * ‖potentialCoefficientPair φ false k‖ ^ 2) := by
  rw [← ENNReal.tsum_add]
  unfold potentialCoefficientEnergy
  exact tsum_congr fun k => by
    have h1 : 0 ≤ w k ^ 2 * ‖potentialCoefficientPair φ true k‖ ^ 2 := by positivity
    have h2 : 0 ≤ w k ^ 2 * ‖potentialCoefficientPair φ false k‖ ^ 2 := by positivity
    rw [← ENNReal.ofReal_add h1 h2]
    congr 1
    ring

/-- Main estimate for an explicit shift `s` (the upper output uses `s`, the lower `-s`). -/
theorem main_bound
    (w : ℤ → ℝ) (hw : ∀ k : ℤ, 1 ≤ w k)
    (hwmul : NlsGge.Atomic.DM046.SubmultiplicativeWeight w)
    (φ : PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (s : ℤ) (f : KSTPairL2)
    (hφ : potentialCoefficientEnergy w φ ≠ ⊤)
    (hf : ∑' k : ℤ, ENNReal.ofReal (w (k + -s) ^ 2 * ‖coefficientPair f true k‖ ^ 2 +
        w (k + s) ^ 2 * ‖coefficientPair f false k‖ ^ 2) ≠ ⊤) :
    ∑' k : ℤ, ENNReal.ofReal (w (k + s) ^ 2 * ‖Tcoeff φ n lam hlam f true k‖ ^ 2 +
        w (k + -s) ^ 2 * ‖Tcoeff φ n lam hlam f false k‖ ^ 2) ≤
      4 * potentialCoefficientEnergy w φ *
        ∑' k : ℤ, ENNReal.ofReal (w (k + -s) ^ 2 * ‖coefficientPair f true k‖ ^ 2 +
          w (k + s) ^ 2 * ‖coefficientPair f false k‖ ^ 2) := by
  have hU : ∀ k : ℤ, Tcoeff φ n lam hlam f true k =
      ∑' l : ℤ, potentialCoefficientPair φ true (k - l) *
        (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam l *
          coefficientPair f false l) := by
    intro k
    rw [Tcoeff_eq_kernel]
    simp
  have hV : ∀ k : ℤ, Tcoeff φ n lam hlam f false k =
      ∑' l : ℤ, potentialCoefficientPair φ false (k - l) *
        (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-l) *
          coefficientPair f true l) := by
    intro k
    rw [Tcoeff_eq_kernel]
    simp
  have hP_split := potentialCoefficientEnergy_eq w φ
  have hPa_ne : ∑' k : ℤ, ENNReal.ofReal (w k ^ 2 * ‖potentialCoefficientPair φ true k‖ ^ 2) ≠ ⊤ :=
    fun h => hφ (by rw [hP_split, h, top_add])
  have hPb_ne : ∑' k : ℤ, ENNReal.ofReal (w k ^ 2 * ‖potentialCoefficientPair φ false k‖ ^ 2) ≠ ⊤ :=
    fun h => hφ (by rw [hP_split, h, add_top])
  have hEin_split := tsum_ofReal_add_split
    (fun k => w (k + -s) ^ 2 * ‖coefficientPair f true k‖ ^ 2)
    (fun k => w (k + s) ^ 2 * ‖coefficientPair f false k‖ ^ 2)
    (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hEv_ne : ∑' k : ℤ, ENNReal.ofReal (w (k + s) ^ 2 * ‖coefficientPair f false k‖ ^ 2) ≠ ⊤ :=
    fun h => hf (by rw [hEin_split, h, add_top])
  have hEu_ne : ∑' k : ℤ, ENNReal.ofReal (w (k + -s) ^ 2 * ‖coefficientPair f true k‖ ^ 2) ≠ ⊤ :=
    fun h => hf (by rw [hEin_split, h, top_add])
  have hD := D_facts n lam hlam
  have hDn := D_facts_neg n lam hlam
  have hUb := comp_bound w hw hwmul s (potentialCoefficientPair φ true)
    (coefficientPair f false) (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam)
    hD.1 hD.2.1 hD.2.2 hPa_ne hEv_ne
  have hVb := comp_bound w hw hwmul (-s) (potentialCoefficientPair φ false)
    (coefficientPair f true) (fun l => NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-l))
    hDn.1 hDn.2.1 hDn.2.2 hPb_ne hEu_ne
  simp only [hU, hV]
  rw [tsum_ofReal_add_split
    (fun k => w (k + s) ^ 2 * ‖∑' l : ℤ, potentialCoefficientPair φ true (k - l) *
      (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam l * coefficientPair f false l)‖ ^ 2)
    (fun k => w (k + -s) ^ 2 * ‖∑' l : ℤ, potentialCoefficientPair φ false (k - l) *
      (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-l) * coefficientPair f true l)‖ ^ 2)
    (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)) ]
  rw [hP_split, hEin_split]
  calc _ ≤ 4 * (∑' k : ℤ, ENNReal.ofReal (w k ^ 2 * ‖potentialCoefficientPair φ true k‖ ^ 2)) *
          (∑' k : ℤ, ENNReal.ofReal (w (k + s) ^ 2 * ‖coefficientPair f false k‖ ^ 2)) +
        4 * (∑' k : ℤ, ENNReal.ofReal (w k ^ 2 * ‖potentialCoefficientPair φ false k‖ ^ 2)) *
          (∑' k : ℤ, ENNReal.ofReal (w (k + -s) ^ 2 * ‖coefficientPair f true k‖ ^ 2)) := add_le_add hUb hVb
    _ ≤ _ := ennreal_mix _ _ _ _

/-- Section-8 head (Pro rounds 7-8, M-021), with the lexical `open NlsGge.Analysis` only. -/
theorem T_shifted_bound
    (w : ℤ → ℝ) (hw : ∀ k : ℤ, 1 ≤ w k)
    (hwmul : NlsGge.Atomic.DM046.SubmultiplicativeWeight w)
    (φ : PotPair)
    (hφ : potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (i : Bool) (f : KSTPairL2)
    (hf : shiftedPairEnergy w n (!i) (coefficientPair f) ≠ ⊤) :
  shiftedPairEnergy w n i (Tcoeff φ n lam hlam f) ≠ ⊤ ∧
  shiftedPairNorm w n i (Tcoeff φ n lam hlam f) ≤
    2 * potentialCoefficientNorm w φ *
      shiftedPairNorm w n (!i) (coefficientPair f) := by
  obtain ⟨s, hs_i, hs_b⟩ : ∃ s : ℤ, (if i then n else -n) = s ∧
      (if (!i) then n else -n) = -s :=
    ⟨if i then n else -n, rfl, by cases i <;> simp⟩
  have hE_out : shiftedPairEnergy w n i (Tcoeff φ n lam hlam f) =
      ∑' k : ℤ, ENNReal.ofReal (w (k + s) ^ 2 * ‖Tcoeff φ n lam hlam f true k‖ ^ 2 +
        w (k + -s) ^ 2 * ‖Tcoeff φ n lam hlam f false k‖ ^ 2) := by
    simp only [shiftedPairEnergy, hs_i, sub_eq_add_neg]
  have hE_in : shiftedPairEnergy w n (!i) (coefficientPair f) =
      ∑' k : ℤ, ENNReal.ofReal (w (k + -s) ^ 2 * ‖coefficientPair f true k‖ ^ 2 +
        w (k + s) ^ 2 * ‖coefficientPair f false k‖ ^ 2) := by
    simp only [shiftedPairEnergy, hs_b, sub_neg_eq_add]
  have hf' : ∑' k : ℤ, ENNReal.ofReal (w (k + -s) ^ 2 * ‖coefficientPair f true k‖ ^ 2 +
        w (k + s) ^ 2 * ‖coefficientPair f false k‖ ^ 2) ≠ ⊤ := by
    rw [← hE_in]
    exact hf
  have hmain := main_bound w hw hwmul φ n lam hlam s f hφ hf'
  rw [← hE_out] at hmain
  rw [← hE_in] at hmain
  have hP_ne : potentialCoefficientEnergy w φ ≠ ⊤ := hφ
  have h4PE_ne : 4 * potentialCoefficientEnergy w φ * shiftedPairEnergy w n (!i) (coefficientPair f) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hP_ne) hf
  have hout_le : shiftedPairEnergy w n i (Tcoeff φ n lam hlam f) ≤
      4 * potentialCoefficientEnergy w φ * shiftedPairEnergy w n (!i) (coefficientPair f) :=
    hmain
  have hout_ne : shiftedPairEnergy w n i (Tcoeff φ n lam hlam f) ≠ ⊤ :=
    ne_top_of_le_ne_top h4PE_ne hout_le
  refine ⟨hout_ne, ?_⟩
  have hreal : (shiftedPairEnergy w n i (Tcoeff φ n lam hlam f)).toReal ≤
      4 * (potentialCoefficientEnergy w φ).toReal *
        (shiftedPairEnergy w n (!i) (coefficientPair f)).toReal := by
    have h1 := ENNReal.toReal_mono h4PE_ne hout_le
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofNat] at h1
    exact h1
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  calc shiftedPairNorm w n i (Tcoeff φ n lam hlam f)
      = Real.sqrt (shiftedPairEnergy w n i (Tcoeff φ n lam hlam f)).toReal := rfl
    _ ≤ Real.sqrt (4 * (potentialCoefficientEnergy w φ).toReal *
          (shiftedPairEnergy w n (!i) (coefficientPair f)).toReal) :=
        Real.sqrt_le_sqrt hreal
    _ = Real.sqrt (4 * (potentialCoefficientEnergy w φ).toReal) *
          Real.sqrt (shiftedPairEnergy w n (!i) (coefficientPair f)).toReal :=
        Real.sqrt_mul (by positivity) _
    _ = 2 * Real.sqrt (potentialCoefficientEnergy w φ).toReal *
          Real.sqrt (shiftedPairEnergy w n (!i) (coefficientPair f)).toReal := by
        rw [Real.sqrt_mul (by norm_num), h4]
    _ = 2 * potentialCoefficientNorm w φ *
          shiftedPairNorm w n (!i) (coefficientPair f) := rfl

end
end NlsGge.ThirdConsultation.MTwoMode
