import Mathlib
import NlsGge.Atomic.M.M021
import NlsGge.Atomic.KST.KST004
import NlsGge.ThirdConsultation.M.M022Host
import NlsGge.ThirdConsultation.M.M022Chain2

                                                                                                      
                                                                                                     
                                                                                  

set_option autoImplicit false

open scoped ENNReal

namespace NlsGge.ThirdConsultation.M
noncomputable section

theorem cr_bound_gen (n : ℤ) (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (m t : ℤ) (ht : t = m - n ∨ t = n - m) :
    ‖NlsGge.Atomic.KST004.complementaryResolventCoeff n lam m‖ ≤
      if t = 0 then 0 else 1 / |((t : ℤ) : ℝ)| := by
  by_cases h0 : t = 0
  · have hm : m = n := by rcases ht with h | h <;> omega
    rw [if_pos h0, hm]
    simp [NlsGge.Atomic.KST004.complementaryResolventCoeff]
  · rw [if_neg h0]
    have hb := NlsGge.Atomic.KST004.complementaryResolventCoeff_bound n m lam hlam
    have habs : |((t : ℤ) : ℝ)| = ((m - n).natAbs : ℝ) := by
      rcases ht with h | h
      · rw [h, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
      · rw [h, ← Int.cast_abs, abs_sub_comm, Int.abs_eq_natAbs, Int.cast_natCast]
    rw [habs]
    exact hb

theorem final_real (R Pt Pf E ρ : ℝ) (hR : 0 ≤ R) (hPt : 0 ≤ Pt) (hPf : 0 ≤ Pf) (hE : 0 ≤ E)
    (hρ : 0 < ρ) (hle : R ≤ 16 / ρ ^ 2 * Pt * Pf * E) :
    Real.sqrt R ≤ 4 * (Pt + Pf) / ρ * Real.sqrt E := by
  have hT0 : 0 ≤ 4 * (Pt + Pf) / ρ * Real.sqrt E := by positivity
  have hT2 : (4 * (Pt + Pf) / ρ * Real.sqrt E) ^ 2 = 16 / ρ ^ 2 * (Pt + Pf) ^ 2 * E := by
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hE]
    ring
  have hPP : Pt * Pf ≤ (Pt + Pf) ^ 2 := by
    nlinarith [sq_nonneg (Pt - Pf), mul_nonneg hPt hPf]
  have hc : 0 ≤ 16 / ρ ^ 2 * E := by positivity
  have hR2 : R ≤ (4 * (Pt + Pf) / ρ * Real.sqrt E) ^ 2 := by
    rw [hT2]
    calc R ≤ 16 / ρ ^ 2 * Pt * Pf * E := hle
      _ = (16 / ρ ^ 2 * E) * (Pt * Pf) := by ring
      _ ≤ (16 / ρ ^ 2 * E) * (Pt + Pf) ^ 2 := mul_le_mul_of_nonneg_left hPP hc
      _ = 16 / ρ ^ 2 * (Pt + Pf) ^ 2 * E := by ring
  calc Real.sqrt R ≤ Real.sqrt ((4 * (Pt + Pf) / ρ * Real.sqrt E) ^ 2) := Real.sqrt_le_sqrt hR2
    _ = 4 * (Pt + Pf) / ρ * Real.sqrt E := Real.sqrt_sq hT0

theorem split_finite (X Y : ℤ → ℝ) (hX : ∀ k, 0 ≤ X k) (hY : ∀ k, 0 ≤ Y k)
    (h : ∑' k, ENNReal.ofReal (X k + Y k) ≠ ⊤) : Summable X ∧ Summable Y := by
  rw [NlsGge.ThirdConsultation.MTwoMode.tsum_ofReal_add_split X Y hX hY] at h
  constructor
  · exact NlsGge.ThirdConsultation.MTwoMode.Real21.summable_of_ofReal_tsum_ne_top X hX
      (fun h' => h (by rw [h', top_add]))
  · exact NlsGge.ThirdConsultation.MTwoMode.Real21.summable_of_ofReal_tsum_ne_top Y hY
      (fun h' => h (by rw [h', add_top]))

open NlsGge.ThirdConsultation.MTwoMode in
theorem shifted_split_eq (w : ℤ → ℝ) (n : ℤ)
    (f : NlsGge.ThirdConsultation.MTwoMode.CoefficientPair)
    (hX : Summable fun k : ℤ => w (k + -n) ^ 2 * ‖f true k‖ ^ 2)
    (hY : Summable fun k : ℤ => w (k - -n) ^ 2 * ‖f false k‖ ^ 2) :
    NlsGge.ThirdConsultation.MTwoMode.shiftedPairEnergy w n false f =
      ENNReal.ofReal (∑' k : ℤ, w (k + -n) ^ 2 * ‖f true k‖ ^ 2) +
        ENNReal.ofReal (∑' k : ℤ, w (k - -n) ^ 2 * ‖f false k‖ ^ 2) := by
  have h0 : ∀ k : ℤ, 0 ≤ w (k + -n) ^ 2 * ‖f true k‖ ^ 2 :=
    fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h1 : ∀ k : ℤ, 0 ≤ w (k - -n) ^ 2 * ‖f false k‖ ^ 2 :=
    fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [ENNReal.ofReal_tsum_of_nonneg h0 hX, ENNReal.ofReal_tsum_of_nonneg h1 hY]
  unfold NlsGge.ThirdConsultation.MTwoMode.shiftedPairEnergy
  exact NlsGge.ThirdConsultation.MTwoMode.tsum_ofReal_add_split _ _ h0 h1

open NlsGge.ThirdConsultation.MTwoMode NlsGge.Atomic.M.M054 in
theorem T_squared_bound
    (w : ℤ → ℝ) (hw : OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair)
    (hφ : NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy
      w φ ≠ ⊤)
    (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (f : NlsGge.Atomic.KST003.KSTPairL2)
    (hf : NlsGge.ThirdConsultation.MTwoMode.shiftedPairEnergy
      w n false
      (NlsGge.ThirdConsultation.MTwoMode.coefficientPair f) ≠ ⊤) :
    NlsGge.ThirdConsultation.MTwoMode.shiftedPairEnergy
      w n false
      (NlsGge.ThirdConsultation.MTwoMode.coefficientPair
        (NlsGge.ThirdConsultation.MTwoMode.T φ n lam hlam
          (NlsGge.ThirdConsultation.MTwoMode.T φ n lam hlam f))) ≠ ⊤ ∧
    NlsGge.ThirdConsultation.MTwoMode.shiftedPairNorm
      w n false
      (NlsGge.ThirdConsultation.MTwoMode.coefficientPair
        (NlsGge.ThirdConsultation.MTwoMode.T φ n lam hlam
          (NlsGge.ThirdConsultation.MTwoMode.T φ n lam hlam f))) ≤
      (4 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm
        w φ ^ 2 / NlsGge.Atomic.M.M054.indexWeight n) *
      NlsGge.ThirdConsultation.MTwoMode.shiftedPairNorm
        w n false
        (NlsGge.ThirdConsultation.MTwoMode.coefficientPair f) := by
  obtain ⟨v, hv1, heven, hsub, hwv⟩ := hw
  have hPtnn : ∀ (b : Bool) (j : ℤ), 0 ≤ w j ^ 2 * ‖potentialCoefficientPair φ b j‖ ^ 2 :=
    fun b j => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- finiteness of the potential energy splits (ENNReal, before any toReal)
  have hEφ := potentialCoefficientEnergy_eq w φ
  have hPt_ne : ∑' k : ℤ, ENNReal.ofReal (w k ^ 2 * ‖potentialCoefficientPair φ true k‖ ^ 2) ≠ ⊤ :=
    fun h => hφ (by rw [hEφ, h, top_add])
  have hPf_ne : ∑' k : ℤ, ENNReal.ofReal (w k ^ 2 * ‖potentialCoefficientPair φ false k‖ ^ 2) ≠ ⊤ :=
    fun h => hφ (by rw [hEφ, h, add_top])
  have hPo : Summable fun j : ℤ => w j ^ 2 * ‖potentialCoefficientPair φ true j‖ ^ 2 :=
    NlsGge.ThirdConsultation.MTwoMode.Real21.summable_of_ofReal_tsum_ne_top
      (fun j => w j ^ 2 * ‖potentialCoefficientPair φ true j‖ ^ 2) (hPtnn true) hPt_ne
  have hPf : Summable fun j : ℤ => w j ^ 2 * ‖potentialCoefficientPair φ false j‖ ^ 2 :=
    NlsGge.ThirdConsultation.MTwoMode.Real21.summable_of_ofReal_tsum_ne_top
      (fun j => w j ^ 2 * ‖potentialCoefficientPair φ false j‖ ^ 2) (hPtnn false) hPf_ne
  -- finiteness of the input energy split
  obtain ⟨hXt, hYf⟩ := split_finite
    (fun k => w (k + -n) ^ 2 * ‖coefficientPair f true k‖ ^ 2)
    (fun k => w (k - -n) ^ 2 * ‖coefficientPair f false k‖ ^ 2)
    (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hf
  have hYf' : Summable fun l : ℤ => w (l + n) ^ 2 * ‖coefficientPair f false l‖ ^ 2 :=
    hYf.congr fun l => by rw [sub_neg_eq_add]
  -- the two chain applications (upper: shift -n, lower: shift n)
  have hαU : ∀ m : ℤ, ‖NlsGge.Atomic.KST004.complementaryResolventCoeff n lam m‖ ≤
      if m + -n = 0 then 0 else 1 / |((m + -n : ℤ) : ℝ)| :=
    fun m => cr_bound_gen n lam hlam m (m + -n) (Or.inl (by ring))
  have hβU : ∀ l : ℤ, ‖NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-l)‖ ≤
      if l - -n = 0 then 0 else 1 / |((l - -n : ℤ) : ℝ)| :=
    fun l => cr_bound_gen n lam hlam (-l) (l - -n) (Or.inr (by ring))
  have hαL : ∀ m : ℤ, ‖NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-m)‖ ≤
      if m + n = 0 then 0 else 1 / |((m + n : ℤ) : ℝ)| :=
    fun m => cr_bound_gen n lam hlam (-m) (m + n) (Or.inr (by ring))
  have hβL : ∀ l : ℤ, ‖NlsGge.Atomic.KST004.complementaryResolventCoeff n lam l‖ ≤
      if l - n = 0 then 0 else 1 / |((l - n : ℤ) : ℝ)| :=
    fun l => cr_bound_gen n lam hlam l (l - n) (Or.inl rfl)
  have hU := NlsGge.ThirdConsultation.M.M022.chain_bound w v hwv hv1 heven hsub (-n)
    (potentialCoefficientPair φ true) (potentialCoefficientPair φ false)
    (coefficientPair f true)
    (fun m => NlsGge.Atomic.KST004.complementaryResolventCoeff n lam m)
    (fun l => NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-l))
    hαU hβU hPo hPf hXt
  have hL := NlsGge.ThirdConsultation.M.M022.chain_bound w v hwv hv1 heven hsub n
    (potentialCoefficientPair φ false) (potentialCoefficientPair φ true)
    (coefficientPair f false)
    (fun m => NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-m))
    (fun l => NlsGge.Atomic.KST004.complementaryResolventCoeff n lam l)
    hαL hβL hPf hPo hYf'
  -- coefficient identities for T(T f) from Tcoeff_eq_kernel
  have hHt : ∀ k : ℤ, coefficientPair (T φ n lam hlam (T φ n lam hlam f)) true k =
      ∑' m : ℤ, potentialCoefficientPair φ true (k - m) *
        (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam m *
          ∑' l : ℤ, potentialCoefficientPair φ false (m - l) *
            (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-l) * coefficientPair f true l)) := by
    intro k
    refine (Tcoeff_eq_kernel φ n lam hlam (T φ n lam hlam f) true k).trans (tsum_congr fun m => ?_)
    congr 1
    have e : coefficientPair (T φ n lam hlam f) false m =
        ∑' l : ℤ, potentialCoefficientPair φ false (m - l) *
          (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-l) * coefficientPair f true l) :=
      Tcoeff_eq_kernel φ n lam hlam f false m
    simp [e]
  have hHf : ∀ k : ℤ, coefficientPair (T φ n lam hlam (T φ n lam hlam f)) false k =
      ∑' m : ℤ, potentialCoefficientPair φ false (k - m) *
        (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-m) *
          ∑' l : ℤ, potentialCoefficientPair φ true (m - l) *
            (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam l * coefficientPair f false l)) := by
    intro k
    refine (Tcoeff_eq_kernel φ n lam hlam (T φ n lam hlam f) false k).trans (tsum_congr fun m => ?_)
    congr 1
    have e : coefficientPair (T φ n lam hlam f) true m =
        ∑' l : ℤ, potentialCoefficientPair φ true (m - l) *
          (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam l * coefficientPair f false l) :=
      Tcoeff_eq_kernel φ n lam hlam f true m
    simp [e]
  -- summability of the output components
  have hXo : Summable fun k : ℤ =>
      w (k + -n) ^ 2 * ‖coefficientPair (T φ n lam hlam (T φ n lam hlam f)) true k‖ ^ 2 :=
    hU.1.congr fun k => by rw [hHt k, mul_pow]
  have hYo : Summable fun k : ℤ =>
      w (k - -n) ^ 2 * ‖coefficientPair (T φ n lam hlam (T φ n lam hlam f)) false k‖ ^ 2 :=
    hL.1.congr fun k => by rw [sub_neg_eq_add, hHf k, mul_pow]
  -- real abbreviations
  obtain ⟨Pt, hPt⟩ : ∃ P : ℝ, P = ∑' j : ℤ, w j ^ 2 * ‖potentialCoefficientPair φ true j‖ ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨Pf, hPf'⟩ : ∃ P : ℝ, P = ∑' j : ℤ, w j ^ 2 * ‖potentialCoefficientPair φ false j‖ ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨Et, hEt⟩ : ∃ E : ℝ, E = ∑' l : ℤ, w (l + -n) ^ 2 * ‖coefficientPair f true l‖ ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨Ef, hEf⟩ : ∃ E : ℝ, E = ∑' l : ℤ, w (l + n) ^ 2 * ‖coefficientPair f false l‖ ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨Xs, hXs⟩ : ∃ R : ℝ, R = ∑' k : ℤ,
      w (k + -n) ^ 2 * ‖coefficientPair (T φ n lam hlam (T φ n lam hlam f)) true k‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Ys, hYs⟩ : ∃ R : ℝ, R = ∑' k : ℤ,
      w (k - -n) ^ 2 * ‖coefficientPair (T φ n lam hlam (T φ n lam hlam f)) false k‖ ^ 2 := ⟨_, rfl⟩
  have hPt0 : 0 ≤ Pt := by rw [hPt]; exact tsum_nonneg (hPtnn true)
  have hPf0 : 0 ≤ Pf := by rw [hPf']; exact tsum_nonneg (hPtnn false)
  have hEt0 : 0 ≤ Et := by rw [hEt]; exact tsum_nonneg fun l => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hEf0 : 0 ≤ Ef := by rw [hEf]; exact tsum_nonneg fun l => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hXs0 : 0 ≤ Xs := by rw [hXs]; exact tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hYs0 : 0 ≤ Ys := by rw [hYs]; exact tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  -- chain bounds in the squared-sum form
  have hUb : Xs ≤ 16 / (1 + |((-n : ℤ) : ℝ)|) ^ 2 * Pt * Pf * Et := by
    rw [hXs, hPt, hPf', hEt]
    calc ∑' k : ℤ, w (k + -n) ^ 2 * ‖coefficientPair (T φ n lam hlam (T φ n lam hlam f)) true k‖ ^ 2
        = ∑' k : ℤ, (w (k + -n) * ‖∑' m : ℤ, potentialCoefficientPair φ true (k - m) *
            (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam m *
              ∑' l : ℤ, potentialCoefficientPair φ false (m - l) *
                (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-l) *
                  coefficientPair f true l))‖) ^ 2 :=
          tsum_congr fun k => by rw [hHt k, mul_pow]
      _ ≤ _ := hU.2
  have hLb : Ys ≤ 16 / (1 + |((n : ℤ) : ℝ)|) ^ 2 * Pf * Pt * Ef := by
    rw [hYs, hPt, hPf', hEf]
    calc ∑' k : ℤ, w (k - -n) ^ 2 * ‖coefficientPair (T φ n lam hlam (T φ n lam hlam f)) false k‖ ^ 2
        = ∑' k : ℤ, (w (k + n) * ‖∑' m : ℤ, potentialCoefficientPair φ false (k - m) *
            (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-m) *
              ∑' l : ℤ, potentialCoefficientPair φ true (m - l) *
                (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam l *
                  coefficientPair f false l))‖) ^ 2 :=
          tsum_congr fun k => by rw [sub_neg_eq_add, hHf k, mul_pow]
      _ ≤ _ := hL.2
  -- combine: Xs + Ys <= (16/rho^2) Pt Pf (Et + Ef)
  have hρdef : indexWeight n = 1 + |((n : ℤ) : ℝ)| := rfl
  have hρpos : 0 < indexWeight n := by
    rw [hρdef]
    positivity
  have hc_eq : (16 : ℝ) / (1 + |((-n : ℤ) : ℝ)|) ^ 2 = 16 / (1 + |((n : ℤ) : ℝ)|) ^ 2 := by
    rw [Int.cast_neg, abs_neg]
  rw [hc_eq] at hUb
  have hle : Xs + Ys ≤ 16 / indexWeight n ^ 2 * Pt * Pf * (Et + Ef) := by
    rw [hρdef]
    have e : 16 / (1 + |((n : ℤ) : ℝ)|) ^ 2 * Pt * Pf * (Et + Ef) =
        16 / (1 + |((n : ℤ) : ℝ)|) ^ 2 * Pt * Pf * Et + 16 / (1 + |((n : ℤ) : ℝ)|) ^ 2 * Pf * Pt * Ef := by
      ring
    rw [e]
    linarith
  -- energies: finite, split, then toReal
  have hEo : NlsGge.ThirdConsultation.MTwoMode.shiftedPairEnergy w n false
      (coefficientPair (T φ n lam hlam (T φ n lam hlam f))) = ENNReal.ofReal (Xs + Ys) := by
    rw [shifted_split_eq w n (coefficientPair (T φ n lam hlam (T φ n lam hlam f))) hXo hYo,
      hXs, hYs, ← ENNReal.ofReal_add (tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hEin : NlsGge.ThirdConsultation.MTwoMode.shiftedPairEnergy w n false
      (coefficientPair f) = ENNReal.ofReal (Et + Ef) := by
    have hEf2 : ∑' k : ℤ, w (k - -n) ^ 2 * ‖coefficientPair f false k‖ ^ 2 = Ef := by
      rw [hEf]
      exact tsum_congr fun l => by rw [sub_neg_eq_add]
    rw [shifted_split_eq w n (coefficientPair f) hXt hYf, ← hEt, hEf2,
      ← ENNReal.ofReal_add hEt0 hEf0]
  have hNout : NlsGge.ThirdConsultation.MTwoMode.shiftedPairNorm w n false
      (coefficientPair (T φ n lam hlam (T φ n lam hlam f))) = Real.sqrt (Xs + Ys) := by
    unfold NlsGge.ThirdConsultation.MTwoMode.shiftedPairNorm
    rw [hEo, ENNReal.toReal_ofReal (add_nonneg hXs0 hYs0)]
  have hNin : NlsGge.ThirdConsultation.MTwoMode.shiftedPairNorm w n false
      (coefficientPair f) = Real.sqrt (Et + Ef) := by
    unfold NlsGge.ThirdConsultation.MTwoMode.shiftedPairNorm
    rw [hEin, ENNReal.toReal_ofReal (add_nonneg hEt0 hEf0)]
  have hEφ' : NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w φ =
      ENNReal.ofReal (Pt + Pf) := by
    have hA : ∑' k : ℤ, ENNReal.ofReal (w k ^ 2 * ‖potentialCoefficientPair φ true k‖ ^ 2) =
        ENNReal.ofReal Pt := by
      rw [hPt, ENNReal.ofReal_tsum_of_nonneg (hPtnn true) hPo]
    have hB : ∑' k : ℤ, ENNReal.ofReal (w k ^ 2 * ‖potentialCoefficientPair φ false k‖ ^ 2) =
        ENNReal.ofReal Pf := by
      rw [hPf', ENNReal.ofReal_tsum_of_nonneg (hPtnn false) hPf]
    rw [hEφ, hA, hB, ENNReal.ofReal_add hPt0 hPf0]
  have hNφ : NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ =
      Real.sqrt (Pt + Pf) := by
    unfold NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm
    rw [hEφ', ENNReal.toReal_ofReal (add_nonneg hPt0 hPf0)]
  refine ⟨?_, ?_⟩
  · rw [hEo]
    exact ENNReal.ofReal_ne_top
  · rw [hNout, hNin, hNφ, Real.sq_sqrt (add_nonneg hPt0 hPf0)]
    exact final_real (Xs + Ys) Pt Pf (Et + Ef) (indexWeight n)
      (add_nonneg hXs0 hYs0) hPt0 hPf0 (add_nonneg hEt0 hEf0) hρpos hle

end
end NlsGge.ThirdConsultation.M
