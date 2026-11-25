import Mathlib
import NlsGge.ThirdConsultation.M.MSchurBound

/-!
# MSchurDiag: the diagonal (odd) path bound (proof development, AUTHOR; not self-reviewed)

Support for M-027.  The odd path term is `<e_i, T (T^2)^j V e_i>`; its pairing with `T` is bounded by a
Cauchy-Schwarz estimate on the Fourier kernel of `T` using the complementary-resolvent bound
`|c(m)| <= 1/|t|` and the integer inequality `<n> <= |m + 2n| w(m)` (for `m + 2n != 0`).
The product `||phi_+||_w ||phi_-||_w <= ||phi||_w^2 / 2` then closes the constant 1 of the printed head.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace NlsGge.ThirdConsultation.MTwoModeB

open NlsGge.ThirdConsultation.MTwoMode NlsGge.Atomic.M.M054 NlsGge.Atomic.KST003

/-! ### the integer inequality -/

theorem key_ineq (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (m t n : ℤ) (ht : t = m + 2 * n) (h0 : t ≠ 0) :
    indexWeight n ≤ |((t : ℤ) : ℝ)| * w m := by
  have hint : 1 + |n| ≤ |t| * (1 + |m|) := by
    have h1 : 1 ≤ |t| := Int.one_le_abs h0
    by_cases hc : |n| ≤ |m|
    · calc 1 + |n| ≤ 1 + |m| := by linarith
        _ ≤ |t| * (1 + |m|) := le_mul_of_one_le_left (by positivity) h1
    · push_neg at hc
      have e : t - m = 2 * n := by rw [ht]; ring
      have h2 : |2 * n| ≤ |t| + |m| := by
        calc |2 * n| = |t - m| := by rw [e]
          _ ≤ |t| + |m| := abs_sub t m
      have h3 : |2 * n| = 2 * |n| := by rw [abs_mul]; norm_num
      have h5 : |m| + 1 ≤ |n| := Int.add_one_le_iff.mpr hc
      have h4 : 1 + |n| ≤ |t| := by linarith
      calc 1 + |n| ≤ |t| := h4
        _ = |t| * 1 := (mul_one _).symm
        _ ≤ |t| * (1 + |m|) := mul_le_mul_of_nonneg_left (by linarith [abs_nonneg m]) (abs_nonneg _)
  have hreal : (1 : ℝ) + |(n : ℝ)| ≤ |(t : ℝ)| * (1 + |(m : ℝ)|) := by exact_mod_cast hint
  have hwm : 1 + |(m : ℝ)| ≤ w m :=
    NlsGge.ThirdConsultation.MTwoModeW.indexWeight_le_of_oneDerivative w hw m
  unfold indexWeight
  exact hreal.trans (mul_le_mul_of_nonneg_left hwm (abs_nonneg _))

theorem indexWeight_neg' (n : ℤ) : indexWeight (-n) = indexWeight n := by
  unfold indexWeight
  push_cast
  rw [abs_neg]

/-! ### generic real-analysis steps -/

theorem sq_reindex (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (c : ℤ → ℂ) (hc : Summable fun j : ℤ => w j ^ 2 * ‖c j‖ ^ 2) (e : ℤ ≃ ℤ) :
    Summable (fun l : ℤ => ‖c (e l)‖ ^ 2) ∧
      ∑' l : ℤ, ‖c (e l)‖ ^ 2 ≤ ∑' j : ℤ, w j ^ 2 * ‖c j‖ ^ 2 := by
  have h1 : Summable fun l : ℤ => w (e l) ^ 2 * ‖c (e l)‖ ^ 2 :=
    (e.summable_iff (f := fun j : ℤ => w j ^ 2 * ‖c j‖ ^ 2)).2 hc
  have hle : ∀ l : ℤ, ‖c (e l)‖ ^ 2 ≤ w (e l) ^ 2 * ‖c (e l)‖ ^ 2 := fun l =>
    le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ (one_le_weight w hw _))
  have hs := Summable.of_nonneg_of_le (fun l => sq_nonneg _) hle h1
  refine ⟨hs, ?_⟩
  calc ∑' l : ℤ, ‖c (e l)‖ ^ 2 ≤ ∑' l : ℤ, w (e l) ^ 2 * ‖c (e l)‖ ^ 2 := hs.tsum_le_tsum hle h1
    _ = ∑' j : ℤ, w j ^ 2 * ‖c j‖ ^ 2 := e.tsum_eq (fun j : ℤ => w j ^ 2 * ‖c j‖ ^ 2)

theorem cs_pair (α β : ℤ → ℝ) (hα : ∀ l, 0 ≤ α l) (hβ : ∀ l, 0 ≤ β l) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hαs : Summable fun l => α l ^ 2) (hβs : Summable fun l => β l ^ 2)
    (hα2 : ∑' l, α l ^ 2 ≤ A ^ 2) (hβ2 : ∑' l, β l ^ 2 ≤ B ^ 2) :
    Summable (fun l => α l * β l) ∧ ∑' l, α l * β l ≤ A * B := by
  obtain ⟨hs, hle⟩ := NlsGge.ThirdConsultation.MTwoMode.Real21.cs_sq α β hα hβ hαs hβs
  refine ⟨hs, le_of_sq_le_sq' _ _ (mul_nonneg hA hB) ?_⟩
  calc (∑' l, α l * β l) ^ 2 ≤ (∑' l, α l ^ 2) * (∑' l, β l ^ 2) := hle
    _ ≤ A ^ 2 * B ^ 2 :=
        mul_le_mul hα2 hβ2 (tsum_nonneg fun l => sq_nonneg _) (sq_nonneg _)
    _ = (A * B) ^ 2 := by ring

theorem shifted_parts (w : ℤ → ℝ) (n : ℤ) (f : CoefficientPair)
    (hf : shiftedPairEnergy w n false f ≠ ⊤) :
    Summable (fun k : ℤ => w (k + -n) ^ 2 * ‖f true k‖ ^ 2) ∧
    Summable (fun k : ℤ => w (k - -n) ^ 2 * ‖f false k‖ ^ 2) ∧
    shiftedPairNorm w n false f ^ 2 =
      (∑' k : ℤ, w (k + -n) ^ 2 * ‖f true k‖ ^ 2) +
        ∑' k : ℤ, w (k - -n) ^ 2 * ‖f false k‖ ^ 2 := by
  obtain ⟨hXt, hYf⟩ := NlsGge.ThirdConsultation.M.split_finite
    (fun k => w (k + -n) ^ 2 * ‖f true k‖ ^ 2) (fun k => w (k - -n) ^ 2 * ‖f false k‖ ^ 2)
    (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hf
  refine ⟨hXt, hYf, ?_⟩
  have he := NlsGge.ThirdConsultation.M.shifted_split_eq w n f hXt hYf
  have hX0 : 0 ≤ ∑' k : ℤ, w (k + -n) ^ 2 * ‖f true k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hY0 : 0 ≤ ∑' k : ℤ, w (k - -n) ^ 2 * ‖f false k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  unfold shiftedPairNorm
  rw [he, ← ENNReal.ofReal_add hX0 hY0, ENNReal.toReal_ofReal (add_nonneg hX0 hY0),
    Real.sq_sqrt (add_nonneg hX0 hY0)]

/-! ### the pairing `<e_i, T g>` -/

theorem pair_false_le (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair) (hφ : potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ) (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (g : KSTPairL2) (hg : shiftedPairEnergy w n false (coefficientPair g) ≠ ⊤) :
    ‖inner ℂ (schurFrame n false : KSTPairL2) (ambientT φ n lam hlam g)‖ ≤
      NlsGge.ThirdConsultation.M.componentNorm w φ true / indexWeight n *
        shiftedPairNorm w n false (coefficientPair g) := by
  rw [inner_frame_false]
  have hρ : 0 < indexWeight n := NlsGge.ThirdConsultation.MTwoModeW.indexWeight_pos n
  have hc : coefficientPair (ambientT φ n lam hlam g) false n =
      ∑' l : ℤ, potentialCoefficientPair φ false (n - l) *
        (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-l) *
          coefficientPair g true l) :=
    Tcoeff_eq_kernel φ n lam hlam g false n
  rw [hc]
  obtain ⟨hXs, _, hN2⟩ := shifted_parts w n (coefficientPair g) hg
  have hY0 : 0 ≤ ∑' k : ℤ, w (k - -n) ^ 2 * ‖coefficientPair g false k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hG := compEnergy_summable w φ true (compEnergy_ne_top w φ hφ true)
  obtain ⟨hαs, hα2⟩ := sq_reindex w hw (fun j => fourierPotential φ true j) hG (Equiv.subLeft n)
  set N := shiftedPairNorm w n false (coefficientPair g) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  set A := NlsGge.ThirdConsultation.M.componentNorm w φ true with hA
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hA2 : A ^ 2 = ∑' j : ℤ, w j ^ 2 * ‖fourierPotential φ true j‖ ^ 2 := by
    rw [hA, componentNorm_eq, Real.sq_sqrt ENNReal.toReal_nonneg,
      compEnergy_toReal w φ true (compEnergy_ne_top w φ hφ true)]
  have hβs : Summable fun l : ℤ =>
      (w (l + -n) * ‖coefficientPair g true l‖ / indexWeight n) ^ 2 :=
    (hXs.div_const (indexWeight n ^ 2)).congr fun l => by rw [div_pow, mul_pow]
  have hβ2 : ∑' l : ℤ, (w (l + -n) * ‖coefficientPair g true l‖ / indexWeight n) ^ 2 ≤
      (N / indexWeight n) ^ 2 := by
    have e : ∑' l : ℤ, (w (l + -n) * ‖coefficientPair g true l‖ / indexWeight n) ^ 2 =
        (∑' l : ℤ, w (l + -n) ^ 2 * ‖coefficientPair g true l‖ ^ 2) / indexWeight n ^ 2 := by
      rw [← tsum_div_const]
      exact tsum_congr fun l => by rw [div_pow, mul_pow]
    rw [e, div_pow]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  obtain ⟨hs, hle⟩ := cs_pair
    (fun l : ℤ => ‖potentialCoefficientPair φ false (n - l)‖)
    (fun l : ℤ => w (l + -n) * ‖coefficientPair g true l‖ / indexWeight n)
    (fun l => norm_nonneg _)
    (fun l => div_nonneg (mul_nonneg (weight_pos w hw _).le (norm_nonneg _)) hρ.le)
    A (N / indexWeight n) hA0 (div_nonneg hN0 hρ.le) hαs hβs (hα2.trans hA2.ge) hβ2
  have hterm : ∀ l : ℤ,
      ‖potentialCoefficientPair φ false (n - l) *
        (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-l) * coefficientPair g true l)‖ ≤
      ‖potentialCoefficientPair φ false (n - l)‖ *
        (w (l + -n) * ‖coefficientPair g true l‖ / indexWeight n) := by
    intro l
    have hcr : ‖NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-l)‖ ≤
        w (l + -n) / indexWeight n := by
      have h := NlsGge.ThirdConsultation.M.cr_bound_gen n lam hlam (-l) (l + n)
        (Or.inr (by ring))
      by_cases h0 : l + n = 0
      · rw [if_pos h0] at h
        exact h.trans (div_nonneg (weight_pos w hw _).le hρ.le)
      · rw [if_neg h0] at h
        refine h.trans ?_
        have hk := key_ineq w hw (l + -n) (l + n) n (by ring) h0
        have hpos : 0 < |((l + n : ℤ) : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr h0)
        rw [div_le_div_iff₀ hpos hρ]
        linarith
    rw [norm_mul, norm_mul]
    calc ‖potentialCoefficientPair φ false (n - l)‖ *
          (‖NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-l)‖ *
            ‖coefficientPair g true l‖)
        ≤ ‖potentialCoefficientPair φ false (n - l)‖ *
          (w (l + -n) / indexWeight n * ‖coefficientPair g true l‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcr (norm_nonneg _))
            (norm_nonneg _)
      _ = _ := by ring
  have hmain := tsum_of_norm_bounded hs.hasSum hterm
  calc _ ≤ _ := hmain
    _ ≤ A * (N / indexWeight n) := hle
    _ = A / indexWeight n * N := by ring

theorem pair_true_le (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair) (hφ : potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ) (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (g : KSTPairL2) (hg : shiftedPairEnergy w n false (coefficientPair g) ≠ ⊤) :
    ‖inner ℂ (schurFrame n true : KSTPairL2) (ambientT φ n lam hlam g)‖ ≤
      NlsGge.ThirdConsultation.M.componentNorm w φ false / indexWeight n *
        shiftedPairNorm w n false (coefficientPair g) := by
  rw [inner_frame_true]
  have hρ : 0 < indexWeight n := NlsGge.ThirdConsultation.MTwoModeW.indexWeight_pos n
  have hc : coefficientPair (ambientT φ n lam hlam g) true (-n) =
      ∑' l : ℤ, potentialCoefficientPair φ true (-n - l) *
        (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam l *
          coefficientPair g false l) :=
    Tcoeff_eq_kernel φ n lam hlam g true (-n)
  rw [hc]
  obtain ⟨_, hYs, hN2⟩ := shifted_parts w n (coefficientPair g) hg
  have hX0 : 0 ≤ ∑' k : ℤ, w (k + -n) ^ 2 * ‖coefficientPair g true k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hG := compEnergy_summable w φ false (compEnergy_ne_top w φ hφ false)
  obtain ⟨hαs, hα2⟩ := sq_reindex w hw (fun j => fourierPotential φ false j) hG
    (Equiv.subLeft (-n))
  set N := shiftedPairNorm w n false (coefficientPair g) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  set A := NlsGge.ThirdConsultation.M.componentNorm w φ false with hA
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hA2 : A ^ 2 = ∑' j : ℤ, w j ^ 2 * ‖fourierPotential φ false j‖ ^ 2 := by
    rw [hA, componentNorm_eq, Real.sq_sqrt ENNReal.toReal_nonneg,
      compEnergy_toReal w φ false (compEnergy_ne_top w φ hφ false)]
  have hβs : Summable fun l : ℤ =>
      (w (l - -n) * ‖coefficientPair g false l‖ / indexWeight n) ^ 2 :=
    (hYs.div_const (indexWeight n ^ 2)).congr fun l => by rw [div_pow, mul_pow]
  have hβ2 : ∑' l : ℤ, (w (l - -n) * ‖coefficientPair g false l‖ / indexWeight n) ^ 2 ≤
      (N / indexWeight n) ^ 2 := by
    have e : ∑' l : ℤ, (w (l - -n) * ‖coefficientPair g false l‖ / indexWeight n) ^ 2 =
        (∑' l : ℤ, w (l - -n) ^ 2 * ‖coefficientPair g false l‖ ^ 2) / indexWeight n ^ 2 := by
      rw [← tsum_div_const]
      exact tsum_congr fun l => by rw [div_pow, mul_pow]
    rw [e, div_pow]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  obtain ⟨hs, hle⟩ := cs_pair
    (fun l : ℤ => ‖potentialCoefficientPair φ true (-n - l)‖)
    (fun l : ℤ => w (l - -n) * ‖coefficientPair g false l‖ / indexWeight n)
    (fun l => norm_nonneg _)
    (fun l => div_nonneg (mul_nonneg (weight_pos w hw _).le (norm_nonneg _)) hρ.le)
    A (N / indexWeight n) hA0 (div_nonneg hN0 hρ.le) hαs hβs (hα2.trans hA2.ge) hβ2
  have hterm : ∀ l : ℤ,
      ‖potentialCoefficientPair φ true (-n - l) *
        (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam l * coefficientPair g false l)‖ ≤
      ‖potentialCoefficientPair φ true (-n - l)‖ *
        (w (l - -n) * ‖coefficientPair g false l‖ / indexWeight n) := by
    intro l
    have hcr : ‖NlsGge.Atomic.KST004.complementaryResolventCoeff n lam l‖ ≤
        w (l - -n) / indexWeight n := by
      have h := NlsGge.ThirdConsultation.M.cr_bound_gen n lam hlam l (l - n) (Or.inl rfl)
      by_cases h0 : l - n = 0
      · rw [if_pos h0] at h
        exact h.trans (div_nonneg (weight_pos w hw _).le hρ.le)
      · rw [if_neg h0] at h
        refine h.trans ?_
        have hk := key_ineq w hw (l - -n) (l - n) (-n) (by ring) h0
        rw [indexWeight_neg'] at hk
        have hpos : 0 < |((l - n : ℤ) : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr h0)
        rw [div_le_div_iff₀ hpos hρ]
        linarith
    rw [norm_mul, norm_mul]
    calc ‖potentialCoefficientPair φ true (-n - l)‖ *
          (‖NlsGge.Atomic.KST004.complementaryResolventCoeff n lam l‖ *
            ‖coefficientPair g false l‖)
        ≤ ‖potentialCoefficientPair φ true (-n - l)‖ *
          (w (l - -n) / indexWeight n * ‖coefficientPair g false l‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcr (norm_nonneg _))
            (norm_nonneg _)
      _ = _ := by ring
  have hmain := tsum_of_norm_bounded hs.hasSum hterm
  calc _ ≤ _ := hmain
    _ ≤ A * (N / indexWeight n) := hle
    _ = A / indexWeight n * N := by ring

/-! ### the odd path terms and the odd remainder -/

theorem odd_term_le (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair) (hφ : potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ) (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (plus : Bool) (j : ℕ) :
    ‖schurPathTerm φ n lam hlam (2 * j + 1)
        (if plus then false else true) (if plus then false else true)‖ ≤
      (NlsGge.ThirdConsultation.M.componentNorm w φ plus *
          NlsGge.ThirdConsultation.M.componentNorm w φ (!plus) / indexWeight n) *
        (4 * potentialCoefficientNorm w φ ^ 2 / indexWeight n) ^ j := by
  have hρ : 0 < indexWeight n := NlsGge.ThirdConsultation.MTwoModeW.indexWeight_pos n
  have hq : 0 ≤ (4 * potentialCoefficientNorm w φ ^ 2 / indexWeight n) ^ j :=
    pow_nonneg (div_nonneg (by positivity) hρ.le) j
  cases plus
  · -- minus: frame `true`
    have hK : shiftedPairEnergy w n false (coefficientPair
        (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
          (schurFrame n true : KSTPairL2))) ≠ ⊤ := by
      rw [shifted_V_upper]
      exact compEnergy_ne_top w φ hφ true
    obtain ⟨h1, h2⟩ := iter_w w hw φ hφ n lam hlam _ hK j
    have h3 := pair_true_le w hw φ hφ n lam hlam _ h1
    have h4 : schurPathTerm φ n lam hlam (2 * j + 1) true true =
        inner ℂ (schurFrame n true : KSTPairL2) (ambientT φ n lam hlam
          ((((ambientT φ n lam hlam) ^ 2) ^ j)
            (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
              (schurFrame n true : KSTPairL2)))) := by
      unfold schurPathTerm
      rw [NlsGge.ThirdConsultation.MTwoModeSupp.pow_two_mul_add_one,
        ContinuousLinearMap.mul_apply]
    change ‖schurPathTerm φ n lam hlam (2 * j + 1) true true‖ ≤ _
    rw [h4]
    refine h3.trans ?_
    rw [shifted_norm_V_upper] at h2
    calc NlsGge.ThirdConsultation.M.componentNorm w φ false / indexWeight n *
          shiftedPairNorm w n false (coefficientPair
            ((((ambientT φ n lam hlam) ^ 2) ^ j)
              (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
                (schurFrame n true : KSTPairL2))))
        ≤ NlsGge.ThirdConsultation.M.componentNorm w φ false / indexWeight n *
            ((4 * potentialCoefficientNorm w φ ^ 2 / indexWeight n) ^ j *
              NlsGge.ThirdConsultation.M.componentNorm w φ true) :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg (Real.sqrt_nonneg _) hρ.le)
      _ = _ := by simp only [Bool.not_false]; ring
  · -- plus: frame `false`
    have hK : shiftedPairEnergy w n false (coefficientPair
        (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
          (schurFrame n false : KSTPairL2))) ≠ ⊤ := by
      rw [shifted_V_lower]
      exact compEnergy_ne_top w φ hφ false
    obtain ⟨h1, h2⟩ := iter_w w hw φ hφ n lam hlam _ hK j
    have h3 := pair_false_le w hw φ hφ n lam hlam _ h1
    have h4 : schurPathTerm φ n lam hlam (2 * j + 1) false false =
        inner ℂ (schurFrame n false : KSTPairL2) (ambientT φ n lam hlam
          ((((ambientT φ n lam hlam) ^ 2) ^ j)
            (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
              (schurFrame n false : KSTPairL2)))) := by
      unfold schurPathTerm
      rw [NlsGge.ThirdConsultation.MTwoModeSupp.pow_two_mul_add_one,
        ContinuousLinearMap.mul_apply]
    change ‖schurPathTerm φ n lam hlam (2 * j + 1) false false‖ ≤ _
    rw [h4]
    refine h3.trans ?_
    rw [shifted_norm_V_lower] at h2
    calc NlsGge.ThirdConsultation.M.componentNorm w φ true / indexWeight n *
          shiftedPairNorm w n false (coefficientPair
            ((((ambientT φ n lam hlam) ^ 2) ^ j)
              (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
                (schurFrame n false : KSTPairL2))))
        ≤ NlsGge.ThirdConsultation.M.componentNorm w φ true / indexWeight n *
            ((4 * potentialCoefficientNorm w φ ^ 2 / indexWeight n) ^ j *
              NlsGge.ThirdConsultation.M.componentNorm w φ false) :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg (Real.sqrt_nonneg _) hρ.le)
      _ = _ := by simp only [Bool.not_true]; ring

theorem tsum_geom_bound0 (f : ℕ → ℂ) (q c : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (hc : 0 ≤ c)
    (h : ∀ j : ℕ, ‖f j‖ ≤ c * q ^ j) : ‖∑' j : ℕ, f j‖ ≤ 2 * c := by
  have hq1 : q < 1 := by linarith
  have hHas : HasSum (fun j : ℕ => c * q ^ j) (c * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left _
  have hn := tsum_of_norm_bounded hHas h
  have hinv : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc ‖∑' j : ℕ, f j‖ ≤ c * (1 - q)⁻¹ := hn
    _ ≤ c * 2 := mul_le_mul_of_nonneg_left hinv hc
    _ = 2 * c := by ring

theorem odd_remainder_bound (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair) (hφ : potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ) (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hthreshold : 8 * potentialCoefficientNorm w φ ^ 2 ≤ indexWeight n) (plus : Bool) :
    ‖schurOddRemainder φ n lam hlam plus‖ ≤ potentialCoefficientNorm w φ ^ 2 / indexWeight n := by
  have hρ : 0 < indexWeight n := NlsGge.ThirdConsultation.MTwoModeW.indexWeight_pos n
  have hq0 : 0 ≤ 4 * potentialCoefficientNorm w φ ^ 2 / indexWeight n :=
    div_nonneg (by positivity) hρ.le
  have hq : 4 * potentialCoefficientNorm w φ ^ 2 / indexWeight n ≤ 1 / 2 := by
    rw [div_le_iff₀ hρ]
    linarith
  have ha : 0 ≤ NlsGge.ThirdConsultation.M.componentNorm w φ plus := Real.sqrt_nonneg _
  have hb : 0 ≤ NlsGge.ThirdConsultation.M.componentNorm w φ (!plus) := Real.sqrt_nonneg _
  have key := tsum_geom_bound0
    (fun j : ℕ => schurPathTerm φ n lam hlam (2 * j + 1)
      (if plus then false else true) (if plus then false else true))
    (4 * potentialCoefficientNorm w φ ^ 2 / indexWeight n)
    (NlsGge.ThirdConsultation.M.componentNorm w φ plus *
      NlsGge.ThirdConsultation.M.componentNorm w φ (!plus) / indexWeight n) hq0 hq
    (div_nonneg (mul_nonneg ha hb) hρ.le)
    (fun j => odd_term_le w hw φ hφ n lam hlam plus j)
  have hE : schurOddRemainder φ n lam hlam plus =
      ∑' j : ℕ, schurPathTerm φ n lam hlam (2 * j + 1)
        (if plus then false else true) (if plus then false else true) := by
    cases plus <;> rfl
  rw [hE]
  refine key.trans ?_
  have hP := potentialNorm_sq w φ hφ
  have hsq : 2 * (NlsGge.ThirdConsultation.M.componentNorm w φ plus *
      NlsGge.ThirdConsultation.M.componentNorm w φ (!plus)) ≤
      potentialCoefficientNorm w φ ^ 2 := by
    rw [hP]
    cases plus
    · simp only [Bool.not_false]
      nlinarith [sq_nonneg (NlsGge.ThirdConsultation.M.componentNorm w φ true -
        NlsGge.ThirdConsultation.M.componentNorm w φ false)]
    · simp only [Bool.not_true]
      nlinarith [sq_nonneg (NlsGge.ThirdConsultation.M.componentNorm w φ true -
        NlsGge.ThirdConsultation.M.componentNorm w φ false)]
  calc 2 * (NlsGge.ThirdConsultation.M.componentNorm w φ plus *
        NlsGge.ThirdConsultation.M.componentNorm w φ (!plus) / indexWeight n)
      = 2 * (NlsGge.ThirdConsultation.M.componentNorm w φ plus *
        NlsGge.ThirdConsultation.M.componentNorm w φ (!plus)) / indexWeight n := by ring
    _ ≤ potentialCoefficientNorm w φ ^ 2 / indexWeight n :=
        div_le_div_of_nonneg_right hsq hρ.le

end NlsGge.ThirdConsultation.MTwoModeB

end
