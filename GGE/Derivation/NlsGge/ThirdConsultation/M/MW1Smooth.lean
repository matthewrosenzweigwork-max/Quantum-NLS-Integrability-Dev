import Mathlib
import NlsGge.ThirdConsultation.M.MW1Seq
import NlsGge.ThirdConsultation.M.M021Host
import NlsGge.Atomic.M.M021
import NlsGge.Atomic.M.M022

/-!
# MW1Smooth: the smoothing estimate `T : L^2 -> X_0` (proof development, AUTHOR; not self-reviewed)

Support for the Pro round 11 section 7.3 weighted-threshold bridge (M-024..026).  Let `w0 = indexWeight`
(`1 + |k|`, the M-054 linear weight).  For `phi` with finite `w0` potential energy, the landed pair operator
`T` of M-021 maps the unweighted `L^2` pair space into the source shifted `w0` space at `n` (the
`shiftedPairEnergy w0 n false` carrier of M-022) with an explicit bound:

  `shiftedPairNorm w0 n false (coefficientPair (T f)) <= sqrt K * potentialCoefficientNorm w0 phi * ||f||`.

This is the bounded lift `U : H -> X_0` of Pro 7.3 at the level of the landed coefficient-energy carriers.  The estimate
uses the additive splitting `w0 (k+s) <= w0 (k-l) + w0 (l+s)` and the matching-shift bound `w0 (l+s) |c (l)| <= 2`
of the complementary resolvent coefficient.  Also: `||h||_H <= ||h||_{w0}`.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace NlsGge.ThirdConsultation.MTwoModeW

open NlsGge.ThirdConsultation.MTwoMode NlsGge.Atomic.M.M054 NlsGge.Atomic.KST003

theorem indexWeight_pos (k : ℤ) : 0 < indexWeight k := by
  unfold indexWeight; positivity

theorem one_le_indexWeight (k : ℤ) : 1 ≤ indexWeight k := by
  unfold indexWeight
  have := abs_nonneg ((k : ℝ))
  linarith

theorem indexWeight_add (k l s : ℤ) :
    indexWeight (k + s) ≤ indexWeight (k - l) + indexWeight (l + s) := by
  unfold indexWeight
  have h : |((k + s : ℤ) : ℝ)| ≤ |((k - l : ℤ) : ℝ)| + |((l + s : ℤ) : ℝ)| := by
    have e : ((k + s : ℤ) : ℝ) = ((k - l : ℤ) : ℝ) + ((l + s : ℤ) : ℝ) := by push_cast; ring
    rw [e]
    exact abs_add_le _ _
  linarith

/-- `w0 t * (if t = 0 then 0 else 1/|t|) <= 2`. -/
theorem indexWeight_mul_inv_le (t : ℤ) :
    indexWeight t * (if t = 0 then 0 else 1 / |((t : ℤ) : ℝ)|) ≤ 2 := by
  by_cases h : t = 0
  · simp [h]
  · rw [if_neg h]
    have ht : (1 : ℝ) ≤ |((t : ℤ) : ℝ)| := by
      have : (1 : ℤ) ≤ |t| := Int.one_le_abs h
      exact_mod_cast this
    have hpos : 0 < |((t : ℤ) : ℝ)| := by linarith
    unfold indexWeight
    rw [mul_one_div, div_le_iff₀ hpos]
    linarith

theorem summable_inv_sq : Summable fun m : ℤ => (1 / indexWeight m) ^ 2 := by
  have hbase : Summable (fun d : ℤ => 1 / (d : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  refine Summable.of_norm_bounded_eventually hbase ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with m hm
  have hm' : 0 < |((m : ℤ) : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hm)
  have hw := indexWeight_pos m
  rw [Real.norm_of_nonneg (by positivity), div_pow, one_pow, ← sq_abs ((m : ℤ) : ℝ)]
  apply one_div_le_one_div_of_le (by positivity)
  have : |((m : ℤ) : ℝ)| ≤ indexWeight m := by unfold indexWeight; linarith
  exact pow_le_pow_left₀ hm'.le this 2

/-- `a` is summable and `(sum |a|)^2 <= (sum (1/w0)^2) * sum (w0 |a|)^2`. -/
theorem sum_norm_le (a : ℤ → ℂ) (hsa : Summable fun m => (indexWeight m * ‖a m‖) ^ 2) :
    Summable (fun m => ‖a m‖) ∧
      (∑' m, ‖a m‖) ^ 2 ≤
        (∑' m : ℤ, (1 / indexWeight m) ^ 2) * ∑' m, (indexWeight m * ‖a m‖) ^ 2 := by
  obtain ⟨hs, hle⟩ := NlsGge.ThirdConsultation.MTwoMode.Real21.cs_sq
    (fun m => 1 / indexWeight m) (fun m => indexWeight m * ‖a m‖)
    (fun m => by have := indexWeight_pos m; positivity)
    (fun m => mul_nonneg (indexWeight_pos m).le (norm_nonneg _)) summable_inv_sq hsa
  have e : ∀ m, 1 / indexWeight m * (indexWeight m * ‖a m‖) = ‖a m‖ := fun m => by
    field_simp [(indexWeight_pos m).ne']
  simp only [e] at hs hle
  exact ⟨hs, hle⟩

/-- The smoothing constant. -/
def smoothK : ℝ := 8 + 8 * ∑' m : ℤ, (1 / indexWeight m) ^ 2

theorem smoothK_nonneg : 0 ≤ smoothK := by
  unfold smoothK
  have : 0 ≤ ∑' m : ℤ, (1 / indexWeight m) ^ 2 := tsum_nonneg fun m => sq_nonneg _
  linarith

/-- One component of the smoothing estimate in `Real` form. -/
theorem smooth_T_comp (s : ℤ) (a x D out : ℤ → ℂ)
    (hker : ∀ k, out k = ∑' l, a (k - l) * (D l * x l))
    (hD1 : ∀ l, ‖D l‖ ≤ 1) (hDs : Summable fun l => ‖D l‖ ^ 2)
    (hD4 : ∑' l, ‖D l‖ ^ 2 ≤ 4) (hDw : ∀ l, indexWeight (l + s) * ‖D l‖ ≤ 2)
    (hsa : Summable fun m => (indexWeight m * ‖a m‖) ^ 2)
    (hsx : Summable fun l => ‖x l‖ ^ 2) :
    Summable (fun k : ℤ => (indexWeight (k + s) * ‖out k‖) ^ 2) ∧
      ∑' k : ℤ, (indexWeight (k + s) * ‖out k‖) ^ 2 ≤
        smoothK * (∑' m, (indexWeight m * ‖a m‖) ^ 2) * ∑' l, ‖x l‖ ^ 2 := by
  obtain ⟨hsa1, hl1⟩ := sum_norm_le a hsa
  have h := NlsGge.ThirdConsultation.MTwoModeW.smooth_comp indexWeight one_le_indexWeight
    indexWeight_add s a x D 2 hD1 hDs hD4 hDw hsa hsa1 hsx
  have hker' : (fun k : ℤ => (indexWeight (k + s) * ‖out k‖) ^ 2) =
      fun k : ℤ => (indexWeight (k + s) * ‖∑' l, a (k - l) * (D l * x l)‖) ^ 2 := by
    funext k; rw [hker k]
  rw [hker']
  refine ⟨h.1, h.2.trans ?_⟩
  have hP : 0 ≤ ∑' m, (indexWeight m * ‖a m‖) ^ 2 := tsum_nonneg fun m => sq_nonneg _
  have hE : 0 ≤ ∑' l, ‖x l‖ ^ 2 := tsum_nonneg fun l => sq_nonneg _
  unfold smoothK
  have h2 : 2 * (∑' m, ‖a m‖) ^ 2 * (2 ^ 2 * ∑' l, ‖x l‖ ^ 2) ≤
      8 * (∑' m : ℤ, (1 / indexWeight m) ^ 2) * (∑' m, (indexWeight m * ‖a m‖) ^ 2) *
        ∑' l, ‖x l‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hl1 hE
    nlinarith [this]
  nlinarith [h2]

/-- Parseval in each component. -/
theorem coef_hasSum_sq (g : KSTPairL2) (b : Bool) :
    HasSum (fun k : ℤ => ‖coefficientPair g b k‖ ^ 2) (‖g b‖ ^ 2) := by
  have h1 : ∀ k, coefficientPair g b k = (fourierBasis (T := (2 : ℝ))).repr (g b) k :=
    fun k => (fourierBasis_repr _ _).symm
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num)
    ((fourierBasis (T := (2 : ℝ))).repr (g b))
  have hn : ‖(fourierBasis (T := (2 : ℝ))).repr (g b)‖ = ‖g b‖ := LinearIsometryEquiv.norm_map _ _
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  simpa only [h1, hn] using h

theorem pair_norm_sq (g : KSTPairL2) : ‖g‖ ^ 2 = ‖g true‖ ^ 2 + ‖g false‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_bool]

theorem comp_norm_le (g : KSTPairL2) (b : Bool) : ‖g b‖ ^ 2 ≤ ‖g‖ ^ 2 := by
  rw [pair_norm_sq]
  cases b <;> nlinarith [sq_nonneg ‖g true‖, sq_nonneg ‖g false‖]

/-- `||h||_H <= ||h||_{w0}` on the finite-energy carrier. -/
theorem norm_le_shifted (n : ℤ) (h : KSTPairL2)
    (hf : shiftedPairEnergy indexWeight n false (coefficientPair h) ≠ ⊤) :
    ‖h‖ ≤ shiftedPairNorm indexWeight n false (coefficientPair h) := by
  obtain ⟨hXt, hYf⟩ := NlsGge.ThirdConsultation.M.split_finite
    (fun k => indexWeight (k + -n) ^ 2 * ‖coefficientPair h true k‖ ^ 2)
    (fun k => indexWeight (k - -n) ^ 2 * ‖coefficientPair h false k‖ ^ 2)
    (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hf
  have he := NlsGge.ThirdConsultation.M.shifted_split_eq indexWeight n (coefficientPair h) hXt hYf
  have hX0 : 0 ≤ ∑' k : ℤ, indexWeight (k + -n) ^ 2 * ‖coefficientPair h true k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hY0 : 0 ≤ ∑' k : ℤ, indexWeight (k - -n) ^ 2 * ‖coefficientPair h false k‖ ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hN : shiftedPairNorm indexWeight n false (coefficientPair h) =
      Real.sqrt ((∑' k : ℤ, indexWeight (k + -n) ^ 2 * ‖coefficientPair h true k‖ ^ 2) +
        ∑' k : ℤ, indexWeight (k - -n) ^ 2 * ‖coefficientPair h false k‖ ^ 2) := by
    unfold shiftedPairNorm
    rw [he, ← ENNReal.ofReal_add hX0 hY0, ENNReal.toReal_ofReal (add_nonneg hX0 hY0)]
  rw [hN]
  apply Real.le_sqrt_of_sq_le
  rw [pair_norm_sq]
  have hone : ∀ k : ℤ, ∀ s : ℤ, 1 ≤ indexWeight (k + s) ^ 2 := fun k s =>
    one_le_pow₀ (one_le_indexWeight _)
  have h1 : ‖h true‖ ^ 2 ≤ ∑' k : ℤ, indexWeight (k + -n) ^ 2 * ‖coefficientPair h true k‖ ^ 2 := by
    rw [← (coef_hasSum_sq h true).tsum_eq]
    exact Summable.tsum_le_tsum
      (fun k => le_mul_of_one_le_left (sq_nonneg _) (hone k (-n)))
      (coef_hasSum_sq h true).summable hXt
  have h2 : ‖h false‖ ^ 2 ≤ ∑' k : ℤ, indexWeight (k - -n) ^ 2 * ‖coefficientPair h false k‖ ^ 2 := by
    rw [← (coef_hasSum_sq h false).tsum_eq]
    exact Summable.tsum_le_tsum
      (fun k => le_mul_of_one_le_left (sq_nonneg _) (by rw [sub_neg_eq_add]; exact hone k n))
      (coef_hasSum_sq h false).summable hYf
  linarith

/-- Pair-level smoothing estimate: `T` maps `L^2` pairs into the source shifted `w0` space. -/
theorem T_smooth (φ : NlsGge.GK38.PotPair)
    (hφ : potentialCoefficientEnergy indexWeight φ ≠ ⊤)
    (n : ℤ) (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) (f : KSTPairL2) :
    shiftedPairEnergy indexWeight n false (coefficientPair (T φ n lam hlam f)) ≠ ⊤ ∧
      shiftedPairNorm indexWeight n false (coefficientPair (T φ n lam hlam f)) ≤
        Real.sqrt smoothK * potentialCoefficientNorm indexWeight φ * ‖f‖ := by
  have hnn : ∀ (b : Bool) (j : ℤ),
      0 ≤ indexWeight j ^ 2 * ‖potentialCoefficientPair φ b j‖ ^ 2 :=
    fun b j => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hEφ := potentialCoefficientEnergy_eq indexWeight φ
  have hPt_ne : ∑' k : ℤ, ENNReal.ofReal
      (indexWeight k ^ 2 * ‖potentialCoefficientPair φ true k‖ ^ 2) ≠ ⊤ :=
    fun h => hφ (by rw [hEφ, h, top_add])
  have hPf_ne : ∑' k : ℤ, ENNReal.ofReal
      (indexWeight k ^ 2 * ‖potentialCoefficientPair φ false k‖ ^ 2) ≠ ⊤ :=
    fun h => hφ (by rw [hEφ, h, add_top])
  have hPo : Summable fun j : ℤ => indexWeight j ^ 2 * ‖potentialCoefficientPair φ true j‖ ^ 2 :=
    NlsGge.ThirdConsultation.MTwoMode.Real21.summable_of_ofReal_tsum_ne_top _ (hnn true) hPt_ne
  have hPf : Summable fun j : ℤ => indexWeight j ^ 2 * ‖potentialCoefficientPair φ false j‖ ^ 2 :=
    NlsGge.ThirdConsultation.MTwoMode.Real21.summable_of_ofReal_tsum_ne_top _ (hnn false) hPf_ne
  have hPo' : Summable fun m : ℤ => (indexWeight m * ‖potentialCoefficientPair φ true m‖) ^ 2 :=
    hPo.congr fun m => (mul_pow _ _ _).symm
  have hPf' : Summable fun m : ℤ => (indexWeight m * ‖potentialCoefficientPair φ false m‖) ^ 2 :=
    hPf.congr fun m => (mul_pow _ _ _).symm
  -- kernel representations of the two components of `T f`
  have hU : ∀ k : ℤ, coefficientPair (T φ n lam hlam f) true k =
      ∑' l : ℤ, potentialCoefficientPair φ true (k - l) *
        (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam l * coefficientPair f false l) := by
    intro k
    refine (Tcoeff_eq_kernel φ n lam hlam f true k).trans (tsum_congr fun l => ?_)
    simp
  have hV : ∀ k : ℤ, coefficientPair (T φ n lam hlam f) false k =
      ∑' l : ℤ, potentialCoefficientPair φ false (k - l) *
        (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-l) * coefficientPair f true l) := by
    intro k
    refine (Tcoeff_eq_kernel φ n lam hlam f false k).trans (tsum_congr fun l => ?_)
    simp
  have hD := NlsGge.ThirdConsultation.MTwoMode.Comp21.D_facts n lam hlam
  have hDn := NlsGge.ThirdConsultation.MTwoMode.Comp21.D_facts_neg n lam hlam
  have hDwU : ∀ l : ℤ, indexWeight (l + -n) *
      ‖NlsGge.Atomic.KST004.complementaryResolventCoeff n lam l‖ ≤ 2 := by
    intro l
    have hb := NlsGge.ThirdConsultation.M.cr_bound_gen n lam hlam l (l + -n) (Or.inl (by ring))
    exact le_trans (mul_le_mul_of_nonneg_left hb (indexWeight_pos _).le)
      (indexWeight_mul_inv_le _)
  have hDwV : ∀ l : ℤ, indexWeight (l + n) *
      ‖NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-l)‖ ≤ 2 := by
    intro l
    have hb := NlsGge.ThirdConsultation.M.cr_bound_gen n lam hlam (-l) (l + n) (Or.inr (by ring))
    exact le_trans (mul_le_mul_of_nonneg_left hb (indexWeight_pos _).le)
      (indexWeight_mul_inv_le _)
  have hXt := smooth_T_comp (-n) (potentialCoefficientPair φ true) (coefficientPair f false)
    (NlsGge.Atomic.KST004.complementaryResolventCoeff n lam)
    (coefficientPair (T φ n lam hlam f) true) hU hD.1 hD.2.1 hD.2.2 hDwU hPo'
    (coef_hasSum_sq f false).summable
  have hYf := smooth_T_comp n (potentialCoefficientPair φ false) (coefficientPair f true)
    (fun l => NlsGge.Atomic.KST004.complementaryResolventCoeff n lam (-l))
    (coefficientPair (T φ n lam hlam f) false) hV hDn.1 hDn.2.1 hDn.2.2 hDwV hPf'
    (coef_hasSum_sq f true).summable
  have hXo : Summable fun k : ℤ => indexWeight (k + -n) ^ 2 *
      ‖coefficientPair (T φ n lam hlam f) true k‖ ^ 2 :=
    hXt.1.congr fun k => mul_pow _ _ _
  have hYo : Summable fun k : ℤ => indexWeight (k - -n) ^ 2 *
      ‖coefficientPair (T φ n lam hlam f) false k‖ ^ 2 :=
    hYf.1.congr fun k => by rw [sub_neg_eq_add, mul_pow]
  obtain ⟨Pt, hPt⟩ : ∃ P : ℝ, P = ∑' m : ℤ,
      (indexWeight m * ‖potentialCoefficientPair φ true m‖) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Pf, hPf2⟩ : ∃ P : ℝ, P = ∑' m : ℤ,
      (indexWeight m * ‖potentialCoefficientPair φ false m‖) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Xs, hXs⟩ : ∃ R : ℝ, R = ∑' k : ℤ, indexWeight (k + -n) ^ 2 *
      ‖coefficientPair (T φ n lam hlam f) true k‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨Ys, hYs⟩ : ∃ R : ℝ, R = ∑' k : ℤ, indexWeight (k - -n) ^ 2 *
      ‖coefficientPair (T φ n lam hlam f) false k‖ ^ 2 := ⟨_, rfl⟩
  have hPt0 : 0 ≤ Pt := by rw [hPt]; exact tsum_nonneg fun m => sq_nonneg _
  have hPf0 : 0 ≤ Pf := by rw [hPf2]; exact tsum_nonneg fun m => sq_nonneg _
  have hXs0 : 0 ≤ Xs := by
    rw [hXs]; exact tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hYs0 : 0 ≤ Ys := by
    rw [hYs]; exact tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hK := smoothK_nonneg
  have hXb : Xs ≤ smoothK * Pt * ‖f false‖ ^ 2 := by
    have h1 := hXt.2
    rw [(coef_hasSum_sq f false).tsum_eq, ← hPt] at h1
    rw [hXs]
    calc _ = ∑' k : ℤ, (indexWeight (k + -n) *
          ‖coefficientPair (T φ n lam hlam f) true k‖) ^ 2 :=
          tsum_congr fun k => (mul_pow _ _ _).symm
      _ ≤ _ := h1
  have hYb : Ys ≤ smoothK * Pf * ‖f true‖ ^ 2 := by
    have h1 := hYf.2
    rw [(coef_hasSum_sq f true).tsum_eq, ← hPf2] at h1
    rw [hYs]
    calc _ = ∑' k : ℤ, (indexWeight (k + n) *
          ‖coefficientPair (T φ n lam hlam f) false k‖) ^ 2 :=
          tsum_congr fun k => by rw [sub_neg_eq_add, mul_pow]
      _ ≤ _ := h1
  have hle : Xs + Ys ≤ smoothK * (Pt + Pf) * ‖f‖ ^ 2 := by
    have h1 := comp_norm_le f false
    have h2 := comp_norm_le f true
    have h3 : smoothK * Pt * ‖f false‖ ^ 2 ≤ smoothK * Pt * ‖f‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (mul_nonneg hK hPt0)
    have h4 : smoothK * Pf * ‖f true‖ ^ 2 ≤ smoothK * Pf * ‖f‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hK hPf0)
    nlinarith [hXb, hYb, h3, h4]
  have hEo : shiftedPairEnergy indexWeight n false
      (coefficientPair (T φ n lam hlam f)) = ENNReal.ofReal (Xs + Ys) := by
    rw [NlsGge.ThirdConsultation.M.shifted_split_eq indexWeight n _ hXo hYo, hXs, hYs,
      ← ENNReal.ofReal_add (tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hEφ' : potentialCoefficientEnergy indexWeight φ = ENNReal.ofReal (Pt + Pf) := by
    have hA : ∑' k : ℤ, ENNReal.ofReal
        (indexWeight k ^ 2 * ‖potentialCoefficientPair φ true k‖ ^ 2) = ENNReal.ofReal Pt := by
      rw [hPt, ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg _) hPo']
      exact tsum_congr fun k => by rw [mul_pow]
    have hB : ∑' k : ℤ, ENNReal.ofReal
        (indexWeight k ^ 2 * ‖potentialCoefficientPair φ false k‖ ^ 2) = ENNReal.ofReal Pf := by
      rw [hPf2, ENNReal.ofReal_tsum_of_nonneg (fun m => sq_nonneg _) hPf']
      exact tsum_congr fun k => by rw [mul_pow]
    rw [hEφ, hA, hB, ENNReal.ofReal_add hPt0 hPf0]
  have hNφ : potentialCoefficientNorm indexWeight φ = Real.sqrt (Pt + Pf) := by
    unfold potentialCoefficientNorm
    rw [hEφ', ENNReal.toReal_ofReal (add_nonneg hPt0 hPf0)]
  refine ⟨by rw [hEo]; exact ENNReal.ofReal_ne_top, ?_⟩
  unfold shiftedPairNorm
  rw [hEo, ENNReal.toReal_ofReal (add_nonneg hXs0 hYs0), hNφ]
  calc Real.sqrt (Xs + Ys) ≤ Real.sqrt (smoothK * (Pt + Pf) * ‖f‖ ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt smoothK * Real.sqrt (Pt + Pf) * ‖f‖ := by
        rw [Real.sqrt_mul (mul_nonneg hK (add_nonneg hPt0 hPf0)), Real.sqrt_mul hK,
          Real.sqrt_sq (norm_nonneg _)]

end NlsGge.ThirdConsultation.MTwoModeW

end
