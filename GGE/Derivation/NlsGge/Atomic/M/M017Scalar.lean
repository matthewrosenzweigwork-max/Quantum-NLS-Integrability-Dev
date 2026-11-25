import Mathlib

/- M-017 SCALAR CORE, PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). SUPPORT (no packet increment).
   Mathlib only. Target NlsGge/Atomic/M/M017Scalar.lean, namespace NlsGge.ThirdConsultation.M017S.
   Two scalar facts for the finite-gap trace formula (Molnar Thm 4(3) via Lemma 4, finite-gap case):
   * `cauchy_moments`: for a continuous real density v supported in [-A, A], the Cauchy integral along the imaginary axis
     has the moment expansion ∫ v(t)/(t − iy) dt = −Σ_{m<K} M_m (iy)^{−(m+1)} + O(y^{−(K+1)}), M_m = ∫ t^m v; exact
     remainder t^K z^{−K}/(t − z) with |t − iy| ≥ y.
   * `coeffs_zero`: a polynomial Σ_{1≤j≤K} d_j w^j in w = (iy)^{-1} that is O(y^{−(K+1)}) as y → ∞ has all d_j = 0
     (least nonzero index argument). -/
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators

namespace NlsGge.ThirdConsultation.M017S

theorem geom_identity (t z : ℂ) (htz : t - z ≠ 0) (hz : z ≠ 0) (K : ℕ) :
    1 / (t - z) + ∑ m ∈ Finset.range K, t ^ m * z⁻¹ ^ (m + 1) = t ^ K * z⁻¹ ^ K / (t - z) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    field_simp
    linear_combination (-(t ^ K * z⁻¹ ^ K)) * mul_inv_cancel₀ hz

theorem cauchy_moments (v : ℝ → ℝ) (hv : Continuous v) (A : ℝ) (hA : 0 ≤ A)
    (hsupp : ∀ t : ℝ, A < |t| → v t = 0) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y →
      Integrable (fun t : ℝ => (v t : ℂ) / ((t : ℂ) - Complex.I * y)) ∧
      ‖(∫ t : ℝ, (v t : ℂ) / ((t : ℂ) - Complex.I * y)) +
        ∑ m ∈ Finset.range K, (∫ t : ℝ, (v t : ℂ) * (t : ℂ) ^ m) * (Complex.I * y)⁻¹ ^ (m + 1)‖ ≤
        C * y⁻¹ ^ (K + 1) := by
  have hcs : HasCompactSupport v := HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A))
    (fun t ht => hsupp t (by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with h | h
      · exact lt_abs.2 (Or.inr (by linarith))
      · exact lt_abs.2 (Or.inl h)))
  have hvi : Integrable v := hv.integrable_of_hasCompactSupport hcs
  refine ⟨(∫ t, |v t|) * A ^ K, mul_nonneg (integral_nonneg fun t => abs_nonneg _) (pow_nonneg hA K),
    fun y hy => ?_⟩
  set z : ℂ := Complex.I * y with hz_def
  have hz0 : z ≠ 0 := by
    rw [hz_def]; exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hy.ne')
  have hsub : ∀ t : ℝ, (t : ℂ) - z ≠ 0 := fun t h => by
    have := congrArg Complex.im h
    simp [hz_def] at this
    linarith
  have hnorm_sub : ∀ t : ℝ, y ≤ ‖(t : ℂ) - z‖ := fun t => by
    have h := Complex.abs_im_le_norm ((t : ℂ) - z)
    simp [hz_def] at h
    rw [abs_of_pos hy] at h
    exact h
  have hcz : ∀ (f : ℝ → ℂ), Continuous f → (∀ t, v t = 0 → f t = 0) → Integrable f := by
    intro f hf h0
    refine hf.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A))
      (fun t ht => h0 t ?_))
    apply hsupp
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · exact lt_abs.2 (Or.inr (by linarith))
    · exact lt_abs.2 (Or.inl h)
  have hcont_div : Continuous (fun t : ℝ => (v t : ℂ) / ((t : ℂ) - z)) :=
    (Complex.continuous_ofReal.comp hv).div (Complex.continuous_ofReal.sub continuous_const) hsub
  have hint0 : Integrable (fun t : ℝ => (v t : ℂ) / ((t : ℂ) - z)) :=
    hcz _ hcont_div (fun t h => by simp [h])
  have hintm : ∀ m : ℕ, Integrable (fun t : ℝ => (v t : ℂ) * (t : ℂ) ^ m) := fun m =>
    hcz _ ((Complex.continuous_ofReal.comp hv).mul (Complex.continuous_ofReal.pow m))
      (fun t h => by simp [h])
  refine ⟨hint0, ?_⟩
  have hsum : ∑ m ∈ Finset.range K, (∫ t : ℝ, (v t : ℂ) * (t : ℂ) ^ m) * z⁻¹ ^ (m + 1) =
      ∫ t : ℝ, ∑ m ∈ Finset.range K, (v t : ℂ) * (t : ℂ) ^ m * z⁻¹ ^ (m + 1) := by
    rw [integral_finset_sum _ (fun m _ => (hintm m).mul_const _)]
    exact Finset.sum_congr rfl (fun m _ => (integral_mul_const _ _).symm)
  have hint2 : Integrable (fun t : ℝ => ∑ m ∈ Finset.range K, (v t : ℂ) * (t : ℂ) ^ m * z⁻¹ ^ (m + 1)) :=
    integrable_finset_sum _ (fun m _ => (hintm m).mul_const _)
  rw [hsum, ← integral_add hint0 hint2]
  have hpt : ∀ t : ℝ, (v t : ℂ) / ((t : ℂ) - z) +
      ∑ m ∈ Finset.range K, (v t : ℂ) * (t : ℂ) ^ m * z⁻¹ ^ (m + 1) =
      (v t : ℂ) * ((t : ℂ) ^ K * z⁻¹ ^ K / ((t : ℂ) - z)) := by
    intro t
    rw [← geom_identity (t : ℂ) z (hsub t) hz0 K, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun m _ => by ring)
  simp_rw [hpt]
  have hbound : ∀ t : ℝ, ‖(v t : ℂ) * ((t : ℂ) ^ K * z⁻¹ ^ K / ((t : ℂ) - z))‖ ≤
      |v t| * (A ^ K * y⁻¹ ^ (K + 1)) := by
    intro t
    by_cases h0 : v t = 0
    · simp [h0]
    have ht : |t| ≤ A := by
      by_contra h; exact h0 (hsupp t (not_le.1 h))
    have hzn : ‖z⁻¹‖ = y⁻¹ := by
      rw [norm_inv, hz_def, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hy]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div, norm_mul, norm_pow, norm_pow, hzn,
      Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hs := hnorm_sub t
    have hspos : 0 < ‖(t : ℂ) - z‖ := lt_of_lt_of_le hy hs
    rw [div_le_iff₀ hspos, pow_succ]
    have h1 : |t| ^ K ≤ A ^ K := pow_le_pow_left₀ (abs_nonneg _) ht K
    have h2 : 0 ≤ y⁻¹ ^ K := by positivity
    have h3 : y⁻¹ * ‖(t : ℂ) - z‖ ≥ 1 := by
      rw [ge_iff_le, inv_mul_eq_div, le_div_iff₀ hy]; linarith
    calc |t| ^ K * y⁻¹ ^ K ≤ A ^ K * y⁻¹ ^ K := mul_le_mul_of_nonneg_right h1 h2
      _ ≤ A ^ K * y⁻¹ ^ K * (y⁻¹ * ‖(t : ℂ) - z‖) := by
          have : 0 ≤ A ^ K * y⁻¹ ^ K := by positivity
          nlinarith
      _ = A ^ K * (y⁻¹ ^ K * y⁻¹) * ‖(t : ℂ) - z‖ := by ring
  calc ‖∫ t : ℝ, (v t : ℂ) * ((t : ℂ) ^ K * z⁻¹ ^ K / ((t : ℂ) - z))‖
      ≤ ∫ t : ℝ, |v t| * (A ^ K * y⁻¹ ^ (K + 1)) :=
        norm_integral_le_of_norm_le (hvi.abs.mul_const _) (Filter.Eventually.of_forall hbound)
    _ = (∫ t : ℝ, |v t|) * A ^ K * y⁻¹ ^ (K + 1) := by rw [integral_mul_const]; ring

theorem coeffs_zero (K : ℕ) (d : ℕ → ℂ) (C Y0 : ℝ)
    (h : ∀ y : ℝ, Y0 ≤ y → 0 < y →
      ‖∑ j ∈ Finset.Icc 1 K, d j * (Complex.I * y)⁻¹ ^ j‖ ≤ C * y⁻¹ ^ (K + 1)) :
    ∀ j ∈ Finset.Icc 1 K, d j = 0 := by
  classical
  by_contra hne
  push_neg at hne
  have hex : ∃ j, j ∈ Finset.Icc 1 K ∧ d j ≠ 0 := hne
  set j0 := Nat.find hex with hj0
  obtain ⟨hj0mem, hj0ne⟩ := Nat.find_spec hex
  have hmin : ∀ k ∈ Finset.Icc 1 K, k < j0 → d k = 0 := fun k hk hlt => by
    by_contra h; exact Nat.find_min hex hlt ⟨hk, h⟩
  set D : ℝ := ∑ k ∈ Finset.Icc 1 K, ‖d k‖ with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg (fun k _ => norm_nonneg _)
  have hdpos : 0 < ‖d j0‖ := norm_pos_iff.2 hj0ne
  set y : ℝ := max (max Y0 1) (2 * (|C| + D + 1) / ‖d j0‖) with hy
  have hy1 : 1 ≤ y := le_trans (le_max_right _ _) (le_max_left _ _)
  have hypos : 0 < y := by linarith
  have hyY : Y0 ≤ y := le_trans (le_max_left _ _) (le_max_left _ _)
  have hyb : 2 * (|C| + D + 1) / ‖d j0‖ ≤ y := le_max_right _ _
  set t : ℝ := y⁻¹ with ht
  have ht0 : 0 < t := inv_pos.2 hypos
  have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ hy1
  have hw : ‖(Complex.I * y)⁻¹‖ = t := by
    rw [norm_inv, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hypos]
  have hb := h y hyY hypos
  rw [← Finset.add_sum_erase _ _ hj0mem] at hb
  have hrest : ‖∑ k ∈ (Finset.Icc 1 K).erase j0, d k * (Complex.I * y)⁻¹ ^ k‖ ≤ D * t ^ (j0 + 1) := by
    calc _ ≤ ∑ k ∈ (Finset.Icc 1 K).erase j0, ‖d k * (Complex.I * y)⁻¹ ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ (Finset.Icc 1 K).erase j0, ‖d k‖ * t ^ (j0 + 1) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          obtain ⟨hk2, hk1⟩ := Finset.mem_erase.1 hk
          rw [norm_mul, norm_pow, hw]
          rcases lt_or_gt_of_ne hk2 with hlt | hgt
          · rw [hmin k hk1 hlt, norm_zero, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht0.le ht1 hgt) (norm_nonneg _)
      _ = (∑ k ∈ (Finset.Icc 1 K).erase j0, ‖d k‖) * t ^ (j0 + 1) := by rw [Finset.sum_mul]
      _ ≤ D * t ^ (j0 + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun k _ _ => norm_nonneg _)
  have hjK : j0 ≤ K := (Finset.mem_Icc.1 hj0mem).2
  have hmain : ‖d j0‖ * t ^ j0 ≤ |C| * t ^ (j0 + 1) + D * t ^ (j0 + 1) := by
    have e1 : ‖d j0 * (Complex.I * y)⁻¹ ^ j0‖ = ‖d j0‖ * t ^ j0 := by rw [norm_mul, norm_pow, hw]
    rw [← hj0] at hb
    have h2 := norm_sub_le (d j0 * (Complex.I * y)⁻¹ ^ j0 +
      ∑ k ∈ (Finset.Icc 1 K).erase j0, d k * (Complex.I * y)⁻¹ ^ k)
      (∑ k ∈ (Finset.Icc 1 K).erase j0, d k * (Complex.I * y)⁻¹ ^ k)
    simp only [add_sub_cancel_right] at h2
    rw [e1] at h2
    have hCt : C * y⁻¹ ^ (K + 1) ≤ |C| * t ^ (j0 + 1) := by
      rw [← ht]
      calc C * t ^ (K + 1) ≤ |C| * t ^ (K + 1) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| * t ^ (j0 + 1) := mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one ht0.le ht1 (by omega)) (abs_nonneg C)
    linarith
  have hdiv : ‖d j0‖ ≤ (|C| + D) * t := by
    have htj : 0 < t ^ j0 := pow_pos ht0 j0
    have e : (|C| + D) * t * t ^ j0 = |C| * t ^ (j0 + 1) + D * t ^ (j0 + 1) := by ring
    nlinarith
  have hty : (|C| + D) * t < ‖d j0‖ := by
    have hyb' : 2 * (|C| + D + 1) ≤ y * ‖d j0‖ := by rwa [div_le_iff₀ hdpos] at hyb
    rw [ht, ← div_eq_mul_inv, div_lt_iff₀ hypos]
    nlinarith [abs_nonneg C]
  linarith

end NlsGge.ThirdConsultation.M017S
