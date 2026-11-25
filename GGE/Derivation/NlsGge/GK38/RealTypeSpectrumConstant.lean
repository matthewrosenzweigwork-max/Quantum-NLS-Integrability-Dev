import NlsGge.GK38.RealTypeSpectrum
import NlsGge.GK38.PairRealBridgeProbe

/-! # S5: concrete nonfree constant labels by the real squared-frequency invariant

Supplemental regression route independently approved in
REVIEW_S5_CONSTANT_PROBE_ROUTE.md. The zero-frequency formula is separate;
no S6 multiplicity formula or S7 continuity theorem is used.
-/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations MeasureTheory
namespace NlsGge.GK38
noncomputable section

theorem realType_const_real_smul38 (t : ℝ) : t • constL2 1 = constL2 (t : ℂ) := by
  letI : IsFiniteMeasure spatialMeasure := by unfold spatialMeasure; infer_instance
  have h := (Lp.constₗ 2 spatialMeasure ℝ).map_smul t (1 : ℂ)
  simpa only [Lp.constₗ_apply, Complex.real_smul, mul_one, constL2] using h.symm

/-- A real root of the actual constant model has an integral squared frequency. -/
theorem realType_const_root_frequency38 (t x : ℝ)
    (hx : perChar (realSlice (constL2 (t : ℂ))) (x : ℂ) = 0) :
    ∃ m : ℤ, x ^ 2 - t ^ 2 = ((m : ℝ) * Real.pi) ^ 2 := by
  obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq
    ((x : ℂ) ^ 2 - (t : ℂ) * star (t : ℂ)) (n := 2) (by norm_num)
  have hκreal : κ ^ 2 = (x : ℂ) ^ 2 - (t : ℂ) ^ 2 := by
    simpa [pow_two] using hκ
  by_cases hzero : κ = 0
  · refine ⟨0, ?_⟩
    rw [hzero, zero_pow (by decide : 2 ≠ 0)] at hκreal
    have hreal : x ^ 2 - t ^ 2 = 0 := by exact_mod_cast hκreal.symm
    simpa using hreal
  · have hf := perChar_realSlice_const (t : ℂ) (x : ℂ) κ hzero hκ
    rw [hx] at hf
    have hs : Complex.sin κ = 0 := by
      have hs2 : Complex.sin κ ^ 2 = 0 :=
        (mul_eq_zero.mp hf.symm).resolve_left (by norm_num)
      simpa using hs2
    obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp hs
    refine ⟨m, ?_⟩
    have he : (x : ℂ) ^ 2 - (t : ℂ) ^ 2 = ((m : ℂ) * (Real.pi : ℂ)) ^ 2 := by
      rw [← hκreal, hm]
    exact_mod_cast he

/-- Connectedness of an integer-valued continuous invariant retains the free index. -/
theorem realType_const_label_square38 (k : ℤ) :
    (lamSeq (realSlice (constL2 1)) k).re ^ 2 = 1 + ((k / 2 : ℤ) : ℝ) ^ 2 * Real.pi ^ 2 := by
  let x : ℝ → ℝ := fun t => (lamSeq (realSlice (t • constL2 1)) k).re
  let q : ℝ → ℝ := fun t => (x t ^ 2 - t ^ 2) / Real.pi ^ 2
  have hxcont : ContinuousOn x (Icc 0 1) :=
    Complex.continuous_re.comp_continuousOn (periodic_real_path_continuous38 (constL2 1) k)
  have hqcont : ContinuousOn q (Icc 0 1) :=
    (hxcont.pow 2 |>.sub (continuous_id.continuousOn.pow 2)).div_const (Real.pi ^ 2)
  have hgrid (t : ℝ) (_ht : t ∈ Icc 0 1) : ∃ m : ℤ, q t = (m : ℝ) := by
    have hroot : perChar (realSlice (constL2 (t : ℂ))) (x t : ℂ) = 0 := by
      rw [← realType_const_real_smul38, ← lamSeq_real_cast38]
      exact (lamSeq_enumeration38 (realSlice (t • constL2 1))).1 k
    obtain ⟨m, hm⟩ := realType_const_root_frequency38 t (x t) hroot
    refine ⟨m ^ 2, ?_⟩
    dsimp only [q]
    rw [hm]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hsub : q '' Icc 0 1 ⊆ range ((↑) : ℤ → ℝ) := by
    rintro y ⟨t, ht, rfl⟩
    obtain ⟨m, hm⟩ := hgrid t ht
    exact ⟨m, hm.symm⟩
  have hd : IsDiscrete (q '' Icc 0 1) :=
    Real.isClosedEmbedding_intCast.isInducing.isDiscrete_range.mono hsub
  have hsingle := (isPreconnected_Icc.image q hqcont).isDiscrete_iff_subsingleton.mp hd
  have he := hsingle (mem_image_of_mem q (by norm_num : (1 : ℝ) ∈ Icc 0 1))
    (mem_image_of_mem q (by norm_num : (0 : ℝ) ∈ Icc 0 1))
  have hx0 : x 0 = ((k / 2 : ℤ) : ℝ) * Real.pi := by
    simp only [x, zero_smul, realSlice_zero, lamSeq_zero38, countingCenter_re38]
  have hx1 : x 1 = (lamSeq (realSlice (constL2 1)) k).re := by simp only [x, one_smul]
  dsimp only [q] at he
  rw [hx0, hx1] at he
  have hpi : Real.pi ^ 2 ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  field_simp at he
  nlinarith

theorem realType_const_unit_root_pair38 (x : ℝ) (hx : x ^ 2 = 1)
    (hroot : perChar (realSlice (constL2 1)) (x : ℂ) = 0) :
    (x : ℂ) = lamMinus (realSlice (constL2 1)) 0 ∨
      (x : ℂ) = lamPlus (realSlice (constL2 1)) 0 := by
  obtain ⟨k, hk⟩ := ((lamSeq_enumeration38 (realSlice (constL2 1))).2.1 (x : ℂ)).mp hroot
  have hs := realType_const_label_square38 k
  rw [hk, Complex.ofReal_re, hx] at hs
  have hfreq : ((k / 2 : ℤ) : ℝ) ^ 2 * Real.pi ^ 2 = 0 := by linarith
  have hsq : ((k / 2 : ℤ) : ℝ) ^ 2 = 0 :=
    (mul_eq_zero.mp hfreq).resolve_right (pow_ne_zero _ Real.pi_ne_zero)
  have hm : k / 2 = 0 := by
    have hreal : ((k / 2 : ℤ) : ℝ) = 0 := by nlinarith
    exact_mod_cast hreal
  have hi : k = 0 ∨ k = 1 := by omega
  rcases hi with hi | hi
  · left
    simpa only [hi, lamMinus, mul_zero] using hk.symm
  · right
    simpa only [hi, lamPlus, mul_zero, zero_add] using hk.symm

theorem realType_const_central_labels38 :
    lamMinus (realSlice (constL2 1)) 0 = -1 ∧ lamPlus (realSlice (constL2 1)) 0 = 1 := by
  have hmroot : perChar (realSlice (constL2 1)) (((-1 : ℝ)) : ℂ) = 0 := by
    rw [Complex.ofReal_neg, Complex.ofReal_one]
    exact perChar_realSlice_const_double 1 (-1) (by norm_num)
  have hproot : perChar (realSlice (constL2 1)) ((1 : ℝ) : ℂ) = 0 := by
    rw [Complex.ofReal_one]
    exact perChar_realSlice_const_double 1 1 (by norm_num)
  have hm := realType_const_unit_root_pair38 (-1) (by norm_num) hmroot
  have hp := realType_const_unit_root_pair38 1 (by norm_num) hproot
  have ho := periodic_pair_re_order38 (constL2 1) 0
  rcases hm with hm | hm <;> rcases hp with hp | hp
  · have he := hm.trans hp.symm
    norm_num at he
  · constructor
    · simpa only [Complex.ofReal_neg, Complex.ofReal_one] using hm.symm
    · simpa only [Complex.ofReal_one] using hp.symm
  · have hmre := congrArg Complex.re hm
    have hpre := congrArg Complex.re hp
    simp only [Complex.ofReal_re] at hmre hpre
    linarith
  · have he := hm.trans hp.symm
    norm_num at he

/-- The negative pair lies below the now-identified central root, fixing the square-root sign. -/
theorem realType_const_negative_labels38 :
    lamMinus (realSlice (constL2 1)) (-1) = ((-Real.sqrt (Real.pi ^ 2 + 1) : ℝ) : ℂ) ∧
    lamPlus (realSlice (constL2 1)) (-1) = ((-Real.sqrt (Real.pi ^ 2 + 1) : ℝ) : ℂ) := by
  have hlabel (k : ℤ) (hk : k = -2 ∨ k = -1) :
      lamSeq (realSlice (constL2 1)) k = ((-Real.sqrt (Real.pi ^ 2 + 1) : ℝ) : ℂ) := by
    have hs := realType_const_label_square38 k
    have hdiv : k / 2 = -1 := by rcases hk with hk | hk <;> subst k <;> norm_num
    rw [hdiv] at hs
    simp only [Int.cast_neg, Int.cast_one, neg_sq, one_pow, one_mul] at hs
    have hle := lamSeq_mono38 (realSlice (constL2 1)) (show k ≤ 0 by rcases hk with hk | hk <;> omega)
    change complexLexLE38 (lamSeq (realSlice (constL2 1)) k) (lamMinus (realSlice (constL2 1)) 0) at hle
    rw [realType_const_central_labels38.1] at hle
    have hn : (lamSeq (realSlice (constL2 1)) k).re ≤ -1 := by
      rcases (complexLexLE_iff38 _ _).mp hle with h | h
      · simpa using h.le
      · simpa using h.1.le
    have hsqrt : Real.sqrt (Real.pi ^ 2 + 1) ^ 2 = Real.pi ^ 2 + 1 :=
      Real.sq_sqrt (by positivity)
    have hr : (lamSeq (realSlice (constL2 1)) k).re = -Real.sqrt (Real.pi ^ 2 + 1) := by
      nlinarith [Real.sqrt_nonneg (Real.pi ^ 2 + 1)]
    rw [lamSeq_real_cast38, hr]
  exact ⟨hlabel (-2) (Or.inl rfl), hlabel (-1) (Or.inr rfl)⟩

end
end NlsGge.GK38
