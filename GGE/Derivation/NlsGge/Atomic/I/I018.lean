/- I-018 PRODUCTION01 (proof development landing kit; HELD for landing). Source: proof development/I018_PROOF01.lean.txt (author proof development; independent review proof development/REVIEW_I018_01.md), identical except this header and the removed check/print lines. Target NlsGge/Atomic/I/I018.lean. -/
import NlsGge.Weights.LowerGrowth
import NlsGge.Measure.CountableGaussian
import NlsGge.Measure.FourierGaussian
import NlsGge.Birkhoff.S03Measure38
import NlsGge.Sobolev.SourceWeighted

/- I-018 PROOF01 (proof development, author). Statement: defs3 STATEMENTS/I.md "## I-018" (verbatim).
   Design object: sobolevSequenceWeight := NlsGge.Birkhoff.sobolevWeight38 (DEFINITIONS/I.lean.md:49, copied).
   Reuse: NlsGge.Measure.lintegral_sequenceEnergy, integral_sequenceEnergy_toReal, integrable_sequenceEnergy_toReal,
   lintegral_sequenceEnergy_ne_top, ae_sequenceSummable, fullWeightRate_pos, fullWeightSequenceGaussian;
   NlsGge.Weights.weight_lower_growth_explicit, weight_even. Summability: exponential lower growth of the rate
   versus the polynomial weight (1+n^2)^m, via Real.pow_div_factorial_le_exp and summable_one_div_int_pow. -/

set_option autoImplicit false

open NlsGge.Pilot NlsGge.Measure NlsGge.Weights MeasureTheory Filter Topology
open scoped ENNReal

namespace NlsGge.ThirdConsultation.I
noncomputable section

abbrev sobolevSequenceWeight := NlsGge.Birkhoff.sobolevWeight38

namespace I018Aux

theorem sobW_eq (m : ℕ) (n : ℤ) : sobolevSequenceWeight m n = (1 + (n : ℝ) ^ 2) ^ m := by
  have hj : japaneseBracket n ^ 2 = 1 + (n : ℝ) ^ 2 := by
    unfold japaneseBracket
    exact Real.sq_sqrt (by positivity)
  unfold sobolevSequenceWeight NlsGge.Birkhoff.sobolevWeight38
  rw [show (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_mul, hj]

theorem rate_lower (lower upper : ℝ) (c : ℕ → ℝ) (hl : 0 < lower)
    (hb : ∀ j : ℕ, lower ≤ c j) (hu : ∀ j : ℕ, c j ≤ upper) (n : ℤ)
    (hn : 16 ≤ 2 * Real.pi * |(n : ℝ)|) :
    lower * Real.exp ((Real.log 16 / 4) * Real.sqrt (2 * Real.pi * |(n : ℝ)|)) ≤
      fullWeightRate c n := by
  have key : fullWeightRate c n = weight c (2 * Real.pi * |(n : ℝ)|) := by
    unfold fullWeightRate
    rcases abs_cases (n : ℝ) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
    · rw [h1, mul_neg, weight_even]
  rw [key]
  exact weight_lower_growth_explicit lower upper c hl hb hu _ hn

theorem finite_small :
    {n : ℤ | ¬ (16 ≤ 2 * Real.pi * |(n : ℝ)|)} ⊆
      Set.Icc (-⌈16 / (2 * Real.pi)⌉) ⌈16 / (2 * Real.pi)⌉ := by
  intro n hn
  simp only [Set.mem_setOf_eq, not_le] at hn
  have h1 : |(n : ℝ)| < 16 / (2 * Real.pi) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have h2 : 16 / (2 * Real.pi) ≤ ((⌈16 / (2 * Real.pi)⌉ : ℤ) : ℝ) := Int.le_ceil _
  have h3 : ((|n| : ℤ) : ℝ) ≤ ((⌈16 / (2 * Real.pi)⌉ : ℤ) : ℝ) := by
    rw [Int.cast_abs]
    linarith
  have h4 : |n| ≤ ⌈16 / (2 * Real.pi)⌉ := by exact_mod_cast h3
  exact Set.mem_Icc.2 (abs_le.mp h4)

theorem summable_ratio (lower upper : ℝ) (c : ℕ → ℝ) (hl : 0 < lower)
    (hb : ∀ j : ℕ, lower ≤ c j) (hu : ∀ j : ℕ, c j ≤ upper) (m : ℕ) :
    Summable (fun n : ℤ => sobolevSequenceWeight m n / fullWeightRate c n) := by
  have hκ : 0 < Real.log 16 / 4 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hD : 0 < lower * (Real.log 16 / 4) ^ (2 * (2 * m + 2)) * (2 * Real.pi) ^ (2 * m + 2) /
      ((2 * (2 * m + 2)).factorial : ℝ) :=
    div_pos (mul_pos (mul_pos hl (pow_pos hκ _)) (pow_pos (by positivity) _))
      (by exact_mod_cast Nat.factorial_pos _)
  have hev : ∀ᶠ n : ℤ in cofinite,
      ‖sobolevSequenceWeight m n / fullWeightRate c n‖ ≤
        (2 ^ m / (lower * (Real.log 16 / 4) ^ (2 * (2 * m + 2)) * (2 * Real.pi) ^ (2 * m + 2) /
          ((2 * (2 * m + 2)).factorial : ℝ))) * (1 / (n : ℝ) ^ 2) := by
    have hfin : ∀ᶠ n : ℤ in cofinite, 16 ≤ 2 * Real.pi * |(n : ℝ)| := by
      rw [Filter.eventually_cofinite]
      exact (Set.finite_Icc _ _).subset finite_small
    filter_upwards [hfin] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      intro h0
      rw [h0] at hn
      norm_num at hn
    have ha1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have hne : n ≠ 0 := by
        rintro rfl
        exact hn0 (by norm_num)
      have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs hne
      have h2 : ((|n| : ℤ) : ℝ) = |(n : ℝ)| := Int.cast_abs
      rw [← h2]
      exact_mod_cast h1
    have hapos : 0 < |(n : ℝ)| := by linarith
    have hsq : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
    set a := |(n : ℝ)| with ha
    set L : ℕ := 2 * m + 2 with hL
    set κ := Real.log 16 / 4 with hκdef
    set D := lower * κ ^ (2 * L) * (2 * Real.pi) ^ L / ((2 * L).factorial : ℝ) with hDdef
    have hD0 : 0 < D := hD
    have hx0 : 0 ≤ κ * Real.sqrt (2 * Real.pi * a) :=
      mul_nonneg hκ.le (Real.sqrt_nonneg _)
    have hE := Real.pow_div_factorial_le_exp (κ * Real.sqrt (2 * Real.pi * a)) hx0 (2 * L)
    have hpow : (κ * Real.sqrt (2 * Real.pi * a)) ^ (2 * L) = κ ^ (2 * L) * (2 * Real.pi) ^ L * a ^ L := by
      have hs2 : Real.sqrt (2 * Real.pi * a) ^ (2 * L) = (2 * Real.pi * a) ^ L := by
        rw [pow_mul, Real.sq_sqrt (mul_pos (by positivity) hapos).le]
      rw [mul_pow, hs2]
      ring
    have hq1 : lower * ((κ * Real.sqrt (2 * Real.pi * a)) ^ (2 * L) / ((2 * L).factorial : ℝ)) ≤
        lower * Real.exp (κ * Real.sqrt (2 * Real.pi * a)) :=
      mul_le_mul_of_nonneg_left hE hl.le
    have hq2 := rate_lower lower upper c hl hb hu n hn
    have hq' : D * a ^ L ≤ fullWeightRate c n := by
      have heq : D * a ^ L = lower * ((κ * Real.sqrt (2 * Real.pi * a)) ^ (2 * L) / ((2 * L).factorial : ℝ)) := by
        rw [hpow, hDdef]
        ring
      rw [heq]
      exact hq1.trans hq2
    have hDa : 0 < D * a ^ L := mul_pos hD0 (pow_pos hapos _)
    have hqpos : 0 < fullWeightRate c n := lt_of_lt_of_le hDa hq'
    have hsw : sobolevSequenceWeight m n ≤ 2 ^ m * a ^ (2 * m) := by
      rw [sobW_eq]
      calc (1 + (n : ℝ) ^ 2) ^ m ≤ (2 * (n : ℝ) ^ 2) ^ m :=
            pow_le_pow_left₀ (by positivity) (by nlinarith [hsq, ha1]) m
        _ = 2 ^ m * a ^ (2 * m) := by
            rw [mul_pow, hsq, ← pow_mul]
    have hLn : a ^ L = a ^ (2 * m) * a ^ 2 := by
      rw [hL, pow_add]
    rw [Real.norm_of_nonneg (div_nonneg (NlsGge.Birkhoff.sobolevWeight38_nonneg m n) hqpos.le),
      div_le_iff₀ hqpos]
    have hfin2 : (2 ^ m / D) * (1 / (n : ℝ) ^ 2) * (D * a ^ L) = 2 ^ m * a ^ (2 * m) := by
      rw [hsq, hLn]
      field_simp [hD0.ne', hapos.ne']
    calc sobolevSequenceWeight m n ≤ 2 ^ m * a ^ (2 * m) := hsw
      _ = (2 ^ m / D) * (1 / (n : ℝ) ^ 2) * (D * a ^ L) := hfin2.symm
      _ ≤ (2 ^ m / D) * (1 / (n : ℝ) ^ 2) * fullWeightRate c n :=
          mul_le_mul_of_nonneg_left hq' (mul_nonneg (div_nonneg (by positivity) hD0.le)
            (by positivity))
  exact Summable.of_norm_bounded_eventually (g := fun n : ℤ => (2 ^ m / (lower * (Real.log 16 / 4) ^ (2 * (2 * m + 2)) * (2 * Real.pi) ^ (2 * m + 2) /
      ((2 * (2 * m + 2)).factorial : ℝ))) * (1 / (n : ℝ) ^ 2))
    (((Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)).mul_left _) hev

end I018Aux

theorem i018 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    (∀ m : ℕ,
      Summable (fun n : ℤ => sobolevSequenceWeight m n / fullWeightRate c.val n) ∧
      Integrable (fun z : ℤ → ℂ =>
        (sequenceEnergy (sobolevSequenceWeight m) z).toReal)
        (fullWeightSequenceGaussian c.val) ∧
      (∫ z : ℤ → ℂ, (sequenceEnergy (sobolevSequenceWeight m) z).toReal
        ∂fullWeightSequenceGaussian c.val) =
        ∑' n : ℤ, sobolevSequenceWeight m n / fullWeightRate c.val n ∧
      (∫⁻ z : ℤ → ℂ, sequenceEnergy (sobolevSequenceWeight m) z
        ∂fullWeightSequenceGaussian c.val) =
        ∑' n : ℤ, ENNReal.ofReal
          (sobolevSequenceWeight m n / fullWeightRate c.val n) ∧
      (∫⁻ z : ℤ → ℂ, sequenceEnergy (sobolevSequenceWeight m) z
        ∂fullWeightSequenceGaussian c.val) < ⊤) ∧
    (∀ᵐ z ∂fullWeightSequenceGaussian c.val,
      ∀ m : ℕ, SobolevSquareSummable (m : ℝ) z) := by
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lower ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ upper := fun j => (hb j).2
  have hq : ∀ n : ℤ, 0 < fullWeightRate c.val n :=
    fun n => fullWeightRate_pos lower upper c.val hl hb' hu' n
  have hw : ∀ (m : ℕ) (n : ℤ), 0 ≤ sobolevSequenceWeight m n := fun m n =>
    NlsGge.Birkhoff.sobolevWeight38_nonneg m n
  have hs : ∀ m : ℕ, Summable (fun n : ℤ => sobolevSequenceWeight m n / fullWeightRate c.val n) :=
    fun m => I018Aux.summable_ratio lower upper c.val hl hb' hu' m
  refine ⟨fun m => ⟨hs m, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact integrable_sequenceEnergy_toReal _ _ hq (hw m) (hs m)
  · exact integral_sequenceEnergy_toReal _ _ hq (hw m) (hs m)
  · unfold fullWeightSequenceGaussian
    rw [lintegral_sequenceEnergy _ _ hq (hw m)]
  · exact lt_top_iff_ne_top.2 (lintegral_sequenceEnergy_ne_top _ _ hq (hw m) (hs m))
  · rw [MeasureTheory.ae_all_iff]
    intro m
    filter_upwards [ae_sequenceSummable _ _ hq (hw m) (hs m)] with z hz
    exact hz

end
end NlsGge.ThirdConsultation.I

