import QuantumNLS.Local001L2

set_option autoImplicit false
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate BigOperators
namespace QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.LocalSpectral

/-- The `k`th free mode in the parity sector of `n`. -/
def sourceMode (n k : ℤ) : ℤ := n + 2 * k

theorem sourceMode_parity (n k : ℤ) :
    LocalSpectral.parity (sourceMode n k) = LocalSpectral.parity n := by
  have hk : Even (2 * k : ℤ) := even_two_mul k
  by_cases hn : Even n
  · have hsum : Even (n + 2 * k) := by
      rcases hn with ⟨a, ha⟩
      rcases hk with ⟨b, hb⟩
      change n = a + a at ha
      change 2 * k = b + b at hb
      refine ⟨a + b, ?_⟩
      change n + 2 * k = (a + b) + (a + b)
      rw [ha, hb]
      ring
    simp [sourceMode, LocalSpectral.parity, hn, hsum]
  · have hsum : ¬ Even (n + 2 * k) := by
      intro h
      rcases h with ⟨a, ha⟩
      rcases hk with ⟨b, hb⟩
      change 2 * k = b + b at hb
      apply hn
      refine ⟨a - b, ?_⟩
      change n = (a - b) + (a - b)
      calc
        n = (n + 2 * k) - 2 * k := by ring
        _ = (a + a) - (b + b) := by rw [ha, hb]
        _ = (a - b) + (a - b) := by ring
    simp [sourceMode, LocalSpectral.parity, hn, hsum]

/-- Squared reciprocal gaps indexed over all integer shifts. -/
def denominatorMajorant (L r : ℝ) (k : ℤ) : ℝ :=
  (spacing L * |(k : ℝ)| - r)⁻¹ ^ 2

/-- Each squared multiplier is bounded by the shifted reciprocal-square majorant. -/
theorem freeResolventMultiplier_sq_le_majorant {L r : ℝ} (hL : 0 < L)
    (hr : 0 < r) (hsmall : r < spacing L / 2) {n : ℤ} {z : ℂ}
    (hz : OnGamma L r n z) (k : ℤ) :
    ‖freeResolventMultiplier L n z (sourceMode n k)‖ ^ 2 ≤ denominatorMajorant L r k := by
  by_cases hk : k = 0
  · subst k
    have hz0 : ‖z - (LocalSpectral.pm L n : ℂ)‖ = r := hz
    simp only [sourceMode, mul_zero, add_zero]
    rw [freeResolventMultiplier, norm_inv, hz0]
    simp [denominatorMajorant, spacing, hr.ne']
  · have hdist := contour_distance_lower hL (n := n) (k := k) hz
    have hdist' : spacing L * |(k : ℝ)| - r ≤
        ‖z - (LocalSpectral.pm L (sourceMode n k) : ℂ)‖ := by
      simpa [sourceMode] using hdist
    have hdenpos : 0 < ‖z - (LocalSpectral.pm L (sourceMode n k) : ℂ)‖ :=
      lt_of_lt_of_le hr (contour_denominator_lower hL hsmall hz (sourceMode_parity n k))
    have hkabs : 1 ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    have hd : 0 < spacing L := spacing_pos hL
    have hminor : 0 < spacing L * |(k : ℝ)| - r := by nlinarith
    have hinv : ‖z - (LocalSpectral.pm L (sourceMode n k) : ℂ)‖⁻¹ ≤
        (spacing L * |(k : ℝ)| - r)⁻¹ := (inv_le_inv₀ hdenpos hminor).2 hdist'
    rw [freeResolventMultiplier, norm_inv, denominatorMajorant]
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hinv

/-- The reciprocal-square tail converges by comparison with `∑ (k+1)⁻²`. -/
theorem denominatorTail_summable {L r : ℝ} (hL : 0 < L)
    (hsmall : r < spacing L / 2) :
    Summable (fun k : ℕ => (spacing L * ((k + 1 : ℕ) : ℝ) - r)⁻¹ ^ 2) := by
  have hd : 0 < spacing L := spacing_pos hL
  have hbase : Summable (fun k : ℕ => (k : ℝ) ^ (-2 : ℝ)) :=
    (Real.summable_nat_rpow).2 (by norm_num : (-2 : ℝ) < -1)
  have hnat : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) :=
    hbase.comp_injective (fun _ _ h => by omega)
  refine Summable.of_norm_bounded (hnat.mul_left (4 / spacing L ^ 2)) ?_
  intro k
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hden : spacing L * ((k + 1 : ℕ) : ℝ) - r ≥
      spacing L / 2 * ((k + 1 : ℕ) : ℝ) := by
    have hmul : spacing L / 2 ≤ spacing L / 2 * ((k + 1 : ℕ) : ℝ) := by
      calc
        spacing L / 2 = spacing L / 2 * 1 := by ring
        _ ≤ spacing L / 2 * ((k + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
    have hbase' : spacing L * ((k + 1 : ℕ) : ℝ) -
        spacing L / 2 * ((k + 1 : ℕ) : ℝ) =
        spacing L / 2 * ((k + 1 : ℕ) : ℝ) := by ring
    rw [← hbase']
    nlinarith
  have hpositive : 0 < spacing L * ((k + 1 : ℕ) : ℝ) - r := by
    have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    nlinarith
  have hinv : (spacing L * ((k + 1 : ℕ) : ℝ) - r)⁻¹ ≤
      (spacing L / 2 * ((k + 1 : ℕ) : ℝ))⁻¹ :=
    (inv_le_inv₀ hpositive (by positivity)).2 hden
  have hbound : (spacing L * ((k + 1 : ℕ) : ℝ) - r)⁻¹ ^ 2 ≤
      (4 / spacing L ^ 2) * (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
    have hsq : (spacing L * ((k + 1 : ℕ) : ℝ) - r)⁻¹ ^ 2 ≤
        (spacing L / 2 * ((k + 1 : ℕ) : ℝ))⁻¹ ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 hinv
    have hkpos : ((k + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast Nat.succ_pos k)
    have hdne : spacing L ≠ 0 := ne_of_gt hd
    calc
      (spacing L * ((k + 1 : ℕ) : ℝ) - r)⁻¹ ^ 2 ≤
          (spacing L / 2 * ((k + 1 : ℕ) : ℝ))⁻¹ ^ 2 := hsq
      _ = (4 / spacing L ^ 2) * (((k + 1 : ℕ) : ℝ) ^ (-2 : ℝ)) := by
        rw [Real.rpow_neg (by positivity)]
        field_simp [hdne, hkpos]
        norm_num
        ring
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hbound

/-- The integer-indexed majorant is summable. -/
theorem denominatorMajorant_summable {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) : Summable (denominatorMajorant L r) := by
  have htail := denominatorTail_summable hL hsmall
  have hpos : Summable (fun k : ℕ => denominatorMajorant L r (k + 1 : ℤ)) := by
    apply htail.congr
    intro k
    simp only [denominatorMajorant, Int.cast_add, Int.cast_natCast, Int.cast_one]
    rw [abs_of_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity)]
    rw [Nat.cast_add, Nat.cast_one]
  have hneg : Summable (fun k : ℕ => denominatorMajorant L r (-(k + 1 : ℤ))) := by
    refine hpos.congr ?_
    intro k
    rw [denominatorMajorant, denominatorMajorant]
    simp only [Int.cast_neg, abs_neg]
  have hnat : Summable (fun k : ℕ => denominatorMajorant L r (k : ℤ)) := by
    rw [← summable_nat_add_iff 1]
    convert hpos using 1 <;> simp
  have hnatneg : Summable (fun k : ℕ => denominatorMajorant L r (-(k : ℤ))) := by
    rw [← summable_nat_add_iff 1]
    convert hneg using 1 <;> simp
  exact Summable.of_nat_of_neg hnat hnatneg

/-- The majorant sums to the source denominator series. -/
theorem denominatorMajorant_tsum_eq_source {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) :
    ∑' k : ℤ, denominatorMajorant L r k =
      r⁻¹ ^ 2 + 2 * ∑' k : ℕ+, (spacing L * (k : ℝ) - r)⁻¹ ^ 2 := by
  have hs := denominatorMajorant_summable hL hr hsmall
  rw [tsum_int_eq_zero_add_tsum_pnat]
  · have hpos : (fun k : ℕ+ => denominatorMajorant L r (k : ℤ)) =
        fun k : ℕ+ => (spacing L * (k : ℝ) - r)⁻¹ ^ 2 := by
      funext k
      simp [denominatorMajorant, abs_of_pos (show (0 : ℝ) < (k : ℝ) by exact_mod_cast k.property)]
    have hneg : (fun k : ℕ+ => denominatorMajorant L r (-(k : ℤ))) =
        fun k : ℕ+ => (spacing L * (k : ℝ) - r)⁻¹ ^ 2 := by
      funext k
      simp [denominatorMajorant,
        abs_of_neg (show (-(k : ℝ) : ℝ) < 0 by exact neg_lt_zero.mpr (by exact_mod_cast k.property))]
    rw [hpos, hneg]
    have hzero : denominatorMajorant L r (0 : ℤ) = r⁻¹ ^ 2 := by
      simp [denominatorMajorant, spacing]
    rw [hzero]
    ring
  · exact hs

/-- The squared free-resolvent multipliers have the exact source-series majorant. -/
theorem freeResolventMultiplier_sq_summable_bound {L r : ℝ} (hL : 0 < L)
    (n : ℤ) {z : ℂ} (hr : 0 < r) (hsmall : r < spacing L / 2)
    (hz : OnGamma L r n z) :
    Summable (fun k : ℤ => ‖freeResolventMultiplier L n z (sourceMode n k)‖ ^ 2) ∧
    ∑' k : ℤ, ‖freeResolventMultiplier L n z (sourceMode n k)‖ ^ 2 ≤
      r⁻¹ ^ 2 + 2 * ∑' k : ℕ+, (spacing L * (k : ℝ) - r)⁻¹ ^ 2 := by
  have hmajor := denominatorMajorant_summable hL hr hsmall
  have hsq : Summable (fun k : ℤ =>
      ‖freeResolventMultiplier L n z (sourceMode n k)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _)
      (fun k => freeResolventMultiplier_sq_le_majorant hL hr hsmall hz k) hmajor
  refine ⟨hsq, ?_⟩
  calc
    ∑' k : ℤ, ‖freeResolventMultiplier L n z (sourceMode n k)‖ ^ 2 ≤
        ∑' k : ℤ, denominatorMajorant L r k :=
      hsq.tsum_le_tsum (fun k => freeResolventMultiplier_sq_le_majorant hL hr hsmall hz k) hmajor
    _ = r⁻¹ ^ 2 + 2 * ∑' k : ℕ+, (spacing L * (k : ℝ) - r)⁻¹ ^ 2 :=
      denominatorMajorant_tsum_eq_source hL hr hsmall

#print axioms freeResolventMultiplier_sq_summable_bound

end QuantumNLS.ResetFreeResolventLOCAL001
