import NlsGge.Measure.CountableGaussian
import NlsGge.Sobolev.SourceWeighted

/-! Concrete full-source-rate Sobolev and weighted membership support.
The entire hierarchy and every integer coordinate, including zero, are retained. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace NlsGge.Measure

lemma abs_le_japaneseBracket (n : ℤ) : |(n : ℝ)| ≤ NlsGge.Pilot.japaneseBracket n := by
  unfold NlsGge.Pilot.japaneseBracket
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  linarith

/-- The comparison omits only the zero index in its bound, not in the actual sum. -/
lemma summable_japaneseBracket_rpow_neg (b : ℝ) (hb : 1 < b) :
    Summable (fun n : ℤ => Real.rpow (NlsGge.Pilot.japaneseBracket n) (-b)) := by
  apply (Real.summable_abs_int_rpow hb).of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hp : 0 ≤ Real.rpow (NlsGge.Pilot.japaneseBracket n) (-b) :=
    Real.rpow_nonneg (NlsGge.Pilot.japaneseBracket_pos n).le (-b)
  rw [Real.norm_eq_abs, abs_of_nonneg hp]
  exact Real.rpow_le_rpow_of_nonpos (abs_pos.mpr hn') (abs_le_japaneseBracket n) (by linarith)

lemma summable_japaneseBracket_sobolev_decay (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    Summable (fun n : ℤ => Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s)) := by
  simpa only [neg_mul] using summable_japaneseBracket_rpow_neg (2 * s) (by linarith)

lemma summable_fullWeightRate_invSobolev (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (m : ℕ) :
    Summable (fun n : ℤ => Real.rpow (NlsGge.Pilot.japaneseBracket n) (2 * (m : ℝ)) /
      fullWeightRate c n) := by
  let cb : NlsGge.Pilot.BoundedCoefficients lower upper :=
    ⟨c, hlower, (hbound 0).trans (hupper 0), fun j => ⟨hbound j, hupper j⟩⟩
  obtain ⟨C, _hC, hcmp⟩ := NlsGge.Pilot.sourceSobolevComparison lower upper (m : ℝ) 1 hlower
  have hd := (summable_japaneseBracket_sobolev_decay 1 (by norm_num)).mul_left C
  apply Summable.of_nonneg_of_le
    (fun n => div_nonneg (Real.rpow_nonneg (NlsGge.Pilot.japaneseBracket_pos n).le _)
      (fullWeightRate_pos lower upper c hlower hbound hupper n).le) (fun n => ?_) hd
  apply (div_le_iff₀ (fullWeightRate_pos lower upper c hlower hbound hupper n)).2
  have h := hcmp cb n
  change Real.rpow (NlsGge.Pilot.japaneseBracket n) (2 * (m : ℝ)) ≤
    C * (fullWeightRate c n * Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * 1)) at h
  convert h using 1 <;> ring

lemma ae_fullWeightSequenceGaussian_sobolev (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (m : ℕ) :
    ∀ᵐ z ∂fullWeightSequenceGaussian c, NlsGge.Pilot.SobolevSquareSummable (m : ℝ) z :=
  ae_sequenceSummable (fullWeightRate c)
    (fun n => Real.rpow (NlsGge.Pilot.japaneseBracket n) (2 * (m : ℝ)))
    (fun n => fullWeightRate_pos lower upper c hlower hbound hupper n)
    (fun n => (Real.rpow_nonneg (NlsGge.Pilot.japaneseBracket_pos n).le _))
    (summable_fullWeightRate_invSobolev lower upper c hlower hbound hupper m)

lemma ae_fullWeightSequenceGaussian_allSobolev (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) :
    ∀ᵐ z ∂fullWeightSequenceGaussian c,
      ∀ m : ℕ, NlsGge.Pilot.SobolevSquareSummable (m : ℝ) z := by
  rw [ae_all_iff]
  exact fun m => ae_fullWeightSequenceGaussian_sobolev lower upper c hlower hbound hupper m

lemma ae_fullWeightSequenceGaussian_everyRealSobolev (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) :
    ∀ᵐ z ∂fullWeightSequenceGaussian c,
      ∀ r : ℝ, NlsGge.Pilot.SobolevSquareSummable r z := by
  filter_upwards [ae_fullWeightSequenceGaussian_allSobolev lower upper c hlower hbound hupper]
    with z hz
  intro r
  obtain ⟨m, hm⟩ := exists_nat_ge r
  exact NlsGge.Pilot.sobolevSquareSummable_restrict r (m : ℝ) hm z (hz m)

lemma ae_fullWeightSequenceGaussian_weighted (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    ∀ᵐ z ∂fullWeightSequenceGaussian c,
      NlsGge.Pilot.WeightedSquareSummable (fullWeightRate c) s z := by
  have hq := fun n => fullWeightRate_pos lower upper c hlower hbound hupper n
  have hd : Summable (fun n : ℤ =>
      (fullWeightRate c n * Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s)) /
        fullWeightRate c n) :=
    (summable_japaneseBracket_sobolev_decay s hs).congr (fun n => by
      field_simp [(hq n).ne'])
  exact ae_sequenceSummable (fullWeightRate c)
    (fun n => fullWeightRate c n * Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s)) hq
    (fun n => mul_nonneg (hq n).le (Real.rpow_nonneg (NlsGge.Pilot.japaneseBracket_pos n).le _)) hd

end NlsGge.Measure
