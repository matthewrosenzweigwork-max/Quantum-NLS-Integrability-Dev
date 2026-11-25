import Mathlib
import NlsGge.Atomic.KST.KST055

set_option autoImplicit false
noncomputable section

namespace NlsGge.Atomic.DM019

open NlsGge.Atomic.KST

/-- The nonzero denominator displacements in the source near region
`0 < |ν| ≤ |n|`.  Summing over all integers is convenient; for an even-mode
remainder the odd terms vanish. -/
def nearDisplacements (n : ℤ) : Finset ℤ :=
  (Finset.Icc (-(n.natAbs : ℤ)) (n.natAbs : ℤ)).filter (fun ν => ν ≠ 0)

/-- The near two-denominator contribution of a scalar remainder. -/
def nearDenominatorSum (x : ℤ → ℂ) (n : ℤ) : ℝ :=
  ∑ ν ∈ nearDisplacements n,
    ‖x (2 * n - ν)‖ ^ 2 / (ν.natAbs : ℝ) ^ 2

/-- The near fourth-denominator factor in the Cauchy estimate. -/
def nearFourthDenominatorSum (x : ℤ → ℂ) (n : ℤ) : ℝ :=
  ∑ ν ∈ nearDisplacements n,
    ‖x (2 * n - ν)‖ ^ 2 / (ν.natAbs : ℝ) ^ 4

/-- The even-mode hypotheses needed from a slowly increasing source weight.
No positivity, monotonicity, or doubling condition is imposed on odd modes. -/
structure EvenSlowWeight (ω : ℤ → ℝ) (C₀ : ℝ) : Prop where
  positive : ∀ k, k % 2 = 0 → 0 < ω k
  even : ∀ k, k % 2 = 0 → ω (-k) = ω k
  radial_mono : ∀ k l, k % 2 = 0 → l % 2 = 0 →
    k.natAbs ≤ l.natAbs → ω k ≤ ω l
  doubling : ∀ k, k % 2 = 0 → ω (2 * k) ≤ C₀ * ω k

/-- The actual weighted remainder `r̄=ωr`, extended by zero on odd modes. -/
def weightedRemainder (ω : ℤ → ℝ) (r : ℤ → ℂ) : ℤ → ℂ :=
  fun k => (ω k : ℂ) * r k

private lemma natAbs_le_of_near_mem {n ν : ℤ} (hν : ν ∈ nearDisplacements n) :
    ν.natAbs ≤ n.natAbs := by
  have hmem := Finset.mem_filter.mp hν
  rw [Finset.mem_Icc] at hmem
  rcases hmem with ⟨hlo, hhi⟩
  have hνabs : (ν.natAbs : ℤ) ≤ (n.natAbs : ℤ) := by
    rw [Int.natCast_natAbs]
    exact (abs_le).2 ⟨by omega, by omega⟩
  exact_mod_cast hνabs

private lemma near_frequency_tail {n ν : ℤ} (hν : ν ∈ nearDisplacements n) :
    n.natAbs ≤ (2 * n - ν).natAbs := by
  have hνabs := natAbs_le_of_near_mem hν
  let k := 2 * n - ν
  rcases le_total 0 n with hn | hn
  · have hnabs : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hn
    have hkpos : 0 ≤ k := by
      have hlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hν).1).1
      have hhi := (Finset.mem_Icc.mp (Finset.mem_filter.mp hν).1).2
      rw [← hnabs] at hlo hhi
      omega
    have hkabs : (k.natAbs : ℤ) = k := Int.natAbs_of_nonneg hkpos
    have hcast : (n.natAbs : ℤ) ≤ (k.natAbs : ℤ) := by rw [hnabs, hkabs]; omega
    exact_mod_cast hcast
  · have hnneg : n ≤ 0 := hn
    have hnabs : (n.natAbs : ℤ) = -n := by
      have h := Int.natAbs_of_nonneg (show 0 ≤ -n by omega)
      simpa [Int.natAbs_neg] using h
    have hkneg : k ≤ 0 := by
      have hlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hν).1).1
      have hhi := (Finset.mem_Icc.mp (Finset.mem_filter.mp hν).1).2
      rw [hnabs] at hlo hhi
      omega
    have hkabs : (k.natAbs : ℤ) = -k := by
      have h := Int.natAbs_of_nonneg (show 0 ≤ -k by omega)
      simpa [Int.natAbs_neg] using h
    have hcast : (n.natAbs : ℤ) ≤ (k.natAbs : ℤ) := by rw [hnabs, hkabs]; omega
    exact_mod_cast hcast

private lemma near_weight_compare {ω : ℤ → ℝ} {C₀ : ℝ}
    (hω : EvenSlowWeight ω C₀) {n ν : ℤ}
    (hν : ν ∈ nearDisplacements n) (hkEven : (2 * n - ν) % 2 = 0) :
    ω (2 * n) ≤ C₀ * ω (2 * n - ν) := by
  let k := 2 * n - ν
  have htail := near_frequency_tail hν
  have htwoN : (2 * n).natAbs ≤ (2 * k).natAbs := by
    simpa [Int.natAbs_mul] using Nat.mul_le_mul_left 2 htail
  have hmono : ω (2 * n) ≤ ω (2 * k) :=
    hω.radial_mono (2 * n) (2 * k) (by omega) (by omega) htwoN
  calc
    ω (2 * n) ≤ ω (2 * k) := hmono
    _ ≤ C₀ * ω k := hω.doubling k hkEven

private lemma near_pointwise_weighted_bound {ω : ℤ → ℝ} {C₀ : ℝ}
    {r : ℤ → ℂ} (hω : EvenSlowWeight ω C₀)
    (hreven : ∀ k, k % 2 ≠ 0 → r k = 0)
    (n ν : ℤ) (hν : ν ∈ nearDisplacements n) :
    ‖r (2 * n - ν)‖ ^ 2 / (ν.natAbs : ℝ) ^ 2 ≤
      (C₀ ^ 2 / ω (2 * n) ^ 2) *
        (‖weightedRemainder ω r (2 * n - ν)‖ ^ 2 / (ν.natAbs : ℝ) ^ 2) := by
  let k := 2 * n - ν
  have hden : 0 < (ν.natAbs : ℝ) := by
    have hne := (Finset.mem_filter.mp hν).2
    exact_mod_cast Int.natAbs_pos.mpr hne
  by_cases hk : k % 2 = 0
  · have hcmp := near_weight_compare hω hν hk
    have hwpos : 0 < ω (2 * n) := hω.positive (2 * n) (by omega)
    have hkpos : 0 < ω k := hω.positive k hk
    have hratio : (ω (2 * n)) ^ 2 ≤ C₀ ^ 2 * (ω k) ^ 2 := by
      nlinarith [sq_nonneg (ω (2 * n)), sq_nonneg (C₀ * ω k)]
    have hnorm : ‖weightedRemainder ω r k‖ = ω k * ‖r k‖ := by
      simp [weightedRemainder, Real.norm_of_nonneg hkpos.le]
    have hbase : ‖weightedRemainder ω r k‖ ^ 2 = (ω k) ^ 2 * ‖r k‖ ^ 2 := by
      rw [hnorm]
      ring
    rw [hbase]
    have hwden : 0 < ω (2 * n) ^ 2 := sq_pos_of_pos hwpos
    have hdenne : (ν.natAbs : ℝ) ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hden)
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hratio) (sq_nonneg ‖r k‖)]
  · have hrzero : r k = 0 := hreven k hk
    have hbarzero : weightedRemainder ω r k = 0 := by simp [weightedRemainder, hrzero]
    change ‖r k‖ ^ 2 / (ν.natAbs : ℝ) ^ 2 ≤
      (C₀ ^ 2 / ω (2 * n) ^ 2) *
        (‖weightedRemainder ω r k‖ ^ 2 / (ν.natAbs : ℝ) ^ 2)
    rw [hrzero, hbarzero]
    simp

private lemma near_frequency_tail_tsum {ω : ℤ → ℝ} {r : ℤ → ℂ}
    (hbar : Memℓp (weightedRemainder ω r) 2) (n : ℤ) :
    (∑ ν ∈ nearDisplacements n,
      ‖weightedRemainder ω r (2 * n - ν)‖ ^ 2) ≤
      tailEnergy (weightedRemainder ω r) n.natAbs ^ 2 := by
  by_cases hn : n.natAbs = 0
  · have hn0 : n = 0 := Int.natAbs_eq_zero.mp hn
    subst n
    simp [nearDisplacements]
    positivity
  · have hnpos : 0 < n.natAbs := Nat.pos_of_ne_zero hn
    have htail := tailEnergy_sq_int hbar n.natAbs hnpos
    have hpoint : ∀ ν ∈ nearDisplacements n,
        ‖weightedRemainder ω r (2 * n - ν)‖ ^ 2 ≤
          (if n.natAbs ≤ (2 * n - ν).natAbs then
            ‖weightedRemainder ω r (2 * n - ν)‖ ^ 2 else 0) := by
      intro ν hν
      have hfreq := near_frequency_tail hν
      by_cases h : n.natAbs ≤ (2 * n - ν).natAbs
      · simp [h]
      · omega
    have hsum : (∑ ν ∈ nearDisplacements n,
        ‖weightedRemainder ω r (2 * n - ν)‖ ^ 2) ≤
        ∑ ν ∈ nearDisplacements n,
          (if n.natAbs ≤ (2 * n - ν).natAbs then
            ‖weightedRemainder ω r (2 * n - ν)‖ ^ 2 else 0) :=
      Finset.sum_le_sum (fun ν hν => hpoint ν hν)
    let tail : ℤ → ℝ := fun k =>
      if n.natAbs ≤ k.natAbs then ‖weightedRemainder ω r k‖ ^ 2 else 0
    have hsquare : Summable (fun k : ℤ => ‖weightedRemainder ω r k‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hbar.summable (by norm_num)
    have htailSummable : Summable tail := by
      apply Summable.of_nonneg_of_le (fun k => by simp [tail]; positivity)
        (fun k => by simp only [tail]; split_ifs <;> first | rfl | positivity) hsquare
    let modes := (nearDisplacements n).image (fun ν => 2 * n - ν)
    have hinj : Set.InjOn (fun ν : ℤ => 2 * n - ν) (nearDisplacements n : Set ℤ) := by
      intro a ha b hb hab
      nlinarith [hab]
    have himage : (∑ ν ∈ nearDisplacements n,
        (if n.natAbs ≤ (2 * n - ν).natAbs then
          ‖weightedRemainder ω r (2 * n - ν)‖ ^ 2 else 0)) =
        ∑ k ∈ modes, tail k := by
      rw [Finset.sum_image hinj]
    have hsumtail : (∑ k ∈ modes, tail k) ≤ ∑' k : ℤ, tail k :=
      htailSummable.sum_le_tsum modes (fun k hk => by
        simp only [tail]
        split_ifs <;> positivity)
    calc
      _ ≤ ∑ k ∈ modes, tail k := hsum.trans_eq himage
      _ ≤ ∑' k : ℤ, tail k := hsumtail
      _ = tailEnergy (weightedRemainder ω r) n.natAbs ^ 2 := htail.symm

/-- Source near estimate: the two-denominator contribution is controlled by
the corresponding weighted remainder contribution with the exact `C₀²/ω(2n)²`
factor. The weight assumptions are imposed only on even modes, and the
remainder is zero off the source even lattice. -/
theorem dm_weighted_near_denominator_bound
    (ω : ℤ → ℝ) (r : ℤ → ℂ) (n : ℤ) (C₀ : ℝ)
    (hω : EvenSlowWeight ω C₀)
    (hreven : ∀ k, k % 2 ≠ 0 → r k = 0) :
    nearDenominatorSum r n ≤
      (C₀ ^ 2 / ω (2 * n) ^ 2) *
        nearDenominatorSum (weightedRemainder ω r) n := by
  have hwpos : 0 < ω (2 * n) := hω.positive (2 * n) (by omega)
  unfold nearDenominatorSum
  calc
    _ ≤ ∑ ν ∈ nearDisplacements n,
        (C₀ ^ 2 / ω (2 * n) ^ 2) *
          (‖weightedRemainder ω r (2 * n - ν)‖ ^ 2 /
            (ν.natAbs : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro ν hν
      exact near_pointwise_weighted_bound hω hreven n ν hν
    _ = (C₀ ^ 2 / ω (2 * n) ^ 2) *
        nearDenominatorSum (weightedRemainder ω r) n := by
      rw [← Finset.mul_sum]
      rfl

/-- The squared form used in source equation (2.88): Cauchy isolates the
actual integer-lattice tail energy `E_|n|(r̄)^2` and leaves the finite near
`ν⁻⁴` sum explicit. -/
theorem dm_weighted_near_denominator_sq_bound
    (ω : ℤ → ℝ) (r : ℤ → ℂ) (n : ℤ) (C₀ : ℝ)
    (hω : EvenSlowWeight ω C₀)
    (hreven : ∀ k, k % 2 ≠ 0 → r k = 0)
    (hbar : Memℓp (weightedRemainder ω r) 2) :
    nearDenominatorSum r n ^ 2 ≤
      (C₀ ^ 4 / ω (2 * n) ^ 4) *
        tailEnergy (weightedRemainder ω r) n.natAbs ^ 2 *
        nearFourthDenominatorSum (weightedRemainder ω r) n := by
  have hnear := dm_weighted_near_denominator_bound ω r n C₀ hω hreven
  have hwpos : 0 < ω (2 * n) := hω.positive (2 * n) (by omega)
  have hnearbar_nonneg : 0 ≤ nearDenominatorSum (weightedRemainder ω r) n := by
    unfold nearDenominatorSum
    positivity
  have hnear4_nonneg : 0 ≤ nearFourthDenominatorSum (weightedRemainder ω r) n := by
    unfold nearFourthDenominatorSum
    positivity
  have htail_nonneg : 0 ≤ tailEnergy (weightedRemainder ω r) n.natAbs ^ 2 := sq_nonneg _
  have hCfac : 0 ≤ C₀ ^ 2 / ω (2 * n) ^ 2 := by positivity
  have hsq : nearDenominatorSum (weightedRemainder ω r) n ^ 2 ≤
      tailEnergy (weightedRemainder ω r) n.natAbs ^ 2 *
        nearFourthDenominatorSum (weightedRemainder ω r) n := by
    have hnearEq : nearDenominatorSum (weightedRemainder ω r) n =
        ∑ ν ∈ nearDisplacements n,
          ‖weightedRemainder ω r (2 * n - ν)‖ *
            (‖weightedRemainder ω r (2 * n - ν)‖ / (ν.natAbs : ℝ) ^ 2) := by
      unfold nearDenominatorSum
      apply Finset.sum_congr rfl
      intro ν hν
      have hνpos : 0 < (ν.natAbs : ℝ) := by
        have hne := (Finset.mem_filter.mp hν).2
        exact_mod_cast Int.natAbs_pos.mpr hne
      field_simp
    rw [hnearEq]
    have hc := Finset.sum_mul_sq_le_sq_mul_sq (nearDisplacements n)
      (fun ν => ‖weightedRemainder ω r (2 * n - ν)‖)
      (fun ν => ‖weightedRemainder ω r (2 * n - ν)‖ / (ν.natAbs : ℝ) ^ 2)
    have htail := near_frequency_tail_tsum hbar n
    have hsum1 : (∑ ν ∈ nearDisplacements n,
        ‖weightedRemainder ω r (2 * n - ν)‖ ^ 2) ≤
        tailEnergy (weightedRemainder ω r) n.natAbs ^ 2 := htail
    have hsecond : (∑ ν ∈ nearDisplacements n,
        (‖weightedRemainder ω r (2 * n - ν)‖ /
          (ν.natAbs : ℝ) ^ 2) ^ 2) ≤
        nearFourthDenominatorSum (weightedRemainder ω r) n := by
      unfold nearFourthDenominatorSum
      apply Finset.sum_le_sum
      intro ν hν
      rw [div_pow, pow_two]
      have hne : (ν.natAbs : ℝ) ≠ 0 := by
        have hνne := (Finset.mem_filter.mp hν).2
        exact_mod_cast (Nat.ne_of_gt (Int.natAbs_pos.mpr hνne))
      field_simp [hne]
      rfl
    calc
      _ ≤ (∑ ν ∈ nearDisplacements n,
          ‖weightedRemainder ω r (2 * n - ν)‖ ^ 2) *
            ∑ ν ∈ nearDisplacements n,
              (‖weightedRemainder ω r (2 * n - ν)‖ /
                (ν.natAbs : ℝ) ^ 2) ^ 2 := hc
      _ ≤ tailEnergy (weightedRemainder ω r) n.natAbs ^ 2 *
            nearFourthDenominatorSum (weightedRemainder ω r) n := by
          exact mul_le_mul hsum1 hsecond (by positivity) (by positivity)
  have hsqnear : nearDenominatorSum r n ^ 2 ≤
      (C₀ ^ 2 / ω (2 * n) ^ 2) ^ 2 *
        nearDenominatorSum (weightedRemainder ω r) n ^ 2 := by
    have hleft : 0 ≤ nearDenominatorSum r n := by
      unfold nearDenominatorSum
      positivity
    have hright : 0 ≤ (C₀ ^ 2 / ω (2 * n) ^ 2) *
        nearDenominatorSum (weightedRemainder ω r) n := by positivity
    simpa [mul_pow] using (sq_le_sq₀ hleft hright).mpr hnear
  calc
    nearDenominatorSum r n ^ 2 ≤
        (C₀ ^ 2 / ω (2 * n) ^ 2) ^ 2 *
          nearDenominatorSum (weightedRemainder ω r) n ^ 2 := hsqnear
    _ ≤ (C₀ ^ 2 / ω (2 * n) ^ 2) ^ 2 *
          (tailEnergy (weightedRemainder ω r) n.natAbs ^ 2 *
            nearFourthDenominatorSum (weightedRemainder ω r) n) :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg (C₀ ^ 2 / ω (2 * n) ^ 2))
    _ = (C₀ ^ 4 / ω (2 * n) ^ 4) *
          tailEnergy (weightedRemainder ω r) n.natAbs ^ 2 *
            nearFourthDenominatorSum (weightedRemainder ω r) n := by
      field_simp

end NlsGge.Atomic.DM019
