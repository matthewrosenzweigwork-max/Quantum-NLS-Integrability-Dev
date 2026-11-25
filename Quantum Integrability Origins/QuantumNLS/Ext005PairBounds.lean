import QuantumNLS.Ext005Spectral

/-! A scalar sector-sum estimate used for pair-creation forms. This module
assumes no pair operator: the operator-level Hilbert–Schmidt bound remains to
be established independently. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace QuantumNLS.Ext005PairBounds

/-- The two-sector Cauchy–Schwarz estimate, with the exact pair coefficient. -/
theorem pair_sector (n : ℕ) (u v : ℝ) :
    Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * u * v ≤
      (((n : ℝ) + 1) * u ^ 2 + ((n : ℝ) + 2) * v ^ 2) / 2 := by
  have h1 : 0 ≤ (n : ℝ) + 1 := by positivity
  have h2 : 0 ≤ (n : ℝ) + 2 := by positivity
  rw [Real.sqrt_mul h1]
  have hs1 := Real.sq_sqrt h1
  have hs2 := Real.sq_sqrt h2
  nlinarith [sq_nonneg (Real.sqrt ((n : ℝ) + 1) * u -
    Real.sqrt ((n : ℝ) + 2) * v)]

/-- Summing the sector estimate over every particle number. `q` is the
first number moment, and the shift loses the nonnegative first two terms. -/
theorem pair_series (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hq : Summable (fun (n : ℕ) => ((n : ℝ) + 1) * (u n) ^ 2)) :
    Summable (fun (n : ℕ) => Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * u n * u (n + 2)) ∧
    (∑' (n : ℕ), Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * u n * u (n + 2)) ≤
      ∑' (n : ℕ), ((n : ℝ) + 1) * (u n) ^ 2 := by
  let q : ℕ → ℝ := fun (n : ℕ) => ((n : ℝ) + 1) * (u n) ^ 2
  let p : ℕ → ℝ := fun (n : ℕ) => Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * u n * u (n + 2)
  have hq' : Summable q := hq
  have hshift : Summable (fun n => q (n + 2)) := (summable_nat_add_iff 2).2 hq'
  have hmajor : Summable (fun n => (q n + q (n + 2)) / 2) := by
    exact (hq'.add hshift).div_const 2
  have hnonneg (n : ℕ) : 0 ≤ p n := by
    dsimp [p]; exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hu n)) (hu (n + 2))
  have hbound (n : ℕ) : p n ≤ (q n + q (n + 2)) / 2 := by
    have h := pair_sector n (u n) (u (n + 2))
    dsimp [p, q]
    push_cast
    nlinarith [sq_nonneg (u (n + 2))]
  have hp : Summable p := Summable.of_nonneg_of_le hnonneg hbound hmajor
  have hshift_le : (∑' n, q (n + 2)) ≤ ∑' n, q n := by
    have hs := hq'.sum_add_tsum_nat_add 2
    have hn : 0 ≤ ∑ i ∈ Finset.range 2, q i := by
      apply Finset.sum_nonneg
      intro i hi
      dsimp [q]; positivity
    linarith
  constructor
  · exact hp
  · calc
      (∑' n, p n) ≤ ∑' n, (q n + q (n + 2)) / 2 := hp.tsum_le_tsum hbound hmajor
      _ = ((∑' n, q n) + ∑' n, q (n + 2)) / 2 := by
        rw [tsum_div_const, hq'.tsum_add hshift]
      _ ≤ ∑' n, q n := by linarith

/-- Polynomial growth of the number-weight difference for a two-particle shift. -/
theorem weight_difference (j n : ℕ) :
    |((n : ℝ) + 1) ^ j - ((n : ℝ) + 3) ^ j| ≤
      (2 * (j : ℝ) * 3 ^ (j - 1)) * ((n : ℝ) + 1) ^ (j - 1) := by
  have ha : 0 ≤ (n : ℝ) + 1 := by positivity
  have hb : 0 ≤ (n : ℝ) + 3 := by positivity
  have hab : (n : ℝ) + 1 ≤ (n : ℝ) + 3 := by linarith
  have hc : (n : ℝ) + 3 ≤ 3 * ((n : ℝ) + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hp : ((n : ℝ) + 3) ^ (j - 1) ≤
      3 ^ (j - 1) * ((n : ℝ) + 1) ^ (j - 1) := by
    have h := pow_le_pow_left₀ hb hc (j - 1)
    simpa only [mul_pow] using h
  have h := abs_pow_sub_pow_le ((n : ℝ) + 1) ((n : ℝ) + 3) j
  rw [abs_of_nonneg ha, abs_of_nonneg hb, max_eq_right hab] at h
  have hd : |((n : ℝ) + 1) - ((n : ℝ) + 3)| = 2 := by
    have : ((n : ℝ) + 1) - ((n : ℝ) + 3) = -2 := by ring
    rw [this]; norm_num
  rw [hd] at h
  calc
    _ ≤ 2 * (j : ℝ) * ((n : ℝ) + 3) ^ (j - 1) := h
    _ ≤ 2 * (j : ℝ) * (3 ^ (j - 1) * ((n : ℝ) + 1) ^ (j - 1)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- The same sector estimate with an arbitrary higher polynomial weight. -/
theorem weighted_pair_series (k : ℕ) (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hq : Summable (fun (n : ℕ) => (((n : ℝ) + 1) ^ (k + 1)) * (u n) ^ 2)) :
    Summable (fun (n : ℕ) => ((n : ℝ) + 1) ^ k *
      (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * u n * u (n + 2))) ∧
    (∑' (n : ℕ), ((n : ℝ) + 1) ^ k *
      (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * u n * u (n + 2))) ≤
      ∑' (n : ℕ), (((n : ℝ) + 1) ^ (k + 1)) * (u n) ^ 2 := by
  let q : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (k + 1) * (u n) ^ 2
  let p : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ k *
    (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * u n * u (n + 2))
  have hq' : Summable q := hq
  have hshift : Summable (fun n => q (n + 2)) := (summable_nat_add_iff 2).2 hq'
  have hmajor : Summable (fun n => (q n + q (n + 2)) / 2) :=
    (hq'.add hshift).div_const 2
  have hnonneg (n : ℕ) : 0 ≤ p n := by
    dsimp [p]
    exact mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hu n)) (hu (n + 2)))
  have hbound (n : ℕ) : p n ≤ (q n + q (n + 2)) / 2 := by
    have ha : 0 ≤ (n : ℝ) + 1 := by positivity
    have hc : ((n : ℝ) + 1) ^ k * ((n : ℝ) + 2) ≤
        ((n : ℝ) + 3) ^ k * ((n : ℝ) + 3) := by
      gcongr <;> linarith
    have hs := mul_le_mul_of_nonneg_left (pair_sector n (u n) (u (n + 2))) (pow_nonneg ha k)
    have hv := mul_le_mul_of_nonneg_right hc (sq_nonneg (u (n + 2)))
    dsimp [p, q]
    push_cast
    have heq : (n : ℝ) + 2 + 1 = (n : ℝ) + 3 := by ring
    rw [heq]
    simp only [pow_succ, pow_zero, one_mul]
    nlinarith
  have hp : Summable p := Summable.of_nonneg_of_le hnonneg hbound hmajor
  have hshift_le : (∑' n, q (n + 2)) ≤ ∑' n, q n := by
    have hs := hq'.sum_add_tsum_nat_add 2
    have hn : 0 ≤ ∑ i ∈ Finset.range 2, q i := by
      apply Finset.sum_nonneg
      intro i hi
      dsimp [q]; positivity
    linarith
  constructor
  · exact hp
  · calc
      (∑' n, p n) ≤ ∑' n, (q n + q (n + 2)) / 2 := hp.tsum_le_tsum hbound hmajor
      _ = ((∑' n, q n) + ∑' n, q (n + 2)) / 2 := by
        rw [tsum_div_const, hq'.tsum_add hshift]
      _ ≤ ∑' n, q n := by linarith

#print axioms QuantumNLS.Ext005PairBounds.weighted_pair_series

/-- A family of complex sector matrix elements satisfying the pair block
bound defines an absolutely convergent form with the first-moment bound. -/
theorem pair_form_of_sector_bound (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hq : Summable (fun (n : ℕ) => ((n : ℝ) + 1) * (u n) ^ 2))
    (z : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ n, ‖z n‖ ≤ C *
      (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * u n * u (n + 2))) :
    Summable z ∧ ‖∑' n, z n‖ ≤ C * ∑' (n : ℕ), ((n : ℝ) + 1) * (u n) ^ 2 := by
  obtain ⟨hp, hpbound⟩ := pair_series u hu hq
  have hmajor := hp.mul_left C
  have hzabs : Summable (fun n => ‖z n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hz hmajor
  refine ⟨Summable.of_norm hzabs, ?_⟩
  calc
    ‖∑' n, z n‖ ≤ ∑' n, ‖z n‖ := norm_tsum_le_tsum_norm hzabs
    _ ≤ ∑' (n : ℕ), C *
        (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * u n * u (n + 2)) :=
      hzabs.tsum_le_tsum hz hmajor
    _ = C * ∑' (n : ℕ),
        Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * u n * u (n + 2) := by
      rw [tsum_mul_left]
    _ ≤ C * ∑' (n : ℕ), ((n : ℝ) + 1) * (u n) ^ 2 :=
      mul_le_mul_of_nonneg_left hpbound hC

/-- Specialization of the scalar estimate to the actual physical Fock moment
domain. The caller must still establish the stated sector block bound. -/
theorem physical_pair_form_of_sector_bound {L : ℝ} [Fact (0 < L)]
    (x : QuantumNLS.Ext005Moments.momentDomain (L := L) 1)
    (z : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ n, ‖z n‖ ≤ C *
      (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * ‖x.val n‖ * ‖x.val (n + 2)‖)) :
    Summable z ∧ ‖∑' n, z n‖ ≤ C * ‖QuantumNLS.Ext005Moments.momentRoot 1 x‖ ^ 2 := by
  have hq : Summable (fun (n : ℕ) => ((n : ℝ) + 1) * ‖x.val n‖ ^ 2) := by
    simpa [QuantumNLS.Ext005Moments.momentWeight] using
      (QuantumNLS.Ext005Moments.momentDomain_iff 1 x.val).1 x.property
  have h := pair_form_of_sector_bound (fun n => ‖x.val n‖) (fun _ => norm_nonneg _) hq z C hC hz
  have he := QuantumNLS.Ext005Moments.momentRoot_norm_sq 1 x
  simp only [QuantumNLS.Ext005Moments.momentWeight, pow_one] at he
  rw [he]
  exact h

#print axioms QuantumNLS.Ext005PairBounds.pair_form_of_sector_bound
#print axioms QuantumNLS.Ext005PairBounds.physical_pair_form_of_sector_bound
#print axioms QuantumNLS.Ext005PairBounds.weight_difference
#print axioms QuantumNLS.Ext005PairBounds.pair_sector
#print axioms QuantumNLS.Ext005PairBounds.pair_series
end QuantumNLS.Ext005PairBounds
