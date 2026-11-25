import QuantumNLS.Local005LabelsB

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators ENNReal
namespace QuantumNLS.Local005
open QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.ResolventWordCoefficientLOCAL005
open QuantumNLS.ResolventWordLabelInjectiveLOCAL005
open QuantumNLS.ResolventWordEstimateStage2LOCAL005

/-- Product of the independent absolute Fourier inputs along a path. -/
def amplitude {k : ℕ} (u : Fin k → ℤ → ℂ) (n : ℤ) (q : Fin (k - 1) → ℤ) : ℝ :=
  ∏ j, ‖u j (wordLabel n q j)‖

/-- A common, square-summable bound on each intermediate resolvent multiplier. -/
def gapWeight (L r : ℝ) (m : ℤ) : ℝ := Real.sqrt (denominatorMajorant L r m)

def pathWeight (L r : ℝ) {k : ℕ} (q : Fin (k - 1) → ℤ) : ℝ :=
  ∏ i, gapWeight L r (q i)

/-- Uniform denominator square sum. -/
def gapSum (L r : ℝ) : ℝ := ∑' m : ℤ, denominatorMajorant L r m

/-- Absolute word with a contour-independent denominator envelope. -/
def envelope (L r κ : ℝ) (k : ℕ) (u : Fin k → ℤ → ℂ) (n : ℤ) : ℝ :=
  (2 * Real.sqrt (κ / L)) ^ k *
    ∑' q : Fin (k - 1) → ℤ, amplitude u n q * pathWeight L r q

theorem amplitude_nonneg {k : ℕ} (u : Fin k → ℤ → ℂ) (n : ℤ)
    (q : Fin (k - 1) → ℤ) : 0 ≤ amplitude u n q :=
  Finset.prod_nonneg fun _ _ => norm_nonneg _

theorem pathWeight_nonneg (L r : ℝ) {k : ℕ} (q : Fin (k - 1) → ℤ) :
    0 ≤ pathWeight L r q := Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _

theorem gapSum_nonneg (L r : ℝ) : 0 ≤ gapSum L r :=
  tsum_nonneg fun _ => sq_nonneg _

theorem envelope_nonneg (L r κ : ℝ) (k : ℕ) (u : Fin k → ℤ → ℂ) (n : ℤ) :
    0 ≤ envelope L r κ k u n :=
  mul_nonneg (pow_nonneg (by positivity) _) (tsum_nonneg fun q =>
    mul_nonneg (amplitude_nonneg u n q) (pathWeight_nonneg L r q))

theorem input_data {k : ℕ} (u : Fin k → ℤ → ℂ)
    (hu : ∀ j, Summable fun m => ‖u j m‖ ^ 2) :
    Summable (fun a : Fin k → ℤ => ∏ j, ‖u j (a j)‖ ^ 2) ∧
      ∑' a : Fin k → ℤ, ∏ j, ‖u j (a j)‖ ^ 2 =
        (∏ j, inputL2Norm u j) ^ 2 := by
  obtain ⟨hs, he⟩ := pi_tsum (fun j m => ‖u j m‖ ^ 2) (fun _ _ => sq_nonneg _) hu
  refine ⟨hs, ?_⟩
  rw [he, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun j _ => (inputL2Norm_sq u j).symm

theorem row_input_data {k : ℕ} (u : Fin k → ℤ → ℂ)
    (hu : ∀ j, Summable fun m => ‖u j m‖ ^ 2) (n : ℤ) :
    Summable (fun q : Fin (k - 1) → ℤ => amplitude u n q ^ 2) ∧
      ∑' q : Fin (k - 1) → ℤ, amplitude u n q ^ 2 ≤
        (∏ j, inputL2Norm u j) ^ 2 := by
  obtain ⟨hs, he⟩ := input_data u hu
  have hi : Function.Injective (wordLabel (k := k) n) := by
    intro q q' h
    exact pathLabels_injective n (congrFun h)
  refine ⟨?_, ?_⟩
  · simpa only [amplitude, ← Finset.prod_pow, Function.comp_def] using hs.comp_injective hi
  · rw [← he]
    simpa only [amplitude, ← Finset.prod_pow, Function.comp_def] using
      tsum_comp_le_tsum_of_inj hs (fun a => Finset.prod_nonneg fun _ _ => sq_nonneg _) hi

theorem odd_input_data {k : ℕ} (hk : Odd k) (u : Fin k → ℤ → ℂ)
    (hu : ∀ j, Summable fun m => ‖u j m‖ ^ 2) :
    Summable (fun n : ℤ => ∑' q : Fin (k - 1) → ℤ, amplitude u n q ^ 2) ∧
      ∑' n : ℤ, ∑' q : Fin (k - 1) → ℤ, amplitude u n q ^ 2 ≤
        (∏ j, inputL2Norm u j) ^ 2 := by
  obtain ⟨hs, he⟩ := input_data u hu
  have hj : Summable (fun p : ℤ × (Fin (k - 1) → ℤ) => amplitude u p.1 p.2 ^ 2) := by
    simpa only [amplitude, ← Finset.prod_pow, Function.comp_def] using hs.comp_injective (odd_labels_injective hk)
  refine ⟨hj.prod, ?_⟩
  rw [← hj.tsum_prod]
  rw [← he]
  simpa only [amplitude, ← Finset.prod_pow, Function.comp_def] using
    tsum_comp_le_tsum_of_inj hs (fun a => Finset.prod_nonneg fun _ _ => sq_nonneg _)
      (odd_labels_injective hk)

theorem weight_data {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (k : ℕ) :
    Summable (fun q : Fin (k - 1) → ℤ => pathWeight L r q ^ 2) ∧
      ∑' q : Fin (k - 1) → ℤ, pathWeight L r q ^ 2 = gapSum L r ^ (k - 1) := by
  have hmajor := denominatorMajorant_summable hL hr hsmall
  obtain ⟨hs, he⟩ := pi_tsum (fun _ : Fin (k - 1) => denominatorMajorant L r)
    (fun _ _ => sq_nonneg _) (fun _ => hmajor)
  have hw : ∀ q : Fin (k - 1) → ℤ,
      pathWeight L r q ^ 2 = ∏ i, denominatorMajorant L r (q i) := by
    intro q
    rw [pathWeight, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => Real.sq_sqrt (sq_nonneg _)
  refine ⟨by simpa only [hw] using hs, ?_⟩
  simp only [hw, he, gapSum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem envelope_row {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (κ : ℝ) {k : ℕ}
    (u : Fin k → ℤ → ℂ) (hu : ∀ j, Summable fun m => ‖u j m‖ ^ 2) (n : ℤ) :
    Summable (fun q : Fin (k - 1) → ℤ => amplitude u n q * pathWeight L r q) ∧
      envelope L r κ k u n ^ 2 ≤
        ((2 * Real.sqrt (κ / L)) ^ k) ^ 2 * gapSum L r ^ (k - 1) *
          ∑' q : Fin (k - 1) → ℤ, amplitude u n q ^ 2 := by
  obtain ⟨hf, _⟩ := row_input_data u hu n
  obtain ⟨hg, he⟩ := weight_data hL hr hsmall k
  obtain ⟨hs, hb⟩ := cauchy (amplitude u n) (pathWeight L r)
    (amplitude_nonneg u n) (pathWeight_nonneg L r) hf hg
  refine ⟨hs, ?_⟩
  unfold envelope
  rw [mul_pow]
  rw [he] at hb
  nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg ((2 * Real.sqrt (κ / L)) ^ k))]

/-- One constant bounds the uniform denominator power in every positive degree. -/
theorem degree_constant (L r κ : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ((2 * Real.sqrt (κ / L)) ^ k) ^ 2 * gapSum L r ^ (k - 1) ≤
      ((2 * Real.sqrt (κ / L) * (1 + gapSum L r)) ^ k) ^ 2 := by
  have hB := gapSum_nonneg L r
  have hbase : gapSum L r ≤ (1 + gapSum L r) ^ 2 := by nlinarith
  have hp := pow_le_pow_left₀ hB hbase (k - 1)
  have hp' : (1 + gapSum L r) ^ (2 * (k - 1)) ≤
      (1 + gapSum L r) ^ (2 * k) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hh : gapSum L r ^ (k - 1) ≤ ((1 + gapSum L r) ^ k) ^ 2 := by
    calc
      _ ≤ ((1 + gapSum L r) ^ 2) ^ (k - 1) := hp
      _ = (1 + gapSum L r) ^ (2 * (k - 1)) := by rw [← pow_mul]
      _ ≤ (1 + gapSum L r) ^ (2 * k) := hp'
      _ = ((1 + gapSum L r) ^ k) ^ 2 := by rw [← pow_mul, Nat.mul_comm]
  simpa only [mul_pow] using mul_le_mul_of_nonneg_left hh
    (sq_nonneg ((2 * Real.sqrt (κ / L)) ^ k))

#print axioms input_data
#print axioms row_input_data
#print axioms odd_input_data
#print axioms weight_data
#print axioms envelope_row
#print axioms degree_constant
end QuantumNLS.Local005
