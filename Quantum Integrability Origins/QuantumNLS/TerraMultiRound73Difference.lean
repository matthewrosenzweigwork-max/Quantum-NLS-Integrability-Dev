import QuantumNLS.TerraMultiRound72Interpolation

/-! Strictly lower weighted convergence of differences of nonnegative masses.
The uniformly bounded higher moment is an explicit intermediate hypothesis. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace QuantumNLS.TerraMultiRound73Difference
open QuantumNLS.TerraMultiRound72Interpolation

theorem lower_weight_difference {ι : Type*} (w : ι → ℝ) (a : ℕ → ι → ℝ) (b : ι → ℝ)
    (p q B : ℝ) (hw : ∀ n, 1 ≤ w n) (ha : ∀ j n, 0 ≤ a j n)
    (hb : ∀ n, 0 ≤ b n) (hp : 0 ≤ p) (hpq : p < q) (hB : 0 ≤ B)
    (hbase : Tendsto (fun j => ∑' n, |a j n - b n|) atTop (𝓝 0))
    (hfs : ∀ j, Summable (fun n => |a j n - b n|))
    (hqa : ∀ j, Summable (fun n => w n ^ q * a j n))
    (hqb : Summable (fun n => w n ^ q * b n))
    (hbound : ∀ j, (∑' n, w n ^ q * a j n) ≤ B) :
    Tendsto (fun j => ∑' n, w n ^ p * |a j n - b n|) atTop (𝓝 0) := by
  have hwq : ∀ n, 0 ≤ w n ^ q := by
    intro n
    exact Real.rpow_nonneg (by linarith [hw n]) _
  have hnonneg : ∀ j n, 0 ≤ w n ^ q * |a j n - b n| :=
    fun j n => mul_nonneg (hwq n) (abs_nonneg _)
  have hle : ∀ j n, w n ^ q * |a j n - b n| ≤
      w n ^ q * a j n + w n ^ q * b n := by
    intro j n
    have h : |a j n - b n| ≤ a j n + b n := by
      calc
        _ ≤ |a j n| + |b n| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (a j n) (-b n)
        _ = _ := by rw [abs_of_nonneg (ha j n), abs_of_nonneg (hb n)]
    have := mul_le_mul_of_nonneg_left h (hwq n)
    nlinarith
  have hqs : ∀ j, Summable (fun n => w n ^ q * |a j n - b n|) := by
    intro j
    exact ((hqa j).add hqb).of_nonneg_of_le (hnonneg j) (hle j)
  have hbound' : ∀ j, (∑' n, w n ^ q * |a j n - b n|) ≤
      B + (∑' n, w n ^ q * b n) := by
    intro j
    calc
      _ ≤ ∑' n, (w n ^ q * a j n + w n ^ q * b n) :=
        (hqs j).tsum_le_tsum (hle j) ((hqa j).add hqb)
      _ = (∑' n, w n ^ q * a j n) + ∑' n, w n ^ q * b n := (hqa j).tsum_add hqb
      _ ≤ _ := by linarith [hbound j]
  exact lower_weight_tendsto_zero w (fun j n => |a j n - b n|) hw
    (fun j n => abs_nonneg _) hp hpq
    (add_nonneg hB (tsum_nonneg (fun n => mul_nonneg (hwq n) (hb n))))
    hfs hqs hbound' hbase

#print axioms lower_weight_difference
end QuantumNLS.TerraMultiRound73Difference
