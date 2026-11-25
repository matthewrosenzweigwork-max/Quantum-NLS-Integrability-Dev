import QuantumNLS.TerraMultiRound71Sequence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! An interpolation estimate for nonnegative weighted action differences.
It uses a strictly higher moment and is only a partial REG-010 step. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace QuantumNLS.TerraMultiRound72Interpolation

/-- A lower power is bounded by a small multiple of a strictly higher power,
plus a constant, uniformly on the half-line starting at one. -/
theorem lower_power_le {p q ε : ℝ} (hp : 0 ≤ p) (hpq : p < q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → x ^ p ≤ C + ε * x ^ q := by
  have hlim := tendsto_rpow_neg_atTop (sub_pos.mpr hpq)
  have hevent : ∀ᶠ x : ℝ in atTop, x ^ (-(q-p)) < ε :=
    hlim.eventually (gt_mem_nhds hε)
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 hevent
  let A := max R 1
  refine ⟨A ^ p, by positivity, ?_⟩
  intro x hx
  by_cases h : A ≤ x
  · have hxpos : 0 < x := by linarith
    have hh : x ^ (-(q-p)) ≤ ε := le_of_lt (hR x (le_trans (le_max_left _ _) h))
    have heq : x ^ p = x ^ q * x ^ (-(q-p)) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    rw [heq]
    have hxq : 0 ≤ x ^ q := Real.rpow_nonneg hxpos.le _
    have hA : 0 ≤ A ^ p := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hh hxq]
  · have hxA : x ≤ A := le_of_not_ge h
    have hh := Real.rpow_le_rpow (by linarith : 0 ≤ x) hxA hp
    have hxq : 0 ≤ x ^ q := by positivity
    nlinarith

/-- The corresponding quantitative estimate for any nonnegative summable
sequence, including the exact momentum weights used by REG-010. -/
theorem weighted_sum_interpolation {ι : Type*} (w f : ι → ℝ)
    (hw : ∀ n, 1 ≤ w n) (hf : ∀ n, 0 ≤ f n)
    {p q ε : ℝ} (hp : 0 ≤ p) (hpq : p < q) (hε : 0 < ε)
    (hfs : Summable f) (hqs : Summable (fun n => w n ^ q * f n)) :
    ∃ C : ℝ, 0 ≤ C ∧ Summable (fun n => w n ^ p * f n) ∧
      (∑' n, w n ^ p * f n) ≤ C * (∑' n, f n) + ε * (∑' n, w n ^ q * f n) := by
  obtain ⟨C, hC, hweight⟩ := lower_power_le hp hpq hε
  have hupper : Summable (fun n => C * f n + ε * (w n ^ q * f n)) :=
    (hfs.mul_left C).add (hqs.mul_left ε)
  have hnonneg : ∀ n, 0 ≤ w n ^ p * f n := by
    intro n
    exact mul_nonneg (Real.rpow_nonneg (by linarith [hw n]) _) (hf n)
  have hle : ∀ n, w n ^ p * f n ≤ C * f n + ε * (w n ^ q * f n) := by
    intro n
    have h := mul_le_mul_of_nonneg_right (hweight (w n) (hw n)) (hf n)
    nlinarith
  have hps := hupper.of_nonneg_of_le hnonneg hle
  refine ⟨C, hC, hps, ?_⟩
  calc
    _ ≤ ∑' n, (C * f n + ε * (w n ^ q * f n)) := hps.tsum_le_tsum hle hupper
    _ = C * (∑' n, f n) + ε * (∑' n, w n ^ q * f n) := by
      rw [(hfs.mul_left C).tsum_add (hqs.mul_left ε), tsum_mul_left, tsum_mul_left]

/-- Uniform control of a strictly higher moment upgrades convergence of the
unweighted nonnegative sums to convergence of the lower weighted sums. -/
theorem lower_weight_tendsto_zero {ι : Type*} (w : ι → ℝ) (f : ℕ → ι → ℝ)
    (hw : ∀ n, 1 ≤ w n) (hf : ∀ j n, 0 ≤ f j n)
    {p q B : ℝ} (hp : 0 ≤ p) (hpq : p < q) (hB : 0 ≤ B)
    (hfs : ∀ j, Summable (f j))
    (hqs : ∀ j, Summable (fun n => w n ^ q * f j n))
    (hbound : ∀ j, (∑' n, w n ^ q * f j n) ≤ B)
    (hbase : Tendsto (fun j => ∑' n, f j n) atTop (𝓝 0)) :
    Tendsto (fun j => ∑' n, w n ^ p * f j n) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε / (2 * (B + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C, hC, hweight⟩ := lower_power_le hp hpq hδ
  have hCconv : Tendsto (fun j => C * (∑' n, f j n)) atTop (𝓝 0) := by
    simpa using hbase.const_mul C
  have hevent : ∀ᶠ j in atTop, C * (∑' n, f j n) < ε / 2 :=
    hCconv.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hevent] with j hj
  have hupper : Summable (fun n => C * f j n + δ * (w n ^ q * f j n)) :=
    ((hfs j).mul_left C).add ((hqs j).mul_left δ)
  have hnonneg : ∀ n, 0 ≤ w n ^ p * f j n := by
    intro n
    exact mul_nonneg (Real.rpow_nonneg (by linarith [hw n]) _) (hf j n)
  have hle : ∀ n, w n ^ p * f j n ≤ C * f j n + δ * (w n ^ q * f j n) := by
    intro n
    have h := mul_le_mul_of_nonneg_right (hweight (w n) (hw n)) (hf j n)
    nlinarith
  have hps := hupper.of_nonneg_of_le hnonneg hle
  have hsum : (∑' n, w n ^ p * f j n) ≤ C * (∑' n, f j n) + δ * B := by
    calc
      _ ≤ ∑' n, (C * f j n + δ * (w n ^ q * f j n)) := hps.tsum_le_tsum hle hupper
      _ = C * (∑' n, f j n) + δ * (∑' n, w n ^ q * f j n) := by
        rw [((hfs j).mul_left C).tsum_add ((hqs j).mul_left δ), tsum_mul_left, tsum_mul_left]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (hbound j) hδ.le
        linarith
  have hsmall : δ * B < ε / 2 := by
    dsimp [δ]
    have hden : 0 < 2 * (B + 1) := by positivity
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg hnonneg)]
  linarith

#print axioms lower_weight_tendsto_zero
#print axioms lower_power_le
#print axioms weighted_sum_interpolation
end QuantumNLS.TerraMultiRound72Interpolation
