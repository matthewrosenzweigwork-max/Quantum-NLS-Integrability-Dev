import QuantumNLS.TerraMultiRound79ActionDifference
import QuantumNLS.TerraMultiRound73Actions

/-! A same-order weighted convergence lemma with uniform tails. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace QuantumNLS.TerraMultiRound80TailLemma

/-- A uniformly small weighted tail and convergence of the unweighted
absolute differences imply convergence at the full weight. -/
theorem weighted_tendsto_of_tails {ι : Type*} (w : ι → ℝ) (a : ℕ → ι → ℝ) (b : ι → ℝ)
    (hw : ∀ n, 0 ≤ w n) (ha : ∀ j n, 0 ≤ a j n) (hb : ∀ n, 0 ≤ b n)
    (hbase : Tendsto (fun j => ∑' n, |a j n - b n|) atTop (𝓝 0))
    (hbs : ∀ j, Summable (fun n => |a j n - b n|))
    (hsa : ∀ j, Summable (fun n => w n * a j n))
    (hsb : Summable (fun n => w n * b n))
    (htail : ∀ ε > 0, ∃ (P : ι → Prop) (_ : DecidablePred P) (C : ℝ), 0 ≤ C ∧
      (∀ n, ¬ P n → w n ≤ C) ∧
      (∀ j, (∑' n, if P n then w n * a j n else 0) < ε) ∧
      (∑' n, if P n then w n * b n else 0) < ε) :
    Tendsto (fun j => ∑' n, w n * |a j n - b n|) atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨P, hP, C, hC, hcut, hta, htb⟩ := htail (ε/4) (by positivity)
  letI : DecidablePred P := hP
  have hc : Tendsto (fun j => C * (∑' n, |a j n - b n|)) atTop (𝓝 0) := by
    simpa using hbase.const_mul C
  have he : ∀ᶠ j in atTop, C * (∑' n, |a j n - b n|) < ε/2 :=
    hc.eventually (gt_mem_nhds (by positivity))
  filter_upwards [he] with j hj
  have htaS : Summable (fun n => if P n then w n * a j n else 0) := by
    apply (hsa j).of_nonneg_of_le
    · intro n; split_ifs
      · exact mul_nonneg (hw n) (ha j n)
      · exact le_rfl
    · intro n; split_ifs
      · exact le_rfl
      · exact mul_nonneg (hw n) (ha j n)
  have htbS : Summable (fun n => if P n then w n * b n else 0) := by
    apply hsb.of_nonneg_of_le
    · intro n; split_ifs
      · exact mul_nonneg (hw n) (hb n)
      · exact le_rfl
    · intro n; split_ifs
      · exact le_rfl
      · exact mul_nonneg (hw n) (hb n)
  have hupper := ((hbs j).mul_left C |>.add htaS).add htbS
  have hnonneg : ∀ n, 0 ≤ w n * |a j n - b n| := fun n => mul_nonneg (hw n) (abs_nonneg _)
  have hle : ∀ n, w n * |a j n - b n| ≤
      C * |a j n - b n| + (if P n then w n * a j n else 0) +
        (if P n then w n * b n else 0) := by
    intro n
    by_cases hn : P n
    · simp only [if_pos hn]
      have hd : |a j n - b n| ≤ a j n + b n := by
        calc
          _ ≤ |a j n| + |b n| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (a j n) (-b n)
          _ = _ := by rw [abs_of_nonneg (ha j n), abs_of_nonneg (hb n)]
      have := mul_le_mul_of_nonneg_left hd (hw n)
      nlinarith [mul_nonneg hC (abs_nonneg (a j n - b n))]
    · simp only [if_neg hn, add_zero]
      exact mul_le_mul_of_nonneg_right (hcut n hn) (abs_nonneg _)
  have hs := hupper.of_nonneg_of_le hnonneg hle
  have hsum : (∑' n, w n * |a j n - b n|) ≤
      C * (∑' n, |a j n - b n|) +
        (∑' n, if P n then w n * a j n else 0) +
        (∑' n, if P n then w n * b n else 0) := by
    calc
      _ ≤ ∑' n, (C * |a j n - b n| + (if P n then w n * a j n else 0) +
          (if P n then w n * b n else 0)) := hs.tsum_le_tsum hle hupper
      _ = _ := by rw [((hbs j).mul_left C |>.add htaS).tsum_add htbS,
          ((hbs j).mul_left C).tsum_add htaS, tsum_mul_left]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg hnonneg)]
  linarith [hta j, htb]

#print axioms weighted_tendsto_of_tails
end QuantumNLS.TerraMultiRound80TailLemma
