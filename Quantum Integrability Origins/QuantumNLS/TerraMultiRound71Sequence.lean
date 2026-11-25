import QuantumNLS.TerraMultiRound71Tail
import Mathlib.Analysis.Normed.Group.Tannery

/-! A discrete nonnegative convergence lemma for the REG-010 continuity step. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace QuantumNLS.TerraMultiRound71Sequence

/-- Pointwise convergence and convergence of the total masses imply ℓ¹
convergence for nonnegative summable sequences. -/
theorem nonnegative_tsum_abs_sub_tendsto {ι : Type*} (f : ℕ → ι → ℝ) (g : ι → ℝ)
    (hf : ∀ j n, 0 ≤ f j n) (hg : ∀ n, 0 ≤ g n)
    (hfs : ∀ j, Summable (f j)) (hgs : Summable g)
    (hpt : ∀ n, Tendsto (fun j => f j n) atTop (𝓝 (g n)))
    (htot : Tendsto (fun j => ∑' n, f j n) atTop (𝓝 (∑' n, g n))) :
    Tendsto (fun j => ∑' n, |f j n - g n|) atTop (𝓝 0) := by
  have hminsum : ∀ j, Summable (fun n => min (f j n) (g n)) := by
    intro j
    apply hgs.of_nonneg_of_le
    · intro n; exact le_min (hf j n) (hg n)
    · intro n; exact min_le_right _ _
  have hmin : Tendsto (fun j => ∑' n, min (f j n) (g n)) atTop (𝓝 (∑' n, g n)) := by
    have h := tendsto_tsum_of_dominated_convergence hgs
      (fun n => (hpt n).min tendsto_const_nhds)
      (show ∀ᶠ j : ℕ in atTop, ∀ n, ‖min (f j n) (g n)‖ ≤ g n from by
        filter_upwards with j n
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hf j n) (hg n))]
        exact min_le_right _ _)
    simpa only [min_self] using h
  have hformula : ∀ j, (∑' n, |f j n - g n|) =
      (∑' n, f j n) + (∑' n, g n) - 2 * (∑' n, min (f j n) (g n)) := by
    intro j
    have heq : (fun n => |f j n - g n|) =
        (fun n => f j n + g n - 2 * min (f j n) (g n)) := by
      funext n
      rcases le_total (f j n) (g n) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
    rw [heq, (hfs j).add hgs |>.tsum_sub ((hminsum j).mul_left 2),
      (hfs j).tsum_add hgs, tsum_mul_left]
  have hlim := (htot.add_const (∑' n, g n)).sub (hmin.const_mul 2)
  have hz : (∑' n, g n) + (∑' n, g n) - 2 * (∑' n, g n) = 0 := by ring
  rw [hz] at hlim
  exact hlim.congr' (Filter.Eventually.of_forall fun j => (hformula j).symm)

/-- For the physical actions, convergence of the weighted totals is enough
for convergence in the weighted ℓ¹ metric, once the inputs converge in L².
The weighted-total convergence is an explicit intermediate premise, not a
claim that the REG-010 Sobolev argument has been completed. -/
theorem physical_weighted_convergence_of_totals {L κ : ℝ} [Fact (0 < L)]
    (hκ : 0 < κ) (u : ℕ → QuantumNLS.PhysicalTensor.L2T L)
    (v : QuantumNLS.PhysicalTensor.L2T L) (p : ℝ)
    (hu : Tendsto u atTop (𝓝 v))
    (hs : ∀ j, Summable (fun n : ℤ => (1+|QuantumNLS.RootWeightedCellsR26.momentum L n|)^p *
      (QuantumNLS.RootIndexedMasses.masses hκ (u j)).1 n))
    (hv : Summable (fun n : ℤ => (1+|QuantumNLS.RootWeightedCellsR26.momentum L n|)^p *
      (QuantumNLS.RootIndexedMasses.masses hκ v).1 n))
    (ht : Tendsto (fun j => ∑' n : ℤ, (1+|QuantumNLS.RootWeightedCellsR26.momentum L n|)^p *
      (QuantumNLS.RootIndexedMasses.masses hκ (u j)).1 n) atTop
      (𝓝 (∑' n : ℤ, (1+|QuantumNLS.RootWeightedCellsR26.momentum L n|)^p *
      (QuantumNLS.RootIndexedMasses.masses hκ v).1 n))) :
    Tendsto (fun j => ∑' n : ℤ, (1+|QuantumNLS.RootWeightedCellsR26.momentum L n|)^p *
      |(QuantumNLS.RootIndexedMasses.masses hκ (u j)).1 n -
        (QuantumNLS.RootIndexedMasses.masses hκ v).1 n|) atTop (𝓝 0) := by
  let w : ℤ → ℝ := fun n => (1+|QuantumNLS.RootWeightedCellsR26.momentum L n|)^p
  have hw : ∀ n, 0 ≤ w n := by intro n; dsimp [w]; positivity
  have hpoint : ∀ n, Tendsto (fun j => w n * (QuantumNLS.RootIndexedMasses.masses hκ (u j)).1 n)
      atTop (𝓝 (w n * (QuantumNLS.RootIndexedMasses.masses hκ v).1 n)) := by
    intro n
    exact ((QuantumNLS.DEF014Continuity.continuous_physical_coordinate hκ n).tendsto v).comp hu |>.const_mul (w n)
  have h := nonnegative_tsum_abs_sub_tendsto
    (fun j n => w n * (QuantumNLS.RootIndexedMasses.masses hκ (u j)).1 n)
    (fun n => w n * (QuantumNLS.RootIndexedMasses.masses hκ v).1 n)
    (fun j n => mul_nonneg (hw n) ((QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ (u j)).2.1 n))
    (fun n => mul_nonneg (hw n) ((QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ v).2.1 n))
    hs hv hpoint ht
  convert h using 1
  funext j
  apply tsum_congr
  intro n
  rw [← mul_sub, abs_mul, abs_of_nonneg (hw n)]

#print axioms nonnegative_tsum_abs_sub_tendsto
#print axioms physical_weighted_convergence_of_totals
end QuantumNLS.TerraMultiRound71Sequence
