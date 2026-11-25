import QuantumNLS.OverlapMoments

/-! The no-overlap probability tends to one for fixed input degrees. -/
set_option autoImplicit false
noncomputable section
open Filter Topology Finset
open QuantumNLS.PlacementFusion QuantumNLS.OverlapMoments
namespace QuantumNLS.TerraMultiRound18OverlapLimit

theorem positive_overlap_tendsto_zero (p q : ℕ) :
    Tendsto (fun N : ℕ => ∑ s ∈ (range (q + 1)).filter (fun s => 1 ≤ s),
      overlapCoefficient N p q s) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => (p * q : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hlim
  · exact Finset.sum_nonneg fun s _ => overlapCoefficient_nonneg N p q s
  · filter_upwards [eventually_ge_atTop (max (max p q) 1)] with N hN
    exact prob_intersect_le
      (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
      (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
      (le_trans (le_max_right _ _) hN)

theorem zero_overlap_tendsto_one (p q : ℕ) :
    Tendsto (fun N : ℕ => overlapCoefficient N p q 0) atTop (𝓝 1) := by
  have hevent : ∀ᶠ N : ℕ in atTop,
      overlapCoefficient N p q 0 = 1 -
        ∑ s ∈ (range (q + 1)).filter (fun s => 1 ≤ s), overlapCoefficient N p q s := by
    filter_upwards [eventually_ge_atTop (max p q)] with N hN
    have hp : p ≤ N := (le_max_left p q).trans hN
    have hq : q ≤ N := (le_max_right p q).trans hN
    have hsplit : ∑ s ∈ range (q + 1), overlapCoefficient N p q s =
        overlapCoefficient N p q 0 +
          ∑ s ∈ (range (q + 1)).filter (fun s => 1 ≤ s), overlapCoefficient N p q s := by
      rw [Finset.sum_filter]
      calc
        _ = ∑ s ∈ range (q + 1),
            ((if s = 0 then overlapCoefficient N p q s else 0) +
              (if 1 ≤ s then overlapCoefficient N p q s else 0)) := by
              apply Finset.sum_congr rfl
              intro s hs
              rcases s with _ | s <;> simp
        _ = _ := by rw [Finset.sum_add_distrib]; simp
    have hsum := sum_overlapCoefficient_eq_one hp hq
    rw [hsplit] at hsum
    linarith
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hlim := hconst.sub (positive_overlap_tendsto_zero p q)
  have hlim' : Tendsto (fun N : ℕ => 1 -
      ∑ s ∈ (range (q + 1)).filter (fun s => 1 ≤ s), overlapCoefficient N p q s)
      atTop (𝓝 1) := by simpa using hlim
  apply hlim'.congr'
  filter_upwards [hevent] with N hN
  exact hN.symm

#print axioms positive_overlap_tendsto_zero
#print axioms zero_overlap_tendsto_one
end QuantumNLS.TerraMultiRound18OverlapLimit
