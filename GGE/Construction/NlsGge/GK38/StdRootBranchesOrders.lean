import NlsGge.GK38.StdRootBranchesFactors

/-! Characteristic endpoint orders retain both occurrences in a collapsed pair.
These are orders of the entire characteristic, not of a branch at a cut. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem perChar_endpoint_order_count38 (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (z : ℂ) (hz : z = lamMinus φ n ∨ z = lamPlus φ n) :
    analyticOrderAt (perChar φ) z =
      ((lamMinus φ n ::ₘ lamPlus φ n ::ₘ (0 : Multiset ℂ)).count z : ℕ∞) := by
  classical
  obtain ⟨c, N, hgeom, hspec⟩ := isolating_family38 φ hφ
  have hpair := (hspec.1 n).2.2.2.2.1
  have hmem : z ∈ ball (discC φ n) (discR φ n) := by
    apply (hspec.1 n).1
    rcases hz with rfl | rfl
    · exact left_mem_segment ℝ _ _
    · exact right_mem_segment ℝ _ _
  have hc := Lib.count_zeroMultiset_ball
    ((analyticOnNhd_perChar_z φ).mono (subset_univ (closedBall (discC φ n) (discR φ n)))) z
  rw [← hpair, ite_eq_left hmem] at hc
  obtain ⟨U, hU, K, _, hcount⟩ := prescribed_common_counting38 φ 0
  have hperiodic := (hcount φ (mem_of_mem_nhds hU)).1
  rw [← Nat.cast_analyticOrderNatAt (counting_order_ne_top38 hperiodic z), ← hc]

theorem perChar_simple_endpoint_orders38 (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (hne : lamMinus φ n ≠ lamPlus φ n) :
    analyticOrderAt (perChar φ) (lamMinus φ n) = 1 ∧
      analyticOrderAt (perChar φ) (lamPlus φ n) = 1 := by
  classical
  constructor
  · rw [perChar_endpoint_order_count38 φ hφ n _ (Or.inl rfl)]
    simp [hne]
  · rw [perChar_endpoint_order_count38 φ hφ n _ (Or.inr rfl)]
    simp [hne, Ne.symm hne]

theorem perChar_collapsed_endpoint_order38 (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (he : lamMinus φ n = lamPlus φ n) :
    analyticOrderAt (perChar φ) (lamMinus φ n) = 2 := by
  classical
  rw [perChar_endpoint_order_count38 φ hφ n _ (Or.inl rfl)]
  simp [he]

end
end NlsGge.GK38
