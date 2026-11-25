import NlsGge.GK38.AngleDiagonalCoefficient
import Mathlib.Order.Filter.Finite
import Mathlib.Data.Int.Interval

/-! A genuine full signed OPnorm limit and ALL-index equicontinuity transfer
separate positive DIAGONAL bounds to one common local lower bound. An
invertible full Jacobian alone does not supply the diagonal hypotheses. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem angleFinite_diagonal_lower38 (F : Finset ℤ)
    (T : ℤ → Lib.L2Seq →L[ℂ] Lib.L2Seq)
    (hbase : ∀ n : ℤ, ∃ d : ℝ, 0 < d ∧ ∀ m : ℤ,
      d ≤ ‖T n (lp.single 2 m (1 : ℂ)) m‖) :
    ∃ d : ℝ, 0 < d ∧ ∀ n ∈ F, ∀ m : ℤ,
      d ≤ ‖T n (lp.single 2 m (1 : ℂ)) m‖ := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1,zero_lt_one,by simp⟩
  | @insert n F hn ih =>
    obtain ⟨a,ha,hTa⟩ := hbase n
    obtain ⟨b,hb,hTb⟩ := ih
    refine ⟨min a b,lt_min ha hb,?_⟩
    intro k hk m
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact (min_le_left a b).trans (hTa m)
    · exact (min_le_right a b).trans (hTb k hk m)

theorem angleAllSigned_diagonal_lower_eventually38
    {X : Type*} [TopologicalSpace X]
    (T : ℤ → X → (Lib.L2Seq →L[ℂ] Lib.L2Seq))
    (S : Lib.L2Seq →L[ℂ] Lib.L2Seq) (x : X)
    (hS : ∃ d : ℝ, 0 < d ∧ ∀ m : ℤ,
      d ≤ ‖S (lp.single 2 m (1 : ℂ)) m‖)
    (hbase : ∀ n : ℤ, ∃ d : ℝ, 0 < d ∧ ∀ m : ℤ,
      d ≤ ‖T n x (lp.single 2 m (1 : ℂ)) m‖)
    (hlimit : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n : ℤ, (N : ℤ) < |n| → ‖T n x-S‖ < ε)
    (hequi : ∀ ε : ℝ, 0 < ε → ∀ᶠ y in nhds x,
      ∀ n : ℤ, ‖T n y-T n x‖ < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ y in nhds x, ∀ n m : ℤ,
      d ≤ ‖T n y (lp.single 2 m (1 : ℂ)) m‖ := by
  obtain ⟨a,ha,hSa⟩ := hS
  obtain ⟨N,hN⟩ := hlimit (a/2) (half_pos ha)
  let F : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  obtain ⟨b,hb,hFb⟩ := angleFinite_diagonal_lower38 F (fun n => T n x) hbase
  let c : ℝ := min (a/2) b
  have hc : 0 < c := lt_min (half_pos ha) hb
  have hfixed (n m : ℤ) : c ≤ ‖T n x (lp.single 2 m (1 : ℂ)) m‖ := by
    by_cases hn : (N : ℤ) < |n|
    · have hd := angleActual_diagonal_norm_transfer38 S (T n x) m
      have ht : ‖S-T n x‖ < a/2 := by
        rw [norm_sub_rev]
        exact hN n hn
      have hs := hSa m
      have hca : c ≤ a/2 := min_le_left _ _
      linarith
    · have hnF : n ∈ F := by
        simpa only [F,Finset.mem_Icc] using abs_le.mp (le_of_not_gt hn)
      exact (min_le_right _ _).trans (hFb n hnF m)
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [hequi (c/2) (half_pos hc)] with y hy n m
  have hd := angleActual_diagonal_norm_transfer38 (T n x) (T n y) m
  have ht : ‖T n x-T n y‖ < c/2 := by
    rw [norm_sub_rev]
    exact hy n
  have hf := hfixed n m
  linarith

end
end NlsGge.GK38
