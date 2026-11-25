import NlsGge.GK38.AbelianZeroGap

/-! Uncompiled P4/P5 common prerequisite. ANY actual closed-gap selection
has a genuine shifted lp2 sequence and distinct nodes in the ORIGINAL discs. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p5GapChoice_norm_bound38 (u : PhysicalL2) (x : ℤ → ℂ)
    (hx : ∀ m, x m ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m))
    (m : ℤ) : ‖x m-countingCenter38 m‖ ≤
      ‖lamMinus (realSlice u) m-countingCenter38 m‖+
        ‖lamPlus (realSlice u) m-countingCenter38 m‖ := by
  have ha : lamMinus (realSlice u) m ∈ closedBall (countingCenter38 m)
      (‖lamMinus (realSlice u) m-countingCenter38 m‖+
        ‖lamPlus (realSlice u) m-countingCenter38 m‖) := by
    rw [mem_closedBall,dist_eq_norm]
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hb : lamPlus (realSlice u) m ∈ closedBall (countingCenter38 m)
      (‖lamMinus (realSlice u) m-countingCenter38 m‖+
        ‖lamPlus (realSlice u) m-countingCenter38 m‖) := by
    rw [mem_closedBall,dist_eq_norm]
    exact le_add_of_nonneg_left (norm_nonneg _)
  have hc := (convex_closedBall (countingCenter38 m) _).segment_subset ha hb (hx m)
  simpa only [mem_closedBall,dist_eq_norm] using hc

theorem p5GapChoice_summable38 (u : PhysicalL2) (x : ℤ → ℂ)
    (hx : ∀ m, x m ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m)) :
    Summable (fun m : ℤ => ‖x m-countingCenter38 m‖^2) := by
  have hs := ((periodic_minus_summable38 (realSlice u)).add
    (periodic_plus_summable38 (realSlice u))).mul_left 2
  apply hs.of_nonneg_of_le (fun _ => sq_nonneg _)
  intro m
  have h := p5GapChoice_norm_bound38 u x hx m
  have hsq := mul_self_le_mul_self (norm_nonneg _) h
  dsimp only [countingCenter38] at hsq ⊢
  nlinarith [sq_nonneg (‖lamMinus (realSlice u) m-(m : ℂ)*(Real.pi : ℂ)‖-
    ‖lamPlus (realSlice u) m-(m : ℂ)*(Real.pi : ℂ)‖)]

theorem p5GapChoice_mem_own_disc38 (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (x : ℤ → ℂ)
    (hx : ∀ m, x m ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m)) :
    ∀ m, x m ∈ ball (C m) (R m) := by
  obtain ⟨c,N,_hg,hsp⟩ := hfam
  exact fun m => (hsp.1 m).1 (hx m)

theorem p5GapChoice_injective38 (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (x : ℤ → ℂ)
    (hx : ∀ m, x m ∈ segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m)) :
    Function.Injective x := by
  have hown := p5GapChoice_mem_own_disc38 u C R hfam x hx
  obtain ⟨c,N,hg,_hsp⟩ := hfam
  intro m k he
  by_contra hne
  have hm := hown m
  rw [he] at hm
  exact Set.disjoint_left.mp (isolating_geometry_disjoint38 C R c N hg hne) hm (hown k)

end
end NlsGge.GK38
