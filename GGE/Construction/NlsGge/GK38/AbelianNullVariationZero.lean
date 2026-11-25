import NlsGge.GK38.AbelianWeightedInterpolation
import NlsGge.GK38.AbelianGapChoiceGeometry

/-! Actual book14.7 null direction: earn every interpolation-node hypothesis
from genuine closed-gap roots. The missing node is the actual lower endpoint. -/
set_option autoImplicit false
open Set
open NlsGge.Pilot
namespace NlsGge.GK38.P4NumeratorVariation
noncomputable section

theorem null_direction_variation_zero (n : ℤ) (u : PhysicalL2) (s h : P2Space38 n)
    (hs : p2RealSeq38 n s) (hh : p2RealSeq38 n h)
    (hnull : (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (realSlice u,t)) s) h=0) :
    ∀ z : ℂ, p4NumeratorVariation38 n (p2Extend38 n s) (p2Extend38 n h) z=0 := by
  classical
  choose x hxgap hxzero using null_direction_gap_roots n u s h hs hh hnull
  let nodes : ℤ → ℂ := fun m =>
    if hm : m=n then lamMinus (realSlice u) n else (x ⟨m,hm⟩ : ℂ)
  have hnodes : ∀ m, nodes m ∈
      segment ℝ (lamMinus (realSlice u) m) (lamPlus (realSlice u) m) := by
    intro m
    by_cases hm : m=n
    · subst m
      simp only [nodes,dite_eq_left rfl]
      exact left_mem_segment ℝ _ _
    · simpa only [nodes,dite_eq_right hm] using hxgap ⟨m,hm⟩
  have hsum : Summable (fun m : ℤ => ‖nodes m-(m : ℂ)*(Real.pi : ℂ)‖^2) := by
    simpa only [countingCenter38] using p5GapChoice_summable38 u nodes hnodes
  have hinj : Function.Injective nodes :=
    p5GapChoice_injective38 u (discC (realSlice u)) (discR (realSlice u))
      (isolating_family38 (realSlice u) (realSlice_mem_gkW u)) nodes hnodes
  apply null_variation_zero_of_gap_nodes n s h nodes hsum hinj
  intro m hm
  simpa only [nodes,dite_eq_right hm] using hxzero ⟨m,hm⟩

end
end NlsGge.GK38.P4NumeratorVariation
