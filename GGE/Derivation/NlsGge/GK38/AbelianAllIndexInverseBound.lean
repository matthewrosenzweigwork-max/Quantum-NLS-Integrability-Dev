import NlsGge.GK38.AbelianAllIndexInverseNeighborhood
import Mathlib.Analysis.Normed.Ring.Units

/-! Earned invertibility precedes every totalized inverse here. A genuine
signed operator limit and earned all-index equicontinuity give ONE inverse
norm bound on ONE neighborhood, before ALL signed indices. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38.P6InverseNeighborhood
noncomputable section
variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem operator_inverse_continuousAt (T : E →L[ℂ] E) (hT : T.IsInvertible) :
    ContinuousAt (fun A : E →L[ℂ] E => A.inverse) T := by
  rw [← ContinuousLinearMap.ringInverse_eq_inverse]
  obtain ⟨e,he⟩ := hT
  rw [← he]
  change ContinuousAt Ring.inverse (e.toUnit : E →L[ℂ] E)
  exact NormedRing.inverse_continuousAt e.toUnit

theorem inverse_nearby_norm_bound (T : E →L[ℂ] E) (hT : T.IsInvertible) :
    ∀ᶠ A in 𝓝 T, A.IsInvertible ∧ ‖A.inverse‖ ≤ ‖T.inverse‖+1 := by
  have hi := operator_inverse_continuousAt T hT
  have hn := hi (ball_mem_nhds T.inverse (by norm_num : (0 : ℝ)<1))
  filter_upwards [hT.eventually_nhds,hn] with A hA hdist
  refine ⟨hA,?_⟩
  have hd : dist A.inverse T.inverse < (1 : ℝ) := mem_ball.mp hdist
  have hdn : ‖A.inverse-T.inverse‖ < (1 : ℝ) := by
    simpa only [dist_eq_norm] using hd
  calc
    ‖A.inverse‖ = ‖(A.inverse-T.inverse)+T.inverse‖ := by rw [sub_add_cancel]
    _ ≤ ‖A.inverse-T.inverse‖+‖T.inverse‖ := norm_add_le _ _
    _ ≤ 1+‖T.inverse‖ := add_le_add hdn.le le_rfl
    _ = ‖T.inverse‖+1 := add_comm _ _

theorem all_signed_inverse_bounded_eventually
    (T : ℤ → X → E →L[ℂ] E) (S : E →L[ℂ] E) (x : X)
    (hS : S.IsInvertible) (hbase : ∀ n : ℤ, (T n x).IsInvertible)
    (hcont : ∀ n : ℤ, ContinuousAt (T n) x)
    (hlimit : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ n : ℤ, (N : ℤ) < |n| → dist (T n x) S < ε)
    (hequi : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y in 𝓝 x, ∀ n : ℤ, dist (T n y) (T n x) < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ y in 𝓝 x, ∀ n : ℤ,
      (T n y).IsInvertible ∧ ‖(T n y).inverse‖ ≤ B := by
  classical
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (inverse_nearby_norm_bound S hS)
  obtain ⟨N,hN⟩ := hlimit (ε/2) (half_pos hε)
  let F : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let A : ℤ → ℝ := fun n => ‖(T n x).inverse‖+1
  have hA (n : ℤ) : 0 ≤ A n := add_nonneg (norm_nonneg _) zero_le_one
  let B : ℝ := ‖S.inverse‖+1+∑ n ∈ F, A n
  have hsum : 0 ≤ ∑ n ∈ F, A n := Finset.sum_nonneg (fun n _ => hA n)
  have hB : 0 < B := by dsimp [B]; linarith [norm_nonneg S.inverse]
  refine ⟨B,hB,?_⟩
  have hfinite : ∀ᶠ y in 𝓝 x, ∀ n ∈ F,
      (T n y).IsInvertible ∧ ‖(T n y).inverse‖ ≤ A n := by
    apply (F.eventually_all).mpr
    intro n _hn
    exact (hcont n) (inverse_nearby_norm_bound (T n x) (hbase n))
  filter_upwards [hfinite,hequi (ε/2) (half_pos hε)] with y hy he n
  by_cases hn : (N : ℤ) < |n|
  · have hnear : T n y ∈ ball S ε := by
      apply mem_ball.mpr
      have htri := dist_triangle (T n y) (T n x) S
      have hfirst := he n
      have hsecond := hN n hn
      linarith
    obtain ⟨hinv,hbound⟩ := hball hnear
    exact ⟨hinv,hbound.trans (le_add_of_nonneg_right hsum)⟩
  · have hnF : n ∈ F := by
      simpa only [F,Finset.mem_Icc] using abs_le.mp (le_of_not_gt hn)
    obtain ⟨hinv,hbound⟩ := hy n hnF
    have haSum : A n ≤ ∑ k ∈ F, A k := Finset.single_le_sum (fun k _ => hA k) hnF
    refine ⟨hinv,hbound.trans (haSum.trans ?_)⟩
    exact le_add_of_nonneg_left (by positivity : 0 ≤ ‖S.inverse‖+1)

end
end NlsGge.GK38.P6InverseNeighborhood
