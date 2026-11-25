import NlsGge.GK38.AbelianPaddedLinearApproximation
import NlsGge.GK38.AbelianPaddedPotentialResidual
import Mathlib.Topology.Compactness.Compact

/-! Genuine finite-cover globalization for actual period maps. ONE radius
and residual constant precede every seed in the compact set and every signed
index. No open Banach ball is claimed compact. -/
set_option autoImplicit false
open Set Metric Filter Topology
open scoped NNReal
namespace NlsGge.GK38
noncomputable section

theorem p6PaddedFn_compact_common_estimates38
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (K : Set Lib.L2Seq) (hK : IsCompact K)
    (c : ℝ≥0) (hc : 0 < c) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ball φ₀ r ⊆ gkW ∧
      ∀ b ∈ K, ∀ φ ∈ ball φ₀ r, ∀ n : ℤ,
        ApproximatesLinearOn (fun x : Lib.L2Seq => p6PaddedFn38 n (φ,x))
          (p6PaddedJacobian38 n φ₀ b) (closedBall b r) c ∧
        ‖p6PaddedFn38 n (φ,b)-p6PaddedFn38 n (φ₀,b)‖ ≤ M*‖φ-φ₀‖ := by
  classical
  have hlocal (s : K) : ∃ ρ M : ℝ, 0 < ρ ∧ 0 ≤ M ∧
      ball φ₀ ρ ⊆ gkW ∧
      (∀ b ∈ ball s.val ρ, ∀ φ ∈ ball φ₀ ρ, ∀ n : ℤ,
        ApproximatesLinearOn (fun x : Lib.L2Seq => p6PaddedFn38 n (φ,x))
          (p6PaddedJacobian38 n φ₀ b) (closedBall b ρ) c) ∧
      (∀ b ∈ ball s.val ρ, ∀ φ ∈ ball φ₀ ρ, ∀ n : ℤ,
        ‖p6PaddedFn38 n (φ,b)-p6PaddedFn38 n (φ₀,b)‖ ≤ M*‖φ-φ₀‖) := by
    obtain ⟨a,ha,haW,happrox⟩ :=
      p6PaddedFn_local_common_linear_approximation38 φ₀ hφ₀ s.val c hc
    obtain ⟨d,M,hd,hM,_hdW,hres⟩ :=
      p6PaddedFn_local_uniform_potential_residual38 φ₀ hφ₀ s.val
    let ρ : ℝ := min a d
    have hρa : ρ ≤ a := min_le_left _ _
    have hρd : ρ ≤ d := min_le_right _ _
    refine ⟨ρ,M,lt_min ha hd,hM,(ball_subset_ball hρa).trans haW,?_,?_⟩
    · intro b hb φ hφ n
      exact (happrox b (ball_subset_ball hρa hb) φ (ball_subset_ball hρa hφ) n).mono_set
        (closedBall_subset_closedBall hρa)
    · intro b hb φ hφ n
      exact hres b (ball_subset_ball hρd hb) φ (ball_subset_ball hρd hφ) n
  choose ρ M hρ hM hW happrox hres using hlocal
  let U : K → Set Lib.L2Seq := fun s => ball s.val (ρ s)
  have hcover : K ⊆ ⋃ s : K, U s := by
    intro b hb
    exact mem_iUnion.mpr ⟨⟨b,hb⟩,mem_ball_self (hρ ⟨b,hb⟩)⟩
  obtain ⟨F,hF⟩ := hK.elim_finite_subcover U (fun _ => isOpen_ball) hcover
  have hfinite (G : Finset K) : ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ G, δ ≤ ρ s := by
    induction G using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert s G hs ih =>
      obtain ⟨δ,hδ,hbound⟩ := ih
      refine ⟨min (ρ s) δ,lt_min (hρ s) hδ,?_⟩
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hbound t ht)
  obtain ⟨δ,hδ,hδbound⟩ := hfinite F
  obtain ⟨a,ha,haW⟩ := Metric.mem_nhds_iff.mp (isOpen_gkW.mem_nhds hφ₀)
  let r : ℝ := min δ a
  let B : ℝ := ∑ s ∈ F, M s
  have hrδ : r ≤ δ := min_le_left _ _
  have hr (s : K) (hs : s ∈ F) : r ≤ ρ s := hrδ.trans (hδbound s hs)
  refine ⟨r,B,lt_min hδ ha,Finset.sum_nonneg (fun s _ => hM s),
    (ball_subset_ball (min_le_right _ _)).trans haW,?_⟩
  intro b hb φ hφ n
  obtain ⟨s,hs,hbs⟩ := mem_iUnion₂.mp (hF hb)
  have hφs : φ ∈ ball φ₀ (ρ s) := ball_subset_ball (hr s hs) hφ
  refine ⟨(happrox s b hbs φ hφs n).mono_set (closedBall_subset_closedBall (hr s hs)),?_⟩
  have hMB : M s ≤ B := Finset.single_le_sum (fun t _ => hM t) hs
  exact (hres s b hbs φ hφs n).trans (mul_le_mul_of_nonneg_right hMB (norm_nonneg _))

end
end NlsGge.GK38
