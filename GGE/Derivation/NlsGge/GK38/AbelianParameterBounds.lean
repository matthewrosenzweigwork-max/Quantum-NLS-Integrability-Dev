import NlsGge.GK38.AbelianSpace
import NlsGge.GK38.Lib.ParamCircleAnalyticBounds

/-! Generic and genuine-input parameter bounds for P2. UNCOMPILED prospective source.
Only the spectral compact set is compact; the parameter space remains arbitrary Banach. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

/-- Compactness is used ONLY in z, never for an infinite-dimensional parameter ball. -/
theorem p2Compact_parameter_bound38 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (F : E → ℂ → ℂ) (x₀ : E) (K : Set ℂ) (hK : IsCompact K)
    (hF : ∀ z ∈ K, AnalyticAt ℂ (Function.uncurry F) (x₀,z)) :
    ∃ ε > 0, ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ ball x₀ ε, ∀ z ∈ K, ‖F x z‖ ≤ B := by
  have hv : ContinuousOn (F x₀) K := by
    intro z hz
    have ha : AnalyticAt ℂ (F x₀) z :=
      AnalyticAt.comp (g := Function.uncurry F) (f := fun w : ℂ => (x₀,w))
        (hF z hz) (analyticAt_const.prod analyticAt_id)
    exact ha.continuousAt.continuousWithinAt
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn hv
  let B : ℝ := max A 0+1
  have hlocal : ∀ z ∈ K, ∀ᶠ p : E × ℂ in 𝓝 (x₀,z), ‖F p.1 p.2‖ ≤ B := by
    intro z hz
    have he := (hF z hz).continuousAt.norm.eventually
      (gt_mem_nhds (lt_add_one ‖F x₀ z‖))
    filter_upwards [he] with p hp
    change ‖F p.1 p.2‖ < ‖F x₀ z‖+1 at hp
    have hAz : ‖F x₀ z‖ ≤ max A 0 := (hA z hz).trans (le_max_left _ _)
    dsimp [B]
    linarith
  have hu := hK.eventually_forall_of_forall_eventually
    (P := fun x z => ‖F x z‖ ≤ B) hlocal
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff_ball.mp hu
  exact ⟨ε,hε,B,by dsimp [B]; positivity,he⟩

/-- Actual Hilbert-input tails at s0 are genuinely small before a common neighbourhood
is chosen. A local mass bound ALONE would not imply this uniform-tail conclusion. -/
theorem p2Input_uniform_tail38 (s₀ : Lib.L2Seq) (δ : ℝ) (hδ : 0 < δ) :
    ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧ ∃ N : ℕ,
      ∀ s ∈ V, ∀ n : ℤ, (N:ℤ) < |n| → ‖s n‖ < δ := by
  have hs := (Lib.hasSum_sq_l2 s₀).summable
  have ht : ∀ᶠ n : ℤ in cofinite, ‖s₀ n‖ < δ/2 := by
    have he := hs.tendsto_cofinite_zero.eventually
      (gt_mem_nhds (by positivity : 0 < (δ/2)^2))
    filter_upwards [he] with n hn
    nlinarith [norm_nonneg (s₀ n)]
  have hbad : {n : ℤ | ¬ ‖s₀ n‖ < δ/2}.Finite := eventually_cofinite.mp ht
  obtain ⟨b,hb⟩ := (hbad.image (fun n : ℤ => |n|)).bddAbove
  have htail : ∀ n : ℤ, (b.natAbs:ℤ) < |n| → ‖s₀ n‖ < δ/2 := by
    intro n hn
    by_contra he
    have hnle : |n| ≤ b := hb ⟨n,he,rfl⟩
    have hbabs : b ≤ (b.natAbs:ℤ) := by rw [Int.natCast_natAbs]; exact le_abs_self b
    omega
  refine ⟨ball s₀ (δ/2),ball_mem_nhds _ (half_pos hδ),b.natAbs,?_⟩
  intro s hs n hn
  have hnorm : ‖s-s₀‖ < δ/2 := mem_ball_iff_norm.mp hs
  have hcoord := Lib.norm_coord_le (s-s₀) n
  have htri := norm_le_norm_sub_add (s n) (s₀ n)
  have heval : (s-s₀) n=s n-s₀ n := rfl
  rw [heval] at hcoord
  linarith [htail n hn]

#print axioms p2Compact_parameter_bound38
#print axioms p2Input_uniform_tail38
end
end NlsGge.GK38
