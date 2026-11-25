import NlsGge.GK38.PairRealBridge
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! # F6: weak tests, boundedness, and compact sets of tests

Source: GK, Chapter I, Proposition 1.2. Hilbert duality is applied to the
individual components; `PotPair` retains its accepted maximum product norm.
-/
set_option autoImplicit false
open Filter Topology
namespace NlsGge.GK38
open NlsGge.Pilot
noncomputable section

/-- Riesz represents every scalar continuous linear test of a weak limit. -/
theorem weakLim_clm38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    (hu : IsWeakLim u u₀) (L : PhysicalL2 →L[ℂ] ℂ) :
    Tendsto (fun k => L (u k)) atTop (𝓝 (L u₀)) := by
  simpa only [InnerProductSpace.toDual_symm_apply] using
    hu ((InnerProductSpace.toDual ℂ PhysicalL2).symm L)

/-- Scalar tests on the product split into scalar tests on each component. -/
theorem weakLimComp_clm38 {φ : ℕ → PotPair} {φ₀ : PotPair}
    (hw : IsWeakLimComp φ φ₀) (L : PotPair →L[ℂ] ℂ) :
    Tendsto (fun k => L (φ k)) atTop (𝓝 (L φ₀)) := by
  have h1 := weakLim_clm38 hw.1 (L.comp (ContinuousLinearMap.inl ℂ PhysicalL2 PhysicalL2))
  have h2 := weakLim_clm38 hw.2 (L.comp (ContinuousLinearMap.inr ℂ PhysicalL2 PhysicalL2))
  have heq (p : PotPair) : L p = L (p.1, 0) + L (0, p.2) := by
    rw [← map_add]; congr 1; ext <;> simp
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, ← heq] using h1.add h2

/-- Weakly convergent Hilbert sequences are norm bounded. -/
theorem weakLim_bounded38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    (hu : IsWeakLim u u₀) : ∃ B : ℝ, 0 ≤ B ∧ ∀ k, ‖u k‖ ≤ B := by
  have hp : ∀ v : PhysicalL2, ∃ C : ℝ, ∀ k,
      ‖InnerProductSpace.toDual ℂ PhysicalL2 (u k) v‖ ≤ C := by
    intro v
    obtain ⟨C, hC⟩ := (hu v).norm.bddAbove_range
    refine ⟨C, fun k => ?_⟩
    simpa only [InnerProductSpace.toDual_apply_apply, norm_inner_symm (u k) v] using
      hC (Set.mem_range_self k)
  obtain ⟨B, hB⟩ := banach_steinhaus hp
  refine ⟨max B 0, le_max_right _ _, fun k => ?_⟩
  have hk : ‖u k‖ ≤ B := by
    simpa only [(InnerProductSpace.toDual ℂ PhysicalL2).norm_map] using hB k
  exact hk.trans (le_max_left _ _)

/-- No boundedness assumption is added to componentwise weak convergence. -/
theorem weakLimComp_bounded38 {φ : ℕ → PotPair} {φ₀ : PotPair}
    (hw : IsWeakLimComp φ φ₀) : ∃ B : ℝ, 0 ≤ B ∧ ∀ k, ‖φ k‖ ≤ B := by
  obtain ⟨B₁, h₁, hb₁⟩ := weakLim_bounded38 hw.1
  obtain ⟨B₂, h₂, hb₂⟩ := weakLim_bounded38 hw.2
  exact ⟨max B₁ B₂, le_max_of_le_left h₁, fun k =>
    norm_prod_le_iff.mpr ⟨(hb₁ k).trans (le_max_left _ _),
      (hb₂ k).trans (le_max_right _ _)⟩⟩

/-- Weak evaluations converge uniformly over every compact set of scalar tests. -/
theorem weakLimComp_uniform_tests38 {φ : ℕ → PotPair} {φ₀ : PotPair}
    (hw : IsWeakLimComp φ φ₀) {S : Set (PotPair →L[ℂ] ℂ)} (hS : IsCompact S) :
    TendstoUniformlyOn (fun k L => L (φ k)) (fun L => L φ₀) atTop S := by
  obtain ⟨B, hB, hb⟩ := weakLimComp_bounded38 hw
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hLip (k : ℕ) : LipschitzWith ⟨B, hB⟩ (fun L : S => L.1 (φ k)) := by
    refine LipschitzWith.of_dist_le_mul fun L M => ?_
    rw [dist_eq_norm]
    change ‖L.1 (φ k) - M.1 (φ k)‖ ≤ B * dist L M
    calc
      ‖L.1 (φ k) - M.1 (φ k)‖ = ‖(L.1 - M.1) (φ k)‖ := rfl
      _ ≤ ‖L.1 - M.1‖ * ‖φ k‖ := (L.1 - M.1).le_opNorm _
      _ ≤ B * dist L M := by
        rw [mul_comm, Subtype.dist_eq, dist_eq_norm]
        exact mul_le_mul_of_nonneg_right (hb k) (norm_nonneg (L.1 - M.1))
  have heq := (LipschitzWith.uniformEquicontinuous
    (fun k (L : S) => L.1 (φ k)) ⟨B, hB⟩ hLip).equicontinuous
  rw [tendstoUniformlyOn_iff_restrict]
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
  exact (heq.tendsto_uniformFun_iff_pi atTop (fun L : S => L.1 φ₀)).mpr
    (tendsto_pi_nhds.mpr fun L => weakLimComp_clm38 hw L.1)

end
end NlsGge.GK38
