import NlsGge.GK38.AbelianLocalComplexAnalyticLevel

/-! A chosen actual interior level branch is analytic. Its continuity is
EARNED from local analytic implicit charts and full-ball uniqueness, never
assumed as a selection hypothesis. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p6PaddedFn_interior_level_selection_analytic38 (n : ℤ)
    (b : Lib.L2Seq) (r : ℝ) (U : Set PotPair) (hU : IsOpen U) (hUW : U ⊆ gkW)
    (z : Lib.L2Seq) (f : PotPair → Lib.L2Seq)
    (hroot : ∀ φ ∈ U, f φ ∈ ball b r ∧ p6PaddedFn38 n (φ,f φ)=z)
    (hunique : ∀ φ ∈ U, ∀ y ∈ ball b r, p6PaddedFn38 n (φ,y)=z → y=f φ)
    (hQ : ∀ φ ∈ U, (p6PaddedJacobian38 n φ (f φ)).IsInvertible) :
    AnalyticOnNhd ℂ f U := by
  intro φ hφ
  obtain ⟨ψ,hψbase,hψan,hψlevel,_hψgraph⟩ :=
    p6PaddedFn_local_complex_analytic_level_of_inverse38 n φ (hUW hφ) (f φ) (hQ φ hφ)
  have hψball : ∀ᶠ q in 𝓝 φ, ψ q ∈ ball b r :=
    hψan.continuousAt.preimage_mem_nhds
      (by rw [hψbase]; exact isOpen_ball.mem_nhds (hroot φ hφ).1)
  have he : ψ =ᶠ[𝓝 φ] f := by
    filter_upwards [hU.mem_nhds hφ,hψball,hψlevel] with q hq hqb hqlevel
    exact hunique q hq (ψ q) hqb (hqlevel.trans (hroot φ hφ).2)
  exact hψan.congr he

end
end NlsGge.GK38
