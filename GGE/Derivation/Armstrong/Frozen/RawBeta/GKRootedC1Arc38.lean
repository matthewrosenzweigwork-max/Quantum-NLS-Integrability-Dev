import Armstrong.Frozen.RawBeta.GKOriginalSlit38

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory intervalIntegral
namespace NlsGge.GK38
noncomputable section

def GKRootedC1Arc38 (φ : GKPotential38) (m : ℤ) : Type :=
  {u : (ℝ → ℂ) × (ℝ → ℂ) //
    ContinuousOn u.1 (Icc (0 : ℝ) 1) ∧
    ContDiffOn ℝ 1 u.1 (Icc (0 : ℝ) 1) ∧
    ContinuousOn u.2 (Icc (0 : ℝ) 1) ∧
    (∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      u.2 t ^ 2 = perChar φ.1 (u.1 t)) ∧
    (∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      u.1 t ∈ ball (discC φ.1 m) (discR φ.1 m)) ∧
    (∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      u.1 t ∈ GKOriginalSlit38 φ m)}


end
end NlsGge.GK38
