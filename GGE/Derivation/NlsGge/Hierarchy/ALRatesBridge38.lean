import NlsGge.Hierarchy.ALFreeFields38
import NlsGge.Hierarchy.ALGaussianNormalizer38

/-! Integrator bridge: the lattice symbol and rates of `ALFreeFields38` (L07/L08) agree with those
of `ALGaussianNormalizer38` (L03) at the mesh `h = 1/(2N+1)`. -/

namespace NlsGge.AblowitzLadik

theorem alMeshStep38_eq_inv (N : ℕ) : alMeshStep38 N = ((2 * N + 1 : ℕ) : ℝ)⁻¹ := by
  unfold alMeshStep38; push_cast; ring

theorem alOmegaFree38_eq_alOmega38 (N : ℕ) (k : ℤ) :
    alOmegaFree38 N k = alOmega38 (alMeshStep38 N) k := rfl

theorem alRateFree38_eq_alRate38 (c : ℕ → ℝ) (N : ℕ) (k : ℤ) :
    alRateFree38 c N k = alRate38 c (alMeshStep38 N) k := rfl

end NlsGge.AblowitzLadik
