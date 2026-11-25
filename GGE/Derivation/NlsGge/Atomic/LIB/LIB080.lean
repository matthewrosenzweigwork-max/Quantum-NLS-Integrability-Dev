import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Symmetry of the scalar second Frechet derivative

For a real or complex scalar field, `ContDiffAt` of order two supplies the
actual iterated Frechet derivative, with no extra smoothness or directional
hypotheses. The ambient Banach-space assumptions are not needed by this
standard local symmetry theorem, so this statement works for every normed
space over the field.
-/

namespace NlsGge.Atomic.LIB

/-- The second Frechet derivative of a C² scalar-valued map is symmetric in
arbitrary directions over the real or complex field. -/
theorem secondFrechetDeriv_swap
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (f : E → 𝕜) (x u v : E) (hf : ContDiffAt 𝕜 2 f x) :
    fderiv 𝕜 (fderiv 𝕜 f) x u v = fderiv 𝕜 (fderiv 𝕜 f) x v u := by
  exact (hf.isSymmSndFDerivAt (by simp)).eq u v

end NlsGge.Atomic.LIB
