import QuantumNLS.TerraMultiRound27Swap
import QuantumNLS.TerraMultiRound27Ball

/-! Antiunitary covariance of the actual compression. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.LocalSpectral.Round27
open QuantumNLS.Local002 Round23 Round24 Round25 Round26

/-- The actual compression commutes with swap-conjugation on the Neumann ball. -/
theorem compression_swap {L κ r : ℝ} (hyp : FreeResolventHyp L κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L))
    (hq : qpar κ L r u < 1) (v : E2) :
    compressionMatrix L κ (u : ℝ → ℂ) n r (swapConj v) =
      swapConj (compressionMatrix L κ (u : ℝ → ℂ) n r v) := by
  change (ContinuousLinearMap.adjoint (embed L n))
      (perturbedProj L κ (u : ℝ → ℂ) n r (embed L n (swapConj v))) =
    swapConj ((ContinuousLinearMap.adjoint (embed L n))
      (perturbedProj L κ (u : ℝ → ℂ) n r (embed L n v)))
  rw [← embed_swap]
  change (ContinuousLinearMap.adjoint (embed L n))
      (rieszProj L κ (u : ℝ → ℂ) (parity n) n r (swapOp L (embed L n v))) = _
  rw [(contour_swap hyp hr hr2 n u hq _).1, adjoint_embed_swap]
  rfl

end QuantumNLS.LocalSpectral.Round27
#print axioms QuantumNLS.LocalSpectral.Round27.compression_swap
