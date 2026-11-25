import QuantumNLS.TerraMultiRound27SwapSeries

/-! Swap-conjugation for the actual normalized free-subspace map. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.LocalSpectral.Round27
open QuantumNLS.Local002 Round23 Round24 Round25 Round26

variable {L κ r : ℝ} (hyp : FreeResolventHyp L κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L))
    (hq : qpar κ L r u < 1) (hu : SmallCompression L κ (u : ℝ → ℂ) n r)

include hyp hr hr2 hq

theorem invSqrtCompression_swap (v : E2) :
    invSqrtCompression L κ (u : ℝ → ℂ) n r hu (swapConj v) =
      swapConj (invSqrtCompression L κ (u : ℝ → ℂ) n r hu v) := by
  apply invSqrtM_swap _ hu
  exact compression_swap hyp hr hr2 n u hq

theorem normalized_swap (v : E2) :
    normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu (swapConj v) =
      swapOp L (normalizedIsometry2 L κ (u : ℝ → ℂ) n r hu v) := by
  change perturbedProj L κ (u : ℝ → ℂ) n r
      (embed L n (invSqrtCompression L κ (u : ℝ → ℂ) n r hu (swapConj v))) =
    swapOp L (perturbedProj L κ (u : ℝ → ℂ) n r
      (embed L n (invSqrtCompression L κ (u : ℝ → ℂ) n r hu v)))
  rw [invSqrtCompression_swap hyp hr hr2 n u hq hu, ← embed_swap]
  exact (contour_swap hyp hr hr2 n u hq _).1

end QuantumNLS.LocalSpectral.Round27
#print axioms QuantumNLS.LocalSpectral.Round27.invSqrtCompression_swap
#print axioms QuantumNLS.LocalSpectral.Round27.normalized_swap
