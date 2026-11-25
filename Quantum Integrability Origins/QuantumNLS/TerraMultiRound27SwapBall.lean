import QuantumNLS.TerraMultiRound27SwapReduced

/-! Swap symmetry of the reduced map with compression smallness discharged. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.LocalSpectral.Round27
open QuantumNLS.Local002 Round23

/-- The same ball works for every Fourier mode and supplies the smallness
needed to define the inverse-square-root series. -/
theorem reducedMatrix_swap_on_ball {L κ r : ℝ} (hL : 0 < L)
    (hyp : FreeResolventHyp L κ) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L)
    (u : Lp ℂ 2 (μI L)) (hu : ‖u‖ < compressionRadius κ L r) (n : ℤ) (v : E2) :
    let hs := (smallCompression_on_ball hL hyp hr hr2 u hu n).1
    reducedMatrix2 L κ (u : ℝ → ℂ) n r hs (swapConj v) =
      swapConj (reducedMatrix2 L κ (u : ℝ → ℂ) n r hs v) := by
  dsimp only
  apply reducedMatrix_swap hyp hr hr2 n u
  have h := qpar_lt_half_of_norm_lt_radius u hu
  linarith

end QuantumNLS.LocalSpectral.Round27
#print axioms QuantumNLS.LocalSpectral.Round27.reducedMatrix_swap_on_ball
