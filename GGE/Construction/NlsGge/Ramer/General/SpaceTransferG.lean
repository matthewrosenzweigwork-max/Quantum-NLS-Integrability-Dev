import NlsGge.Ramer.General.RamerDensityG

/-!
# Transfer layer over a `RamerSetting`: the Ramer density on `E`

Adapted from `NlsGge/Ramer/SpaceTransfer.lean`. The transfer part (`coordE`, `R`,
`measurePreserving_coordE`, integral and convergence-in-measure transfer) lives in
`RamerSettingMeasure` (G1); this file adds the remaining thin layer and `ramerJE`, the Ramer
density as a function on `S.E`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Analysis.RegularizedDeterminant

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- (Old: `coordE_apply`.) -/
theorem coordE_apply (x : S.E) (n : ℤ) : S.coordE x n = S.coord n x := rfl

/-- (Old: `continuous_coordE_apply`.) -/
theorem continuous_coordE_apply (n : ℤ) : Continuous (fun x : S.E => S.coordE x n) :=
  (S.coord n).continuous

/-- (Old: `realization_coordE`.) -/
theorem realization_coordE (x : S.E) : S.R (S.coordE x) = x := S.R_coordE x

/-- (Old: `coordE_realization_ae`.) -/
theorem coordE_realization_ae : ∀ᵐ z ∂S.γ, S.coordE (S.R z) = z := S.coordE_R_ae

/-- (Old: `measurePreserving_realization`.) -/
theorem measurePreserving_realization : MeasurePreserving S.R S.γ S.γE :=
  S.measurePreserving_R

/-- The Ramer density as a function on `E`. (Old: `ramerJE`.) -/
def ramerJE (K : S.E → S.H) (δK : (ℤ → ℂ) → ℝ) (x : S.E) : ℝ :=
  S.ramerJ K δK (S.coordE x)

/-- (Old: `ramerJE_eq`.) -/
theorem ramerJE_eq (K : S.E → S.H) (δK : (ℤ → ℂ) → ℝ) (x : S.E) :
    S.ramerJE K δK x =
      |det2 (S.hsDerivH K x)| * Real.exp (-(δK (S.coordE x)) - ‖K x‖ ^ 2 / 2) := by
  unfold ramerJE ramerJ
  rw [S.R_coordE]

/-- (Old: `aestronglyMeasurable_ramerJE`.) -/
theorem aestronglyMeasurable_ramerJE (K : S.E → S.H) (hK : ContDiff ℝ 1 K)
    (δK : (ℤ → ℂ) → ℝ) (hδ : AEStronglyMeasurable δK S.γ) :
    AEStronglyMeasurable (S.ramerJE K δK) S.γE :=
  AEStronglyMeasurable.comp_quasiMeasurePreserving
    (S.aestronglyMeasurable_ramerJ K hK δK hδ)
    S.measurePreserving_coordE.quasiMeasurePreserving

/-- (Old: `ramerJE_pos`.) -/
theorem ramerJE_pos (T : S.E ≃ₜ S.E) (K K' : S.E → S.H)
    (hT : ∀ x, T x = x + S.incl (K x))
    (hTs : ∀ y, T.symm y = y + S.incl (K' y))
    (hK : ContDiff ℝ 1 K) (hK' : ContDiff ℝ 1 K')
    (δK : (ℤ → ℂ) → ℝ) (x : S.E) :
    0 < S.ramerJE K δK x :=
  S.ramerJ_pos T K K' hT hTs hK hK' δK (S.coordE x)


end NlsGge.Ramer.General.RamerSetting
