import Mathlib
import QuantumNLS.Fourier
import QuantumNLS.ProductEnergyPreparation
import QuantumNLS.RootCoreFinal

/-!
# R-1602B09D `CC:F03:core` for unit `H¹` inputs

The printed lemma states its last sentence for "every unit `H¹` input".  The repository's `H¹` hypothesis on a one-particle profile is
`ProductEnergyPreparation.OneH1 u : Mem04 L 1 (û)` (finite `Σ (1+p_n²)|û(n)|²`, DEF-002 `s = 1`).

* `periodicRep_of_mem04`: Sobolev embedding on the torus, from `Fourier.f04_l1_sup_continuous_representative` (absolute summability of the coefficients,
  Cauchy-Schwarz with `Σ (1+p_n²)⁻¹ < ∞`): a profile with `Mem04 L 1 û` has a continuous `L`-periodic representative `uf : ℝ → ℂ`
  (`BulkResponseActual.IsPeriodicRepresentative`).
* `coreDensity_unitH1`, `core_unitH1`: the density hypotheses of the lemma (`BulkResponseForm.CoreDensity`) and the density of `C_c^∞` in the form domain for
  `μ_{κ,u}` hold for every nonzero `u` with `OneH1 u` (so for every unit `H¹` input), without any continuity hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff Real

noncomputable section

namespace QuantumNLS.RootCoreH1

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.PhysicalQuantumMeasure (measure)
open QuantumNLS.BulkResponseActual (IsPeriodicRepresentative)
open QuantumNLS.FormCore (formN Approx)

variable {L κ : ℝ} [Fact (0 < L)]

theorem periodicRep_of_mem04 (u : L2T L) (hu : QuantumNLS.Fourier.Mem04 L 1 (fun n => QuantumNLS.Fourier.fourierL2 L u n)) :
    ∃ uf : ℝ → ℂ, IsPeriodicRepresentative L u uf := by
  obtain ⟨-, -, g, hgc, hae, -⟩ := QuantumNLS.Fourier.f04_l1_sup_continuous_representative u hu
  refine ⟨fun x => g (x : AddCircle L), hgc.comp (continuous_quotient_mk'), fun x => ?_, ?_⟩
  · show g ((x + L : ℝ) : AddCircle L) = g (x : AddCircle L)
    rw [AddCircle.coe_add_period]
  · filter_upwards [hae] with y hy
    rw [hy]
    show g y = g ((AddCircle.equivIco L 0 y : ℝ) : AddCircle L)
    rw [AddCircle.coe_equivIco]

theorem periodicRep_of_oneH1 (u : L2T L) (hu : QuantumNLS.ProductEnergyPreparation.OneH1 u) :
    ∃ uf : ℝ → ℂ, IsPeriodicRepresentative L u uf :=
  periodicRep_of_mem04 u hu

theorem coreDensity_unitH1 (hκ : 0 < κ) {u : L2T L} (hu0 : u ≠ 0)
    (hu : QuantumNLS.ProductEnergyPreparation.OneH1 u) :
    QuantumNLS.BulkResponseForm.CoreDensity (measure hκ u) := by
  obtain ⟨uf, hrep⟩ := periodicRep_of_oneH1 u hu
  exact QuantumNLS.RootCoreDensity.coreDensity_actual hκ hu0 hrep

/-- **`CC:F03:core` for unit `H¹` inputs**: `C_c^∞(ℝ;ℝ)` is dense in the form domain of `μ_{κ,u}`. -/
theorem core_unitH1 (hκ : 0 < κ) {u : L2T L} (hu0 : u ≠ 0)
    (hu : QuantumNLS.ProductEnergyPreparation.OneH1 u) {h : ℝ → ℝ} (hh : Measurable h)
    (hN : formN (measure hκ u) h < ⊤) : Approx (measure hκ u) h := by
  obtain ⟨uf, hrep⟩ := periodicRep_of_oneH1 u hu
  exact QuantumNLS.RootCoreFinal.core_actual hκ hu0 hrep hh hN

end QuantumNLS.RootCoreH1

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RootCoreH1.periodicRep_of_mem04
#print axioms QuantumNLS.RootCoreH1.coreDensity_unitH1
#print axioms QuantumNLS.RootCoreH1.core_unitH1
