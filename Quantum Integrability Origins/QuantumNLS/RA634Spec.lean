import QuantumNLS.RA634Main
/-! integrator-authored trusted spec for R-A634027E F04:cor-spectral (review record r50 PASS): headline statement(s) copied verbatim from RA634Main (QuantumNLS.RA634Main). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull
  QuantumNLS.F04Regularity QuantumNLS.RootEnergyVariation
namespace QuantumNLS.RA634Spec
open QuantumNLS.RA634Main
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.RootNlsInvariance
variable {L : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem F04_cor_spectral_spec {κ : ℝ} (hκ : 0 < κ) (u0 : h04 L 1) :
    ∀ t s : ℝ,
      (∀ z : ℂ,
        L2SpatialTransfer.discriminant κ (physical (m10 (umax (le_refl (1 : ℝ)) κ u0 t))) z =
          L2SpatialTransfer.discriminant κ (physical (m10 (umax (le_refl (1 : ℝ)) κ u0 s))) z) ∧
      (∀ z : ℂ,
        NormalizedTransfer.productSymbol L κ (physical (m10 (umax (le_refl (1 : ℝ)) κ u0 t))) z =
          NormalizedTransfer.productSymbol L κ (physical (m10 (umax (le_refl (1 : ℝ)) κ u0 s))) z) ∧
      FullMass.Mmeas κ (physical (m10 (umax (le_refl (1 : ℝ)) κ u0 t))) =
        FullMass.Mmeas κ (physical (m10 (umax (le_refl (1 : ℝ)) κ u0 s))) ∧
      ∀ n : ℤ,
        (RootIndexedMasses.masses hκ (physical (m10 (umax (le_refl (1 : ℝ)) κ u0 t)))).1 n =
          (RootIndexedMasses.masses hκ (physical (m10 (umax (le_refl (1 : ℝ)) κ u0 s)))).1 n := by
  exact QuantumNLS.RA634Main.F04_cor_spectral hκ u0

end QuantumNLS.RA634Spec
#print axioms QuantumNLS.RA634Spec.F04_cor_spectral_spec
