import QuantumNLS.RootIndexedMassesCollapsed
/-! integrator-authored trusted spec for R-950BFB30 thm:root-indexed-masses (Terra r166 FULL ACCEPT): headline statement(s) copied verbatim from RootIndexedMassesCollapsed (QuantumNLS.RootIndexedMassesCollapsed). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace QuantumNLS.R950Spec
open QuantumNLS.RootIndexedMassesCollapsed
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.RootIndexedMasses (masses)
open QuantumNLS.RootDensity (hfun)
open QuantumNLS.PhysicalQuantumMeasure (measure)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem root_indexed_masses_collapsed_spec (hκ : 0 < κ) (u : L2T L) :
    (∀ n : ℤ, (masses hκ u).1 n =
      (measure hκ u (Ioo
        (QuantumNLS.RootIndexedPhase.separator hκ u (n-1)) (QuantumNLS.RootIndexedPhase.separator hκ u n))).toReal) ∧
    (∀ n : ℤ, 0 ≤ (masses hκ u).1 n) ∧
    Summable (fun n => (masses hκ u).1 n) ∧
    (∑' n, (masses hκ u).1 n) = ‖u‖^2 ∧
    Continuous (fun p : QuantumNLS.DEF014Phase.Param L => masses p.1.2 p.2) ∧
    (∀ n : ℤ, (¬ PosInterval hκ u n → (masses hκ u).1 n = 0) ∧
      (∀ a b : ℝ, a < b → Ioo a b ⊆ cell hκ u n → (∀ x ∈ Ioo a b, 2 < |Dre κ u x|) →
        ∀ x ∈ Ioo a b, QuantumNLS.RootIndexedPhase.theta hκ u x = n * Real.pi)) ∧
    (∀ c : ℂ, ‖c‖ = 1 → masses hκ (c • u) = masses hκ u) ∧
    (∀ a : ℝ, masses hκ (QuantumNLS.BornTranslation.trans a u) = masses hκ u) ∧
    Tendsto (fun k : QuantumNLS.RootMassFree.Coupling => masses k.2 u) QuantumNLS.RootMassFree.zeroCoupling
      (𝓝 (QuantumNLS.RootMassFreeLimit.intensities u)) ∧
    (∀ (a : ℂ) (k n : ℤ),
      (masses hκ (((Real.sqrt L : ℂ)*a) • QuantumNLS.Fourier.modeLp L k)).1 n =
        if n=k then L*‖a‖^2 else 0) ∧
    (∀ (k n : ℤ), (masses hκ (QuantumNLS.RootMassBoostSymbol.boost k u)).1 n = (masses hκ u).1 (n-k)) := by
  exact QuantumNLS.RootIndexedMassesCollapsed.root_indexed_masses_collapsed hκ u

end QuantumNLS.R950Spec
#print axioms QuantumNLS.R950Spec.root_indexed_masses_collapsed_spec
