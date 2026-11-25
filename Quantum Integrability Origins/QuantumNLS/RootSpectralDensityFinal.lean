import Mathlib
import QuantumNLS.RootSpectralDensity
import QuantumNLS.RootTraceAsymptotics

/-!
# R-7E0532E7: `root_density_structure` WITHOUT the asymptotics hypothesis (continuous representatives)

`RootSpectralDensity.root_density_structure` assumed `eq:root-trace-asymptotic`; `RootTraceAsymptotics.trace_asymptotic`
proves it (Riemann-Lebesgue + factorial majorant).  The two together give the density statements unconditionally for
continuous `u` (the DEF-013 class of `SpatialTransfer`/`LinearFundamental`).  Still not here: the identification of the
root measure `μ_{κ,u}` with `rootDensity` (R-09E1EAE9, `eq:root-trace-symbol`, EXT-025) and the `L¹/L²` class.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open QuantumNLS.SpatialTransfer QuantumNLS.RootDiscriminant QuantumNLS.RootDensity

namespace QuantumNLS.RootSpectralDensityFinal

theorem root_density_structure_final (L κ : ℝ) (hL : 0 < L) (hκ : 0 < κ) {u : ℝ → ℂ} (hu : Continuous u) :
    Continuous (rootDensity κ (discReal L κ u)) ∧
    (∀ t, 0 ≤ rootDensity κ (discReal L κ u) t) ∧
    (∀ t, rootDensity κ (discReal L κ u) t ≤
      (∫ x in (0 : ℝ)..L, ‖u x‖) / (Real.pi * Real.sqrt κ)) ∧
    (∀ t, rootDensity κ (discReal L κ u) t = 0 ↔ |discReal L κ u t| ≤ 2) ∧
    (∀ x, 2 < |discReal L κ u x| → ∃ a b : ℝ, a < x ∧ x < b ∧
      connectedComponentIn {t | 2 < |discReal L κ u t|} x = Ioo a b ∧
      |discReal L κ u a| = 2 ∧ |discReal L κ u b| = 2) ∧
    (∀ a b : ℝ, {t : ℝ | t ∈ Icc a b ∧ |discReal L κ u t| = 2}.Finite) ∧
    (volume.withDensity (fun t => ENNReal.ofReal (rootDensity κ (discReal L κ u) t))).support =
      closure {t | 2 < |discReal L κ u t|} :=
  QuantumNLS.RootSpectralDensity.root_density_structure L κ hL hκ hu
    (QuantumNLS.RootTraceAsymptotics.trace_asymptotic hκ hu hL.le)

#print axioms root_density_structure_final

end QuantumNLS.RootSpectralDensityFinal
