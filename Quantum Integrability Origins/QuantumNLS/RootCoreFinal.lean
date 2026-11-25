import Mathlib
import QuantumNLS.RootCoreDensity
import QuantumNLS.FormCoreMollifyFinal

/-!
# R-1602B09D `CC:F03:core` (`F03.tex:26`) for the quantum limiting measure

* `coreHyp_actual`: for `κ > 0` and nonzero `u` with a continuous `L`-periodic representative (every `H¹` input has one), `ρ = dens κ u` satisfies `FormCore.CoreHyp`:
  continuous, nonnegative, bounded (R-7E0532E7), `μ_ρ = measure hκ u` finite, and the frontier of `{ρ > 0} = {|Re Δ| > 2}` is contained in `{|Δ| = 2}`, finite on compacts.
* `core_actual`: **`C_c^∞(ℝ;ℝ)` is dense in `𝒟_μ` for the form norm `(‖h‖²_{L²(μ)} + 𝓔_μ(h))^{1/2}`** for `μ = M_{κ,u}` (the full-mass quantum measure; for unit `u` this is `μ_{κ,u}`
  by `RootSpectralInputsDischarge.measure_eq_limit`): every measurable `h` with `N_μ(h) < ∞` is a limit of `C_c^∞` functions.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff Real

noncomputable section

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace QuantumNLS.RootCoreFinal

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.PhysicalQuantumMeasure (measure)
open QuantumNLS.RootGapMultiplicity (Dl)
open QuantumNLS.RootGapLevelSets (dens_pos_iff continuous_re_Delta measure_eq_dens)
open QuantumNLS.RootDensityIdentification (dens continuous_dens dens_nonneg disc_eq_rep root_density_structure)
open QuantumNLS.RootDiscriminant (discReal)
open QuantumNLS.BulkResponseActual (IsPeriodicRepresentative)
open QuantumNLS.FormCore (CoreHyp muRho formN Approx core_density')

variable {L κ : ℝ} [Fact (0 < L)]

theorem coreHyp_actual (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) {uf : ℝ → ℂ}
    (hrep : IsPeriodicRepresentative L u uf) : CoreHyp (dens κ u) := by
  have hL : 0 < L := Fact.out
  have hDre : ∀ x : ℝ, (Dl κ u (x : ℂ)).re = discReal L κ uf x := fun x =>
    congrArg Complex.re (disc_eq_rep hrep κ (x : ℂ))
  obtain ⟨-, hbound, -⟩ := root_density_structure hκ hu hrep
  have hstruct := QuantumNLS.RootSpectralDensityFinal.root_density_structure_final L κ hL hκ hrep.1
  have hfin := hstruct.2.2.2.2.2.1
  refine ⟨continuous_dens κ u, dens_nonneg hκ u, ⟨_, hbound⟩, ?_, ?_⟩
  · have e : muRho (dens κ u) = measure hκ u := (measure_eq_dens hκ u).symm
    rw [e]; infer_instance
  · intro R
    refine (hfin (-R) R).subset ?_
    rintro x ⟨hxf, hxI⟩
    refine ⟨hxI, ?_⟩
    have hP : {y : ℝ | 0 < dens κ u y} = {y : ℝ | 2 < |(Dl κ u (y : ℂ)).re|} := by
      ext y; exact dens_pos_iff hκ u y
    rw [hP] at hxf
    have hopen : IsOpen {y : ℝ | 2 < |(Dl κ u (y : ℂ)).re|} :=
      isOpen_lt continuous_const (continuous_re_Delta κ u).abs
    have hcl : closure {y : ℝ | 2 < |(Dl κ u (y : ℂ)).re|} ⊆ {y : ℝ | 2 ≤ |(Dl κ u (y : ℂ)).re|} :=
      closure_minimal (fun y (hy : 2 < |(Dl κ u (y : ℂ)).re|) => (le_of_lt hy : 2 ≤ |(Dl κ u (y : ℂ)).re|)) (isClosed_le continuous_const (continuous_re_Delta κ u).abs)
    have h1 : 2 ≤ |(Dl κ u (x : ℂ)).re| := hcl hxf.1
    have h2 : ¬ 2 < |(Dl κ u (x : ℂ)).re| := by
      intro h
      have := hxf.2
      rw [hopen.interior_eq] at this
      exact this h
    have h3 : |(Dl κ u (x : ℂ)).re| = 2 := le_antisymm (not_lt.1 h2) h1
    rw [hDre] at h3
    exact h3

/-- **`CC:F03:core`** for the quantum limiting measure: `C_c^∞(ℝ;ℝ)` is dense in the form domain. -/
theorem core_actual (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) {uf : ℝ → ℂ}
    (hrep : IsPeriodicRepresentative L u uf) {h : ℝ → ℝ} (hh : Measurable h)
    (hN : formN (measure hκ u) h < ⊤) : Approx (measure hκ u) h := by
  have e : muRho (dens κ u) = measure hκ u := (measure_eq_dens hκ u).symm
  have := core_density' (coreHyp_actual hκ hu hrep) hh (by rw [e]; exact hN)
  rwa [e] at this

end QuantumNLS.RootCoreFinal

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RootCoreFinal.coreHyp_actual
#print axioms QuantumNLS.RootCoreFinal.core_actual
