import QuantumNLS.RootDensityIdentification
import QuantumNLS.RootTraceSymbolUpper
import QuantumNLS.PhysicalL2Normalization
/-! integrator-authored trusted spec for R-7E0532E7 thm:root-spectral-density (Terra r154 FULL ACCEPT):
the canonical quantum measure (= FullMass.Mmeas, = μ_{κ,u} on the unit sphere) of every nonzero L² input is
absolutely continuous with density (πκ)⁻¹ arcosh(|Δ_u|/2) on {|Δ_u| > 2} and 0 elsewhere, Δ_u the spatial
transfer discriminant; for a continuous periodic representative this is the printed eq:root-explicit-density, with
the density bound and support = closure {|Δ| > 2}. Includes the trace-symbol identity exp(−izL/2) s(z;u) = Δ_u(z).
Statements verbatim; import closure contains no Ext025 module (Terra r154). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped Real ENNReal
namespace R7E05Spec
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.PhysicalQuantumMeasure (measure)
open QuantumNLS.RootDensityIdentification (dens)
open QuantumNLS.RootDensity (hfun)
open QuantumNLS.BulkResponseActual (rootDensityFormula HasRootDensity IsPeriodicRepresentative)

theorem traceSymbol_all_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 ≤ κ) (u : L2T L) (z : ℂ) :
    Complex.exp (-(Complex.I * z * L / 2)) * QuantumNLS.NormalizedTransfer.productSymbol L κ u z =
      QuantumNLS.L2SpatialTransfer.discriminant κ u z :=
  QuantumNLS.RootTraceSymbolFinal.traceSymbol_all hκ u z

theorem measure_eq_Mmeas_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (u : L2T L) :
    measure hκ u = QuantumNLS.FullMass.Mmeas κ u :=
  QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas hκ u

theorem root_density_spec {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    measure hκ u = volume.withDensity (fun t => ENNReal.ofReal (dens κ u t)) :=
  QuantumNLS.RootDensityIdentification.root_density hκ hu

theorem measure_absolutelyContinuous_spec {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) :
    measure hκ u ≪ volume :=
  QuantumNLS.RootDensityIdentification.measure_absolutelyContinuous hκ hu

theorem root_density_rep_spec {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) {uf : ℝ → ℂ}
    (hrep : IsPeriodicRepresentative L u uf) : HasRootDensity L κ uf (measure hκ u) :=
  QuantumNLS.RootDensityIdentification.root_density_rep hκ hu hrep

theorem root_density_structure_spec {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0)
    {uf : ℝ → ℂ} (hrep : IsPeriodicRepresentative L u uf) :
    measure hκ u ≪ volume ∧
    (∀ t, dens κ u t ≤ (∫ x in (0 : ℝ)..L, ‖uf x‖) / (Real.pi * Real.sqrt κ)) ∧
    (measure hκ u).support = closure {t : ℝ | 2 < |QuantumNLS.RootDiscriminant.discReal L κ uf t|} :=
  QuantumNLS.RootDensityIdentification.root_density_structure hκ hu hrep

theorem dens_def {L : ℝ} [Fact (0 < L)] (κ : ℝ) (u : L2T L) (t : ℝ) : dens κ u t =
  (Real.pi * κ)⁻¹ * hfun |(QuantumNLS.L2SpatialTransfer.discriminant κ u (t : ℂ)).re| := rfl
theorem hfun_def (r : ℝ) : hfun r = if 2 < r then Real.arcosh (r / 2) else 0 := rfl
theorem rootDensityFormula_def (L κ : ℝ) (uf : ℝ → ℂ) (t : ℝ) : rootDensityFormula L κ uf t =
  if 2 < ‖QuantumNLS.SpatialTransfer.discriminant L κ uf (t : ℂ)‖ then
    Real.arcosh (‖QuantumNLS.SpatialTransfer.discriminant L κ uf (t : ℂ)‖ / 2) / (Real.pi * κ)
  else 0 := rfl
theorem HasRootDensity_def (L κ : ℝ) (uf : ℝ → ℂ) (μ : Measure ℝ) : HasRootDensity L κ uf μ =
  (μ = volume.withDensity (fun t => ENNReal.ofReal (rootDensityFormula L κ uf t))) := rfl
theorem IsPeriodicRepresentative_def (L : ℝ) [Fact (0 < L)] (u : L2T L) (uf : ℝ → ℂ) :
    IsPeriodicRepresentative L u uf = (Continuous uf ∧ (∀ x, uf (x + L) = uf x) ∧
    (u : AddCircle L → ℂ) =ᵐ[volume] fun x => uf ((AddCircle.equivIco L 0 x : ℝ))) := rfl
end R7E05Spec
#print axioms R7E05Spec.root_density_spec
#print axioms R7E05Spec.root_density_structure_spec
#print axioms R7E05Spec.traceSymbol_all_spec
