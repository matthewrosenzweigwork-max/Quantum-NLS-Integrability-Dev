import QuantumNLS.PlaneWaveSemicircle
import QuantumNLS.FreeLimit
/-! integrator-authored trusted spec for R-28C650F0 prop:root-free (Terra r143 free-limit support, r153 ACCEPT):
(i) free limit: μ_{κ,u} → Σ_n |û(n)|² δ_{2πn/L} weakly as κ ↓ 0; (ii) plane wave u = L^{-1/2}e^{ipx}, p = 2πm/L:
μ_{κ,u} is the semicircle law of parameter κ/L centred at p, with density √(4κ/L−(t−p)²)₊/(2πκ/L).
Statements verbatim from FreeLimit 092c666f and PlaneWaveSemicircle e1f14c1a; muKappa is the unique quantum
limiting measure (muKappa_spec / IsLimitingRapidityMeasure). No Ext025 module in the import closure. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped Real ENNReal
namespace R28CSpec
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Fourier (modeLp coeff)
open QuantumNLS.FreeLimit (freeMeasure freeProb muKappa)
open QuantumNLS.PlaneWaveSymbol (pm)
open QuantumNLS.PlaneWaveSemicircle (nuP)
open QuantumNLS.SemicircleStieltjes (scMeasure)
open QuantumNLS.BulkResponseActual (IsLimitingRapidityMeasure)

theorem muKappa_spec_spec {L : ℝ} [Fact (0 < L)] (u : L2T L) (hu : ‖u‖ = 1) {κ : ℝ} (h : 0 < κ) :
    IsLimitingRapidityMeasure L κ h u hu (muKappa u hu κ) :=
  QuantumNLS.FreeLimit.muKappa_spec u hu h

theorem tendsto_muKappa_free_spec {L : ℝ} [Fact (0 < L)] (u : L2T L) (hu : ‖u‖ = 1) :
    Tendsto (muKappa u hu) (𝓝[>] 0) (𝓝 (freeProb u hu)) :=
  QuantumNLS.FreeLimit.tendsto_muKappa_free u hu

theorem plane_wave_semicircle_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (m : ℤ)
    (hu : ‖modeLp L m‖ = 1) :
    (muKappa (modeLp L m) hu κ : Measure ℝ) = nuP (κ / L) (pm L m) :=
  QuantumNLS.PlaneWaveSemicircle.plane_wave_semicircle hκ m hu

theorem plane_wave_density_spec {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (m : ℤ)
    (hu : ‖modeLp L m‖ = 1) :
    (muKappa (modeLp L m) hu κ : Measure ℝ) =
      volume.withDensity (fun t => ENNReal.ofReal
        (Real.sqrt (4 * (κ / L) - (t - pm L m) ^ 2) / (2 * π * (κ / L)))) :=
  QuantumNLS.PlaneWaveSemicircle.plane_wave_density hκ m hu

theorem freeMeasure_def (L : ℝ) [Fact (0 < L)] (u : L2T L) : freeMeasure L u =
  Measure.sum (fun n : ℤ => ENNReal.ofReal (‖coeff L (u : AddCircle L → ℂ) n‖ ^ 2) •
    Measure.dirac (2 * Real.pi * n / L)) := rfl
theorem muKappa_def {L : ℝ} [Fact (0 < L)] (u : L2T L) (hu : ‖u‖ = 1) (κ : ℝ) : muKappa u hu κ =
  if h : 0 < κ then Classical.choose (QuantumNLS.RootMeasureExistence.exists_limiting_measure h u hu)
  else freeProb u hu := rfl
theorem pm_def (L : ℝ) (m : ℤ) : pm L m = 2 * Real.pi * m / L := rfl
theorem nuP_def (a p : ℝ) : nuP a p = (scMeasure a).map (fun t => t + p) := rfl
end R28CSpec
#print axioms R28CSpec.plane_wave_density_spec
#print axioms R28CSpec.tendsto_muKappa_free_spec
