import QuantumNLS.Prop020Main
/-! integrator-authored trusted spec for PROP-020 Q7A:thm:main, full comparison (review record r15 FULL ACCEPT): headline statement(s) copied verbatim from Prop020Main (QuantumNLS.Prop020Main). -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace QuantumNLS.P020SpecB
open QuantumNLS.Prop020Main
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN)
open QuantumNLS.PROP018Probability (cutN regime_eventually)
open QuantumNLS.Prop017Quantum (qAct eta0)
open QuantumNLS.Prop017Physical (RootSpectralInputs event_projection)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.Prop018Phase (qch C0ev C1ev phase_of_bundle)
open QuantumNLS.Prop018Scalar (cscal scalar_of_bundle Lbd Lbd_nonneg)
open QuantumNLS.Prop018Bundle (moving_contour_bundle)
open QuantumNLS.Prop019Linearization (pw continuous_pw)
open QuantumNLS.Prop019Discharge (mp_statement)
open QuantumNLS.Prop020Vector (normalize_proj)
open QuantumNLS.Prop020Diag (C0op_eigen evol_isometry)
open QuantumNLS.Prop020Link
open QuantumNLS.Prop020Chain
open QuantumNLS.MPContour (ThetaSpace nu zθ uθ rectPieces continuous_zθ)
open QuantumNLS.MPFamily (BgFam gθ dθ good contDiff_gθ)
open QuantumNLS.MPChartSmooth (rad)
open QuantumNLS.MPChartBounds (rho_pos)
open QuantumNLS.MPOps (C0op Lop)
open QuantumNLS.FunctionalLinearization (evol)
open QuantumNLS.TensorCarrier (SymSector HilbertTensorPower reducedDensityPower)
open QuantumNLS.TraceClass (traceNorm)
open QuantumNLS.NormalizedTransfer (normalizedTransfer)
open QuantumNLS.UnconditionalBetheBasis (meanField_physicalBasis transfer_physicalBasis)
open QuantumNLS.BetheSpectralCharges (evolution eigenvalue)
open QuantumNLS.HighMomentsOps (wvec)
variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

set_option maxHeartbeats 8000000 in
theorem prop020_main_spec (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (d k : ℕ) (ords : Finset ℕ) (hords : ords ⊆ Finset.range (d + 1)) (T : ℕ → ℝ)
    (α γ : ℝ) (b : ℕ) (hα : 0 < α) (hα' : α < 1 / (3 * (d : ℝ) + 4))
    (hγ1 : ((d : ℝ) + 1) * α < γ) (hγ2 : γ < (1 - α) / 3) (hb : (d : ℝ) + 1 < b)
    (Ψ : (q : ℕ) → SymSector ℂ (L2T L) (k + q)) (hΨ : ∀ q, ‖Ψ q‖ = 1)
    (hconv : Tendsto (fun q => ‖Ψ q - wvec (k + q) u‖) atTop (𝓝 0)) :
    Tendsto (fun q : ℕ => ⨆ (t : ℕ → ℝ) (_ : ∀ r ∈ ords, |t r| ≤ T r),
      traceNorm (reducedDensityPower k q
          ((evolution (physBasis L hκ (k + q))
            (fun m => ∑ r ∈ ords, t r * eigenvalue L (k + q) (κ / ((k + q : ℕ) : ℝ)) r m) 1 (Ψ q) :
            SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)) -
        reducedDensityPower k q
          ((evol ((((k + q : ℕ) : ℝ) : ℂ) • ∑ r ∈ ords, ((t r : ℝ) : ℂ) •
              Lwin L κ (μ : Measure ℝ) α h (k + q) (fun z => z ^ r) (continuous_pow r)) 1
            (wvec (k + q) u) : SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q))))
      atTop (𝓝 0) := by
  exact QuantumNLS.Prop020Main.prop020_main hκ u hu hμ hηh hδ hd0 hin d k ords hords T α γ b hα hα' hγ1 hγ2 hb Ψ hΨ hconv

end QuantumNLS.P020SpecB
#print axioms QuantumNLS.P020SpecB.prop020_main_spec
