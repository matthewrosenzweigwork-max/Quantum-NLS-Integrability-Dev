import QuantumNLS.Prop020Explicit
/-! integrator-authored trusted spec for PROP-020 Q7A:thm:main, explicit rate (review record r15 FULL ACCEPT): headline statement(s) copied verbatim from Prop020Explicit (QuantumNLS.Prop020Explicit). -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace QuantumNLS.P020Spec
open QuantumNLS.Prop020Explicit
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN)
open QuantumNLS.PROP018Probability (cutN regime_eventually propBound cut_bounds pow_rpow_nat)
open QuantumNLS.Prop017Quantum (qAct eta0)
open QuantumNLS.Prop017Physical (RootSpectralInputs event_projection)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.Prop018Phase (qch C0ev C1ev phase_of_bundle)
open QuantumNLS.Prop018Scalar (cscal scalar_of_bundle Lbd Lbd_nonneg)
open QuantumNLS.Prop018BundleFull (moving_contour_bundle_full)
open QuantumNLS.Prop020Main (norm_wvec)
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
open QuantumNLS.RootEvent (prop017Cb)
open QuantumNLS.Prop017Quantum (Ctail Dtail)
open QuantumNLS.RootMeasureConcentrationSharp (Csharp)

set_option maxHeartbeats 8000000 in
theorem prop020_rate_explicit_spec (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (d k : ℕ) (ords : Finset ℕ) (hords : ords ⊆ Finset.range (d + 1)) (T : ℕ → ℝ)
    (α γ : ℝ) (b : ℕ) (hα : 0 < α) (_hα' : α < 1 / (3 * (d : ℝ) + 4))
    (hγ1 : ((d : ℝ) + 1) * α < γ) (hγ2 : γ < (1 - α) / 3) (hb : (d : ℝ) + 1 < b)
    (p0 : ℕ) (hp0 : 1 < 2 * (p0 : ℝ) * α) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ Cp Dp Cb : ℝ, 0 ≤ Cb ∧
      (∀ᶠ N : ℕ in atTop, (bornMeasure (physBasis L hκ N) u hu).real
        (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ α) (cutN L α N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)ᶜ ≤
          Cp * (N : ℝ) ^ (1 - 2 * (p0 : ℝ) * α) + Dp * (N : ℝ) ^ (-α) + Cb * (N : ℝ) ^ (α - 1 + 3 * γ)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ q : ℕ in atTop, ∀ Ψ : SymSector ℂ (L2T L) (k + q), ‖Ψ‖ = 1 →
        ∀ t : ℕ → ℝ, (∀ r ∈ ords, |t r| ≤ T r) →
          traceNorm (reducedDensityPower k q
              ((evolution (physBasis L hκ (k + q))
                (fun m => ∑ r ∈ ords, t r * eigenvalue L (k + q) (κ / ((k + q : ℕ) : ℝ)) r m) 1 Ψ :
                SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)) -
            reducedDensityPower k q
              ((evol ((((k + q : ℕ) : ℝ) : ℂ) • ∑ r ∈ ords, ((t r : ℝ) : ℂ) •
                  Lwin L κ (μ : Measure ℝ) α h (k + q) (fun z => z ^ r) (continuous_pow r)) 1
                (wvec (k + q) u) : SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q))) ≤
          ENNReal.ofReal (2 * ‖Ψ - wvec (k + q) u‖ +
            8 * Real.sqrt (Cp * (((k + q : ℕ) : ℝ)) ^ (1 - 2 * (p0 : ℝ) * α) + Dp * (((k + q : ℕ) : ℝ)) ^ (-α) +
              Cb * (((k + q : ℕ) : ℝ)) ^ (α - 1 + 3 * γ)) +
            C * ((((k + q : ℕ) : ℝ)) ^ (α * ((d : ℝ) + 1) - γ) +
              (((k + q : ℕ) : ℝ)) ^ (-(α * ((b : ℝ) - d - 1))) +
              (((k + q : ℕ) : ℝ)) ^ (α * ((d : ℝ) + 1) - 1))) := by
  exact QuantumNLS.Prop020Explicit.prop020_rate_explicit hκ u hu hμ hηh hδ hd0 hin d k ords hords T α γ b hα _hα' hγ1 hγ2 hb p0 hp0

end QuantumNLS.P020Spec
#print axioms QuantumNLS.P020Spec.prop020_rate_explicit_spec
