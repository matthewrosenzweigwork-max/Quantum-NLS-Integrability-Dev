import QuantumNLS.Prop019Linearization
import QuantumNLS.MPLinearization

/-!
# PROP-019 (`Q7A:lem:linearization`): discharge of the named hypothesis `MPLinearizationStatement`

sonnet_fourier's PROP-026 actual-contour theorem `MPLinearization.mp_linearization` is frozen (`79098fb1`, with
`MPContourBound` `d68cca0c`, `MPFamilyMeas` `234d96be`). Its statement is exactly W2's named hypothesis
`Prop019Linearization.MPLinearizationStatement` (the weighted length `MPContour.wlen P` unfolds definitionally to the integral
written out there; the instantiation below is checked by the kernel with no rewriting). Hence PROP-019 holds with
`RootSpectralInputs` as its only open hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop019Discharge

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN)
open QuantumNLS.PROP018Probability (cutN)
open QuantumNLS.Prop017Quantum (qAct eta0)
open QuantumNLS.Prop017Physical (RootSpectralInputs)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.Prop019Linearization (MPLinearizationStatement pw continuous_pw prop019_linearization)
open QuantumNLS.MPContour (Piece ThetaSpace nu zθ uθ affinePiece rectPieces)
open QuantumNLS.MPFamily (BgFam gθ dθ)
open QuantumNLS.MPOps (C0op Lop)
open QuantumNLS.FunctionalLinearization (evol)
open QuantumNLS.TensorCarrier (SymSector HilbertTensorPower reducedDensityPower)
open QuantumNLS.NormalizedTransfer (normalizedTransfer)
open QuantumNLS.UnconditionalBetheBasis (meanField_physicalBasis)

/-- **The named hypothesis is sonnet_fourier's frozen theorem** (one-line instantiation; `wlen` is definitional). -/
theorem mp_statement (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (h : ℝ) (k : ℕ) :
    ∀ d₀ s₁ a₀ c₁ : ℝ, 0 < d₀ → 0 ≤ s₁ → 0 < a₀ → 0 ≤ c₁ → MPLinearizationStatement L κ h k d₀ s₁ a₀ c₁ :=
  fun d₀ s₁ a₀ c₁ h1 h2 h3 h4 => QuantumNLS.MPLinearization.mp_linearization L κ hκ h k d₀ s₁ a₀ c₁ h1 h2 h3 h4

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- **PROP-019** with `RootSpectralInputs` as the only open hypothesis (W2's `prop019_linearization` with
`MPLinearizationStatement` discharged by `mp_statement`). -/
theorem prop019_linearization_unconditional (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (θ γ : ℝ) (hθ : 0 < θ) (hγ : 0 < γ) (hsum : 3 * γ + θ < 1) (pt : ℕ) (hpt : 1 < 2 * (pt : ℝ) * θ)
    (d k : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real
        (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)ᶜ)
        atTop (𝓝 0) ∧
      ∃ d₀ s₁ a₀ c₁ C : ℝ, 0 < d₀ ∧ 0 ≤ s₁ ∧ 0 < a₀ ∧ 0 ≤ c₁ ∧ 0 ≤ C ∧
        ∀ᶠ q : ℕ in atTop, ∀ (hN : 1 ≤ k + q) (φ : SymSector ℂ (L2T L) (k + q)), ‖φ‖ = 1 →
          (∀ m ∉ EN (μ : Measure ℝ) (qAct L κ (k + q)) (((k + q : ℕ) : ℝ) ^ θ) (cutN L θ (k + q)) ρ h (eta0 L κ)
              (((k + q : ℕ) : ℝ) ^ (-γ)) b, ⟪meanField_physicalBasis L (k + q) hN hκ m, φ⟫_ℂ = 0) →
          ∃ B : BgFam (NbhdN (cutN L θ (k + q)) h (ρ / 8)) d₀ s₁ a₀ c₁,
            B.c0 = (fun z => Complex.I * κ * Gfull (μ : Measure ℝ) z) ∧ B.D = Df L κ (Gfull (μ : Measure ℝ)) ∧
            B.s = sf L κ (Gfull (μ : Measure ℝ)) ∧ B.A = Af κ (Gfull (μ : Measure ℝ)) ∧
            ∀ (t : ℝ) (p : ℕ → ℝ),
              QuantumNLS.TraceClass.traceNorm
                (reducedDensityPower k q
                    ((evol (((((k + q : ℕ) : ℝ) : ℂ)) •
                      C0op (nu 6) (fun θ' => normalizedTransfer L κ (k + q)
                        (zθ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)) θ'))
                        (uθ κ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)))
                        (gθ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)) B)) 1 φ :
                      SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)) -
                  reducedDensityPower k q
                    ((evol (((((k + q : ℕ) : ℝ) : ℂ)) •
                      Lop (nu 6) (fun θ' => normalizedTransfer L κ (k + q)
                        (zθ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)) θ'))
                        (uθ κ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)))
                        (dθ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)) B)) 1 φ :
                      SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q))) ≤
                ENNReal.ofReal (C * (|t| * ∑ r ∈ Finset.range (d + 1), |p r|) *
                  (1 + cutN L θ (k + q)) ^ (d + 1) *
                  ((((k + q : ℕ) : ℝ)) ^ (-γ) + 1 / ((((k + q : ℕ) : ℝ)) ^ θ) ^ b + 1 / ((k + q : ℕ) : ℝ))) := prop019_linearization hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc θ γ hθ hγ hsum pt hpt d k (mp_statement L hκ h k)

end QuantumNLS.Prop019Discharge

#print axioms QuantumNLS.Prop019Discharge.mp_statement
#print axioms QuantumNLS.Prop019Discharge.prop019_linearization_unconditional
