import QuantumNLS.ExactDensity
/-! integrator-authored trusted spec for R-BB03032A prop:exact-density (projective_reconstruction.tex:27–90): the frozen statements of ExactDensity restated verbatim
(Terra r131 ACCEPT). -/
namespace ExactDensitySpec
open scoped InnerProductSpace ComplexConjugate ENNReal
open Filter Topology
open QuantumNLS.Occupation QuantumNLS.OccupationHilbert
open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform QuantumNLS.BetheOccupationGauge
  QuantumNLS.CartesianOccupationTransfer
open QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform QuantumNLS.BetheOccupationGauge
  QuantumNLS.CartesianOccupationTransfer QuantumNLS.AuxiliaryDensity
open QuantumNLS QuantumNLS.ExactDensity

theorem exact_density_spec {L : ℝ} [Fact (0 < L)] {q : ℕ} (b : BetheBasis L (1 + q)) (g : Gauge) (ψ : HN L (1 + q)) (hψ : ‖ψ‖ = 1) :
    ∃ Γ : OneParticle →L[ℂ] OneParticle,
      Γ.IsPositive ∧ QuantumNLS.TraceClass.IsTraceClass Γ ∧ QuantumNLS.TraceClass.posTrace Γ = 1 ∧
      (∀ a c : ℤ, ⟪oneBasis a, Γ (oneBasis c)⟫_ℂ = gammaEntry b g ψ a c) ∧
      (∀ a c : ℤ, gammaEntry b g ψ a c =
        ⟪coordinates b g ψ, E (1 + q) a c (coordinates b g ψ)⟫_ℂ) ∧
      (∀ a c : ℤ, gammaEntry b g ψ a c =
        ⟪fockTransform (gaugedBasis b g) ψ, auxiliary q a c (fockTransform (gaugedBasis b g) ψ)⟫_ℂ) ∧
      (∀ a c : ℤ, HasSum (fun ν : Arr q =>
        ((Real.sqrt (((ν.1 a : ℝ) + 1) * ((ν.1 c : ℝ) + 1)) / ((1 + q : ℕ) : ℝ) : ℝ) : ℂ) *
          coordinates b g ψ (plusE ν a) * conj (coordinates b g ψ (plusE ν c)))
        (gammaEntry b g ψ a c)) ∧
      (∀ a c : ℤ, Summable (fun ν : Arr q => ‖
        ((Real.sqrt (((ν.1 a : ℝ) + 1) * ((ν.1 c : ℝ) + 1)) / ((1 + q : ℕ) : ℝ) : ℝ) : ℂ) *
          coordinates b g ψ (plusE ν a) * conj (coordinates b g ψ (plusE ν c))‖)) ∧
      (∀ a c : ℤ, a ≠ c → HasSum (fun m : Donor (1 + q) a =>
        ((Real.sqrt ((m.1.1 a : ℝ) * ((m.1.1 c : ℝ) + 1)) / ((1 + q : ℕ) : ℝ) : ℝ) : ℂ) *
          (qPhase g m.1 * conj (qPhase g (destination (1 + q) a c m))) *
          (gCoef b ψ m.1 * conj (gCoef b ψ (destination (1 + q) a c m))))
        (gammaEntry b g ψ a c))  := by
  apply QuantumNLS.ExactDensity.exact_density <;> assumption

end ExactDensitySpec
#print axioms ExactDensitySpec.exact_density_spec
