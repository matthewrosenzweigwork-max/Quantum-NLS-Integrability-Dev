import QuantumNLS.ExactOccupationAlgebra
/-! integrator-authored trusted spec for R-61E9CD1F prop:exact-occupation-algebra (canonical_algebra.tex:4–35): the
frozen whole-sector statements of ExactOccupationAlgebra restated verbatim (Terra r131 ACCEPT). -/
namespace ExactOccupationAlgebraSpec
open scoped InnerProductSpace ComplexConjugate
open QuantumNLS.OccupationHilbert QuantumNLS.BetheCoefficientTransform QuantumNLS.BetheOccupationGauge QuantumNLS.CartesianOccupationTransfer QuantumNLS.QuantumFourierSpecification
open QuantumNLS.OccupationUnitary QuantumNLS.OccupationConjugacy
open QuantumNLS QuantumNLS.ExactOccupationAlgebra

theorem physical_comm_spec {N : ℕ} {L : ℝ} [Fact (0 < L)] (hN : 0 < N) (β : BetheBasis L N) (γ : Gauge) (a b c d : ℤ) :
    physical β γ a b * physical β γ c d - physical β γ c d * physical β γ a b =
      (N : ℂ)⁻¹ • ((if a = d then (1 : ℂ) else 0) • physical β γ c b -
        (if b = c then (1 : ℂ) else 0) • physical β γ a d) := by
  apply QuantumNLS.ExactOccupationAlgebra.physical_comm <;> assumption

theorem count_comm_spec {N : ℕ} {L : ℝ} [Fact (0 < L)] (hN : 0 < N) (β : BetheBasis L N) (γ : Gauge) (j a b : ℤ) :
    count β γ j * physical β γ a b - physical β γ a b * count β γ j =
      (((if j = b then (1 : ℂ) else 0) - (if j = a then (1 : ℂ) else 0)) / N) •
        physical β γ a b := by
  apply QuantumNLS.ExactOccupationAlgebra.count_comm <;> assumption

theorem coefficient_count_comm_spec {N : ℕ} {L : ℝ} [Fact (0 < L)] (hN : 0 < N) (j a b : ℤ) :
    E N j j * E N a b - E N a b * E N j j =
      (((if j = b then (1 : ℂ) else 0) - (if j = a then (1 : ℂ) else 0)) / N) • E N a b := by
  apply QuantumNLS.ExactOccupationAlgebra.coefficient_count_comm <;> assumption

theorem count_basis_spec {N : ℕ} {L : ℝ} [Fact (0 < L)] (β : BetheBasis L N) (γ : Gauge) (j : ℤ) (m : BetheLabels.MArr N) :
    count β γ j (gaugedBasis β γ m) =
      ((((marrArr N m).1 j : ℝ) / N : ℝ) : ℂ) • gaugedBasis β γ m := by
  apply QuantumNLS.ExactOccupationAlgebra.count_basis <;> assumption

theorem selected_comm_spec {N : ℕ} {L : ℝ} [Fact (0 < L)] (hcont : BetheConditionalBasis.AbstractContinuity) (s : UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 0 < N) (a b c d : ℤ) :
    selectedPhysical hcont s L κ hκ N a b * selectedPhysical hcont s L κ hκ N c d -
      selectedPhysical hcont s L κ hκ N c d * selectedPhysical hcont s L κ hκ N a b =
    (N : ℂ)⁻¹ • ((if a = d then (1 : ℂ) else 0) • selectedPhysical hcont s L κ hκ N c b -
      (if b = c then (1 : ℂ) else 0) • selectedPhysical hcont s L κ hκ N a d) := by
  apply QuantumNLS.ExactOccupationAlgebra.selected_comm <;> assumption

theorem meanField_comm_spec {N : ℕ} {L : ℝ} [Fact (0 < L)] (hcont : BetheConditionalBasis.AbstractContinuity) (s : UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) (a b c d : ℤ) :
    selectedMeanFieldPhysical hcont s L κ hκ N hN a b * selectedMeanFieldPhysical hcont s L κ hκ N hN c d -
      selectedMeanFieldPhysical hcont s L κ hκ N hN c d * selectedMeanFieldPhysical hcont s L κ hκ N hN a b =
    (N : ℂ)⁻¹ • ((if a = d then (1 : ℂ) else 0) • selectedMeanFieldPhysical hcont s L κ hκ N hN c b -
      (if b = c then (1 : ℂ) else 0) • selectedMeanFieldPhysical hcont s L κ hκ N hN a d) := by
  apply QuantumNLS.ExactOccupationAlgebra.meanField_comm <;> assumption

theorem scaled_comm_spec {N : ℕ} {L : ℝ} [Fact (0 < L)] (hN : 0 < N) (β : BetheBasis L N) (γ : Gauge) (a b c d : ℤ) :
    ((N : ℂ) / Complex.I) •
      (physical β γ a b * physical β γ c d - physical β γ c d * physical β γ a b) =
    Complex.I • ((if b = c then (1 : ℂ) else 0) • physical β γ a d -
      (if a = d then (1 : ℂ) else 0) • physical β γ c b) := by
  apply QuantumNLS.ExactOccupationAlgebra.scaled_comm <;> assumption

theorem quadratic_matrixUnit_spec {N : ℕ} {L : ℝ} [Fact (0 < L)] (a b : ℤ) : quadratic (matrixUnit a b) = cartesian a b := by
  apply QuantumNLS.ExactOccupationAlgebra.quadratic_matrixUnit <;> assumption

theorem matrixUnit_product_spec {N : ℕ} {L : ℝ} [Fact (0 < L)] (a b c d : ℤ) :
    matrixUnit a b * matrixUnit c d = (if a = d then (1 : ℂ) else 0) • matrixUnit c b := by
  apply QuantumNLS.ExactOccupationAlgebra.matrixUnit_product <;> assumption

theorem matrixUnit_comm_spec {N : ℕ} {L : ℝ} [Fact (0 < L)] (a b c d : ℤ) :
    matrixUnit a b * matrixUnit c d - matrixUnit c d * matrixUnit a b =
      (if a = d then (1 : ℂ) else 0) • matrixUnit c b -
        (if b = c then (1 : ℂ) else 0) • matrixUnit a d := by
  apply QuantumNLS.ExactOccupationAlgebra.matrixUnit_comm <;> assumption

theorem cartesian_bracket_spec {N : ℕ} {L : ℝ} [Fact (0 < L)] (a b c d : ℤ) (u : OneParticle) :
    SymplecticBracket.pbC (cartesian a b) (cartesian c d) u =
      Complex.I * ((if b = c then (1 : ℂ) else 0) * cartesian a d u -
        (if a = d then (1 : ℂ) else 0) * cartesian c b u) := by
  apply QuantumNLS.ExactOccupationAlgebra.cartesian_bracket <;> assumption

theorem cartesian_diag_spec {N : ℕ} {L : ℝ} [Fact (0 < L)] (j : ℤ) (u : OneParticle) : cartesian j j u = (action j u : ℂ) := by
  apply QuantumNLS.ExactOccupationAlgebra.cartesian_diag <;> assumption

theorem action_bracket_spec {N : ℕ} {L : ℝ} [Fact (0 < L)] (j a b : ℤ) (u : OneParticle) :
    SymplecticBracket.pbC (fun v => (action j v : ℂ)) (cartesian a b) u =
      Complex.I * ((if j = a then (1 : ℂ) else 0) -
        (if j = b then (1 : ℂ) else 0)) * cartesian a b u := by
  apply QuantumNLS.ExactOccupationAlgebra.action_bracket <;> assumption

theorem conjugate_cartesian_spec {N : ℕ} {L : ℝ} [Fact (0 < L)] (a b : ℤ) :
    (fun u => conj (cartesian a b u)) = cartesian b a := by
  apply QuantumNLS.ExactOccupationAlgebra.conjugate_cartesian <;> assumption

theorem pair_bracket_spec {N : ℕ} {L : ℝ} [Fact (0 < L)] (a b : ℤ) (u : OneParticle) :
    SymplecticBracket.pbC (cartesian a b) (fun v => conj (cartesian a b v)) u =
      Complex.I * ((action a u : ℂ) - (action b u : ℂ)) := by
  apply QuantumNLS.ExactOccupationAlgebra.pair_bracket <;> assumption

theorem cartesian_COT1_spec {N : ℕ} {L : ℝ} [Fact (0 < L)] (w : PhysicalField L → Coordinates) (a b : ℤ) (u : PhysicalField L) :
    cartesian a b (w u) = symbol w a b u := by
  apply QuantumNLS.ExactOccupationAlgebra.cartesian_COT1 <;> assumption

end ExactOccupationAlgebraSpec
#print axioms ExactOccupationAlgebraSpec.physical_comm_spec
#print axioms ExactOccupationAlgebraSpec.count_comm_spec
#print axioms ExactOccupationAlgebraSpec.coefficient_count_comm_spec
#print axioms ExactOccupationAlgebraSpec.count_basis_spec
#print axioms ExactOccupationAlgebraSpec.selected_comm_spec
#print axioms ExactOccupationAlgebraSpec.meanField_comm_spec
#print axioms ExactOccupationAlgebraSpec.scaled_comm_spec
#print axioms ExactOccupationAlgebraSpec.quadratic_matrixUnit_spec
#print axioms ExactOccupationAlgebraSpec.matrixUnit_product_spec
#print axioms ExactOccupationAlgebraSpec.matrixUnit_comm_spec
#print axioms ExactOccupationAlgebraSpec.cartesian_bracket_spec
#print axioms ExactOccupationAlgebraSpec.cartesian_diag_spec
#print axioms ExactOccupationAlgebraSpec.action_bracket_spec
#print axioms ExactOccupationAlgebraSpec.conjugate_cartesian_spec
#print axioms ExactOccupationAlgebraSpec.pair_bracket_spec
#print axioms ExactOccupationAlgebraSpec.cartesian_COT1_spec
