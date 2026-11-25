import QuantumNLS.D1Def043
/-! integrator-authored trusted spec for DEF-043 D1 realization (review record r52 PASS): headline statement(s) copied verbatim from D1Def043 (QuantumNLS.D1Def043). -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Set
open QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
namespace QuantumNLS.D1D043Spec
open QuantumNLS.D1Def043
variable {L κ : ℝ}

set_option maxHeartbeats 8000000 in
theorem regular_unique_index_spec {μ : Measure ℝ} {x : ℝ} (hx : regularCut L κ μ x) :
    ∃! a : ℤ, 2 * Real.pi * a < exteriorForce L κ μ x ∧
      exteriorForce L κ μ x < 2 * Real.pi * (a + 1) := by
  exact QuantumNLS.D1Def043.regular_unique_index hx

set_option maxHeartbeats 8000000 in
theorem bracket_regular_spec {μ : Measure ℝ} {x : ℝ} (hx : x ∉ μ.support)
    {a : ℤ} (h1 : 2 * Real.pi * a < exteriorForce L κ μ x)
    (h2 : exteriorForce L κ μ x < 2 * Real.pi * (a + 1)) : regularCut L κ μ x := by
  exact QuantumNLS.D1Def043.bracket_regular hx h1 h2

set_option maxHeartbeats 8000000 in
theorem toFull_toD1_spec (S : IndexedScalarMeasure L κ) : S.toD1.toFull = S := by
  exact QuantumNLS.D1Def043.toFull_toD1 S

set_option maxHeartbeats 8000000 in
theorem toD1_toFull_spec (S : D1ScalarMeasure L κ) : S.toFull.toD1 = S := by
  exact QuantumNLS.D1Def043.toD1_toFull S

set_option maxHeartbeats 8000000 in
theorem full_d1_spec (S : IndexedScalarMeasure L κ) : D1Sep S.toCuts := by
  exact QuantumNLS.D1Def043.full_d1 S

end QuantumNLS.D1D043Spec

/-- integrator pin: the D1 regular-cut definition unfolds to the owner's literal wording. -/
theorem regularCut_literal {L κ : ℝ} {μ : Measure ℝ} {x : ℝ} :
    QuantumNLS.D1Def043.regularCut L κ μ x ↔
      (x ∉ μ.support ∧ ∀ a : ℤ, exteriorForce L κ μ x / (2 * Real.pi) ≠ (a : ℝ)) := Iff.rfl

/-- integrator pin: D1 separation is required at EVERY regular cut, for the bracketing integer. -/
theorem separation_literal {L κ : ℝ} (S : QuantumNLS.D1Def043.D1ScalarMeasure L κ) (x : ℝ)
    (hx : QuantumNLS.D1Def043.regularCut L κ S.μ x) (a : ℤ)
    (h1 : 2 * Real.pi * a < exteriorForce L κ S.μ x) (h2 : exteriorForce L κ S.μ x < 2 * Real.pi * (a + 1)) :
    (∀ᵐ t ∂S.μ, t < x → indexLabel L κ S.reG t ≤ a) ∧
      (∀ᵐ t ∂S.μ, x < t → (a : ℝ) + 1 ≤ indexLabel L κ S.reG t) :=
  S.separation x hx a h1 h2

#print axioms QuantumNLS.D1D043Spec.regular_unique_index_spec
#print axioms QuantumNLS.D1D043Spec.bracket_regular_spec
#print axioms QuantumNLS.D1D043Spec.toFull_toD1_spec
#print axioms QuantumNLS.D1D043Spec.toD1_toFull_spec
#print axioms QuantumNLS.D1D043Spec.full_d1_spec
#print axioms separation_literal
#print axioms regularCut_literal
