import QuantumNLS.Fourier
/-!
Trusted statement for R-00E786F0 `F04:lem-products`, written by the integrator (not the prover) from
`source/chapters/foundations/F04.tex:22–69`. Spec definitions are written here from mathlib primitives:
T_L = `AddCircle L` with Lebesgue measure of mass L, p_n = 2πn/L, e_n = L^{-1/2} e^{i p_n x} (mathlib `fourier n`),
f̂(n) = ⟨e_n, f⟩ = ∫ conj(e_n) f, ‖f‖_{H^s}² = Σ (1+p_n²)^s |f̂(n)|², F(u) = |u|²u.
H^s for s ≥ 1 is modelled as L² functions with finite H^s sum (H^s ⊂ L² for s ≥ 0); products are pointwise on representatives.
-/
open MeasureTheory ComplexConjugate

namespace Spec
variable (L : ℝ) [Fact (0 < L)]
noncomputable def p (n : ℤ) : ℝ := 2 * Real.pi * n / L
noncomputable def e (n : ℤ) (x : AddCircle L) : ℂ := ((Real.sqrt L)⁻¹ : ℝ) * fourier n x
noncomputable def hat (f : AddCircle L → ℂ) (n : ℤ) : ℂ := ∫ x, conj (e L n x) * f x
noncomputable def normH (s : ℝ) (f : AddCircle L → ℂ) : ℝ :=
  Real.sqrt (∑' n : ℤ, (1 + p L n ^ 2) ^ s * ‖hat L f n‖ ^ 2)
def InH (s : ℝ) (f : AddCircle L → ℂ) : Prop :=
  MemLp f 2 (volume : Measure (AddCircle L)) ∧ Summable fun n : ℤ => (1 + p L n ^ 2) ^ s * ‖hat L f n‖ ^ 2
noncomputable def cL : ℝ := Real.sqrt (L⁻¹ * ∑' n : ℤ, (1 + p L n ^ 2)⁻¹)
noncomputable def F (u : AddCircle L → ℂ) (x : AddCircle L) : ℂ := ((‖u x‖ ^ 2 : ℝ) : ℂ) * u x
end Spec
open Spec

def R00E786F0Spec : Prop :=
  ∀ (L : ℝ) [Fact (0 < L)],
  -- c_L finite
  (Summable fun n : ℤ => (1 + p L n ^ 2)⁻¹) ∧
  -- eq:l1
  (∀ f, InH L 1 f → Summable (fun n => ‖hat L f n‖) ∧
      ∑' n, ‖hat L f n‖ ≤ Real.sqrt L * cL L * normH L 1 f ∧
      ∃ g : AddCircle L → ℂ, Continuous g ∧ f =ᵐ[volume] g ∧ ∀ x, ‖g x‖ ≤ cL L * normH L 1 f) ∧
  -- eq:algebra
  (∀ f g, InH L 1 f → InH L 1 g → InH L 1 (fun x => f x * g x) ∧
      normH L 1 (fun x => f x * g x) ≤ 2 * cL L * normH L 1 f * normH L 1 g) ∧
  -- eq:triple
  (∀ s : ℝ, 1 ≤ s → ∀ f g h, InH L s f → InH L s g → InH L s h →
      InH L s (fun x => f x * g x * h x) ∧
      normH L s (fun x => f x * g x * h x) ≤ (3 : ℝ) ^ (s - 1) * cL L ^ 2 *
        (normH L s f * normH L 1 g * normH L 1 h + normH L 1 f * normH L s g * normH L 1 h +
         normH L 1 f * normH L 1 g * normH L s h)) ∧
  -- eq:tame and eq:lipschitz with C_{s,L} = max{1, 3^{s+1} c_L²}
  (∀ s : ℝ, 1 ≤ s →
    (∀ u, InH L s u → InH L s (F L u) ∧
       normH L s (F L u) ≤ max 1 ((3 : ℝ) ^ (s + 1) * cL L ^ 2) * normH L 1 u ^ 2 * normH L s u) ∧
    (∀ u v, InH L s u → InH L s v → InH L s (fun x => F L u x - F L v x) ∧
       normH L s (fun x => F L u x - F L v x) ≤ max 1 ((3 : ℝ) ^ (s + 1) * cL L ^ 2) *
         (normH L s u ^ 2 + normH L s v ^ 2) * normH L s (fun x => u x - v x)))

theorem r00E786F0_spec : R00E786F0Spec := by
  intro L _
  exact QuantumNLS.Fourier.R00E786F0 L

#print axioms r00E786F0_spec
