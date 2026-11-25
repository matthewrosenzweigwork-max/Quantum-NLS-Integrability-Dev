import QuantumNLS.ContactForm
import QuantumNLS.ProductWeakDerivatives

/-! integrator-authored trusted spec for R-C21B75F5 `contact:lem:trace` (A01.tex:13), v1 (2026-11-14).
Scoped core reading; see STATUS for the gaps to the literal statement (smooth-function restriction,
explicit target unitary ℓ²(TIdx) ≃ L²(T_L^{N-1})). -/

open MeasureTheory
open QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.PhysicalTensor QuantumNLS.Fourier
open QuantumNLS.CollisionTrace QuantumNLS.ProductWeakDerivatives

namespace QuantumNLS.C21Spec

/-- (1) estimate with the genuine distributional derivative `∂_i ψ` (every smooth torus test);
(2) on every trigonometric polynomial of H¹, T is the actual pointwise restriction to `x_i = x_j`
expanded in the product modes `Ediag` of `T_L^{N-1}`; (3) T is the unique continuous linear
map with property (2)'s values on trigonometric polynomials. -/
def C21Spec : Prop :=
  ∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (i j : Fin N) (hij : i ≠ j),
    ∃ T : PhysH1 L N →L[ℂ] L2 (TIdx N i j),
      (∀ ε : ℝ, 0 < ε → ∀ (ψ : PhysH1 L N) (G : L2TN L N), HasWeakPartial i ψ.val G →
          ‖T ψ‖ ^ 2 ≤ ε * ‖G‖ ^ 2 + (L⁻¹ + ε⁻¹) * ‖ψ.val‖ ^ 2) ∧
      (∀ (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ) (t : AddCircle L)
          (y : Rest N i j → AddCircle L),
          ∑ w ∈ S, c w * ∏ l, mode L (w l) (diagPoint i j t y l) =
            ∑' τ : TIdx N i j, ((T (trigElem (L := L) S c) : L2 (TIdx N i j)) : TIdx N i j → ℂ) τ *
              Ediag i j τ t y) ∧
      (∀ T' : PhysH1 L N →L[ℂ] L2 (TIdx N i j),
          (∀ (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ),
            T' (trigElem (L := L) S c) = T (trigElem (L := L) S c)) → T' = T)

theorem c21_spec : C21Spec := by
  intro L _ N i j hij
  refine ⟨traceCLM i j hij, ?_, ?_, ?_⟩
  · intro ε hε ψ G hG
    have h := trace_estimate i j hij hε ψ
    have hG2 := norm_sq_of_hasWeakPartial hG
    rw [traceCLM_apply, hG2]
    simpa only [freq, coeffFun] using h
  · intro S c t y
    rw [traceCLM_apply]
    exact trace_trigElem i j hij S c t y
  · intro T' h
    exact traceCLM_unique i j hij T' h

end QuantumNLS.C21Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.C21Spec.c21_spec
  IO.println s!"c21_spec axioms: {ax}"
