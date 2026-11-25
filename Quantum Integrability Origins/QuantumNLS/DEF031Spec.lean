import QuantumNLS.EnergyPreparationDef

/-! integrator-authored trusted spec for DEF-031 (definitions.tex:187-189), following Terra's
reviewer-owned gate specification (review records/terra_review-def031-trusted-spec.md, items 1, 2, 4;
item 3 is an application bridge per Terra R50). Energy preparation: norm-close normalized ψ_N in the
DEF-004 sector whose wave function is in H¹_sym with limsup_N h_N[ψ_N]/N ≤ I₃(u) (EReal), h_N the
closed contact form with coefficient 2κ/N and coordinate diagonal measure, I₃(u) = ‖u'‖² + κ∫|u|⁴.
A_k = 1 − Σ∂² self-adjoint on the k-particle carrier. Additive energy trace norm via the
trace-class form realization: T realizes A_k^{1/2} D A_k^{1/2} on the whole form domain; it is unique,
characterized by D = W T W, exists trace-class iff the norm is finite (no extra hypothesis on summands),
and for positive finite-energy ρ it exists, is positive trace class, with trace and norm = Tr(A_k ρ). -/

open scoped InnerProductSpace ENNReal
open MeasureTheory Filter Topology
open QuantumNLS.PhysicalEnergy QuantumNLS.PhysicalTensor QuantumNLS.EnergyPreparationDef
open QuantumNLS.TensorCarrier QuantumNLS.Energy

noncomputable section

namespace QuantumNLS.DEF031Spec

def Spec : Prop :=
  ∀ (L : ℝ) [Fact (0 < L)],
    -- (4) preparation predicate, literally
    (∀ (κ : ℝ) (u : L2T L) (ψ : ∀ N : ℕ, HilbertTensorPower ℂ (L2T L) N),
      EnergyPreparation κ u ψ ↔
        ((∀ N, ‖ψ N‖ = 1) ∧
          Tendsto (fun N => ‖ψ N - (htpow N u : HilbertTensorPower ℂ (L2T L) N)‖) atTop (𝓝 0)) ∧
        (∀ N, ψ N ∈ physSector L N) ∧
        ∃ x : ∀ N, PhysH1 L N, (∀ N, (x N).val = physUnitary (ψ N)) ∧
          (∀ N, x N ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N))) ∧
          limsup (fun N : ℕ => ((QuantumNLS.ProductEnergyPreparation.hN κ N (x N) / N : ℝ) : EReal))
            atTop ≤ ((I3 κ u : ℝ) : EReal)) ∧
    -- h_N literal: genuine weak gradients and the 2κ/N physical collision pairings
    (∀ (κ : ℝ) (N : ℕ) (x : PhysH1 L N),
      QuantumNLS.ProductEnergyPreparation.hN κ N x =
        ∑ j, ‖QuantumNLS.CollisionIdentification.gradientCLM j x‖ ^ 2 +
          2 * (κ / N) * ∑ p : QuantumNLS.ContactForm.Pair N,
            ‖QuantumNLS.CollisionIdentification.productTrace p.1.1 p.1.2 (ne_of_lt p.2) x‖ ^ 2) ∧
    -- I₃ literal with the weak derivative
    (∀ (κ : ℝ) (u g : L2T L), QuantumNLS.WeakDerivatives.HasWeakDeriv u g →
      I3 κ u = ‖g‖ ^ 2 + κ * ∫ x, ‖(u : AddCircle L → ℂ) x‖ ^ 4) ∧
    -- (1) A_k self-adjoint
    (∀ k : ℕ, IsSelfAdjoint (AkT L k) ∧ IsSelfAdjoint (AhalfT L k)) ∧
    -- (2) form realization: characterization, uniqueness, exact existence domain, positive case
    (∀ (k : ℕ) (D T : Xk L k →L[ℂ] Xk L k),
      (IsFormRealization D T ↔ D = W L k * T * W L k)) ∧
    (∀ (k : ℕ) (D T₁ T₂ : Xk L k →L[ℂ] Xk L k),
      IsFormRealization D T₁ → IsFormRealization D T₂ → T₁ = T₂) ∧
    (∀ (k : ℕ) (D : Xk L k →L[ℂ] Xk L k),
      (∃ T, QuantumNLS.TraceClass.IsTraceClass T ∧ IsFormRealization D T) ↔
        additiveEnergyTraceNorm D < ⊤) ∧
    (∀ (k : ℕ) (ρ : Xk L k →L[ℂ] Xk L k), ρ.IsPositive → energyTrace ρ ≠ ⊤ →
      ∃ T, T.IsPositive ∧ QuantumNLS.TraceClass.IsTraceClass T ∧ IsFormRealization ρ T ∧
        QuantumNLS.TraceClass.posTrace T = energyTrace ρ ∧
        additiveEnergyTraceNorm ρ = energyTrace ρ)

theorem spec : Spec := by
  intro L _
  refine ⟨fun κ u ψ => ?_, fun κ N x => (hN_literal κ x).1, fun κ u g h => I3_eq h,
    fun k => ⟨AkT_isSelfAdjoint, AhalfT_isSelfAdjoint⟩, fun k D T => isFormRealization_iff D T,
    fun k D T₁ T₂ h₁ h₂ => formRealization_unique h₁ h₂,
    fun k D => exists_traceClass_formRealization_iff D,
    fun k ρ hρ hE => positive_formRealization hρ hE⟩
  constructor
  · rintro ⟨⟨hn, hc⟩, hs, he⟩; exact ⟨⟨hn, hc⟩, hs, he⟩
  · rintro ⟨⟨hn, hc⟩, hs, he⟩; exact ⟨⟨hn, hc⟩, hs, he⟩

end QuantumNLS.DEF031Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.DEF031Spec.spec
  IO.println s!"DEF031Spec.spec axioms: {ax}"
