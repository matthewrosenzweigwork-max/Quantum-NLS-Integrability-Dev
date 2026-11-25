import QuantumNLS.BetheFreeFamily

/-! integrator-authored trusted spec for R-7597E2D2 `basis:lem:independence`
(periodic_basis.tex:265-276). For L > 0 and N+1 ≥ 1 particles, over ALL antitone integer labels n
(repeated entries allowed): for c > 0 the actual unnormalized symmetric Bethe waves ψ_{n,c}
(`BetheH1.waveH1`, the H¹ class of the literal extension, Terra R24) are nonzero and linearly
independent; for each n, the map c ↦ ψ_{n,c} (c > 0), ψ_{n,0} := free vector, is norm continuous on
[0,∞), with ψ_{n,0} = Σ_σ exp((2πi/L)⟨σn, x⟩) almost everywhere; and the free vectors are nonzero,
pairwise orthogonal for distinct labels, with dense span in the symmetric L² space H_N. -/

open Filter Topology MeasureTheory Set
open scoped InnerProductSpace
open QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy QuantumNLS.BetheWaveContinuity
open QuantumNLS.BetheFreeFamily

namespace QuantumNLS.R7597Spec

def Spec : Prop :=
  ∀ (L : ℝ) [Fact (0 < L)] (N : ℕ),
    -- c > 0: nonzero and linearly independent
    (∀ c : ℝ, ∀ hc : 0 < c,
      (∀ n : Label (N+1), (BetheH1.waveH1 (L := L) hc n.property).val ≠ 0) ∧
      LinearIndependent ℂ (fun n : Label (N+1) => (BetheH1.waveH1 (L := L) hc n.property).val)) ∧
    -- the extended family: equals the Bethe wave for c > 0, the free vector at c = 0
    (∀ n : Label (N+1),
      (∀ c : ℝ, ∀ hc : 0 < c,
        continuedWave (L := L) n.val n.property c = (BetheH1.waveH1 (L := L) hc n.property).val) ∧
      continuedWave (L := L) n.val n.property 0 = freeVector L n.val ∧
      ContinuousOn (continuedWave (L := L) n.val n.property) (Ici 0)) ∧
    -- literal free formula (permutation sum, multiplicities retained)
    (∀ n : Fin (N+1) → ℤ,
      (freeVector L n : (Fin (N+1) → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L (N+1)]
        (fun x => ∑ σ : Equiv.Perm (Fin (N+1)),
          Complex.exp (Complex.I * ((∑ j, (2 * Real.pi / L * (n (σ j) : ℝ)) *
            QuantumNLS.BetheWeakGradient.representatives L x j : ℝ) : ℂ)))) ∧
    -- free family: nonzero, orthogonal, complete in H_N (symmetric L²)
    (∀ n : Label (N+1), ((freeSym (L := L) n : ContactOperator.SymL2 L (N+1)) : L2TN L (N+1)) =
        freeVector L n.val) ∧
    (∀ n : Label (N+1), freeSym (L := L) n ≠ 0) ∧
    (∀ n m : Label (N+1), n ≠ m → ⟪freeSym (L := L) n, freeSym (L := L) m⟫_ℂ = 0) ∧
    (Submodule.span ℂ (Set.range (freeSym (L := L) :
        Label (N+1) → ContactOperator.SymL2 L (N+1)))).topologicalClosure = ⊤

theorem spec : Spec := by
  intro L _ N
  obtain ⟨h1, h2, h3, h4, h5⟩ := independence_and_free_limit (L := L) (N := N)
  refine ⟨h1, fun n => ⟨fun c hc => continuedWave_pos n.property hc, (h2 n).2.1, (h2 n).1⟩,
    fun n => coe_freeVector n, fun n => rfl, h3, h4, h5⟩

end QuantumNLS.R7597Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R7597Spec.spec
  IO.println s!"R7597Spec.spec axioms: {ax}"
