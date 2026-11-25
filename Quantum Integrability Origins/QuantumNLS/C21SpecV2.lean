import QuantumNLS.CollisionIdentification

/-! integrator-authored trusted spec v2 for R-C21B75F5 `contact:lem:trace` (A01.tex:13).
Literal reading: target `L²(T_L × T_L^{N-2})` with the coordinate measure `dy_ij` (common
coordinate `t`, spectators), estimate with the genuine weak derivative, agreement with the
pointwise restriction for every smooth lattice-periodic function, and uniqueness of the
continuous extension. -/

open MeasureTheory
open QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.PhysicalTensor
open QuantumNLS.CollisionTrace QuantumNLS.ProductWeakDerivatives QuantumNLS.CollisionIdentification

namespace QuantumNLS.C21SpecV2

def Spec : Prop :=
  ∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (i j : Fin N), i ≠ j →
    ∃ T : PhysH1 L N →L[ℂ]
        Lp ℂ 2 ((volume : Measure (AddCircle L)).prod (Measure.pi fun _ : Rest N i j => volume)),
      (∀ ε : ℝ, 0 < ε → ∀ (ψ : PhysH1 L N) (G : L2TN L N), HasWeakPartial i ψ.val G →
          ‖T ψ‖ ^ 2 ≤ ε * ‖G‖ ^ 2 + (L⁻¹ + ε⁻¹) * ‖ψ.val‖ ^ 2) ∧
      (∀ (φ : (Fin N → ℝ) → ℂ), IsTorusTest L φ → ∀ ψ : PhysH1 L N,
          (ψ.val : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N] liftK (L := L) φ →
          (T ψ : (AddCircle L × (Rest N i j → AddCircle L)) → ℂ)
            =ᵐ[(volume : Measure (AddCircle L)).prod (Measure.pi fun _ : Rest N i j => volume)]
            fun p => liftK (L := L) φ (diagPoint i j p.1 p.2)) ∧
      (∀ T' : PhysH1 L N →L[ℂ]
          Lp ℂ 2 ((volume : Measure (AddCircle L)).prod (Measure.pi fun _ : Rest N i j => volume)),
          (∀ (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ),
            T' (trigElem (L := L) S c) = T (trigElem (L := L) S c)) → T' = T)

theorem spec : Spec := by
  intro L _ N i j hij
  obtain ⟨T, h1, h2, h3⟩ := exists_physical_collision_trace (L := L) i j hij
  refine ⟨T, h1, ?_, h3⟩
  intro φ hφ ψ hψ
  have hv : ψ = smoothH1 hφ := by
    apply PhysH1.val_injective
    rw [smoothH1_val]
    exact Lp.ext (hψ.trans (MemLp.coeFn_toLp _).symm)
  subst hv
  exact h2 φ hφ

end QuantumNLS.C21SpecV2

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.C21SpecV2.spec
  IO.println s!"C21SpecV2.spec axioms: {ax}"
