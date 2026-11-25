import QuantumNLS.Ext025BHaar

/-! EXT-025 layer A (part 2), haiku_inventory. Contract GP-15 =
FIN-EXT025-GP-15 (normalized Haar measure and finite-support character
orthogonality on the countable torus), stated at the literal text of
FINAL_EXTERNAL_THEOREM_INSTANCES.json:
  hypotheses: the group is compact Hausdorff, here the countable product of
  circles with the product topology; characters used depend on finitely many
  coordinates;
  conclusion: there is a unique normalized invariant Borel probability measure;
  inversion and continuous group automorphisms preserve it; a nontrivial
  character has integral zero and the trivial character has integral one.
The finite-dependence hypothesis is kept in the statement as written. The proof
uses the frozen Ext025BHaar theorems; the character clause there holds for all
homomorphisms to the circle, so the hypothesis is not needed for it. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure

namespace QuantumNLS.Ext025HGP15

/-- Exact contract GP-15 on G = (ℤ → Circle) with the product topology. -/
theorem contract_GP15 :
    (∃! μ : Measure (ℤ → Circle), IsProbabilityMeasure μ ∧ IsMulLeftInvariant μ) ∧
    (∀ μ : Measure (ℤ → Circle), IsProbabilityMeasure μ → IsMulLeftInvariant μ →
      MeasurePreserving (fun x : ℤ → Circle => x⁻¹) μ μ) ∧
    (∀ μ : Measure (ℤ → Circle), IsProbabilityMeasure μ → IsMulLeftInvariant μ →
      ∀ e : (ℤ → Circle) ≃ₜ* (ℤ → Circle), MeasurePreserving e μ μ) ∧
    (∀ μ : Measure (ℤ → Circle), IsProbabilityMeasure μ → IsMulLeftInvariant μ →
      ∀ χ : (ℤ → Circle) →* Circle,
        (∃ F : Finset ℤ, ∀ x y : ℤ → Circle, (∀ i ∈ F, x i = y i) → χ x = χ y) →
        ((χ = 1 → ∫ x, (χ x : ℂ) ∂μ = 1) ∧ (χ ≠ 1 → ∫ x, (χ x : ℂ) ∂μ = 0))) := by
  have huniq : ∀ μ : Measure (ℤ → Circle), IsProbabilityMeasure μ → IsMulLeftInvariant μ →
      μ = QuantumNLS.Ext025BHaar.normalizedHaar := fun μ h1 h2 =>
    (QuantumNLS.Ext025BHaar.«FIN-EXT025-GP-15» (G := ℤ → Circle)).unique ⟨h1, h2⟩
      ⟨inferInstance, inferInstance⟩
  refine ⟨QuantumNLS.Ext025BHaar.«FIN-EXT025-GP-15» (G := ℤ → Circle), ?_, ?_, ?_⟩
  · intro μ h1 h2
    rw [huniq μ h1 h2]
    exact QuantumNLS.Ext025BHaar.«FIN-EXT025-GP-15-inversion»
  · intro μ h1 h2 e
    rw [huniq μ h1 h2]
    exact QuantumNLS.Ext025BHaar.«FIN-EXT025-GP-15-automorphism» e
  · intro μ h1 h2 χ _hfin
    rw [huniq μ h1 h2]
    have hc := QuantumNLS.Ext025BHaar.«FIN-EXT025-GP-15-character» χ
    constructor
    · intro h
      rw [hc, if_pos h]
    · intro h
      rw [hc, if_neg h]

end QuantumNLS.Ext025HGP15

#print axioms QuantumNLS.Ext025HGP15.contract_GP15
