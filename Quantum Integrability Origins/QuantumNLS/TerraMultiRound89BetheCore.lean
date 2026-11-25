import QuantumNLS.TerraMultiRound89EigenForm

/-! The resolvent representatives of a complete nonnegative-energy eigenbasis
form a core for the physical contact form. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.ContactOperator QuantumNLS.ContactForm
namespace QuantumNLS.TerraMultiRound89BetheCore
variable {L : ℝ} [Fact (0 < L)] {N : ℕ} {c : ℝ}

/-- The actual eigenvector form representatives are form-dense. -/
theorem eigenbasis_form_core {ι : Type*} (hc : 0 ≤ c)
    (b : HilbertBasis ι ℂ (SymL2 L N)) (ev : ι → ℝ) (hev : ∀ i, 0 ≤ ev i)
    (hmem : ∀ i, b i ∈ (Hop (L := L) (N := N) c hc).domain)
    (heig : ∀ i, Hop c hc ⟨b i, hmem i⟩ = (ev i : ℂ) • b i) :
    let y := fun i => psi c hc (((ev i + 1 : ℝ) : ℂ) • b i)
    Dense ((Submodule.span ℂ (Set.range y) : Submodule ℂ (VSym L N)) : Set (VSym L N)) ∧
      (∀ i, valSym (y i) = b i) ∧
      (∀ i (z : VSym L N), q c z.1 (y i).1 = (ev i : ℂ) * ⟪valSym z, b i⟫_ℂ) := by
  let y := fun i => psi c hc (((ev i + 1 : ℝ) : ℂ) • b i)
  have hspan : Submodule.span ℂ (Set.range (fun i => psi c hc (b i))) ≤
      Submodule.span ℂ (Set.range y) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hz : (((ev i + 1 : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (ne_of_gt (by linarith [hev i] : 0 < ev i + 1))
    have hs : y i = (((ev i + 1 : ℝ) : ℂ)) • psi c hc (b i) := by
      simp [y, psi, map_smul]
    have hy : y i ∈ Submodule.span ℂ (Set.range y) := Submodule.subset_span ⟨i, rfl⟩
    have hh := (Submodule.span ℂ (Set.range y)).smul_mem (((ev i + 1 : ℝ) : ℂ)⁻¹) hy
    change psi c hc (b i) ∈ Submodule.span ℂ (Set.range y)
    simpa only [hs, smul_smul, inv_mul_cancel₀ hz, one_smul] using hh
  refine ⟨(TerraMultiRound89FormCore.psi_basis_form_core hc b).mono hspan, ?_, ?_⟩
  · intro i
    exact (TerraMultiRound89EigenForm.eigen_resolvent_form hc (b i) (hmem i) (ev i) (heig i)).1
  · intro i z
    exact (TerraMultiRound89EigenForm.eigen_resolvent_form hc (b i) (hmem i) (ev i) (heig i)).2 z

#print axioms eigenbasis_form_core
end QuantumNLS.TerraMultiRound89BetheCore
