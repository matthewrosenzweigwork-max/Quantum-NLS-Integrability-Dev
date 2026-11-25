import QuantumNLS.TerraMultiRound91NormalizedCore

/-! Completeness of the normalized shifted form core. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.ContactOperator QuantumNLS.ContactForm
open QuantumNLS.TerraMultiRound90Shifted QuantumNLS.TerraMultiRound91ShiftedCore
open QuantumNLS.TerraMultiRound91NormalizedCore
namespace QuantumNLS.TerraMultiRound91ShiftBasis
variable {L : ℝ} [Fact (0 < L)] {N : ℕ} {c : ℝ}

theorem normalized_core_dense {ι : Type*} (hc : 0 ≤ c) (ev : ι → ℝ) (hev : ∀ i, 0 ≤ ev i)
    (y : ι → VSym L N)
    (hdense : Dense ((Submodule.span ℂ (Set.range y) : Submodule ℂ (VSym L N)) : Set (VSym L N))) :
    Dense ((Submodule.span ℂ (Set.range (normalizedCore hc ev y)) :
      Submodule ℂ (VSym L N)) : Set (VSym L N)) := by
  let S : Submodule ℂ (VSym L N) := Submodule.span ℂ (Set.range (normalizedCore hc ev y))
  have hspan : Submodule.span ℂ (Set.range (fun i => shiftRoot hc (y i))) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change shiftRoot hc (y i) ∈ S
    have hp : 0 < ev i + 1 := by linarith [hev i]
    have hs : Real.sqrt (ev i + 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
    have hmem : normalizedCore hc ev y i ∈ S := Submodule.subset_span ⟨i, rfl⟩
    have hm := S.smul_mem ((Real.sqrt (ev i + 1) : ℝ) : ℂ) hmem
    simpa only [normalizedCore, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs,
      Complex.ofReal_one, one_smul] using hm
  exact (shifted_core_dense hc y hdense).mono hspan

/-- The normalized shifted representatives form a complete Hilbert basis. -/
theorem normalized_core_basis {ι : Type*} (hc : 0 ≤ c)
    (b : HilbertBasis ι ℂ (SymL2 L N)) (ev : ι → ℝ) (hev : ∀ i, 0 ≤ ev i)
    (y : ι → VSym L N) (hy : ∀ i, valSym (y i) = b i)
    (hpair : ∀ i (z : VSym L N), q c z.1 (y i).1 = (ev i : ℂ) * ⟪valSym z, b i⟫_ℂ)
    (hdense : Dense ((Submodule.span ℂ (Set.range y) : Submodule ℂ (VSym L N)) : Set (VSym L N))) :
    ∃ a : HilbertBasis ι ℂ (VSym L N), ∀ i, a i = normalizedCore hc ev y i := by
  have ho := normalized_orthonormal hc b ev hev y hy hpair
  have hd := normalized_core_dense hc ev hev y hdense
  have hc' : ⊤ ≤ (Submodule.span ℂ (Set.range (normalizedCore hc ev y))).topologicalClosure := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top.mp hd]
  refine ⟨HilbertBasis.mk ho hc', ?_⟩
  exact fun i => congrFun (HilbertBasis.coe_mk ho hc') i

#print axioms normalized_core_dense
#print axioms normalized_core_basis
end QuantumNLS.TerraMultiRound91ShiftBasis
