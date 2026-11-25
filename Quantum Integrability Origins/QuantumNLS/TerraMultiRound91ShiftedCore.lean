import QuantumNLS.TerraMultiRound91Shifted

/-! Dense shifted eigenvector core and exact inner products, a step toward
Parseval in the contact-form norm. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.ContactOperator QuantumNLS.ContactForm
open QuantumNLS.TerraMultiRound90Shifted
namespace QuantumNLS.TerraMultiRound91ShiftedCore
variable {L : ℝ} [Fact (0 < L)] {N : ℕ} {c : ℝ}

/-- A dense form core stays dense under the surjective shifted square root. -/
theorem shifted_core_dense {ι : Type*} (hc : 0 ≤ c) (y : ι → VSym L N)
    (hdense : Dense ((Submodule.span ℂ (Set.range y) : Submodule ℂ (VSym L N)) : Set (VSym L N))) :
    Dense ((Submodule.span ℂ (Set.range (fun i => shiftRoot hc (y i))) :
      Submodule ℂ (VSym L N)) : Set (VSym L N)) := by
  let S : Submodule ℂ (VSym L N) := Submodule.span ℂ (Set.range y)
  let T : VSym L N →L[ℂ] VSym L N := shiftRoot hc
  have hS : DenseRange (fun x : S => (x : VSym L N)) := by
    rw [DenseRange, Subtype.range_coe_subtype]
    exact hdense
  have hT : DenseRange T := (shiftRoot_surjective hc).denseRange
  have hd := hT.comp hS T.continuous
  apply hd.mono
  rintro _ ⟨x, rfl⟩
  have hx : T (x : VSym L N) ∈ Submodule.map T.toLinearMap S := ⟨x, x.property, rfl⟩
  rw [Submodule.map_span] at hx
  have hset : T.toLinearMap '' Set.range y = Set.range (fun i => shiftRoot hc (y i)) := by
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨y i, ⟨i, rfl⟩, rfl⟩
  rw [hset] at hx
  exact hx

/-- The shifted representatives have the diagonal Gram matrix with the
exact eigenvalue weight 1 + e. -/
theorem shifted_core_pairing {ι : Type*} (hc : 0 ≤ c)
    (b : HilbertBasis ι ℂ (SymL2 L N)) (ev : ι → ℝ) (y : ι → VSym L N)
    (hy : ∀ i, valSym (y i) = b i)
    (hpair : ∀ i (z : VSym L N), q c z.1 (y i).1 = (ev i : ℂ) * ⟪valSym z, b i⟫_ℂ)
    (i j : ι) :
    ⟪shiftRoot hc (y i), shiftRoot hc (y j)⟫_ℂ =
      ((ev j + 1 : ℝ) : ℂ) * ⟪b i, b j⟫_ℂ := by
  rw [shifted_pairing hc (y j) (y i) (b j) (ev j) (hy j) (hpair j), hy i]

#print axioms shifted_core_dense
#print axioms shifted_core_pairing
end QuantumNLS.TerraMultiRound91ShiftedCore
