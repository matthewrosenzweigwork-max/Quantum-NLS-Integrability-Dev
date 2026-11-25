import QuantumNLS.ContactOperator
import QuantumNLS.Ext025LGP07Polar

/-! Density of the variational-resolvent representatives in the actual
symmetric H¹ form space. This is an intermediate form-core step. -/
set_option autoImplicit false
noncomputable section
open QuantumNLS.ContactOperator QuantumNLS.PhysicalEnergy
namespace QuantumNLS.TerraMultiRound89FormCore
variable {L : ℝ} [Fact (0 < L)] {N : ℕ} {c : ℝ}

theorem valSym_injective : Function.Injective (valSym : VSym L N →L[ℂ] SymL2 L N) := by
  intro x y h
  apply Subtype.ext
  apply PhysH1.val_injective
  have hval := congrArg (fun z : SymL2 L N => z.val) h
  exact hval

/-- The variational resolvent images are dense in the physical form space.
No spectral theorem or product operator-domain membership is assumed. -/
theorem psi_dense (hc : 0 ≤ c) : DenseRange (psi (L := L) (N := N) c hc) := by
  have hG : DenseRange (Gop : SymL2 L N →L[ℂ] VSym L N) :=
    Ext025L.Polar.adjoint_denseRange (valSym : VSym L N →L[ℂ] SymL2 L N) valSym_injective
  have hM : Function.Surjective (Minv (L := L) (N := N) c hc) := by
    intro x
    exact ⟨Mop c hc x, Minv_Mop hc x⟩
  exact hM.denseRange.comp hG (Minv c hc).continuous

/-- Applying the variational resolvent to any complete ambient Hilbert
basis gives a form-dense linear span. -/
theorem psi_basis_form_core {ι : Type*} (hc : 0 ≤ c)
    (b : HilbertBasis ι ℂ (SymL2 L N)) :
    Dense ((Submodule.span ℂ (Set.range (fun i => psi c hc (b i))) :
      Submodule ℂ (VSym L N)) : Set (VSym L N)) := by
  let S : Submodule ℂ (SymL2 L N) := Submodule.span ℂ (Set.range b)
  let T : SymL2 L N →L[ℂ] VSym L N := (Minv c hc).comp Gop
  have hS : DenseRange (fun x : S => (x : SymL2 L N)) := by
    rw [DenseRange, Subtype.range_coe_subtype]
    exact Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span
  have hT : DenseRange T := psi_dense hc
  have hd := hT.comp hS T.continuous
  apply hd.mono
  rintro _ ⟨x, rfl⟩
  have hx : T (x : SymL2 L N) ∈ Submodule.map T.toLinearMap S := ⟨x, x.property, rfl⟩
  rw [Submodule.map_span] at hx
  have hset : T.toLinearMap '' Set.range b = Set.range (fun i => psi c hc (b i)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨b i, ⟨i, rfl⟩, rfl⟩
  rw [hset] at hx
  exact hx

#print axioms valSym_injective
#print axioms psi_dense
#print axioms psi_basis_form_core
end QuantumNLS.TerraMultiRound89FormCore
