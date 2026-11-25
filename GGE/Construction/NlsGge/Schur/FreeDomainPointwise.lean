import NlsGge.Schur.MemLpPointwise
set_option autoImplicit false
noncomputable section
namespace NlsGge.Schur

def freeWeightedDomainPointwise (n : ℤ) : Submodule ℂ (SectorSquare n) where
  carrier := {x | Memℓp (freeWeightedCoordinates n x) 2}
  zero_mem' := freeWeightedCoordinates_zero_mem n
  add_mem' := by
    intro x y hx hy
    exact freeWeightedCoordinates_add_mem n x y hx hy
  smul_mem' := by
    intro c x hx
    exact freeWeightedCoordinates_smul_mem n c x hx

def freeWeightedDomainInline (n : ℤ) : Submodule ℂ (SectorSquare n) where
  carrier := {x | Memℓp (fun i : Bool × Sector n => spectralCenter i.2.val * x i) 2}
  zero_mem' := by
    exact freeWeightedCoordinates_zero_mem n
  add_mem' := by
    intro x y hx hy
    exact freeWeightedCoordinates_add_mem n x y hx hy
  smul_mem' := by
    intro c x hx
    exact freeWeightedCoordinates_smul_mem n c x hx

theorem freeWeightedDomainPointwise_eq_inline (n : ℤ) :
    freeWeightedDomainPointwise n = freeWeightedDomainInline n := by
  apply Submodule.ext
  intro x
  rfl

theorem freeWeightedDomainInline_mem_iff (n : ℤ) (x : SectorSquare n) :
    x ∈ freeWeightedDomainInline n ↔
      Memℓp (fun i : Bool × Sector n => spectralCenter i.2.val * x i) 2 := Iff.rfl

end NlsGge.Schur
