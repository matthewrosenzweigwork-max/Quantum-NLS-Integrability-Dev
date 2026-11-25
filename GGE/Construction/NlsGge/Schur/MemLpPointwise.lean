import NlsGge.Schur.FreeResolvent

/-!
Explicit function equalities isolate the actual saved Memℓp elaboration failure.
These are prerequisites for the same free weighted domain, not another domain
or a supplied resolvent/weak-derivative hypothesis.
-/

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace NlsGge.Schur

theorem pointwiseSquare_zero_mem (I : Type) :
    Memℓp (fun _ : I => (0 : ℂ)) 2 :=
  zero_mem_ℓp'

theorem pointwiseSquare_add_mem {I : Type} (f g : I → ℂ)
    (hf : Memℓp f 2) (hg : Memℓp g 2) :
    Memℓp (fun i => f i + g i) 2 := by
  have he : f + g = (fun i => f i + g i) := by
    funext i
    rfl
  rw [← he]
  exact hf.add hg

theorem pointwiseSquare_smul_mem {I : Type} (c : ℂ) (f : I → ℂ)
    (hf : Memℓp f 2) : Memℓp (fun i => c * f i) 2 := by
  have he : c • f = (fun i => c * f i) := by
    funext i
    rfl
  rw [← he]
  exact hf.const_smul c

/-- Exactly the source free eigenvalue mπ on both reflected components. -/
def freeWeightedCoordinates (n : ℤ) (x : SectorSquare n) : Bool × Sector n → ℂ :=
  fun i => spectralCenter i.2.val * x i

theorem freeWeightedCoordinates_zero (n : ℤ) :
    freeWeightedCoordinates n 0 = (fun _ : Bool × Sector n => (0 : ℂ)) := by
  funext i
  change spectralCenter i.2.val * (0 : ℂ) = 0
  exact mul_zero _

theorem freeWeightedCoordinates_add (n : ℤ) (x y : SectorSquare n) :
    freeWeightedCoordinates n (x + y) =
      (fun i => freeWeightedCoordinates n x i + freeWeightedCoordinates n y i) := by
  funext i
  change spectralCenter i.2.val * (x i + y i) =
    spectralCenter i.2.val * x i + spectralCenter i.2.val * y i
  exact mul_add _ _ _

theorem freeWeightedCoordinates_smul (n : ℤ) (c : ℂ) (x : SectorSquare n) :
    freeWeightedCoordinates n (c • x) = (fun i => c * freeWeightedCoordinates n x i) := by
  funext i
  change spectralCenter i.2.val * (c * x i) = c * (spectralCenter i.2.val * x i)
  ring

theorem freeWeightedCoordinates_zero_mem (n : ℤ) :
    Memℓp (freeWeightedCoordinates n 0) 2 := by
  rw [freeWeightedCoordinates_zero]
  exact pointwiseSquare_zero_mem (Bool × Sector n)

theorem freeWeightedCoordinates_add_mem (n : ℤ) (x y : SectorSquare n)
    (hx : Memℓp (freeWeightedCoordinates n x) 2)
    (hy : Memℓp (freeWeightedCoordinates n y) 2) :
    Memℓp (freeWeightedCoordinates n (x + y)) 2 := by
  rw [freeWeightedCoordinates_add]
  exact pointwiseSquare_add_mem _ _ hx hy

theorem freeWeightedCoordinates_smul_mem (n : ℤ) (c : ℂ) (x : SectorSquare n)
    (hx : Memℓp (freeWeightedCoordinates n x) 2) :
    Memℓp (freeWeightedCoordinates n (c • x)) 2 := by
  rw [freeWeightedCoordinates_smul]
  exact pointwiseSquare_smul_mem c _ hx

end NlsGge.Schur
