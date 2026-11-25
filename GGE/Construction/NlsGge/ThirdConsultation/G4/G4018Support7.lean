import Mathlib
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                                                
set_option autoImplicit false

namespace NlsGge.G4018Support

theorem subtype_finset_sum_le {n : ℤ} (F : {m : ℤ // m ≠ n} → ℝ) (hF : Summable F)
    (hnn : ∀ m, 0 ≤ F m) (B : ℝ) (hB : ∑' m, F m ≤ B) (g : ℤ → ℝ)
    (hg : ∀ j, g j = if h : j ≠ n then F ⟨j, h⟩ else 0) (t : Finset ℤ) :
    ∑ j ∈ t, g j ≤ B := by
  have hinj : Function.Injective (Subtype.val : {m : ℤ // m ≠ n} → ℤ) := Subtype.val_injective
  have hsupp : Function.support g ⊆ Set.range (Subtype.val : {m : ℤ // m ≠ n} → ℤ) := by
    intro x hx
    by_contra h
    apply hx
    rw [hg x, dif_neg]
    intro hxn
    exact h ⟨⟨x, hxn⟩, rfl⟩
  have hcomp : Summable (g ∘ (Subtype.val : {m : ℤ // m ≠ n} → ℤ)) := by
    refine hF.congr (fun m => ?_)
    show F m = g m.1
    rw [hg, dif_pos m.2]
  have hsumg : Summable g := by
    refine (hinj.summable_iff ?_).mp hcomp
    intro x hx
    by_contra h
    exact hx (hsupp h)
  have hgnn : ∀ j, 0 ≤ g j := by
    intro j
    rw [hg j]
    split_ifs with h
    · exact hnn _
    · exact le_refl 0
  have htsum : ∑' j, g j = ∑' m : {m : ℤ // m ≠ n}, F m := by
    calc ∑' j, g j = ∑' m : {m : ℤ // m ≠ n}, g m.1 := (hinj.tsum_eq hsupp).symm
      _ = ∑' m : {m : ℤ // m ≠ n}, F m := tsum_congr (fun m => by rw [hg, dif_pos m.2])
  calc ∑ j ∈ t, g j ≤ ∑' j, g j := hsumg.sum_le_tsum t (fun j _ => hgnn j)
    _ = ∑' m : {m : ℤ // m ≠ n}, F m := htsum
    _ ≤ B := hB

end NlsGge.G4018Support
