import NlsGge.Spectral.ComplexZsLocalPicardAnyInitialSourcePiV4
import NlsGge.Spectral.ComplexZsVacuousDerivativeOutsideClosurePrerequisiteV3
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Interval.Set.LinearOrder

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

open scoped Topology

local instance glueMatrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) :=
  instAnyInitialSourcePiNormedAddCommGroup

local instance glueMatrixNormedSpace :
    NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) :=
  instAnyInitialSourcePiNormedSpace

set_option backward.isDefEq.respectTransparency false in
/-- Join two actual within-derivative solutions at a shared endpoint. -/
theorem hasDerivWithinAt_glue_adjacent_Icc
    (f : ℝ → Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (F G : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hmatch : F b = G b)
    (hF : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt F (f t (F t)) (Set.Icc a b) t)
    (hG : ∀ t ∈ Set.Icc b c,
      HasDerivWithinAt G (f t (G t)) (Set.Icc b c) t) :
    let H : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun t => if t ≤ b then F t else G t
    ∀ t ∈ Set.Icc a c,
      HasDerivWithinAt H (f t (H t)) (Set.Icc a c) t := by
  dsimp
  let H : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun t => if t ≤ b then F t else G t
  have hleft : ∀ t ∈ Set.Icc a b, H t = F t := by
    intro t ht
    simp [H, ht.2]
  have hright : ∀ t ∈ Set.Icc b c, H t = G t := by
    intro t ht
    by_cases htb : t ≤ b
    · have hteq : t = b := le_antisymm htb ht.1
      subst t
      simp [H, hmatch]
    · simp [H, htb]
  have hleftDeriv : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt H (f t (H t)) (Set.Icc a b) t := by
    intro t ht
    have h := (hF t ht).congr (fun x hx => hleft x hx) (hleft t ht)
    simpa [hleft t ht] using h
  have hrightDeriv : ∀ t ∈ Set.Icc b c,
      HasDerivWithinAt H (f t (H t)) (Set.Icc b c) t := by
    intro t ht
    have h := (hG t ht).congr (fun x hx => hright x hx) (hright t ht)
    simpa [hright t ht] using h
  have hrightVacuous : ∀ t, t < b →
      HasDerivWithinAt H (f t (H t)) (Set.Icc b c) t := by
    intro t htb
    have hnotclosure : t ∉ closure (Set.Icc b c) := by
      intro hclosure
      have hne := (mem_closure_iff.mp hclosure) (Set.Iio b) isOpen_Iio htb
      rcases hne with ⟨x, hx⟩
      exact (not_lt_of_ge hx.2.1) hx.1
    exact hasDerivWithinAt_matrix_of_notMem_closure H (f t (H t))
      (Set.Icc b c) t hnotclosure
  have hleftVacuous : ∀ t, b < t →
      HasDerivWithinAt H (f t (H t)) (Set.Icc a b) t := by
    intro t htb
    have hnotclosure : t ∉ closure (Set.Icc a b) := by
      intro hclosure
      have hne := (mem_closure_iff.mp hclosure) (Set.Ioi b) isOpen_Ioi htb
      rcases hne with ⟨x, hx⟩
      exact (not_lt_of_ge hx.2.2) hx.1
    exact hasDerivWithinAt_matrix_of_notMem_closure H (f t (H t))
      (Set.Icc a b) t hnotclosure
  intro t ht
  have hleftAt : HasDerivWithinAt H (f t (H t)) (Set.Icc a b) t := by
    by_cases htb : t ≤ b
    · exact hleftDeriv t ⟨ht.1, htb⟩
    · exact hleftVacuous t (lt_of_not_ge htb)
  have hrightAt : HasDerivWithinAt H (f t (H t)) (Set.Icc b c) t := by
    by_cases htb : b ≤ t
    · exact hrightDeriv t ⟨htb, ht.2⟩
    · exact hrightVacuous t (lt_of_not_ge htb)
  have hUnion := hleftAt.union hrightAt
  simpa [Set.Icc_union_Icc_eq_Icc hab hbc] using hUnion

end NlsGge.SpectralFoundations

end
