import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Tactic

/-!
Uncompiled generic polarization helper. This is the source packet's
polarization/coefficient-extraction step, realized through the exact n-th
Fréchet derivative formula already proved in pinned Mathlib. No Fock or
totality assertion is assumed.
-/

noncomputable section
open scoped BigOperators

namespace LiebLiniger.FixedPeriod.Quantum

/-- A symmetric continuous complex n-linear map is determined by its diagonal.
The proof includes the zero-argument case n=0. -/
theorem continuousMultilinearMap_eq_zero_of_diagonal
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {n : ℕ}
    (f : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E),
      f (fun i => v (σ i)) = f v)
    (hdiag : ∀ x : E, f (fun _ : Fin n => x) = 0) : f = 0 := by
  classical
  ext v
  have hf : (fun x : E => f (fun _ : Fin n => x)) = 0 := by
    funext x
    exact hdiag x
  have hp := f.iteratedFDeriv_comp_diagonal (0 : E) v
  rw [hf, iteratedFDeriv_zero] at hp
  simp only [Pi.zero_apply, ContinuousMultilinearMap.zero_apply] at hp
  have hsum : (∑ σ : Equiv.Perm (Fin n), f (fun i => v (σ i))) =
      (n.factorial : ℂ) • f v := by
    simp only [hsym, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
  rw [hsum] at hp
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  exact (smul_eq_zero.mp hp.symm).resolve_left hn

end LiebLiniger.FixedPeriod.Quantum
