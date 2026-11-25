import Mathlib
import NlsGge.Atomic.G6.G6016Host
import NlsGge.Atomic.G6.G6016Sup1Core
import NlsGge.Atomic.G6.G6020

/- G6-018 SUPPORT 1 CORE (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6018Sup1Core.lean, namespace NlsGge.GKDefinitionDesign.G6018Aux.
   GK Theorem 20.1 (finite torus changes): (1) `phase_exists`: equal moduli give a = e^{-it} b (polar form; the
   formula needs no division, so zero radii are allowed); (2) `core18`: G6-018 head; the phase t_n is chosen only where
   the coordinates differ, and the isospectral claim follows by Finset induction on the differing coordinates, one
   coordinate rotation at a time (G6-017 head, hypothesis H17 of its exact type, applied at Psi w with Phi(Psi w) = w;
   the RightInverse is the G6-013 conjunct).  Both are discharged in G6018. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
namespace G6018Aux
noncomputable section

theorem phase_exists (a b : ℂ) (h : ‖a‖ ^ 2 = ‖b‖ ^ 2) :
    ∃ t : ℝ, a = Complex.exp (-Complex.I * (t : ℂ)) * b := by
  have hn : ‖a‖ = ‖b‖ := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h
  refine ⟨Complex.arg b - Complex.arg a, ?_⟩
  have ha := Complex.norm_mul_exp_arg_mul_I a
  have hb := Complex.norm_mul_exp_arg_mul_I b
  calc a = (‖a‖ : ℂ) * Complex.exp (Complex.arg a * Complex.I) := ha.symm
    _ = Complex.exp (-Complex.I * ((Complex.arg b - Complex.arg a : ℝ) : ℂ)) *
          ((‖b‖ : ℂ) * Complex.exp (Complex.arg b * Complex.I)) := by
        rw [hn, mul_left_comm, ← Complex.exp_add]
        congr 2
        push_cast
        ring
    _ = _ := by rw [hb]

theorem rotate_apply_ne (a : ℤ) (τ : ℝ) (w : Lib.L2Z) (n : ℤ) (hn : n ≠ a) :
    rotateOneCoordinate a τ w n = w n := by
  unfold rotateOneCoordinate
  rw [lp.coeFn_add, Pi.add_apply, lp.single_apply_ne _ _ _ hn, add_zero]

/-- Core of G6-018; the G6-017 head (H17) and the G6-013 right inverse (hR) enter as hypotheses. -/
theorem core18
    (hR : Function.RightInverse physicalInverseBirkhoff physicalBirkhoff)
    (H17 : ∀ (u : PhysicalL2) (n : ℤ) (t : ℝ),
      let v := physicalInverseBirkhoff (rotateOneCoordinate n t (physicalBirkhoff u))
      (∀ lam : ℂ, discrim (realSlice v) lam = discrim (realSlice u) lam) ∧
      v ∈ isospectralSet u)
    (z w : Lib.L2Z)
    (hrad : ∀ n : ℤ, ‖z n‖^2 = ‖w n‖^2)
    (hfin : {n : ℤ | z n ≠ w n}.Finite) :
  (∃ t : ℤ → ℝ, (Function.support t).Finite ∧
    Function.support t ⊆ {n : ℤ | z n ≠ w n} ∧
    ∀ n : ℤ, z n = Complex.exp (-Complex.I * (t n : ℂ)) * w n) ∧
  physicalInverseBirkhoff z ∈ isospectralSet (physicalInverseBirkhoff w) := by
  classical
  refine ⟨?_, ?_⟩
  · choose τ hτ using fun n => phase_exists (z n) (w n) (hrad n)
    have hsupp : Function.support (fun n : ℤ => if z n ≠ w n then τ n else 0) ⊆
        {n : ℤ | z n ≠ w n} := by
      intro n hn
      by_contra h
      exact hn (if_neg h)
    refine ⟨fun n : ℤ => if z n ≠ w n then τ n else 0, hfin.subset hsupp, hsupp, fun n => ?_⟩
    by_cases h : z n ≠ w n
    · show z n = Complex.exp (-Complex.I * (((if z n ≠ w n then τ n else 0 : ℝ)) : ℂ)) * w n
      rw [if_pos h]
      exact hτ n
    · show z n = Complex.exp (-Complex.I * (((if z n ≠ w n then τ n else 0 : ℝ)) : ℂ)) * w n
      rw [if_neg h]
      push_neg at h
      simp [h]
  · have key : ∀ S : Finset ℤ, ∀ z w : Lib.L2Z, (∀ n : ℤ, ‖z n‖^2 = ‖w n‖^2) →
        (∀ n : ℤ, n ∉ S → z n = w n) → ∀ lam : ℂ,
          discrim (realSlice (physicalInverseBirkhoff z)) lam =
            discrim (realSlice (physicalInverseBirkhoff w)) lam := by
      intro S
      refine Finset.induction_on S ?_ ?_
      · intro z w _ hS lam
        have hzw : z = w := lp.ext (funext fun n => hS n (by simp))
        rw [hzw]
      · intro a S ha ih z w hr hS lam
        obtain ⟨τ, hτ⟩ := phase_exists (z a) (w a) (hr a)
        have hw'a : rotateOneCoordinate a τ w a = z a := by
          rw [G6016Aux.rotate_apply_self, ← hτ]
        have h1 := ih z (rotateOneCoordinate a τ w)
          (fun n => by
            by_cases hna : n = a
            · subst hna
              rw [hw'a]
            · rw [rotate_apply_ne a τ w n hna]
              exact hr n)
          (fun n hn => by
            by_cases hna : n = a
            · subst hna
              exact hw'a.symm
            · rw [rotate_apply_ne a τ w n hna]
              exact hS n (by simp [hna, hn]))
          lam
        have h17 := H17 (physicalInverseBirkhoff w) a τ
        dsimp only at h17
        obtain ⟨h2, -⟩ := h17
        rw [hR w] at h2
        rw [h1]
        exact h2 lam
    exact key hfin.toFinset z w hrad (fun n hn => by simpa using hn)

end
end G6018Aux
end NlsGge.GKDefinitionDesign
