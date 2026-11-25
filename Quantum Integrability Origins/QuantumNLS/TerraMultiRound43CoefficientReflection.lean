import QuantumNLS.TerraMultiRound41Coefficients
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Reflection of the printed recursive Riccati coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Complex Finset
open scoped ComplexConjugate
namespace QuantumNLS.TerraMultiRound43CoefficientReflection
open QuantumNLS.ClassicalCharges QuantumNLS.TerraMultiRound41Coefficients

/-- Spatial reflection preserves smooth periodicity. -/
theorem smooth_reflect {L : ℝ} {f : ℝ → ℂ} (hf : SmoothPeriodic L f) :
    SmoothPeriodic L (fun t => f (-t)) := by
  refine ⟨hf.smooth.comp contDiff_neg, ?_⟩
  intro t
  have h := hf.periodic (-(t + L))
  have e : -(t + L) + L = -t := by ring
  simpa only [e] using h.symm

/-- The signed recursion changes by `(-1)^(n-1)` under spatial reflection. -/
theorem aseq_reflect {L κ : ℝ} {f : ℝ → ℂ} (hf : SmoothPeriodic L f) :
    ∀ n : ℕ, 1 ≤ n → aseq κ (fun t => f (-t)) n =
      fun t => (-1 : ℂ) ^ (n - 1) * aseq κ f n (-t) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rcases n with _ | n
    · omega
    rcases n with _ | n
    · simp [aseq_one]
    have href := smooth_reflect hf
    rw [aseq_succ κ href n, aseq_succ κ hf n]
    have hprev := ih (n + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hprev
    funext t
    have hdiff : DifferentiableAt ℝ (aseq κ f (n + 1)) (-t) := by
      unfold aseq
      exact (differentiableAt_const _).mul
        ((vseq_regular κ hf (n + 1)).1.differentiable (by simp) _)
    have hd : deriv (aseq κ (fun t => f (-t)) (n + 1)) t =
        -((-1 : ℂ) ^ n * deriv (aseq κ f (n + 1)) (-t)) := by
      rw [hprev]
      change deriv (fun s : ℝ => (-1 : ℂ) ^ n * (aseq κ f (n + 1) ∘ Neg.neg) s) t = _
      rw [deriv_const_mul _ (hdiff.comp t (differentiableAt_id.neg))]
      change (-1 : ℂ) ^ n * deriv (fun s : ℝ => aseq κ f (n + 1) (-s)) t = _
      rw [deriv_comp_neg]
      ring
    rw [hd]
    have hs : (∑ j ∈ Finset.Icc 1 n, aseq κ (fun t => f (-t)) j t *
        aseq κ (fun t => f (-t)) (n + 1 - j) t) =
        (-1 : ℂ) ^ (n - 1) * ∑ j ∈ Finset.Icc 1 n,
          aseq κ f j (-t) * aseq κ f (n + 1 - j) (-t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      rw [ih j (by omega) (by omega), ih (n + 1 - j) (by omega) (by omega)]
      simp only
      have he : j - 1 + (n + 1 - j - 1) = n - 1 := by omega
      calc
        _ = ((-1 : ℂ) ^ (j - 1) * (-1 : ℂ) ^ (n + 1 - j - 1)) *
          (aseq κ f j (-t) * aseq κ f (n + 1 - j) (-t)) := by ring
        _ = _ := by rw [← pow_add, he]
    rw [hs]
    by_cases hn0 : n = 0
    · subst n
      simp
    · simp only [Nat.add_sub_cancel]
      have hp1 : (-1 : ℂ) ^ (n + 1) = -((-1 : ℂ) ^ n) := by
        rw [pow_succ]
        ring
      have hp2 : (-1 : ℂ) ^ n = -((-1 : ℂ) ^ (n - 1)) := by
        have he : n = (n - 1) + 1 := by omega
        conv_lhs => rw [he, pow_succ]
        ring
      rw [hp1, hp2]
      ring

#print axioms smooth_reflect
#print axioms aseq_reflect
end QuantumNLS.TerraMultiRound43CoefficientReflection
