import Mathlib
import QuantumNLS.Local003Analytic
import QuantumNLS.Local002Bridge

/-! LOCAL-003 `thm:reset-uniform-reduction`, stage S4: parity in `u` of the reduced-matrix entries.

Source (proof): "Conjugation by `J` sends `𝓛_u` to `𝓛_{-u}` ... Consequently `b_n` is odd in `u`, whereas `a_n` is even."
From Terra r26/r27 (read-only) `reducedMatrix_parity_on_ball : fiberParity ∘ B(u) = B(-u) ∘ fiberParity` on the common ball,
`fiberParity = diag(1,-1)`.  `Bf_congr` transports the pointwise potential `t ↦ -u t` to the `L²`-class `-u`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local003Odd
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.LocalSpectral.Round26 QuantumNLS.LocalSpectral.Round27
  QuantumNLS.Local003Analytic

variable {L κ r : ℝ}

/-- `Bf` depends on the potential only through its a.e.-class. -/
lemma Bf_congr {u u' : ℝ → ℂ} (h : u =ᵐ[μI L] u') (n : ℤ) (r : ℝ) :
    Bf L κ u n r = Bf L κ u' n r := by
  have h1 : perturbedProj L κ u n r = perturbedProj L κ u' n r :=
    QuantumNLS.Local002Bridge.perturbedProj_congr h n r
  have h2 : dressedIntegral L κ u n r = dressedIntegral L κ u' n r := by
    unfold dressedIntegral
    simp only [QuantumNLS.Local002Bridge.resolvent_congr h]
  unfold Bf Uf compressionMatrix
  rw [h1, h2]

theorem entries_parity (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hu : ‖u‖ < compressionRadius κ L r) :
    Bf L κ ((-u : Lp ℂ 2 (μI L)) : ℝ → ℂ) n r (vec2 1 0) 0 = Bf L κ (u : ℝ → ℂ) n r (vec2 1 0) 0 ∧
    Bf L κ ((-u : Lp ℂ 2 (μI L)) : ℝ → ℂ) n r (vec2 1 0) 1 = -Bf L κ (u : ℝ → ℂ) n r (vec2 1 0) 1 := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  have hsc := reducedMatrix_parity_on_ball hL hyp hr hr2 u hu n
  simp only at hsc
  have hneg : (fun t => -(u : ℝ → ℂ) t) =ᵐ[μI L] ((-u : Lp ℂ 2 (μI L)) : ℝ → ℂ) :=
    (Lp.coeFn_neg u).symm
  have e := congrArg (fun T : E2 →L[ℂ] E2 => T (vec2 1 0)) hsc.eq
  simp only [ContinuousLinearMap.mul_apply] at e
  rw [reducedMatrix2_eq, reducedMatrix2_eq, Bf_congr hneg] at e
  have hfp : ∀ v : E2, fiberParity v = Jm v := fun v => rfl
  have he0 : fiberParity (vec2 1 0) = vec2 1 0 := by
    rw [hfp]; ext i; fin_cases i <;> simp [Jm, vec2]
  rw [he0] at e
  rw [hfp] at e
  constructor
  · have := congrArg (fun w : E2 => w 0) e
    simpa [Jm, vec2] using this.symm
  · have := congrArg (fun w : E2 => w 1) e
    simpa [Jm, vec2] using this.symm

end QuantumNLS.Local003Odd
#print axioms QuantumNLS.Local003Odd.Bf_congr
#print axioms QuantumNLS.Local003Odd.entries_parity
