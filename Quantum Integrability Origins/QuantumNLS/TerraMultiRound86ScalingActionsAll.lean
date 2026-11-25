import QuantumNLS.TerraMultiRound86Chart
import QuantumNLS.TerraMultiRound86FrequencyScaling

/-! The printed scaling-frequency identity on arbitrary nonnegative ℓ¹
sequences, using the actual chart inverse for action realizability. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound86ScalingActionsAll
open QuantumNLS.TerraMultiRound86Chart
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.GlobalCompatR47a QuantumNLS.L2Flow QuantumNLS.ActionTorus
open QuantumNLS.TerraMultiRound85DynamicsInput QuantumNLS.TerraMultiRound86FrequencyScaling
variable {L : ℝ} [Fact (0 < L)] {κ d CL : ℝ} (hκ : 0 < κ)
variable {Φl : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψl : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}
variable {Φ : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψ : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}

/-- Pointwise multiplication of a nonnegative summable action by `s²`. -/
def scaleAction (s : ℝ) (a : PosL1) : PosL1 :=
  ⟨s^2 • a.1, fun n => by
    change 0 ≤ s^2 * a.1 n
    exact mul_nonneg (sq_nonneg s) (a.2 n)⟩

/-- The same frequencies appearing in the dynamics input obey the printed
scaling relation for every nonnegative summable action and active index. -/
theorem frequency_scaling_all_intermediate (s : ℝ) (hs : 0 < s)
    (h : Extension κ hκ d (Φl κ) (Ψl κ) (Φ κ) (Ψ κ))
    (hscaled : Extension (κ*s^2) (mul_pos hκ (sq_pos_of_pos hs)) d
      (Φl (κ*s^2)) (Ψl (κ*s^2)) (Φ (κ*s^2)) (Ψ (κ*s^2)))
    (hc : Compatibility d CL Φ Ψ) :
    ∃ ν ν' : ℤ → PosL1 → ℝ,
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), 0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 n →
        Φ κ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν n (QuantumNLS.RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) * Φ κ u n) ∧
      (∀ (u : L2T L) (t : ℝ) (n : ℤ),
        0 < (QuantumNLS.RootIndexedMasses.masses (mul_pos hκ (sq_pos_of_pos hs)) u).1 n →
        Φ (κ*s^2) (flowMap (mul_pos hκ (sq_pos_of_pos hs)).le u t) n =
          Complex.exp (-Complex.I * ((t * ν' n (QuantumNLS.RootIndexedMasses.masses (mul_pos hκ (sq_pos_of_pos hs)) u) : ℝ) : ℂ)) * Φ (κ*s^2) u n) ∧
      ∀ (a : PosL1) (n : ℤ), 0 < a.1 n → ν n (scaleAction s a) = ν' n a := by
  obtain ⟨ν, ν', hrot, hrot', hfreq⟩ := frequency_scaling_intermediate hκ s hs h hscaled hc
  refine ⟨ν, ν', hrot, hrot', ?_⟩
  intro a n ha
  let u : L2T L := Ψ (κ*s^2) (sqrtVec a)
  have hu : QuantumNLS.RootIndexedMasses.masses (mul_pos hκ (sq_pos_of_pos hs)) u = a := by
    apply Subtype.ext
    apply lp.ext
    funext k
    rw [← hscaled.moduli, hscaled.right_inv]
    exact sqrtVec_mem a k
  have hsu : QuantumNLS.RootIndexedMasses.masses hκ (s • u) = scaleAction s a := by
    apply Subtype.ext
    apply lp.ext
    funext k
    change (QuantumNLS.RootIndexedMasses.masses hκ (s • u)).1 k = s^2 * a.1 k
    rw [← h.moduli]
    have he := congrArg (fun z : QuantumNLS.D01LocalPrimitive.K => z k) (hc.2.1 κ hκ s hs u)
    rw [he]
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow, hscaled.moduli, hu]
  have hactive : 0 < (QuantumNLS.RootIndexedMasses.masses (mul_pos hκ (sq_pos_of_pos hs)) u).1 n := by rw [hu]; exact ha
  simpa only [hu, hsu] using hfreq u n hactive

#print axioms frequency_scaling_all_intermediate
end QuantumNLS.TerraMultiRound86ScalingActionsAll
