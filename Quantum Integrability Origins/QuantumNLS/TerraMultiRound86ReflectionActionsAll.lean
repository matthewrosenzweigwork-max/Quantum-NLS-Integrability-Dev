import QuantumNLS.TerraMultiRound86Chart
import QuantumNLS.TerraMultiRound86ReflectionFrequency

/-! Reflection-frequency identity for all action sequences, through the
actual chart inverse and exact reversed coordinates. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound86ReflectionActionsAll
open QuantumNLS.TerraMultiRound86Chart
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.GlobalCompatR47a QuantumNLS.L2Flow QuantumNLS.ActionTorus
open QuantumNLS.TerraMultiRound85DynamicsInput QuantumNLS.TerraMultiRound86ReflectionFrequency
variable {L : ℝ} [Fact (0 < L)] {κ d CL : ℝ} (hκ : 0 < κ)
variable {Φl : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψl : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}
variable {Φ : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψ : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}

/-- Every nonnegative summable action has a reflected action vector. -/
theorem reflected_action_exists
    (h : Extension κ hκ d (Φl κ) (Ψl κ) (Φ κ) (Ψ κ))
    (hc : Compatibility d CL Φ Ψ) (a : PosL1) :
    ∃ b : PosL1, ∀ n, b.1 n = a.1 (-n) := by
  let u : L2T L := Ψ κ (sqrtVec a)
  have hu : QuantumNLS.RootIndexedMasses.masses hκ u = a := by
    apply Subtype.ext
    apply lp.ext
    funext k
    rw [← h.moduli, h.right_inv]
    exact sqrtVec_mem a k
  refine ⟨QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.ResetNormalizationUniqueness.reflectR L u), ?_⟩
  intro n
  rw [← h.moduli, ((hc.1 κ hκ).1 u n).2.2.2.1, h.moduli, hu]

/-- The predecessor's frequency witness obeys the reflected-frequency
formula for every action vector, where `b` is exactly its index reversal. -/
theorem reflection_frequency_all_intermediate
    (h : Extension κ hκ d (Φl κ) (Ψl κ) (Φ κ) (Ψ κ))
    (hc : Compatibility d CL Φ Ψ) :
    ∃ ν : ℤ → PosL1 → ℝ,
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), 0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 n →
        Φ κ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν n (QuantumNLS.RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) * Φ κ u n) ∧
      ∀ (a b : PosL1) (n : ℤ), (∀ k, b.1 k = a.1 (-k)) → 0 < a.1 (-n) →
        ν n b = ν (-n) a := by
  obtain ⟨ν, hrot, hfreq⟩ := reflection_frequency_intermediate hκ h hc
  refine ⟨ν, hrot, ?_⟩
  intro a b n hb ha
  let u : L2T L := Ψ κ (sqrtVec a)
  have hu : QuantumNLS.RootIndexedMasses.masses hκ u = a := by
    apply Subtype.ext
    apply lp.ext
    funext k
    rw [← h.moduli, h.right_inv]
    exact sqrtVec_mem a k
  have hr : QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) = b := by
    apply Subtype.ext
    apply lp.ext
    funext k
    rw [← h.moduli, ((hc.1 κ hκ).1 u k).2.2.2.1, h.moduli, hu, hb k]
  have hactive : 0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 (-n) := by rw [hu]; exact ha
  simpa only [hu, hr] using hfreq u n hactive

#print axioms reflected_action_exists
#print axioms reflection_frequency_all_intermediate
end QuantumNLS.TerraMultiRound86ReflectionActionsAll
