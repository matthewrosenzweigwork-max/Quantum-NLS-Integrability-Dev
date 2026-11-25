import QuantumNLS.TerraMultiRound86Chart
import QuantumNLS.TerraMultiRound86BoostFrequency

/-! Boost covariance on every summable action vector. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound86BoostActionsAll
open QuantumNLS.TerraMultiRound86Chart
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.GlobalCompatR47a QuantumNLS.L2Flow QuantumNLS.ActionTorus
open QuantumNLS.TerraMultiRound85DynamicsInput QuantumNLS.TerraMultiRound86BoostFrequency
variable {L : ℝ} [Fact (0 < L)] {κ d CL : ℝ} (hκ : 0 < κ)
variable {Φl : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψl : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}
variable {Φ : ℝ → L2T L → QuantumNLS.D01LocalPrimitive.K}
variable {Ψ : ℝ → QuantumNLS.D01LocalPrimitive.K → L2T L}

/-- Every summable action vector has its shifted action vector. -/
theorem boosted_action_exists
    (h : Extension κ hκ d (Φl κ) (Ψl κ) (Φ κ) (Ψ κ))
    (hc : Compatibility d CL Φ Ψ) (a : PosL1) (k : ℤ) :
    ∃ b : PosL1, ∀ n, b.1 n = a.1 (n-k) := by
  let u : L2T L := Ψ κ (sqrtVec a)
  have hu : QuantumNLS.RootIndexedMasses.masses hκ u = a := by
    apply Subtype.ext
    apply lp.ext
    funext j
    rw [← h.moduli, h.right_inv]
    exact sqrtVec_mem a j
  refine ⟨QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.RootMassBoostSymbol.boost k u), ?_⟩
  intro n
  rw [← h.moduli, ((hc.1 κ hκ).1 u n).2.2.1 k, h.moduli, hu]

/-- The same predecessor frequency witness obeys the boost formula on all actions. -/
theorem boost_frequency_all_intermediate
    (h : Extension κ hκ d (Φl κ) (Ψl κ) (Φ κ) (Ψ κ))
    (hc : Compatibility d CL Φ Ψ) :
    ∃ ν : ℤ → PosL1 → ℝ,
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), 0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 n →
        Φ κ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν n (QuantumNLS.RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) * Φ κ u n) ∧
      ∀ (a b : PosL1) (n k : ℤ), (∀ j, b.1 j = a.1 (j-k)) → 0 < a.1 (n-k) →
        ν n b = ν (n-k) a + (QuantumNLS.LocalSpectral.pm L n)^2 -
          (QuantumNLS.LocalSpectral.pm L (n-k))^2 := by
  obtain ⟨ν, hrot, hfreq⟩ := boost_frequency_intermediate hκ h hc
  refine ⟨ν, hrot, ?_⟩
  intro a b n k hb ha
  let u : L2T L := Ψ κ (sqrtVec a)
  have hu : QuantumNLS.RootIndexedMasses.masses hκ u = a := by
    apply Subtype.ext
    apply lp.ext
    funext j
    rw [← h.moduli, h.right_inv]
    exact sqrtVec_mem a j
  have hboost : QuantumNLS.RootIndexedMasses.masses hκ (QuantumNLS.RootMassBoostSymbol.boost k u) = b := by
    apply Subtype.ext
    apply lp.ext
    funext j
    rw [← h.moduli, ((hc.1 κ hκ).1 u j).2.2.1 k, h.moduli, hu, hb j]
  have hactive : 0 < (QuantumNLS.RootIndexedMasses.masses hκ u).1 (n-k) := by rw [hu]; exact ha
  simpa only [hu, hboost] using hfreq u n k hactive

#print axioms boosted_action_exists
#print axioms boost_frequency_all_intermediate
end QuantumNLS.TerraMultiRound86BoostActionsAll
