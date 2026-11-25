import QuantumNLS.TerraMultiRound15LocalPartial

/-! LOCAL-013 partial: the chosen products represent the operator products
and have a uniform radius bound. Coefficient limits and symbols are not
asserted here. -/
set_option autoImplicit false
noncomputable section
open QuantumNLS.KernelDefinition QuantumNLS.LocalPlacement QuantumNLS.RadiusBound
open QuantumNLS.KernelConvergence QuantumNLS.PlacementFiberPrefixProductExpansionLOCAL011
namespace QuantumNLS.TerraMultiRound16LocalPartial

/-- The actual chosen product lists represent the operator products and are
uniformly bounded at every radius at least one on which both inputs converge. -/
theorem chosen_products_uniformly_bounded
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : ℝ} (hR : 1 ≤ R)
    {A B : ∀ N : ℕ, KernelList (H := H) N}
    {Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (hA : ConvergesOnRadius R A Alim) (hB : ConvergesOnRadius R B Blim) :
    (∀ N, represented (chosenProductKernelList N (A N) (B N)) =
      (represented (A N)).comp (represented (B N))) ∧
    (∃ C : ℝ, ∀ N, QuantumNLS.RadiusBound.radiusBound R
      (chosenProductKernelList N (A N) (B N)) ≤ C) := by
  obtain ⟨⟨CA, hCA⟩, _⟩ := hA
  obtain ⟨⟨CB, hCB⟩, _⟩ := hB
  have hCA0 : 0 ≤ CA := (QuantumNLS.RadiusBound.radiusBound_nonneg (by linarith) (A 0)).trans (hCA 0)
  refine ⟨fun N => represented_chosenProductKernelList (A N) (B N), ⟨CA * CB, fun N => ?_⟩⟩
  exact (chosenProductKernelList_radius_le hR (A N) (B N)).trans
    (mul_le_mul (hCA N) (hCB N)
      (QuantumNLS.RadiusBound.radiusBound_nonneg (by linarith) (B N)) hCA0)

#print axioms chosen_products_uniformly_bounded
end QuantumNLS.TerraMultiRound16LocalPartial
