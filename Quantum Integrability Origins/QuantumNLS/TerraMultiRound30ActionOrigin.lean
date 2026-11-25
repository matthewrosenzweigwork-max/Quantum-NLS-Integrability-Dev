import QuantumNLS.TerraMultiRound30HessianBridge

/-! An unconditional first derivative of the actual indexed actions at zero. -/
set_option autoImplicit false
noncomputable section
open Filter Asymptotics
open scoped Topology ENNReal
namespace QuantumNLS.TerraMultiRound30ActionOrigin
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.TerraMultiRound30HessianBridge (Actions)
variable {L κ : ℝ} [Fact (0 < L)]

/-- The actual nonnegative action sequence has norm equal to the total mass. -/
theorem actions_norm (hκ : 0 < κ) (u : L2T L) : ‖Actions hκ u‖ = ‖u‖ ^ 2 := by
  have hn := lp.norm_rpow_eq_tsum (p := (1 : ℝ≥0∞)) (by norm_num) (Actions hκ u)
  have he (n : ℤ) : ‖Actions hκ u n‖ = Actions hκ u n :=
    Real.norm_of_nonneg ((RootIndexedMasses.masses hκ u).2 n)
  have hn' : ‖Actions hκ u‖ = ∑' n, Actions hκ u n := by
    simpa only [ENNReal.toReal_one, Real.rpow_one, he] using hn
  obtain ⟨_, _, _, ht, _⟩ := RootIndexedMasses.root_indexed_masses_proved_clauses hκ u
  exact hn'.trans ht

/-- The action map vanishes at the zero field. -/
theorem actions_zero (hκ : 0 < κ) : Actions (L := L) hκ 0 = 0 := by
  apply norm_eq_zero.mp
  simpa using actions_norm (L := L) hκ 0

/-- The actual sequence-valued action map has zero first Fréchet derivative
at the zero field, with no differentiability assumption. -/
theorem actions_hasFDerivAt_zero (hκ : 0 < κ) :
    HasFDerivAt (Actions (L := L) hκ)
      (0 : L2T L →L[ℝ] lp (fun _ : ℤ => ℝ) 1) 0 := by
  apply hasFDerivAt_iff_isLittleO.mpr
  simp only [actions_zero hκ, sub_zero, zero_apply]
  apply IsLittleO.of_norm_left
  simpa only [actions_norm] using
    (isLittleO_norm_pow_id (E' := L2T L) (n := 2) (by norm_num))

end QuantumNLS.TerraMultiRound30ActionOrigin
#print axioms QuantumNLS.TerraMultiRound30ActionOrigin.actions_norm
#print axioms QuantumNLS.TerraMultiRound30ActionOrigin.actions_zero
#print axioms QuantumNLS.TerraMultiRound30ActionOrigin.actions_hasFDerivAt_zero
