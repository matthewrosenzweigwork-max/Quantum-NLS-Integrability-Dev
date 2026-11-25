import QuantumNLS.RetargetScalarR48b

/-! Integrate each completed seed along its two-label chain. The comparison
of shifts then uses only occupation moduli, in either shift direction. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate Classical

namespace QuantumNLS.DynamicGaugeEdgesR34m
open Occupation OccupationHilbert FullOccupationAffinity FiniteCellGauge
open FiniteCellSupport

variable {N : ℕ}

theorem destination_height (a b : ℤ) (hab : a ≠ b) (d : Donor N a) :
    (destination N a b d).1 a + 1 = d.1.1 a := by
  change shift a b d.1.1 a + 1 = d.1.1 a
  rw [shift_apply]
  have hd := d.2
  change 1 ≤ d.1.1 a at hd
  simp [hab]
  omega

/-- The endpoint has phase one. Each step decreases the donor occupation
by one and leaves the entire exterior array unchanged. -/
def chainGauge (a b : ℤ) (hab : a ≠ b) (c : Donor N a → ℂ) (m : Arr N) : Phase :=
  if hd : DonorOK a m.1 then
    phaseMul (completePhase (c ⟨m, hd⟩))
      (chainGauge a b hab c (destination N a b ⟨m, hd⟩))
  else phaseOne
termination_by m.1 a
decreasing_by
  have h := destination_height a b hab (⟨m, hd⟩ : Donor N a)
  change (destination N a b ⟨m, hd⟩).1 a < m.1 a
  change (destination N a b ⟨m, hd⟩).1 a + 1 = m.1 a at h
  omega

theorem chain_edge (a b : ℤ) (hab : a ≠ b) (c : Donor N a → ℂ) (d : Donor N a) :
    edgePhase (chainGauge a b hab c) a b d = completePhase (c d) := by
  apply Subtype.ext
  change (chainGauge a b hab c d.1).1 *
    conj (chainGauge a b hab c (destination N a b d)).1 = _
  rw [chainGauge, dif_pos d.2]
  change (completePhase (c d)).1 * (chainGauge a b hab c (destination N a b d)).1 *
    conj (chainGauge a b hab c (destination N a b d)).1 = _
  rw [mul_assoc, mul_comm (chainGauge a b hab c (destination N a b d)).1, phase_conj_mul, mul_one]

theorem chain_shift (a b : ℤ) (hab : a ≠ b) (c : Donor N a → ℂ) :
    FiniteCellGauge.W (chainGauge a b hab c) a b = completedSeed a b c := by
  have h : edgePhase (chainGauge a b hab c) a b = fun d => completePhase (c d) :=
    funext (chain_edge a b hab c)
  change transfer a b (edgePhase (chainGauge a b hab c) a b) = _
  rw [h]
  rfl

private theorem difference_eq (q p : Arr N → Phase) (a b : ℤ) (v : H N) :
    FiniteCellGauge.W q a b v - FiniteCellGauge.W p a b v =
      injectL2 (destination N a b) (destination_injective N a b)
        (diagonal (fun d => (edgePhase q a b d).1) 1 zero_le_one
            (fun d => (edgePhase q a b d).2.le) (sourceCoefficients a v) -
          diagonal (fun d => (edgePhase p a b d).1) 1 zero_le_one
            (fun d => (edgePhase p a b d).2.le) (sourceCoefficients a v)) := by
  rw [map_sub]
  rfl

/-- Injectivity of the shift reduces the norm of a difference to an ℓ²
norm over donors, with a multiplier depending only on the two gauges. -/
theorem difference_norm_eq_of_moduli (q p : Arr N → Phase) (a b : ℤ)
    (v x : H N) (h : ∀ m, ‖v m‖ = ‖x m‖) :
    ‖FiniteCellGauge.W q a b v - FiniteCellGauge.W p a b v‖ =
      ‖FiniteCellGauge.W q a b x - FiniteCellGauge.W p a b x‖ := by
  rw [difference_eq, difference_eq, LinearIsometry.norm_map, LinearIsometry.norm_map]
  apply le_antisymm
  · apply lp.norm_mono (by norm_num)
    intro d
    simp only [lp.coeFn_sub, Pi.sub_apply, diagonal_apply, sourceCoefficients, restrictL2_apply,
      ← sub_mul, norm_mul, h]
    exact le_rfl
  · apply lp.norm_mono (by norm_num)
    intro d
    simp only [lp.coeFn_sub, Pi.sub_apply, diagonal_apply, sourceCoefficients, restrictL2_apply,
      ← sub_mul, norm_mul, h]
    exact le_rfl

theorem adjoint_difference_norm_eq_of_moduli (q p : Arr N → Phase) (a b : ℤ)
    (hab : a ≠ b) (v x : H N) (h : ∀ m, ‖v m‖ = ‖x m‖) :
    ‖(FiniteCellGauge.W q a b).adjoint v - (FiniteCellGauge.W p a b).adjoint v‖ =
      ‖(FiniteCellGauge.W q a b).adjoint x - (FiniteCellGauge.W p a b).adjoint x‖ := by
  rw [W_adjoint q a b hab, W_adjoint p a b hab]
  exact difference_norm_eq_of_moduli q p b a v x h

end QuantumNLS.DynamicGaugeEdgesR34m
