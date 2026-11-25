import QuantumNLS.Reg011HForward
import QuantumNLS.Reg011HInverseLow
import QuantumNLS.Reg011HInverseMid
import QuantumNLS.Reg011HInverseUpper
import QuantumNLS.TerraMultiRound80Weighted

/-! REG-011 final (haiku_inventory, module Reg011HFinal), the restricted-lift homeomorphism.

Statement (namespace QuantumNLS.Reg011HFinal, `reg011_final`): for every κ > 0, every V and
every homeomorphism e : L² ≃ₜ V with ExactModuli e, every 0 ≤ s ≤ 2 there is a homeomorphism
F : H^s ≃ₜ (V ∩ h^s) such that the coordinates of F u equal the coordinates of e u:
`toBase s hs0 (F u).1 = (e u.val).val` for all u ∈ H^s.

Forward continuity: `Reg011HForward.restriction_continuous` (REG-010 used directly through
`TerraMultiRound80Weighted.REG010`). Inverse continuity, by the case split
s = 0 (`Reg011HInverseLow.inverse_zero_tendsto`), 0 < s < 1/2 (`inverse_low_tendsto`),
1/2 ≤ s < 1 (`Reg011HInverseMid.inverse_mid_tendsto`), 1 ≤ s ≤ 2
(`Reg011HInverseUpper.inverse_upper_tendsto`).

REG-010 STATUS: the REG-010 chain (TerraMultiRound80Weighted.REG010 and the frozen Reg010Low*
modules) is PENDING REG-010 REVIEW. This module claims no acceptance of REG-010 and no
acceptance of REG-011; every statement here is conditional on that review. Read-only imports
only; no review record unfrozen module is imported. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier
open QuantumNLS.Reg011SettingR48a
namespace QuantumNLS.Reg011HFinal

variable {L κ : ℝ} [Fact (0 < L)] {V : Set Seq}

/-- Inverse continuity along sequences in V ∩ h^s, all orders 0 ≤ s ≤ 2 (case split). -/
theorem inverse_tendsto_all (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ) (s : ℝ)
    (hs0 : 0 ≤ s) (hs2 : s ≤ 2)
    (z : ℕ → h02 L s) (z0 : h02 L s) (hz : Tendsto z atTop (𝓝 z0))
    (hzV : ∀ j, toBase (L := L) s hs0 (z j) ∈ V) (hV0 : toBase (L := L) s hs0 z0 ∈ V) :
    Tendsto (fun j => inverse e hκ he s hs0 hs2 (⟨z j, hzV j⟩ : Target (L := L) V s hs0))
      atTop (𝓝 (inverse e hκ he s hs0 hs2 (⟨z0, hV0⟩ : Target (L := L) V s hs0))) := by
  rcases eq_or_lt_of_le hs0 with h0 | h0
  · subst h0
    exact QuantumNLS.Reg011HInverseLow.inverse_zero_tendsto hκ e he hs2 z z0 hz hzV hV0
  · rcases lt_or_ge s (1/2) with h12 | h12
    · exact QuantumNLS.Reg011HInverseLow.inverse_low_tendsto hκ e he s h0 h12 hs2 z z0 hz hzV hV0
    · rcases lt_or_ge s 1 with h1 | h1
      · exact QuantumNLS.Reg011HInverseMid.inverse_mid_tendsto hκ e he s hs0 h12 h1 hs2 z z0 hz
          hzV hV0
      · exact QuantumNLS.Reg011HInverseUpper.inverse_upper_tendsto hκ e he s hs0 h1 hs2 z z0 hz
          hzV hV0

/-- The inverse map V ∩ h^s → H^s is continuous (sequential criterion). -/
theorem inverse_cont (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ) (s : ℝ)
    (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    Continuous (fun z : QuantumNLS.Reg011HForward.TargetA L V s hs0 =>
      inverse e hκ he s hs0 hs2 z) := by
  refine continuous_iff_seqContinuous.mpr ?_
  intro x a hx
  exact inverse_tendsto_all hκ e he s hs0 hs2 (fun j => (x j).1) a.1
    ((continuous_subtype_val.tendsto a).comp hx) (fun j => (x j).2) a.2

/-- Coordinate-preserving inclusion h^s → ℓ² is injective. -/
theorem toBase_inj (s : ℝ) (hs0 : 0 ≤ s) {a b : h02 L s}
    (h : toBase (L := L) s hs0 a = toBase (L := L) s hs0 b) : a = b := by
  apply PosWeight.WSeq.ext
  funext n
  have h' := congrArg (fun q : Seq => q n) h
  simpa only [toBase_apply] using h'

theorem baseInverse_restriction (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (u : H02 L s) :
    baseInverse e s hs0 (restriction e hκ he s hs0 hs2 u) = u.val := by
  unfold baseInverse
  show e.symm ⟨toBase (L := L) s hs0 (lift e hκ he s hs0 hs2 u),
    (restriction e hκ he s hs0 hs2 u).property⟩ = u.val
  rw [show (⟨toBase (L := L) s hs0 (lift e hκ he s hs0 hs2 u),
      (restriction e hκ he s hs0 hs2 u).property⟩ : V) = e u.val from
    Subtype.ext (toBase_lift e hκ he s hs0 hs2 u), e.symm_apply_apply]

theorem inverse_restriction (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ) (s : ℝ)
    (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (u : H02 L s) :
    inverse e hκ he s hs0 hs2 (restriction e hκ he s hs0 hs2 u) = u := by
  apply WField.ext
  rw [inverse_val e hκ he s hs0 hs2 (restriction e hκ he s hs0 hs2 u)]
  exact baseInverse_restriction hκ e he s hs0 hs2 u

theorem restriction_inverse (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ) (s : ℝ)
    (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (z : QuantumNLS.Reg011HForward.TargetA L V s hs0) :
    restriction e hκ he s hs0 hs2 (inverse e hκ he s hs0 hs2 z) = z := by
  apply Subtype.ext
  apply toBase_inj s hs0
  show toBase (L := L) s hs0 (lift e hκ he s hs0 hs2 (inverse e hκ he s hs0 hs2 z)) =
    toBase (L := L) s hs0 z.1
  rw [toBase_lift, inverse_val e hκ he s hs0 hs2 z]
  unfold baseInverse
  rw [e.apply_symm_apply]

/-- The homeomorphism H^s ≃ₜ (V ∩ h^s) with matching coordinates. -/
theorem final_homeomorph (κ : ℝ) (hκ : 0 < κ) (V : Set Seq) (e : L2T L ≃ₜ V)
    (he : ExactModuli e hκ) (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    ∃ F : H02 L s ≃ₜ QuantumNLS.Reg011HForward.TargetA L V s hs0,
      ∀ u : H02 L s, toBase (L := L) s hs0 (F u).1 = (e u.val).val := by
  refine ⟨{ toFun := fun u => restriction e hκ he s hs0 hs2 u
            invFun := fun z => inverse e hκ he s hs0 hs2 z
            left_inv := fun u => inverse_restriction hκ e he s hs0 hs2 u
            right_inv := fun z => restriction_inverse hκ e he s hs0 hs2 z
            continuous_toFun := QuantumNLS.Reg011HForward.restriction_continuous κ hκ e he s hs0 hs2
            continuous_invFun := inverse_cont hκ e he s hs0 hs2 },
    fun u => toBase_lift e hκ he s hs0 hs2 u⟩

/-- **REG-011 final (restricted lift homeomorphism, coordinates matched).** For every κ > 0, V,
e : L² ≃ₜ V with ExactModuli e, and 0 ≤ s ≤ 2, there is a homeomorphism F : H^s ≃ₜ (V ∩ h^s)
with toBase(F u) = coordinates of e u for all u ∈ H^s. Forward continuity is
`Reg011HForward.restriction_continuous`; inverse continuity is the four-case split (s = 0,
0 < s < 1/2, 1/2 ≤ s < 1, 1 ≤ s ≤ 2). REG-010 PENDING REVIEW (TerraMultiRound80Weighted.REG010
and the frozen Reg010Low chain): no acceptance of REG-010 or REG-011 is claimed. -/
theorem reg011_final : ∀ (κ : ℝ) (hκ : 0 < κ) (V : Set Seq) (e : L2T L ≃ₜ V),
    ExactModuli e hκ → ∀ (s : ℝ) (hs0 : 0 ≤ s), s ≤ 2 →
      ∃ F : H02 L s ≃ₜ QuantumNLS.Reg011HForward.TargetA L V s hs0,
        ∀ u : H02 L s, toBase (L := L) s hs0 (F u).1 = (e u.val).val := by
  intro κ hκ V e he s hs0 hs2
  exact final_homeomorph κ hκ V e he s hs0 hs2

#print axioms inverse_tendsto_all
#print axioms inverse_cont
#print axioms toBase_inj
#print axioms baseInverse_restriction
#print axioms inverse_restriction
#print axioms restriction_inverse
#print axioms final_homeomorph
#print axioms reg011_final
end QuantumNLS.Reg011HFinal
