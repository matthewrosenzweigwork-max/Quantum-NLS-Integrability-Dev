import QuantumNLS.Reg011SettingR48a
import QuantumNLS.Reg011SequencesR48a
import QuantumNLS.TerraMultiRound80Weighted

/-! REG-011 forward continuity (haiku_inventory, module Reg011HForward).
Read-only imports: the frozen `Reg011SettingR48a` (lift, restriction, toBase, ExactModuli),
the frozen `Reg011SequencesR48a` (coordinate/moduli convergence in weighted h^s), and the
authored `TerraMultiRound80Weighted.REG010` used directly. No REG-010 input hypothesis. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier
open QuantumNLS.Reg011SettingR48a
namespace QuantumNLS.Reg011HForward

variable {L : ℝ} [Fact (0 < L)] {V : Set Seq}

/-- V ∩ h^s with the subspace h^s topology. `abbrev` so the subtype topology instance is
found; definitionally equal to `Target`. -/
abbrev TargetA (L : ℝ) [Fact (0 < L)] (V : Set Seq) (s : ℝ) (hs : 0 ≤ s) : Type :=
  {z : h02 L s // toBase (L := L) s hs z ∈ V}

/-- Weighted moduli differences equal the weighted ℓ¹ distance of the REG-010 actions. -/
theorem moduli_sum_eq (κ : ℝ) (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (u v : H02 L s) :
    ∑' n : ℤ, (def002 L s).w n *
        |‖(lift e hκ he s hs0 hs2 u).val n‖ ^ 2 - ‖(lift e hκ he s hs0 hs2 v).val n‖ ^ 2|
      = ‖TerraMultiRound80Weighted.actions κ hκ s hs0 hs2 u
          - TerraMultiRound80Weighted.actions κ hκ s hs0 hs2 v‖ := by
  rw [TerraMultiRound80Weighted.norm_eq_weighted_coordinates (L := L) s]
  apply tsum_congr
  intro n
  have hcs : TerraMultiRound80Weighted.coordinate (L := L) s
      (TerraMultiRound80Weighted.actions κ hκ s hs0 hs2 u
        - TerraMultiRound80Weighted.actions κ hκ s hs0 hs2 v) n
      = TerraMultiRound80Weighted.coordinate (L := L) s
          (TerraMultiRound80Weighted.actions κ hκ s hs0 hs2 u) n
        - TerraMultiRound80Weighted.coordinate (L := L) s
          (TerraMultiRound80Weighted.actions κ hκ s hs0 hs2 v) n := by
    simp only [TerraMultiRound80Weighted.coordinate, lp.coeFn_sub, Pi.sub_apply, sub_div]
  rw [hcs, TerraMultiRound80Weighted.coordinate_actions κ hκ s hs0 hs2 u n,
    TerraMultiRound80Weighted.coordinate_actions κ hκ s hs0 hs2 v n,
    lift_apply, lift_apply, he u.val n, he v.val n]
  rfl

/-- Coordinates of the restricted lift are continuous in u ∈ H^s. -/
theorem coord_continuous (e : L2T L ≃ₜ V) (s : ℝ) (hs0 : 0 ≤ s) (n : ℤ) :
    Continuous (fun u : H02 L s => (e u.val).val n) := by
  have hv : Continuous (fun u : H02 L s => u.val) := (H02.toL2 hs0).continuous
  have hL2 : Continuous (fun u : H02 L s => (e u.val).val) :=
    continuous_subtype_val.comp (e.continuous.comp hv)
  exact (lp.evalCLM (𝕜 := ℂ) (E := fun _ : ℤ => ℂ) (p := 2) n).continuous.comp hL2

/-- The lift from H^s into h^s is continuous, via weighted coordinates and moduli. -/
theorem lift_continuous (κ : ℝ) (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    Continuous (fun u : H02 L s => lift e hκ he s hs0 hs2 u) := by
  have hA : Continuous (TerraMultiRound80Weighted.actions κ hκ s hs0 hs2 :
      H02 L s → TerraMultiRound80Weighted.WeightedL1 L s) :=
    (TerraMultiRound80Weighted.REG010 (L := L) κ hκ s hs0 hs2).2.2.2.1
  refine continuous_iff_seqContinuous.mpr fun x a hx => ?_
  show Tendsto (fun j => lift e hκ he s hs0 hs2 (x j)) atTop
    (𝓝 (lift e hκ he s hs0 hs2 a))
  apply QuantumNLS.Reg011SequencesR48a.tendsto_of_coordinates_moduli (def002 L s)
    (fun j => lift e hκ he s hs0 hs2 (x j)) (lift e hκ he s hs0 hs2 a)
  · intro n
    exact ((coord_continuous e s hs0 n).tendsto a).comp hx
  · have hfun : (fun j => ∑' n : ℤ, (def002 L s).w n *
        |‖(lift e hκ he s hs0 hs2 (x j)).val n‖ ^ 2
          - ‖(lift e hκ he s hs0 hs2 a).val n‖ ^ 2|)
        = fun j => ‖TerraMultiRound80Weighted.actions κ hκ s hs0 hs2 (x j)
          - TerraMultiRound80Weighted.actions κ hκ s hs0 hs2 a‖ :=
      funext fun j => moduli_sum_eq κ hκ e he s hs0 hs2 (x j) a
    rw [hfun]
    exact tendsto_iff_norm_sub_tendsto_zero.mp ((hA.tendsto a).comp hx)

/-- Forward h^s continuity of the restricted map onto V ∩ h^s (printed REG-011, forward part). -/
theorem restriction_continuous (κ : ℝ) (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    Continuous (show H02 L s → TargetA L V s hs0 from fun u => restriction e hκ he s hs0 hs2 u) :=
  Continuous.subtype_mk (p := fun z : h02 L s => toBase (L := L) s hs0 z ∈ V)
    (lift_continuous κ hκ e he s hs0 hs2)
    (fun u => (restriction e hκ he s hs0 hs2 u).property)

#print axioms moduli_sum_eq
#print axioms lift_continuous
#print axioms restriction_continuous
end QuantumNLS.Reg011HForward
