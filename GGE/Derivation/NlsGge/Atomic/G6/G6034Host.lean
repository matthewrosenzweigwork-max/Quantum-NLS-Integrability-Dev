import Mathlib
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.Sobolev.WeightedHilbert

/- G6034 HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6034Host.lean.
   Hosts the G6 action-space design names used by the G6-034 head: `WeightedActionSpace`, `actionWeight`,
   `actionCoefficient`, `weightedActionNorm`, the constructor obligation `weightedCoordinateActions_mem` and
   `coordinateActions`. Bodies/heads byte-identical to followup12 DEFINITIONS/G6.lean.md lines 174-195 (Pro round 14
   ACTIVE REPLACEMENT; round-14 row G6-034: "host the current literal design bodies once"). The other names of that
   design block (ComplexActionSpace, PositiveActionSpace, positiveActionRoot, ...) belong to G6-035+ and are NOT hosted.
   grep NlsGge/ and Work/isolated_20261027 (2026-11-01): none of these six names is declared elsewhere.
   weightedCoordinateActions_mem: the design obligation is proved here (elementary: weighted Parseval of the h^1 carrier,
   NlsGge.Pilot.weightedHilbert_hasSum, nonnegative terms).
   LEXICAL/ELABORATION REPAIR (round-14 cluster 12, uniform ((1 : ℕ) : ℝ) carrier index): `carrierCoe38 1 z` ->
   `carrierCoe38 ((1 : ℕ) : ℝ) z` in the obligation head and the coordinateActions body; with z : SobolevCarrier38 ((1 : ℕ) : ℝ)
   the printed `carrierCoe38 1 z` does not elaborate (SobolevCarrier38 ↑1 vs SobolevCarrier38 1 not defeq; worker-lane
   request ce126ec2). actionWeight keeps its real argument (1 : ℝ). -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

abbrev WeightedActionSpace := lp (fun _ : ℤ => ℝ) 1

def actionWeight (n : ℤ) : ℝ := sobolevModeWeight (1 : ℝ) n

def actionCoefficient (I : WeightedActionSpace) (n : ℤ) : ℝ := I n / actionWeight n

def weightedActionNorm (I : WeightedActionSpace) : ℝ := ‖I‖

theorem weightedCoordinateActions_mem (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
  Memℓp (fun n : ℤ => actionWeight n * ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖^2) 1 := by
  have hs : HasSum (fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n *
      ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖ ^ 2)
      (‖(show WeightedHilbert (sobolevModeWeight ((1 : ℕ) : ℝ)) from z)‖ ^ 2) :=
    weightedHilbert_hasSum (sobolevModeWeight ((1 : ℕ) : ℝ))
      (show WeightedHilbert (sobolevModeWeight ((1 : ℕ) : ℝ)) from z)
  have hw : ∀ n : ℤ, sobolevModeWeight ((1 : ℕ) : ℝ) n = actionWeight n := by
    intro n
    rw [Nat.cast_one]
    rfl
  refine memℓp_gen ?_
  have hnn : ∀ n : ℤ, 0 ≤ actionWeight n * ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖ ^ 2 := fun n =>
    mul_nonneg (sobolevModeWeight_pos 1 n).le (sq_nonneg _)
  have he : (fun n : ℤ =>
      ‖actionWeight n * ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖ ^ 2‖ ^ (1 : ℝ≥0∞).toReal) =
      fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n * ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖ ^ 2 := by
    funext n
    rw [ENNReal.toReal_one, Real.rpow_one, Real.norm_of_nonneg (hnn n), hw n]
  rw [he]
  exact hs.summable

def coordinateActions (z : SobolevCarrier38 ((1 : ℕ) : ℝ)) : WeightedActionSpace :=
  ⟨fun n => actionWeight n * ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖^2,
    weightedCoordinateActions_mem z⟩

end
end NlsGge.GKDefinitionDesign
