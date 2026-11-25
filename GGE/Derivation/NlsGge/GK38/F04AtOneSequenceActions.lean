import NlsGge.GK38.F04AtOneSequenceTerms
import NlsGge.Spectral.ActualActionSumE02_38
import Mathlib.Analysis.Normed.Group.Tannery

/-! Discrete Scheffe: the actual action mass and its minimum with the limit. -/
set_option autoImplicit false
open Filter Set MeasureTheory
open scoped Topology
open NlsGge.SpectralFoundations NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.Sobolev38
namespace NlsGge.GK38
noncomputable section

theorem actionDifference_summable38 (u v : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hv : SobolevSquareSummable 1 (physicalFourier v)) :
    Summable (fun n : ℤ => |actualGapActionAllE02_38 u n - actualGapActionAllE02_38 v n|) := by
  have hs := (actualGapAction_hasSum_E02_38 u hu).summable.add
    (actualGapAction_hasSum_E02_38 v hv).summable
  apply hs.of_nonneg_of_le (fun _ => abs_nonneg _)
  intro n
  have hu0 := actualGapAction_nonneg_F04_38 u n
  have hv0 := actualGapAction_nonneg_F04_38 v n
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem action_l1_tendsto38 (u : ℕ → PhysicalL2) (u₀ : PhysicalL2)
    (hH : ∀ k, SobolevSquareSummable 1 (physicalFourier (u k)))
    (hH₀ : SobolevSquareSummable 1 (physicalFourier u₀))
    (hL2 : Tendsto u atTop (𝓝 u₀)) :
    Tendsto (fun k => ∑' n : ℤ,
      |actualGapActionAllE02_38 (u k) n - actualGapActionAllE02_38 u₀ n|) atTop (𝓝 0) := by
  let I : ℕ → ℤ → ℝ := fun k n => actualGapActionAllE02_38 (u k) n
  let I₀ : ℤ → ℝ := fun n => actualGapActionAllE02_38 u₀ n
  have hs : ∀ k, Summable (I k) := fun k => (actualGapAction_hasSum_E02_38 (u k) (hH k)).summable
  have hs₀ : Summable I₀ := (actualGapAction_hasSum_E02_38 u₀ hH₀).summable
  have hsd : ∀ k, Summable (fun n => |I k n - I₀ n|) :=
    fun k => actionDifference_summable38 (u k) u₀ (hH k) hH₀
  have hmin : ∀ k, Summable (fun n => min (I k n) (I₀ n)) := by
    intro k
    exact hs₀.of_nonneg_of_le
      (fun n => le_min (actualGapAction_nonneg_F04_38 (u k) n)
        (actualGapAction_nonneg_F04_38 u₀ n)) (fun n => min_le_right _ _)
  have hminlim : Tendsto (fun k => ∑' n, min (I k n) (I₀ n)) atTop (𝓝 (∑' n, I₀ n)) := by
    apply tendsto_tsum_of_dominated_convergence hs₀
    · intro n
      have ht := ((gapAction_L2_continuous38 n).tendsto u₀).comp hL2
      simpa [I, I₀, Function.comp_def] using ht.min (tendsto_const_nhds (x := I₀ n))
    · apply Eventually.of_forall
      intro k n
      rw [Real.norm_eq_abs, abs_of_nonneg
        (le_min (actualGapAction_nonneg_F04_38 (u k) n) (actualGapAction_nonneg_F04_38 u₀ n))]
      exact min_le_right _ _
  have he (k : ℕ) : (∑' n, |I k n - I₀ n|) =
      ‖u k‖ ^ 2 + ‖u₀‖ ^ 2 - 2 * ∑' n, min (I k n) (I₀ n) := by
    have hid (n : ℤ) : |I k n - I₀ n| = I k n + I₀ n - 2 * min (I k n) (I₀ n) := by
      rcases le_total (I k n) (I₀ n) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
    have hall : Summable (fun n => I k n + I₀ n - 2 * min (I k n) (I₀ n)) :=
      ((hs k).add hs₀).sub ((hmin k).mul_left 2)
    simp_rw [hid]
    rw [((hs k).add hs₀).tsum_sub ((hmin k).mul_left 2), (hs k).tsum_add hs₀, tsum_mul_left,
      (actualGapAction_hasSum_E02_38 (u k) (hH k)).tsum_eq,
      (actualGapAction_hasSum_E02_38 u₀ hH₀).tsum_eq]
  have hm := ((hL2.norm.pow 2).add (tendsto_const_nhds (x := ‖u₀‖ ^ 2))).sub (hminlim.const_mul 2)
  rw [(actualGapAction_hasSum_E02_38 u₀ hH₀).tsum_eq] at hm
  have hz : ‖u₀‖ ^ 2 + ‖u₀‖ ^ 2 - 2 * ‖u₀‖ ^ 2 = 0 := by ring
  rw [hz] at hm
  exact hm.congr' (Eventually.of_forall (fun k => (he k).symm))

end
end NlsGge.GK38
