import QuantumNLS.Reg011HReverseMoment
import QuantumNLS.Reg011HSobolevConvergence
import QuantumNLS.Reg011HFreeMoment
import QuantumNLS.TerraMultiRound71Sequence
import QuantumNLS.TerraMultiRound77ActionCriteria

/-! REG-011 step 3 (haiku_inventory, module Reg011HInverseLow), low orders 0 ≤ s < 1/2.
Inverse continuity V ∩ h^s → H^s: if z_j → z in h^s with z_j ∈ V, then the inverse images
u_j = inverse z_j converge in H^s. The proof combines
* L² convergence of the inverse images (`Reg011HReverseMoment.inverse_tendsto`),
* same-order physical moment convergence (`Reg011HReverseMoment.moment_tendsto`),
* the free-moment passage (`Reg011HFreeMoment.free_moment_tendsto`, GAP B, 0 < s < 1/2),
* a weighted Scheffé step (`abstract_weighted`, from the frozen `nonnegative_tsum_abs_sub_tendsto`),
  using the inequality (1+|p|)^{2s} ≤ 1 + |p|^{2s} valid for 0 ≤ 2s ≤ 1,
* the H^s criterion `H02_tendsto_of_L2_and_norm`.
The case s = 0 (H^0 = L²) is handled directly by Parseval. REG-010 remains pending review;
the 0 < s < 1/2 case inherits that status through Reg011HFreeMoment. No review record unfrozen
module is imported. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier QuantumNLS.RootWeightedCellsR26
open QuantumNLS.Reg011SettingR48a
namespace QuantumNLS.Reg011HInverseLow

variable {L κ : ℝ} [Fact (0 < L)] {V : Set Seq}

/-- Weighted Scheffé step on ℤ-indexed nonnegative sequences. If the weights satisfy
1 ≤ w, b ≤ w ≤ 1 + b, the sums Σ X_j, Σ b X_j converge to Σ Y, Σ b Y, the coordinates converge
pointwise, and the sequences are dominated by summable weighted sums, then Σ w X_j → Σ w Y. -/
theorem abstract_weighted (X : ℕ → ℤ → ℝ) (Y w b : ℤ → ℝ)
    (hX0 : ∀ j n, 0 ≤ X j n) (hY0 : ∀ n, 0 ≤ Y n)
    (hb0 : ∀ n, 0 ≤ b n) (hbw : ∀ n, b n ≤ w n) (hw1 : ∀ n, 1 ≤ w n) (hwb : ∀ n, w n ≤ 1 + b n)
    (hwX : ∀ j, Summable (fun n => w n * X j n)) (hwY : Summable (fun n => w n * Y n))
    (hpt : ∀ n, Tendsto (fun j => X j n) atTop (𝓝 (Y n)))
    (hnorm : Tendsto (fun j => ∑' n, X j n) atTop (𝓝 (∑' n, Y n)))
    (hsum : Tendsto (fun j => ∑' n, b n * X j n) atTop (𝓝 (∑' n, b n * Y n))) :
    Tendsto (fun j => ∑' n, w n * X j n) atTop (𝓝 (∑' n, w n * Y n)) := by
  have hw0 : ∀ n, 0 ≤ w n := fun n => by linarith [hw1 n]
  have hXs : ∀ j, Summable (X j) := fun j =>
    Summable.of_nonneg_of_le (hX0 j) (fun n => le_mul_of_one_le_left (hX0 j n) (hw1 n)) (hwX j)
  have hbX : ∀ j, Summable (fun n => b n * X j n) := fun j =>
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hb0 n) (hX0 j n))
      (fun n => mul_le_mul_of_nonneg_right (hbw n) (hX0 j n)) (hwX j)
  have hYs : Summable Y :=
    Summable.of_nonneg_of_le hY0 (fun n => le_mul_of_one_le_left (hY0 n) (hw1 n)) hwY
  have hbY : Summable (fun n => b n * Y n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hb0 n) (hY0 n))
      (fun n => mul_le_mul_of_nonneg_right (hbw n) (hY0 n)) hwY
  have hF0 : ∀ j n, 0 ≤ X j n + b n * X j n :=
    fun j n => add_nonneg (hX0 j n) (mul_nonneg (hb0 n) (hX0 j n))
  have hG0 : ∀ n, 0 ≤ Y n + b n * Y n :=
    fun n => add_nonneg (hY0 n) (mul_nonneg (hb0 n) (hY0 n))
  have hFs : ∀ j, Summable (fun n => X j n + b n * X j n) := fun j => (hXs j).add (hbX j)
  have hGs : Summable (fun n => Y n + b n * Y n) := hYs.add hbY
  have e1 : ∀ j, ∑' n, (X j n + b n * X j n) = ∑' n, X j n + ∑' n, b n * X j n :=
    fun j => (hXs j).tsum_add (hbX j)
  have e2 : ∑' n, (Y n + b n * Y n) = ∑' n, Y n + ∑' n, b n * Y n := hYs.tsum_add hbY
  have hFtot : Tendsto (fun j => ∑' n, (X j n + b n * X j n)) atTop
      (𝓝 (∑' n, (Y n + b n * Y n))) := by
    simp only [e1, e2]
    exact hnorm.add hsum
  have hpt' : ∀ n, Tendsto (fun j => X j n + b n * X j n) atTop (𝓝 (Y n + b n * Y n)) :=
    fun n => (hpt n).add ((hpt n).const_mul (b n))
  have hsch := QuantumNLS.TerraMultiRound71Sequence.nonnegative_tsum_abs_sub_tendsto
    (fun j n => X j n + b n * X j n) (fun n => Y n + b n * Y n) hF0 hG0 hFs hGs hpt' hFtot
  have hnn : ∀ a c : ℝ, 0 ≤ a → 0 ≤ c → ‖a - c‖ ≤ a + c := fun a c ha hc => by
    rw [Real.norm_eq_abs]
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hsch
  have hdiff : ∑' n, w n * X j n - ∑' n, w n * Y n = ∑' n, (w n * X j n - w n * Y n) :=
    ((hwX j).tsum_sub hwY).symm
  have hpw : ∀ n, ‖w n * X j n - w n * Y n‖ ≤ ‖X j n + b n * X j n - (Y n + b n * Y n)‖ := by
    intro n
    have e3 : w n * X j n - w n * Y n = w n * (X j n - Y n) := by ring
    have e4 : X j n + b n * X j n - (Y n + b n * Y n) = (1 + b n) * (X j n - Y n) := by ring
    rw [e3, e4, norm_mul, norm_mul, Real.norm_of_nonneg (by linarith [hb0 n] : (0:ℝ) ≤ 1 + b n),
      Real.norm_of_nonneg (hw0 n)]
    exact mul_le_mul_of_nonneg_right (hwb n) (norm_nonneg _)
  have hsn : Summable (fun n => ‖w n * X j n - w n * Y n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => hnn _ _ (mul_nonneg (hw0 n) (hX0 j n)) (mul_nonneg (hw0 n) (hY0 n)))
      ((hwX j).add hwY)
  have hsF : Summable (fun n => ‖X j n + b n * X j n - (Y n + b n * Y n)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => hnn _ _ (hF0 j n) (hG0 n)) ((hFs j).add hGs)
  calc ‖∑' n, w n * X j n - ∑' n, w n * Y n‖
      = ‖∑' n, (w n * X j n - w n * Y n)‖ := by rw [hdiff]
    _ ≤ ∑' n, ‖w n * X j n - w n * Y n‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' n, ‖X j n + b n * X j n - (Y n + b n * Y n)‖ := Summable.tsum_le_tsum hpw hsn hsF
    _ = ∑' n, |X j n + b n * X j n - (Y n + b n * Y n)| :=
        tsum_congr (fun n => Real.norm_eq_abs _)

/-- Parseval on the L² class, in the Fourier coordinates. -/
theorem parseval_L2 (v : L2T L) : ∑' n : ℤ, ‖fourierL2 L v n‖ ^ 2 = ‖v‖ ^ 2 := by
  have h := lp_norm_sq_tsum (fourierL2 L v)
  rw [norm_fourierL2] at h
  exact h.symm

/-- The weighted Fourier sum of an H^s element at order s, with the same-order weight. -/
theorem summable_H02 {s : ℝ} (u : H02 L s) :
    Summable (fun n : ℤ => (1 + |momentum L n|) ^ (2 * s) * ‖fourierL2 L u.val n‖ ^ 2) := by
  have h := QuantumNLS.Sobolev.WField.summable u
  simpa only [QuantumNLS.Reg011HReverseMoment.def002_w_eq] using h

/-- Weighted Fourier sums at order s, 0 ≤ s ≤ 1/2, along an L²-convergent sequence. The
free-moment sums at order 2s converge (the GAP B input), and the H^s weights are controlled by
(1+|p|)^{2s} ≤ 1 + |p|^{2s}; hence the weighted sums converge. -/
theorem weighted_tendsto {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1 / 2)
    (x : ℕ → L2T L) (y : L2T L) (hx : Tendsto x atTop (𝓝 y))
    (hw : ∀ j, Summable (fun n : ℤ => (1 + |momentum L n|) ^ (2 * s) * ‖fourierL2 L (x j) n‖ ^ 2))
    (hwy : Summable (fun n : ℤ => (1 + |momentum L n|) ^ (2 * s) * ‖fourierL2 L y n‖ ^ 2))
    (hfree : Tendsto (fun j => ∑' n : ℤ, |momentum L n| ^ (2 * s) * ‖fourierL2 L (x j) n‖ ^ 2) atTop
      (𝓝 (∑' n : ℤ, |momentum L n| ^ (2 * s) * ‖fourierL2 L y n‖ ^ 2))) :
    Tendsto (fun j => ∑' n : ℤ, (1 + |momentum L n|) ^ (2 * s) * ‖fourierL2 L (x j) n‖ ^ 2) atTop
      (𝓝 (∑' n : ℤ, (1 + |momentum L n|) ^ (2 * s) * ‖fourierL2 L y n‖ ^ 2)) := by
  have hp0 : (0 : ℝ) ≤ 2 * s := by linarith
  have hp1 : 2 * s ≤ 1 := by linarith
  have hwb : ∀ n : ℤ, (1 + |momentum L n|) ^ (2 * s) ≤ 1 + |momentum L n| ^ (2 * s) := by
    intro n
    have h := Real.rpow_add_le_add_rpow (by norm_num : (0 : ℝ) ≤ 1)
      (abs_nonneg (momentum L n)) hp0 hp1
    rwa [Real.one_rpow] at h
  have hbw : ∀ n : ℤ, |momentum L n| ^ (2 * s) ≤ (1 + |momentum L n|) ^ (2 * s) :=
    fun n => Real.rpow_le_rpow (abs_nonneg _) (by linarith [abs_nonneg (momentum L n)]) hp0
  have hw1 : ∀ n : ℤ, (1 : ℝ) ≤ (1 + |momentum L n|) ^ (2 * s) :=
    fun n => Real.one_le_rpow (by linarith [abs_nonneg (momentum L n)]) hp0
  refine abstract_weighted (fun j n => ‖fourierL2 L (x j) n‖ ^ 2) (fun n => ‖fourierL2 L y n‖ ^ 2)
    (fun n => (1 + |momentum L n|) ^ (2 * s)) (fun n => |momentum L n| ^ (2 * s))
    (fun j n => by positivity) (fun n => by positivity) (fun n => by positivity)
    hbw hw1 hwb hw hwy ?_ ?_ ?_
  · intro n
    exact (QuantumNLS.Reg011HSobolevConvergence.coeff_tendsto_of_L2 (L := L) x y hx n).norm.pow 2
  · simp only [parseval_L2]
    exact hx.norm.pow 2
  · exact hfree

/-- **REG-011 step 3, inverse continuity at low order.** For 0 < s < 1/2, if z_j → z in h^s
with z_j ∈ V ∩ h^s, then the inverse images converge in H^s. The rewrites are between closed
terms (`inverse_val` at explicit points), never between metavariable patterns. -/
theorem inverse_low_tendsto (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ) (s : ℝ)
    (hs0 : 0 < s) (hs' : s < 1 / 2) (hs2 : s ≤ 2)
    (z : ℕ → h02 L s) (z0 : h02 L s) (hz : Tendsto z atTop (𝓝 z0))
    (hzV : ∀ j, toBase (L := L) s hs0.le (z j) ∈ V) (hV0 : toBase (L := L) s hs0.le z0 ∈ V) :
    Tendsto (fun j => inverse e hκ he s hs0.le hs2 (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le)) atTop
      (𝓝 (inverse e hκ he s hs0.le hs2 (⟨z0, hV0⟩ : Target (L := L) V s hs0.le))) := by
  have hu := QuantumNLS.Reg011HReverseMoment.inverse_tendsto e s hs0.le z z0 hz hzV hV0
  have hv : ∀ j, (inverse e hκ he s hs0.le hs2 (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le)).val =
      baseInverse e s hs0.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le) :=
    fun j => QuantumNLS.Reg011SettingR48a.inverse_val e hκ he s hs0.le hs2 _
  have hv0 : (inverse e hκ he s hs0.le hs2 (⟨z0, hV0⟩ : Target (L := L) V s hs0.le)).val =
      baseInverse e s hs0.le (⟨z0, hV0⟩ : Target (L := L) V s hs0.le) :=
    QuantumNLS.Reg011SettingR48a.inverse_val e hκ he s hs0.le hs2 _
  have hL2 : Tendsto (fun j => (inverse e hκ he s hs0.le hs2 (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le)).val)
      atTop (𝓝 (inverse e hκ he s hs0.le hs2 (⟨z0, hV0⟩ : Target (L := L) V s hs0.le)).val) := by
    rw [hv0]
    exact hu.congr (fun j => (hv j).symm)
  apply QuantumNLS.Reg011HSobolevConvergence.H02_tendsto_of_L2_and_norm _ _ hL2
  simp only [QuantumNLS.Reg011HSobolevConvergence.H02_norm_sq_eq_tsum,
    QuantumNLS.Reg011HReverseMoment.def002_w_eq]
  have hw : ∀ j, Summable (fun n : ℤ => (1 + |momentum L n|) ^ (2 * s) *
      ‖fourierL2 L (inverse e hκ he s hs0.le hs2 (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le)).val n‖ ^ 2) :=
    fun j => summable_H02 _
  have hwy : Summable (fun n : ℤ => (1 + |momentum L n|) ^ (2 * s) *
      ‖fourierL2 L (inverse e hκ he s hs0.le hs2 (⟨z0, hV0⟩ : Target (L := L) V s hs0.le)).val n‖ ^ 2) :=
    summable_H02 _
  have hxm : ∀ j, Integrable (fun t : ℝ => |t| ^ (2 * s))
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ (inverse e hκ he s hs0.le hs2 (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le)).val) := by
    intro j
    rw [hv j]
    exact (QuantumNLS.TerraMultiRound77ActionCriteria.physical_power_iff_indexed_actions hκ _ s hs0).mpr
      (QuantumNLS.Reg011HReverseMoment.masses_summable hκ e he s hs0.le (z j) (hzV j))
  have hym : Integrable (fun t : ℝ => |t| ^ (2 * s))
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ (inverse e hκ he s hs0.le hs2 (⟨z0, hV0⟩ : Target (L := L) V s hs0.le)).val) := by
    rw [hv0]
    exact (QuantumNLS.TerraMultiRound77ActionCriteria.physical_power_iff_indexed_actions hκ _ s hs0).mpr
      (QuantumNLS.Reg011HReverseMoment.masses_summable hκ e he s hs0.le z0 hV0)
  have hm := QuantumNLS.Reg011HReverseMoment.moment_tendsto hκ e he s hs0 hs2 z z0 hz hzV hV0
  have hphys : Tendsto (fun j => ∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ
      (inverse e hκ he s hs0.le hs2 (⟨z j, hzV j⟩ : Target (L := L) V s hs0.le)).val)) atTop
      (𝓝 (∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ
        (inverse e hκ he s hs0.le hs2 (⟨z0, hV0⟩ : Target (L := L) V s hs0.le)).val))) := by
    rw [hv0]
    exact hm.congr (fun j => by rw [hv j])
  have hfree := QuantumNLS.Reg011HFreeMoment.free_moment_tendsto κ hκ s hs0 hs' _ _ hL2 hxm hym hphys
  exact weighted_tendsto hs0.le hs'.le _ _ hL2 hw hwy hfree

/-- **REG-011 step 3, s = 0.** H^0 is L²: the H^0 norm is the L² norm by Parseval, so inverse
continuity V ∩ h^0 → H^0 follows from L² convergence alone. -/
theorem inverse_zero_tendsto (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ)
    (hs2 : (0 : ℝ) ≤ 2)
    (z : ℕ → h02 L 0) (z0 : h02 L 0) (hz : Tendsto z atTop (𝓝 z0))
    (hzV : ∀ j, toBase (L := L) 0 le_rfl (z j) ∈ V) (hV0 : toBase (L := L) 0 le_rfl z0 ∈ V) :
    Tendsto (fun j => inverse e hκ he 0 le_rfl hs2 (⟨z j, hzV j⟩ : Target (L := L) V 0 le_rfl)) atTop
      (𝓝 (inverse e hκ he 0 le_rfl hs2 (⟨z0, hV0⟩ : Target (L := L) V 0 le_rfl))) := by
  have hu := QuantumNLS.Reg011HReverseMoment.inverse_tendsto e 0 le_rfl z z0 hz hzV hV0
  have hv : ∀ j, (inverse e hκ he 0 le_rfl hs2 (⟨z j, hzV j⟩ : Target (L := L) V 0 le_rfl)).val =
      baseInverse e 0 le_rfl (⟨z j, hzV j⟩ : Target (L := L) V 0 le_rfl) :=
    fun j => QuantumNLS.Reg011SettingR48a.inverse_val e hκ he 0 le_rfl hs2 _
  have hv0 : (inverse e hκ he 0 le_rfl hs2 (⟨z0, hV0⟩ : Target (L := L) V 0 le_rfl)).val =
      baseInverse e 0 le_rfl (⟨z0, hV0⟩ : Target (L := L) V 0 le_rfl) :=
    QuantumNLS.Reg011SettingR48a.inverse_val e hκ he 0 le_rfl hs2 _
  have hL2 : Tendsto (fun j => (inverse e hκ he 0 le_rfl hs2 (⟨z j, hzV j⟩ : Target (L := L) V 0 le_rfl)).val)
      atTop (𝓝 (inverse e hκ he 0 le_rfl hs2 (⟨z0, hV0⟩ : Target (L := L) V 0 le_rfl)).val) := by
    rw [hv0]
    exact hu.congr (fun j => (hv j).symm)
  apply QuantumNLS.Reg011HSobolevConvergence.H02_tendsto_of_L2_and_norm _ _ hL2
  simp only [QuantumNLS.Reg011HSobolevConvergence.H02_norm_sq_eq_tsum,
    QuantumNLS.Reg011HReverseMoment.def002_w_eq, mul_zero, Real.rpow_zero, one_mul, parseval_L2]
  exact hL2.norm.pow 2

#print axioms abstract_weighted
#print axioms parseval_L2
#print axioms summable_H02
#print axioms weighted_tendsto
#print axioms inverse_low_tendsto
#print axioms inverse_zero_tendsto
end QuantumNLS.Reg011HInverseLow
