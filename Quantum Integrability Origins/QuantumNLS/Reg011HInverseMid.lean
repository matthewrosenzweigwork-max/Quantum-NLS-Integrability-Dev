import QuantumNLS.Reg011HInverseLow
import QuantumNLS.Reg010LowPrinted
import QuantumNLS.Reg010LowL4Correction
import QuantumNLS.Reg010LowEmbeddingMap
import QuantumNLS.TerraMultiRound77ActionCriteria

/-! REG-011 step 4 (haiku_inventory, module Reg011HInverseMid), mid orders 1/2 ≤ s < 1.
Inverse continuity V ∩ h^s → H^s at mid order, by the L⁴ route:
* the order-1/3 inverse w_j of the same coordinates converges in H^{1/3}
  (`Reg011HInverseLow.inverse_low_tendsto` at s' = 1/3, since h^s ⊂ h^{1/3} by `h02_mono`
  with the same coordinates),
* H^{1/3} ↪ native L⁴ (`Reg010LowEmbeddingMap.embeddingH02`, continuous, `toL2 ∘ embeddingH02 = val`),
* the L⁴ fractional identity (`Reg010LowPrinted.L4_fractional_identity`, 0 < s < 1) with the
  continuous L⁴ correction `Reg010LowL4Correction.J4_continuous` gives free-moment convergence
  at order 2s,
* the free moments are the H^s weighted sums (`Reg011HFreeMoment.free_moment_eq_tsum`), and the
  mid weight (1+|p|)^{2s} ≤ 2^{2s}(1+|p|^{2s}) (a constant-K weighted Scheffé step) gives H^s
  norm convergence; then `H02_tendsto_of_L2_and_norm`.
The REG-010 chain (Reg010LowPrinted, Reg010LowL4Correction, Reg010LowEmbeddingMap) is frozen but
PENDING REG-010 REVIEW, so every result here is conditional on that review. Read-only imports
only; no review record unfrozen module is imported. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier QuantumNLS.RootWeightedCellsR26
open QuantumNLS.Reg011SettingR48a
namespace QuantumNLS.Reg011HInverseMid

variable {L κ : ℝ} [Fact (0 < L)] {V : Set Seq}

/-- Elementary power bound: (1+a)^q ≤ 2^q (1 + a^q) for a ≥ 0 and q ≥ 0. -/
theorem rpow_one_add_le (a q : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q) :
    (1 + a) ^ q ≤ (2:ℝ) ^ q * (1 + a ^ q) := by
  have hpos : 0 ≤ a ^ q := Real.rpow_nonneg ha q
  rcases le_total a 1 with h | h
  · have h1 : (1 + a) ^ q ≤ (2:ℝ) ^ q := Real.rpow_le_rpow (by linarith) (by linarith) hq
    have h2 : (2:ℝ) ^ q ≤ (2:ℝ) ^ q * (1 + a ^ q) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    linarith
  · have h1 : (1 + a) ^ q ≤ (2 * a) ^ q := Real.rpow_le_rpow (by linarith) (by linarith) hq
    rw [Real.mul_rpow (by norm_num) ha] at h1
    have h2 : (2:ℝ) ^ q * a ^ q ≤ (2:ℝ) ^ q * (1 + a ^ q) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith

/-- Weighted Scheffé step with a constant: if b ≤ w ≤ K(1+b), 1 ≤ w, then Σ w X_j → Σ w Y
whenever the coordinates converge, the free sums Σ b X_j → Σ b Y converge, and the total
masses converge. Same proof as `Reg011HInverseLow.abstract_weighted` with the constant K. -/
theorem abstract_weighted_K {K : ℝ} (hK : 0 ≤ K) (X : ℕ → ℤ → ℝ) (Y w b : ℤ → ℝ)
    (hX0 : ∀ j n, 0 ≤ X j n) (hY0 : ∀ n, 0 ≤ Y n)
    (hb0 : ∀ n, 0 ≤ b n) (hbw : ∀ n, b n ≤ w n) (hw1 : ∀ n, 1 ≤ w n)
    (hwb : ∀ n, w n ≤ K * (1 + b n))
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
  have hlim : Tendsto (fun j => K * ∑' n, |X j n + b n * X j n - (Y n + b n * Y n)|) atTop (𝓝 0) := by
    have h := hsch.const_mul K
    rw [mul_zero] at h
    exact h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hlim
  have hsF : Summable (fun n => ‖X j n + b n * X j n - (Y n + b n * Y n)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => by
        have h1 := norm_add_le (X j n + b n * X j n) (-(Y n + b n * Y n))
        rw [← sub_eq_add_neg] at h1
        have h2 : ‖X j n + b n * X j n‖ = X j n + b n * X j n :=
          Real.norm_of_nonneg (hF0 j n)
        have h3 : ‖Y n + b n * Y n‖ = Y n + b n * Y n := Real.norm_of_nonneg (hG0 n)
        rw [norm_neg, h2, h3] at h1
        exact h1)
      ((hFs j).add hGs)
  have hpw : ∀ n, ‖w n * X j n - w n * Y n‖ ≤ K * ‖X j n + b n * X j n - (Y n + b n * Y n)‖ := by
    intro n
    have e3 : w n * X j n - w n * Y n = w n * (X j n - Y n) := by ring
    have e4 : X j n + b n * X j n - (Y n + b n * Y n) = (1 + b n) * (X j n - Y n) := by ring
    rw [e3, e4, norm_mul, norm_mul, Real.norm_of_nonneg (hw0 n),
      Real.norm_of_nonneg (by linarith [hb0 n] : (0:ℝ) ≤ 1 + b n)]
    have h := mul_le_mul_of_nonneg_right (hwb n) (norm_nonneg (X j n - Y n))
    calc w n * ‖X j n - Y n‖ ≤ K * (1 + b n) * ‖X j n - Y n‖ := h
      _ = K * ((1 + b n) * ‖X j n - Y n‖) := by ring
  have hdiff : ∑' n, w n * X j n - ∑' n, w n * Y n = ∑' n, (w n * X j n - w n * Y n) :=
    ((hwX j).tsum_sub hwY).symm
  have hsn : Summable (fun n => ‖w n * X j n - w n * Y n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => by
        have h1 := norm_sub_le (w n * X j n) (w n * Y n)
        rw [Real.norm_of_nonneg (mul_nonneg (hw0 n) (hX0 j n)),
          Real.norm_of_nonneg (mul_nonneg (hw0 n) (hY0 n))] at h1
        exact h1)
      ((hwX j).add hwY)
  calc ‖∑' n, w n * X j n - ∑' n, w n * Y n‖
      = ‖∑' n, (w n * X j n - w n * Y n)‖ := by rw [hdiff]
    _ ≤ ∑' n, ‖w n * X j n - w n * Y n‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' n, K * ‖X j n + b n * X j n - (Y n + b n * Y n)‖ :=
        Summable.tsum_le_tsum hpw hsn (hsF.mul_left K)
    _ = K * ∑' n, ‖X j n + b n * X j n - (Y n + b n * Y n)‖ := tsum_mul_left
    _ = K * ∑' n, |X j n + b n * X j n - (Y n + b n * Y n)| := by
        congr 1

/-- The H^s norm is controlled by the L² convergence and the convergence of the free
moments of order 2s (0 ≤ s), through the constant-K weighted Scheffé step. -/
theorem norm_sq_tendsto_of_free {s : ℝ} (hs0 : 0 ≤ s) (u : ℕ → H02 L s) (u0 : H02 L s)
    (hL2 : Tendsto (fun j => (u j).val) atTop (𝓝 u0.val))
    (hfree : Tendsto (fun j => ∫ x : ℝ, |x| ^ (2 * s) ∂(QuantumNLS.FreeLimit.freeMeasure L (u j).val))
      atTop (𝓝 (∫ x : ℝ, |x| ^ (2 * s) ∂(QuantumNLS.FreeLimit.freeMeasure L u0.val)))) :
    Tendsto (fun j => ‖u j‖ ^ 2) atTop (𝓝 (‖u0‖ ^ 2)) := by
  have hp0 : (0 : ℝ) ≤ 2 * s := by linarith
  have hK : (0 : ℝ) ≤ (2:ℝ) ^ (2 * s) := by positivity
  have hbw : ∀ n : ℤ, |momentum L n| ^ (2 * s) ≤ (1 + |momentum L n|) ^ (2 * s) :=
    fun n => Real.rpow_le_rpow (abs_nonneg _) (by linarith [abs_nonneg (momentum L n)]) hp0
  have hw1 : ∀ n : ℤ, (1 : ℝ) ≤ (1 + |momentum L n|) ^ (2 * s) :=
    fun n => Real.one_le_rpow (by linarith [abs_nonneg (momentum L n)]) hp0
  have hwb : ∀ n : ℤ, (1 + |momentum L n|) ^ (2 * s) ≤
      (2:ℝ) ^ (2 * s) * (1 + |momentum L n| ^ (2 * s)) :=
    fun n => rpow_one_add_le (|momentum L n|) (2 * s) (abs_nonneg _) hp0
  have hfree' : Tendsto (fun j => ∑' n : ℤ, |momentum L n| ^ (2 * s) * ‖fourierL2 L (u j).val n‖ ^ 2)
      atTop (𝓝 (∑' n : ℤ, |momentum L n| ^ (2 * s) * ‖fourierL2 L u0.val n‖ ^ 2)) := by
    simpa only [QuantumNLS.Reg011HFreeMoment.free_moment_eq_tsum] using hfree
  simp only [QuantumNLS.Reg011HSobolevConvergence.H02_norm_sq_eq_tsum,
    QuantumNLS.Reg011HReverseMoment.def002_w_eq]
  refine abstract_weighted_K hK (fun j n => ‖fourierL2 L (u j).val n‖ ^ 2)
    (fun n => ‖fourierL2 L u0.val n‖ ^ 2) (fun n => (1 + |momentum L n|) ^ (2 * s))
    (fun n => |momentum L n| ^ (2 * s))
    (fun j n => by positivity) (fun n => by positivity) (fun n => by positivity)
    hbw hw1 hwb (fun j => QuantumNLS.Reg011HInverseLow.summable_H02 (u j))
    (QuantumNLS.Reg011HInverseLow.summable_H02 u0) ?_ ?_ hfree'
  · intro n
    exact (QuantumNLS.Reg011HSobolevConvergence.coeff_tendsto_of_L2 (L := L)
      (fun j => (u j).val) u0.val hL2 n).norm.pow 2
  · simp only [QuantumNLS.Reg011HInverseLow.parseval_L2]
    exact hL2.norm.pow 2

/-- The physical-to-free identity on H^{1/3}, through native L⁴: for w ∈ H^{1/3} with finite
physical 2s-moment, the free 2s-moment is the physical one minus the printed correction J. -/
theorem free_eq_phys_sub_J4 (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hsp : 0 < s) (hs' : s < 1)
    (w : H02 L (1 / 3))
    (hm : Integrable (fun t : ℝ => |t| ^ (2 * s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ w.val)) :
    ∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.FreeLimit.freeMeasure L w.val) =
      (∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ w.val)) -
        QuantumNLS.Reg010LowCorrection.J κ hκ s w.val := by
  have h := QuantumNLS.Reg010LowPrinted.L4_fractional_identity κ hκ
    (QuantumNLS.Reg010LowEmbeddingMap.embeddingH02 w) s hsp hs'
    (by rw [QuantumNLS.Reg010LowEmbeddingMap.embeddingH02_toL2]; exact hm)
  dsimp only at h
  rw [QuantumNLS.Reg010LowEmbeddingMap.embeddingH02_toL2] at h
  linarith

/-- Free-moment convergence at order 2s on H^{1/3}, 0 < s < 1, through native L⁴: if w_j → w
in H^{1/3} and the physical 2s-moments converge, the free 2s-moments converge. -/
theorem free_tendsto_of_third (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hsp : 0 < s) (hs' : s < 1)
    (w : ℕ → H02 L (1 / 3)) (w0 : H02 L (1 / 3)) (hw : Tendsto w atTop (𝓝 w0))
    (hm : ∀ j, Integrable (fun t : ℝ => |t| ^ (2 * s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ (w j).val))
    (hm0 : Integrable (fun t : ℝ => |t| ^ (2 * s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ w0.val))
    (hphys : Tendsto (fun j => ∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (w j).val))
      atTop (𝓝 (∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ w0.val)))) :
    Tendsto (fun j => ∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.FreeLimit.freeMeasure L (w j).val)) atTop
      (𝓝 (∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.FreeLimit.freeMeasure L w0.val))) := by
  have hE : Tendsto (fun j => QuantumNLS.Reg010LowEmbeddingMap.embeddingH02 (w j)) atTop
      (𝓝 (QuantumNLS.Reg010LowEmbeddingMap.embeddingH02 w0)) :=
    (QuantumNLS.Reg010LowEmbeddingMap.embeddingH02.continuous.tendsto w0).comp hw
  have hJ4 := ((QuantumNLS.Reg010LowL4Correction.J4_continuous (L := L) κ hκ s hsp hs').tendsto
    (QuantumNLS.Reg010LowEmbeddingMap.embeddingH02 w0)).comp hE
  have eJ : ∀ x : H02 L (1 / 3), QuantumNLS.Reg010LowL4Correction.J4 κ hκ s
      (QuantumNLS.Reg010LowEmbeddingMap.embeddingH02 x) = QuantumNLS.Reg010LowCorrection.J κ hκ s x.val := by
    intro x
    unfold QuantumNLS.Reg010LowL4Correction.J4
    rw [QuantumNLS.Reg010LowEmbeddingMap.embeddingH02_toL2]
  simp only [Function.comp_def, eJ] at hJ4
  have hid0 := free_eq_phys_sub_J4 κ hκ s hsp hs' w0 hm0
  rw [hid0]
  exact (hphys.sub hJ4).congr (fun j => (free_eq_phys_sub_J4 κ hκ s hsp hs' (w j) (hm j)).symm)

/-- The H^s and H^{1/3} inverse images have the same L² vector (coordinates are shared). -/
theorem toBase_h02_mono {s : ℝ} (hs0 : 0 ≤ s) (h13 : 1 / 3 ≤ s) (x : h02 L s) :
    toBase (L := L) (1 / 3) (by norm_num) (h02_mono L h13 x) = toBase (L := L) s hs0 x := by
  apply lp.ext
  funext n
  rw [toBase_apply, toBase_apply]
  rfl

/-- The order-1/3 inverse image of the same coordinates has the same L² vector as the order-s
inverse image (coordinates are shared by `h02_mono`; closed instances, no rewriting of
metavariable patterns). -/
theorem inverse_mono_val (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ) (s : ℝ)
    (hs0 : 0 ≤ s) (h13 : (1 / 3 : ℝ) ≤ s) (hs2 : s ≤ 2) (z : h02 L s)
    (hz : toBase (L := L) s hs0 z ∈ V)
    (hz' : toBase (L := L) (1 / 3) (by norm_num) (h02_mono L h13 z) ∈ V) :
    (inverse e hκ he (1 / 3) (by norm_num) (by norm_num : (1 / 3 : ℝ) ≤ 2)
      (⟨h02_mono L h13 z, hz'⟩ : Target (L := L) V (1 / 3) (by norm_num))).val =
    (inverse e hκ he s hs0 hs2 (⟨z, hz⟩ : Target (L := L) V s hs0)).val := by
  have h1 := inverse_val e hκ he (1 / 3) (by norm_num) (by norm_num : (1 / 3 : ℝ) ≤ 2)
    (⟨h02_mono L h13 z, hz'⟩ : Target (L := L) V (1 / 3) (by norm_num))
  have h2 := inverse_val e hκ he s hs0 hs2 (⟨z, hz⟩ : Target (L := L) V s hs0)
  rw [h1, h2]
  unfold baseInverse
  exact congrArg e.symm (Subtype.ext (toBase_h02_mono hs0 h13 z))

/-- **REG-011 step 4, mid-order inverse continuity.** For 1/2 ≤ s < 1, if z_j → z in h^s with
z_j ∈ V ∩ h^s, then the inverse images converge in H^s. REG-010 pending review: the proof uses
the frozen L⁴ identity (Reg010LowPrinted, Reg010LowL4Correction, Reg010LowEmbeddingMap). -/
theorem inverse_mid_tendsto (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ) (s : ℝ)
    (hs0 : 0 ≤ s) (hs : 1 / 2 ≤ s) (hs' : s < 1) (hs2 : s ≤ 2)
    (z : ℕ → h02 L s) (z0 : h02 L s) (hz : Tendsto z atTop (𝓝 z0))
    (hzV : ∀ j, toBase (L := L) s hs0 (z j) ∈ V) (hV0 : toBase (L := L) s hs0 z0 ∈ V) :
    Tendsto (fun j => inverse e hκ he s hs0 hs2 (⟨z j, hzV j⟩ : Target (L := L) V s hs0)) atTop
      (𝓝 (inverse e hκ he s hs0 hs2 (⟨z0, hV0⟩ : Target (L := L) V s hs0))) := by
  have hsp : 0 < s := by linarith
  have h13 : (1 / 3 : ℝ) ≤ s := by linarith
  have h3p : (0 : ℝ) < 1 / 3 := by norm_num
  have h3s : (1 / 3 : ℝ) < 1 / 2 := by norm_num
  have h3two : (1 / 3 : ℝ) ≤ 2 := by norm_num
  -- the same coordinates, viewed in h^{1/3}
  have hz' : Tendsto (fun j => h02_mono L h13 (z j)) atTop (𝓝 (h02_mono L h13 z0)) :=
    ((h02_mono L h13).continuous.tendsto z0).comp hz
  have hzV' : ∀ j, toBase (L := L) (1 / 3) h3p.le (h02_mono L h13 (z j)) ∈ V := fun j => by
    rw [toBase_h02_mono hs0 h13]
    exact hzV j
  have hV0' : toBase (L := L) (1 / 3) h3p.le (h02_mono L h13 z0) ∈ V := by
    rw [toBase_h02_mono hs0 h13]
    exact hV0
  -- order-1/3 inverse images, convergent in H^{1/3} by Reg011HInverseLow
  have hw := QuantumNLS.Reg011HInverseLow.inverse_low_tendsto hκ e he (1 / 3) h3p h3s h3two
    (fun j => h02_mono L h13 (z j)) (h02_mono L h13 z0) hz' hzV' hV0'
  have hwv : ∀ j, (inverse e hκ he (1 / 3) h3p.le h3two
      (⟨h02_mono L h13 (z j), hzV' j⟩ : Target (L := L) V (1 / 3) h3p.le)).val =
      (inverse e hκ he s hs0 hs2 (⟨z j, hzV j⟩ : Target (L := L) V s hs0)).val :=
    fun j => inverse_mono_val hκ e he s hs0 h13 hs2 (z j) (hzV j) (hzV' j)
  have hwv0 : (inverse e hκ he (1 / 3) h3p.le h3two
      (⟨h02_mono L h13 z0, hV0'⟩ : Target (L := L) V (1 / 3) h3p.le)).val =
      (inverse e hκ he s hs0 hs2 (⟨z0, hV0⟩ : Target (L := L) V s hs0)).val :=
    inverse_mono_val hκ e he s hs0 h13 hs2 z0 hV0 hV0'
  -- L² convergence of the order-s inverse images
  have hu := QuantumNLS.Reg011HReverseMoment.inverse_tendsto e s hs0 z z0 hz hzV hV0
  have hv : ∀ j, (inverse e hκ he s hs0 hs2 (⟨z j, hzV j⟩ : Target (L := L) V s hs0)).val =
      baseInverse e s hs0 (⟨z j, hzV j⟩ : Target (L := L) V s hs0) :=
    fun j => inverse_val e hκ he s hs0 hs2 _
  have hv0 : (inverse e hκ he s hs0 hs2 (⟨z0, hV0⟩ : Target (L := L) V s hs0)).val =
      baseInverse e s hs0 (⟨z0, hV0⟩ : Target (L := L) V s hs0) :=
    inverse_val e hκ he s hs0 hs2 _
  have hL2 : Tendsto (fun j => (inverse e hκ he s hs0 hs2 (⟨z j, hzV j⟩ : Target (L := L) V s hs0)).val)
      atTop (𝓝 (inverse e hκ he s hs0 hs2 (⟨z0, hV0⟩ : Target (L := L) V s hs0)).val) := by
    rw [hv0]
    exact hu.congr (fun j => (hv j).symm)
  -- integrability and physical moments at order 2s
  have hxm : ∀ j, Integrable (fun t : ℝ => |t| ^ (2 * s))
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ (inverse e hκ he s hs0 hs2 (⟨z j, hzV j⟩ : Target (L := L) V s hs0)).val) := by
    intro j
    rw [hv j]
    exact (QuantumNLS.TerraMultiRound77ActionCriteria.physical_power_iff_indexed_actions hκ _ s hsp).mpr
      (QuantumNLS.Reg011HReverseMoment.masses_summable hκ e he s hs0 (z j) (hzV j))
  have hym : Integrable (fun t : ℝ => |t| ^ (2 * s))
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ (inverse e hκ he s hs0 hs2 (⟨z0, hV0⟩ : Target (L := L) V s hs0)).val) := by
    rw [hv0]
    exact (QuantumNLS.TerraMultiRound77ActionCriteria.physical_power_iff_indexed_actions hκ _ s hsp).mpr
      (QuantumNLS.Reg011HReverseMoment.masses_summable hκ e he s hs0 z0 hV0)
  have hm := QuantumNLS.Reg011HReverseMoment.moment_tendsto hκ e he s hsp hs2 z z0 hz hzV hV0
  have hphys : Tendsto (fun j => ∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ
      (inverse e hκ he s hs0 hs2 (⟨z j, hzV j⟩ : Target (L := L) V s hs0)).val)) atTop
      (𝓝 (∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ
        (inverse e hκ he s hs0 hs2 (⟨z0, hV0⟩ : Target (L := L) V s hs0)).val))) := by
    rw [hv0]
    exact hm.congr (fun j => by rw [hv j])
  -- transfer to the order-1/3 inverse images (same L² vectors)
  have hwm : ∀ j, Integrable (fun t : ℝ => |t| ^ (2 * s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ
      (inverse e hκ he (1 / 3) h3p.le h3two (⟨h02_mono L h13 (z j), hzV' j⟩ : Target (L := L) V (1 / 3) h3p.le)).val) :=
    fun j => by rw [hwv j]; exact hxm j
  have hwm0 : Integrable (fun t : ℝ => |t| ^ (2 * s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ
      (inverse e hκ he (1 / 3) h3p.le h3two (⟨h02_mono L h13 z0, hV0'⟩ : Target (L := L) V (1 / 3) h3p.le)).val) := by
    rw [hwv0]; exact hym
  have hphysw : Tendsto (fun j => ∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ
      (inverse e hκ he (1 / 3) h3p.le h3two (⟨h02_mono L h13 (z j), hzV' j⟩ : Target (L := L) V (1 / 3) h3p.le)).val))
      atTop (𝓝 (∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ
        (inverse e hκ he (1 / 3) h3p.le h3two (⟨h02_mono L h13 z0, hV0'⟩ : Target (L := L) V (1 / 3) h3p.le)).val))) := by
    rw [hwv0]
    exact hphys.congr (fun j => by rw [hwv j])
  -- free moments at order 2s, through L⁴
  have hfreeW := free_tendsto_of_third κ hκ s hsp hs' _ _ hw hwm hwm0 hphysw
  have hfreeU : Tendsto (fun j => ∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.FreeLimit.freeMeasure L
      (inverse e hκ he s hs0 hs2 (⟨z j, hzV j⟩ : Target (L := L) V s hs0)).val)) atTop
      (𝓝 (∫ t : ℝ, |t| ^ (2 * s) ∂(QuantumNLS.FreeLimit.freeMeasure L
        (inverse e hκ he s hs0 hs2 (⟨z0, hV0⟩ : Target (L := L) V s hs0)).val))) := by
    rw [← hwv0]
    exact hfreeW.congr (fun j => by rw [hwv j])
  -- H^s norm convergence and the H^s criterion
  have hnorm := norm_sq_tendsto_of_free hs0 (fun j => inverse e hκ he s hs0 hs2 (⟨z j, hzV j⟩ : Target (L := L) V s hs0))
    (inverse e hκ he s hs0 hs2 (⟨z0, hV0⟩ : Target (L := L) V s hs0)) hL2 hfreeU
  exact QuantumNLS.Reg011HSobolevConvergence.H02_tendsto_of_L2_and_norm _ _ hL2 hnorm

#print axioms rpow_one_add_le
#print axioms abstract_weighted_K
#print axioms norm_sq_tendsto_of_free
#print axioms free_eq_phys_sub_J4
#print axioms free_tendsto_of_third
#print axioms toBase_h02_mono
#print axioms inverse_mid_tendsto
end QuantumNLS.Reg011HInverseMid
