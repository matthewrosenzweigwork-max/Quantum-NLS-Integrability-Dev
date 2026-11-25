import QuantumNLS.SobolevSpaces

/-! ROOT-01: reuse the accepted normalized Fourier equivalence. New exact
arbitrary-exponent squared tail estimates keep DEF-002 and F04 distinct. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace QuantumNLS.Ext025A2
open QuantumNLS.Fourier

/-- Factor a lower weight through a higher weight, with a negative tail exponent. -/
theorem root01_weight_ratio {a b s t : ℝ} (hb : 0 < b) (hba : b ≤ a) (hst : t ≤ s) :
    a ^ t ≤ b ^ (t - s) * a ^ s := by
  have ha : 0 < a := hb.trans_le hba
  calc
    a ^ t = a ^ (t - s) * a ^ s := by rw [← Real.rpow_add ha]; congr 1; ring
    _ ≤ b ^ (t - s) * a ^ s :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hb hba (sub_nonpos.mpr hst))
        (Real.rpow_nonneg ha.le _)

/-- A general weighted tail inequality. Summability is proved by domination,
so neither side uses the nonsummable `tsum` default. -/
theorem root01_weighted_tail {q : ℤ → ℝ} {b s t : ℝ} {K : ℕ} {x : ℤ → ℂ}
    (hq : ∀ n, 0 < q n) (hb : 0 < b) (hbase : ∀ n : ℤ, (K : ℝ) < |(n : ℝ)| → b ≤ q n)
    (hst : t ≤ s) (hx : Summable fun n => (q n) ^ s * ‖x n‖ ^ 2) :
    Summable (fun n : ℤ => if (K : ℝ) < |(n : ℝ)| then (q n) ^ t * ‖x n‖ ^ 2 else 0) ∧
    (∑' n : ℤ, if (K : ℝ) < |(n : ℝ)| then (q n) ^ t * ‖x n‖ ^ 2 else 0) ≤
      b ^ (t - s) * ∑' n : ℤ, (q n) ^ s * ‖x n‖ ^ 2 := by
  have hnonneg : ∀ n : ℤ, 0 ≤ (if (K : ℝ) < |(n : ℝ)| then (q n) ^ t * ‖x n‖ ^ 2 else 0) := by
    intro n
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (hq n).le _) (sq_nonneg _)
    · exact le_rfl
  have hle : ∀ n : ℤ,
      (if (K : ℝ) < |(n : ℝ)| then (q n) ^ t * ‖x n‖ ^ 2 else 0) ≤
        b ^ (t - s) * ((q n) ^ s * ‖x n‖ ^ 2) := by
    intro n
    split_ifs with hn
    · calc
        (q n) ^ t * ‖x n‖ ^ 2 ≤ (b ^ (t - s) * (q n) ^ s) * ‖x n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (root01_weight_ratio hb (hbase n hn) hst) (sq_nonneg _)
        _ = _ := by ring
    · exact mul_nonneg (Real.rpow_nonneg hb.le _)
        (mul_nonneg (Real.rpow_nonneg (hq n).le _) (sq_nonneg _))
  have hsum := Summable.of_nonneg_of_le hnonneg hle (hx.mul_left (b ^ (t - s)))
  exact ⟨hsum, (hsum.tsum_le_tsum hle (hx.mul_left _)).trans_eq (tsum_mul_left)⟩

/-- Exact DEF-002 tail factor, valid for every real exponent and every integer cutoff. -/
theorem root01_def002_tail {L s t : ℝ} (hL : 0 < L) (hst : t ≤ s)
    (K : ℕ) {x : ℤ → ℂ} (hx : MemHs L s x) :
    (∑' n : ℤ, if (K : ℝ) < |(n : ℝ)| then sobolevWeight L t n * ‖x n‖ ^ 2 else 0) ≤
      (1 + 2 * Real.pi * K / L) ^ (2 * (t - s)) * hsNormSq L s x := by
  apply (root01_weighted_tail (q := fun n => 1 + |2 * Real.pi * (n : ℝ) / L|)
    (b := 1 + 2 * Real.pi * K / L) (s := 2 * s) (t := 2 * t)
    (fun n => by positivity) (by positivity) ?_ (by linarith) hx).2.trans_eq
  · congr 2; ring
  · intro n hn
    have he : |2 * Real.pi * (n : ℝ) / L| = (2 * Real.pi / L) * |(n : ℝ)| := by
      rw [abs_div, abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos), abs_of_pos hL]
      ring
    rw [he]
    have hc : 0 ≤ 2 * Real.pi / L := by positivity
    calc
      1 + 2 * Real.pi * K / L = 1 + (2 * Real.pi / L) * K := by ring
      _ ≤ 1 + (2 * Real.pi / L) * |(n : ℝ)| :=
        add_le_add_right (mul_le_mul_of_nonneg_left hn.le hc) 1

/-- Exact F04 bracket tail factor, kept separate from the DEF-002 factor. -/
theorem root01_f04_tail {L s t : ℝ} (hst : t ≤ s)
    (K : ℕ) {x : ℤ → ℂ} (hx : Mem04 L s x) :
    (∑' n : ℤ, if (K : ℝ) < |(n : ℝ)| then f04Weight L t n * ‖x n‖ ^ 2 else 0) ≤
      (1 + (2 * Real.pi * K / L) ^ 2) ^ (t - s) * f04NormSq L s x := by
  apply (root01_weighted_tail (q := fun n => 1 + (freq L n) ^ 2)
    (b := 1 + (2 * Real.pi * K / L) ^ 2) (fun n => by positivity) (by positivity)
    ?_ hst hx).2
  intro n hn
  have hsq : (K : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (|(n : ℝ)| - K), sq_abs (n : ℝ), abs_nonneg (n : ℝ),
      (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  dsimp [freq]
  have := mul_le_mul_of_nonneg_left hsq (sq_nonneg (2 * Real.pi / L))
  convert add_le_add_left this 1 using 1 <;> ring

/-- The reused normalized Fourier map retains the full L2 norm. -/
theorem root01_parseval {L : ℝ} [Fact (0 < L)]
    (u : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (AddCircle L))) :
    hsNormSq L 0 (fourierL2 L u) = ‖u‖ ^ 2 := hsNormSq_zero_fourierL2 L u
/-- Weighted truncation density follows by transporting the unconditional
single-coordinate expansion through the accepted weighted Fourier isometry. -/
theorem root01_weighted_density (W : QuantumNLS.Sobolev.PosWeight)
    (x : QuantumNLS.Sobolev.PosWeight.WSeq W) :
    HasSum (fun n : ℤ => (QuantumNLS.Sobolev.PosWeight.toL2ᵢ W).symm
      (lp.single 2 n ((QuantumNLS.Sobolev.PosWeight.toL2ᵢ W x) n))) x := by
  let e := QuantumNLS.Sobolev.PosWeight.toL2ᵢ W
  have h := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (e x)).mapL
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  change HasSum (fun n : ℤ => e.symm (lp.single 2 n ((e x) n))) (e.symm (e x)) at h
  simpa only [LinearIsometryEquiv.symm_apply_apply] using h

/-- Exact comparison of the two declared norms, with constants 1 and 2^(s/2). -/
theorem root01_norm_comparison (L : ℝ) {s : ℝ} (hs : 0 ≤ s)
    (x : QuantumNLS.Sobolev.h02 L s) :
    ‖QuantumNLS.Sobolev.h02EquivH04 L hs x‖ ≤ ‖x‖ ∧
      ‖x‖ ≤ (2 : ℝ) ^ (s / 2) * ‖QuantumNLS.Sobolev.h02EquivH04 L hs x‖ := by
  constructor
  · exact QuantumNLS.Sobolev.norm_h02EquivH04_le L hs x
  · have hp : Real.sqrt ((2 : ℝ) ^ s) = (2 : ℝ) ^ (s / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    simpa only [ContinuousLinearEquiv.symm_apply_apply, hp] using
      QuantumNLS.Sobolev.norm_h02EquivH04_symm_le L hs
        (QuantumNLS.Sobolev.h02EquivH04 L hs x)

end QuantumNLS.Ext025A2
#print axioms QuantumNLS.Ext025A2.root01_weight_ratio
#print axioms QuantumNLS.Ext025A2.root01_weighted_tail
#print axioms QuantumNLS.Ext025A2.root01_def002_tail
#print axioms QuantumNLS.Ext025A2.root01_f04_tail
#print axioms QuantumNLS.Ext025A2.root01_parseval

#print axioms QuantumNLS.Ext025A2.root01_weighted_density
#print axioms QuantumNLS.Ext025A2.root01_norm_comparison
