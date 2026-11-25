import NlsGge.GK38.Lib.InterpolationHilbertOp
import NlsGge.Atomic.KST.KST005
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.PSeries

/-!
# GK Lemma C.1: paired perturbed factors

The two opposite lattice factors are combined before estimating them.  In
particular, the spectral parameter cancels from the linear part of a pair.
The remaining linear coefficient is an ℓ² pairing with the reciprocal
lattice, and the quadratic part is absolutely summable.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.Atomic.G2

open Filter Topology
open NlsGge.GK38.Lib

/-- The perturbation at a nonzero integer spectral label. -/
def perturbedFactor (s : L2Z) (lam : ℂ) (k : ℤ) : ℂ :=
  (s k - lam) / ((k : ℂ) * (Real.pi : ℂ))

/-- The symmetrically paired error at a positive lattice label. -/
def pairedFactorError (s : L2Z) (lam : ℂ) (m : ℕ+) : ℂ :=
  perturbedFactor s lam (m : ℤ) + perturbedFactor s lam (-(m : ℤ)) +
    perturbedFactor s lam (m : ℤ) * perturbedFactor s lam (-(m : ℤ))

private def positiveRay (s : L2Z) : lp (fun _ : ℕ+ => ℂ) 2 :=
  ⟨fun m => s (m : ℤ), by
    have hsq : Summable (fun k : ℤ => ‖s k‖ ^ 2) := summable_sq_lp s
    have hpos : Summable (fun m : ℕ+ => ‖s (m : ℤ)‖ ^ 2) :=
      hsq.comp_injective (i := fun m : ℕ+ => (m : ℤ)) (by
        intro a b hab
        exact PNat.coe_injective (Int.ofNat.inj hab))
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hpos⟩

private def negativeRay (s : L2Z) : lp (fun _ : ℕ+ => ℂ) 2 :=
  ⟨fun m => s (-(m : ℤ)), by
    have hsq : Summable (fun k : ℤ => ‖s k‖ ^ 2) := summable_sq_lp s
    have hneg : Summable (fun m : ℕ+ => ‖s (-(m : ℤ))‖ ^ 2) :=
      hsq.comp_injective (i := fun m : ℕ+ => -(m : ℤ)) (by
        intro a b hab
        exact PNat.coe_injective (Int.ofNat.inj (neg_injective hab)))
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hneg⟩

private theorem reciprocal_sq_summable :
    Summable (fun m : ℕ+ => 1 / ((m : ℝ) ^ 2)) := by
  have hInt : Summable (fun k : ℤ => 1 / ((k : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  have hpos : Summable (fun m : ℕ+ => 1 / (((m : ℤ) : ℝ) ^ 2)) :=
    hInt.comp_injective (i := fun m : ℕ+ => (m : ℤ)) (by
      intro a b hab
      exact PNat.coe_injective (Int.ofNat.inj hab))
  exact hpos.congr fun m => by simp [Int.cast_natCast]

private def reciprocalRay : lp (fun _ : ℕ+ => ℂ) 2 :=
  ⟨fun m => (((m : ℝ)⁻¹ : ℝ) : ℂ), by
    have hpos := reciprocal_sq_summable
    have hposNorm : Summable (fun m : ℕ+ => ‖(((m : ℝ)⁻¹ : ℝ) : ℂ)‖ ^ 2) := by
      apply hpos.congr
      intro m
      simp [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity)), inv_pow,
        one_div]
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hposNorm⟩

private theorem positiveRay_norm_le (s : L2Z) : ‖positiveRay s‖ ≤ ‖s‖ := by
  have hsq : Summable (fun k : ℤ => ‖s k‖ ^ 2) := summable_sq_lp s
  let i : ℕ+ → ℤ := fun m => (m : ℤ)
  have hi : Function.Injective i := by
    intro a b hab
    exact PNat.coe_injective (Int.ofNat.inj hab)
  have hRaySq : Summable (fun m : ℕ+ => ‖s (m : ℤ)‖ ^ 2) :=
    hsq.comp_injective (i := i) hi
  have hsum : (∑' m : ℕ+, ‖s (m : ℤ)‖ ^ 2) ≤ ∑' k : ℤ, ‖s k‖ ^ 2 := by
    exact hRaySq.tsum_le_tsum_of_inj i hi (fun _ _ => sq_nonneg _) (fun _ => le_rfl) hsq
  have hnorm : ‖positiveRay s‖ ^ 2 ≤ ‖s‖ ^ 2 := by
    calc
      ‖positiveRay s‖ ^ 2 = ∑' m : ℕ+, ‖positiveRay s m‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum (by norm_num) (positiveRay s)
      _ = ∑' m : ℕ+, ‖s (m : ℤ)‖ ^ 2 := by
        apply tsum_congr
        intro m
        rfl
      _ ≤ ∑' k : ℤ, ‖s k‖ ^ 2 := hsum
      _ = ‖s‖ ^ 2 := by
        symm
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum (by norm_num) s
  nlinarith [norm_nonneg (positiveRay s), norm_nonneg s]

private theorem negativeRay_norm_le (s : L2Z) : ‖negativeRay s‖ ≤ ‖s‖ := by
  have hsq : Summable (fun k : ℤ => ‖s k‖ ^ 2) := summable_sq_lp s
  let i : ℕ+ → ℤ := fun m => -(m : ℤ)
  have hi : Function.Injective i := by
    intro a b hab
    exact PNat.coe_injective (Int.ofNat.inj (neg_injective hab))
  have hRaySq : Summable (fun m : ℕ+ => ‖s (-(m : ℤ))‖ ^ 2) :=
    hsq.comp_injective (i := i) hi
  have hsum : (∑' m : ℕ+, ‖s (-(m : ℤ))‖ ^ 2) ≤ ∑' k : ℤ, ‖s k‖ ^ 2 := by
    exact hRaySq.tsum_le_tsum_of_inj i hi (fun _ _ => sq_nonneg _) (fun _ => le_rfl) hsq
  have hnorm : ‖negativeRay s‖ ^ 2 ≤ ‖s‖ ^ 2 := by
    calc
      ‖negativeRay s‖ ^ 2 = ∑' m : ℕ+, ‖negativeRay s m‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum (by norm_num) (negativeRay s)
      _ = ∑' m : ℕ+, ‖s (-(m : ℤ))‖ ^ 2 := by
        apply tsum_congr
        intro m
        rfl
      _ ≤ ∑' k : ℤ, ‖s k‖ ^ 2 := hsum
      _ = ‖s‖ ^ 2 := by
        symm
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum (by norm_num) s
  nlinarith [norm_nonneg (negativeRay s), norm_nonneg s]

private def reciprocalTailSq (N : ℕ) : ℝ :=
  ∑' m : ℕ+, if N < (m : ℕ) then 1 / ((m : ℝ) ^ 2) else 0

private def reciprocalTailRay (N : ℕ) : lp (fun _ : ℕ+ => ℂ) 2 :=
  ⟨fun m => if N < (m : ℕ) then (((m : ℝ)⁻¹ : ℝ) : ℂ) else 0, by
    have hsq : Summable (fun m : ℕ+ =>
        ‖if N < (m : ℕ) then (((m : ℝ)⁻¹ : ℝ) : ℂ) else 0‖ ^ 2) := by
      apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun m => by
        by_cases hm : N < (m : ℕ)
        · simp [hm, abs_of_nonneg (inv_nonneg.mpr (by positivity)), inv_pow, one_div]
        · simp [hm]) reciprocal_sq_summable
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hsq⟩

private theorem reciprocalTailSq_nonneg (N : ℕ) : 0 ≤ reciprocalTailSq N := by
  apply tsum_nonneg
  intro m
  split_ifs <;> positivity

private theorem reciprocalTailRay_norm (N : ℕ) :
    ‖reciprocalTailRay N‖ = Real.sqrt (reciprocalTailSq N) := by
  have hnormSq : ‖reciprocalTailRay N‖ ^ 2 = reciprocalTailSq N := by
    calc
      ‖reciprocalTailRay N‖ ^ 2 =
          ∑' m : ℕ+, ‖reciprocalTailRay N m‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum (by norm_num) (reciprocalTailRay N)
      _ = reciprocalTailSq N := by
        apply tsum_congr
        intro m
        by_cases hm : N < (m : ℕ)
        · simp [reciprocalTailRay, reciprocalTailSq, hm,
            abs_of_nonneg (inv_nonneg.mpr (by positivity)), inv_pow, one_div]
        · simp [reciprocalTailRay, reciprocalTailSq, hm]
  have hsq : ‖reciprocalTailRay N‖ ^ 2 = (Real.sqrt (reciprocalTailSq N)) ^ 2 := by
    rw [Real.sq_sqrt (reciprocalTailSq_nonneg N)]
    exact hnormSq
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1 hsq

private theorem reciprocalTailSq_tendsto_zero :
    Tendsto reciprocalTailSq atTop (𝓝 0) := by
  let base : ℕ → ℝ := fun n => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)
  let tail : ℕ → ℕ → ℝ := fun N n => if N ≤ n then base n else 0
  have hbase : Summable base := by
    have h0 : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
      (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
    simpa [base, Nat.cast_add] using
      (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ) ^ 2)) 1).2 h0
  have htail (N : ℕ) : Summable (tail N) := by
    apply Summable.of_nonneg_of_le (fun n => by
      simp only [tail]
      split_ifs <;> positivity) (fun n => by
        simp only [tail]
        split_ifs with h
        · exact le_rfl
        · positivity) hbase
  have hrepr (N : ℕ) : reciprocalTailSq N = ∑' n : ℕ, tail N n := by
    have hpnat := tsum_pnat_eq_tsum_succ
      (f := fun k : ℕ => if N < k then 1 / ((k : ℝ) ^ 2) else 0)
    unfold reciprocalTailSq tail base
    calc
      _ = ∑' n : ℕ, (if N < n + 1 then 1 / (((n + 1 : ℕ) : ℝ) ^ 2) else 0) := by
        simpa [Nat.cast_add] using hpnat
      _ = ∑' n : ℕ, (if N ≤ n then 1 / (((n + 1 : ℕ) : ℝ) ^ 2) else 0) := by
        apply tsum_congr
        intro n
        simp [Nat.lt_succ_iff]
  have hshift (N : ℕ) :
      (∑' n : ℕ, tail N n) = ∑' n : ℕ, base (n + N) := by
    have hdecomp := (htail N).sum_add_tsum_nat_add N
    have hprefix : (∑ i ∈ Finset.range N, tail N i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : i < N := Finset.mem_range.mp hi
      simp [tail, Nat.not_le_of_gt hi']
    calc
      _ = (∑ i ∈ Finset.range N, tail N i) + ∑' n : ℕ, tail N (n + N) :=
        hdecomp.symm
      _ = ∑' n : ℕ, base (n + N) := by
        rw [hprefix, zero_add]
        congr 1
        funext n
        simp [tail, Nat.le_add_left]
  have hlim := tendsto_sum_nat_add base
  apply hlim.congr'
  filter_upwards [eventually_atTop.2 ⟨0, fun N _ => hrepr N⟩] with N hN
  rw [hN, hshift]

private theorem reciprocal_linear_summable (s : L2Z) :
    Summable (fun m : ℕ+ => ‖s (m : ℤ)‖ / (m : ℝ)) := by
  have h := lp.summable_mul (by rw [Real.holderConjugate_iff]; norm_num)
    (positiveRay s) reciprocalRay
  apply h.congr
  intro m
  change ‖s (m : ℤ)‖ * ‖(((m : ℝ)⁻¹ : ℝ) : ℂ)‖ =
    ‖s (m : ℤ)‖ / (m : ℝ)
  simp [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity)),
    div_eq_mul_inv]

private theorem reciprocal_negative_linear_summable (s : L2Z) :
    Summable (fun m : ℕ+ => ‖s (-(m : ℤ))‖ / (m : ℝ)) := by
  have h := lp.summable_mul (by rw [Real.holderConjugate_iff]; norm_num)
    (negativeRay s) reciprocalRay
  apply h.congr
  intro m
  change ‖s (-(m : ℤ))‖ * ‖(((m : ℝ)⁻¹ : ℝ) : ℂ)‖ =
    ‖s (-(m : ℤ))‖ / (m : ℝ)
  simp [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity)),
    div_eq_mul_inv]

private theorem paired_cross_summable (s : L2Z) :
    Summable (fun m : ℕ+ => ‖s (m : ℤ)‖ * ‖s (-(m : ℤ))‖) := by
  have h := lp.summable_mul (by rw [Real.holderConjugate_iff]; norm_num)
    (positiveRay s) (negativeRay s)
  apply h.congr
  intro m
  change ‖s (m : ℤ)‖ * ‖s (-(m : ℤ))‖ =
    ‖s (m : ℤ)‖ * ‖s (-(m : ℤ))‖
  rfl

private theorem pairedFactorError_cancel (s : L2Z) (lam : ℂ) (m : ℕ+) :
    pairedFactorError s lam m =
      (s (m : ℤ) - s (-(m : ℤ))) / (((m : ℤ) : ℂ) * (Real.pi : ℂ)) +
        ((s (m : ℤ) - lam) * (s (-(m : ℤ)) - lam) /
          (-(((m : ℤ) : ℂ) * (Real.pi : ℂ)) ^ 2)) := by
  unfold pairedFactorError perturbedFactor
  have hm : ((m : ℤ) : ℂ) * (Real.pi : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (show (m : ℕ) ≠ 0 by exact m.property.ne')
    · exact_mod_cast Real.pi_ne_zero
  have hnegDen : (-(m : ℤ) : ℂ) * (Real.pi : ℂ) = -(((m : ℤ) : ℂ) * (Real.pi : ℂ)) := by
    push_cast
    ring
  simp only [Int.cast_neg]
  rw [hnegDen]
  field_simp [hm]
  ring_nf

private theorem pairedFactorError_norm_le (s : L2Z) (lam : ℂ) (m : ℕ+) :
    ‖pairedFactorError s lam m‖ ≤
      ‖s (m : ℤ)‖ / (m : ℝ) + ‖s (-(m : ℤ))‖ / (m : ℝ) +
        (‖s (m : ℤ)‖ + ‖lam‖) * (‖s (-(m : ℤ))‖ + ‖lam‖) /
          ((m : ℝ) ^ 2) := by
  rw [pairedFactorError_cancel]
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast m.property
  have hlin : ‖(s (m : ℤ) - s (-(m : ℤ))) / (((m : ℤ) : ℂ) * (Real.pi : ℂ))‖ ≤
      ‖s (m : ℤ)‖ / (m : ℝ) + ‖s (-(m : ℤ))‖ / (m : ℝ) := by
    rw [norm_div]
    have hnormDen : ‖((m : ℤ) : ℂ) * (Real.pi : ℂ)‖ = (m : ℝ) * Real.pi := by
      simp [Complex.norm_intCast, Complex.norm_real,
        abs_of_nonneg (show 0 ≤ (m : ℝ) by positivity), Int.cast_natCast]
    rw [hnormDen]
    have hden : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hnum := norm_sub_le (s (m : ℤ)) (s (-(m : ℤ)))
    calc
      ‖s (m : ℤ) - s (-(m : ℤ))‖ / ((m : ℝ) * Real.pi) ≤
          (‖s (m : ℤ)‖ + ‖s (-(m : ℤ))‖) / ((m : ℝ) * Real.pi) := by
        exact div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (‖s (m : ℤ)‖ + ‖s (-(m : ℤ))‖) / (m : ℝ) := by
        apply div_le_div_of_nonneg_left (by positivity) hmpos
        nlinarith [hden, hmpos]
      _ = _ := by ring
  have hquad :
      ‖((s (m : ℤ) - lam) * (s (-(m : ℤ)) - lam) /
          (-(((m : ℤ) : ℂ) * (Real.pi : ℂ)) ^ 2))‖ ≤
        (‖s (m : ℤ)‖ + ‖lam‖) * (‖s (-(m : ℤ))‖ + ‖lam‖) /
          ((m : ℝ) ^ 2) := by
    rw [norm_div]
    have hnormDen : ‖-(((m : ℤ) : ℂ) * (Real.pi : ℂ)) ^ 2‖ =
        (m : ℝ) ^ 2 * Real.pi ^ 2 := by
      rw [norm_neg, norm_pow, norm_mul, Complex.norm_intCast, Complex.norm_real]
      simp [abs_of_nonneg (show 0 ≤ (m : ℝ) by positivity),
        abs_of_pos Real.pi_pos, Int.cast_natCast]
      ring
    rw [hnormDen]
    have hnum : ‖(s (m : ℤ) - lam) * (s (-(m : ℤ)) - lam)‖ ≤
        (‖s (m : ℤ)‖ + ‖lam‖) * (‖s (-(m : ℤ))‖ + ‖lam‖) := by
      rw [norm_mul]
      exact mul_le_mul (norm_sub_le _ _) (norm_sub_le _ _)
        (norm_nonneg (s (-(m : ℤ)) - lam)) (by positivity)
    have hm2 : 0 < (m : ℝ) ^ 2 := by positivity
    have hpi2 : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    calc
      ‖(s (m : ℤ) - lam) * (s (-(m : ℤ)) - lam)‖ /
          ((m : ℝ) ^ 2 * Real.pi ^ 2) ≤
          ((‖s (m : ℤ)‖ + ‖lam‖) * (‖s (-(m : ℤ))‖ + ‖lam‖)) /
            ((m : ℝ) ^ 2 * Real.pi ^ 2) := by gcongr
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by positivity) hm2
        nlinarith [hpi2, hm2]
  exact (norm_add_le _ _).trans (add_le_add hlin hquad)

private def pairedFactorMajorant (s : L2Z) (lam : ℂ) (m : ℕ+) : ℝ :=
  ‖s (m : ℤ)‖ / (m : ℝ) + ‖s (-(m : ℤ))‖ / (m : ℝ) +
    ‖s (m : ℤ)‖ * ‖s (-(m : ℤ))‖ +
      ‖lam‖ * ‖s (m : ℤ)‖ / (m : ℝ) +
        ‖lam‖ * ‖s (-(m : ℤ))‖ / (m : ℝ) + ‖lam‖ ^ 2 / ((m : ℝ) ^ 2)

private theorem pairedFactorMajorant_summable (s : L2Z) (lam : ℂ) :
    Summable (fun m : ℕ+ => pairedFactorMajorant s lam m) := by
  have hpos := reciprocal_linear_summable s
  have hneg := reciprocal_negative_linear_summable s
  have hab := paired_cross_summable s
  have hinv := reciprocal_sq_summable
  have hLamPos : Summable (fun m : ℕ+ => ‖lam‖ * ‖s (m : ℤ)‖ / (m : ℝ)) := by
    apply (hpos.mul_left ‖lam‖).congr
    intro m
    ring
  have hLamNeg : Summable (fun m : ℕ+ => ‖lam‖ * ‖s (-(m : ℤ))‖ / (m : ℝ)) := by
    apply (hneg.mul_left ‖lam‖).congr
    intro m
    ring
  have hLamSq : Summable (fun m : ℕ+ => ‖lam‖ ^ 2 / ((m : ℝ) ^ 2)) := by
    apply (hinv.mul_left (‖lam‖ ^ 2)).congr
    intro m
    ring
  have hs := hpos.add hneg |>.add hab |>.add hLamPos |>.add hLamNeg |>.add hLamSq
  apply hs.congr
  intro m
  dsimp [pairedFactorMajorant]

private theorem pairedFactorError_majorized (s : L2Z) (lam : ℂ) (m : ℕ+) :
    ‖pairedFactorError s lam m‖ ≤ pairedFactorMajorant s lam m := by
  have hbase := pairedFactorError_norm_le s lam m
  have hm : 1 ≤ (m : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr m.property.ne')
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast m.property
  have hA : 0 ≤ ‖s (m : ℤ)‖ := norm_nonneg _
  have hB : 0 ≤ ‖s (-(m : ℤ))‖ := norm_nonneg _
  have hL : 0 ≤ ‖lam‖ := norm_nonneg _
  have hA2 : 0 ≤ ‖s (m : ℤ)‖ * ‖s (-(m : ℤ))‖ := mul_nonneg hA hB
  have hLA : 0 ≤ ‖lam‖ * ‖s (m : ℤ)‖ := mul_nonneg hL hA
  have hLB : 0 ≤ ‖lam‖ * ‖s (-(m : ℤ))‖ := mul_nonneg hL hB
  have hden : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith [hm]
  have hA2' : ‖s (m : ℤ)‖ * ‖s (-(m : ℤ))‖ / (m : ℝ) ^ 2 ≤
      ‖s (m : ℤ)‖ * ‖s (-(m : ℤ))‖ := by
    apply div_le_self hA2
    nlinarith [hm]
  have hLA' : ‖lam‖ * ‖s (m : ℤ)‖ / (m : ℝ) ^ 2 ≤
      ‖lam‖ * ‖s (m : ℤ)‖ / (m : ℝ) := by
    apply div_le_div_of_nonneg_left hLA hmpos
    exact hden
  have hLB' : ‖lam‖ * ‖s (-(m : ℤ))‖ / (m : ℝ) ^ 2 ≤
      ‖lam‖ * ‖s (-(m : ℤ))‖ / (m : ℝ) := by
    apply div_le_div_of_nonneg_left hLB hmpos
    exact hden
  have hExpand :
      (‖s (m : ℤ)‖ + ‖lam‖) * (‖s (-(m : ℤ))‖ + ‖lam‖) /
          (m : ℝ) ^ 2 =
        ‖s (m : ℤ)‖ * ‖s (-(m : ℤ))‖ / (m : ℝ) ^ 2 +
          ‖lam‖ * ‖s (m : ℤ)‖ / (m : ℝ) ^ 2 +
            ‖lam‖ * ‖s (-(m : ℤ))‖ / (m : ℝ) ^ 2 +
              ‖lam‖ ^ 2 / (m : ℝ) ^ 2 := by
    field_simp [ne_of_gt hmpos]
    ring
  rw [hExpand] at hbase
  have hQuad :
      ‖s (m : ℤ)‖ * ‖s (-(m : ℤ))‖ / (m : ℝ) ^ 2 +
          ‖lam‖ * ‖s (m : ℤ)‖ / (m : ℝ) ^ 2 +
            ‖lam‖ * ‖s (-(m : ℤ))‖ / (m : ℝ) ^ 2 +
              ‖lam‖ ^ 2 / (m : ℝ) ^ 2 ≤
        ‖s (m : ℤ)‖ * ‖s (-(m : ℤ))‖ +
          ‖lam‖ * ‖s (m : ℤ)‖ / (m : ℝ) +
            ‖lam‖ * ‖s (-(m : ℤ))‖ / (m : ℝ) +
              ‖lam‖ ^ 2 / (m : ℝ) ^ 2 := by
    linarith [hA2', hLA', hLB']
  dsimp [pairedFactorMajorant]
  calc
    ‖pairedFactorError s lam m‖ ≤
        ‖s (m : ℤ)‖ / (m : ℝ) + ‖s (-(m : ℤ))‖ / (m : ℝ) +
          (‖s (m : ℤ)‖ * ‖s (-(m : ℤ))‖ / (m : ℝ) ^ 2 +
            ‖lam‖ * ‖s (m : ℤ)‖ / (m : ℝ) ^ 2 +
              ‖lam‖ * ‖s (-(m : ℤ))‖ / (m : ℝ) ^ 2 +
                ‖lam‖ ^ 2 / (m : ℝ) ^ 2) := hbase
    _ ≤ _ := by
      simpa [add_assoc] using hQuad

/-- The opposite-index linear terms cancel their common spectral shift, leaving
an ℓ² pairing with `1/m`; the remaining product is absolutely summable. -/
theorem paired_product_summable (s : L2Z) (lam : ℂ) :
    Summable (fun m : ℕ+ => ‖pairedFactorError s lam m‖) := by
  apply Summable.of_nonneg_of_le (fun m => norm_nonneg _)
    (fun m => pairedFactorError_majorized s lam m)
  exact pairedFactorMajorant_summable s lam

private def positiveLinearTail (N : ℕ) (s : L2Z) (m : ℕ+) : ℝ :=
  if N < (m : ℕ) then ‖s (m : ℤ)‖ / (m : ℝ) else 0

private def negativeLinearTail (N : ℕ) (s : L2Z) (m : ℕ+) : ℝ :=
  if N < (m : ℕ) then ‖s (-(m : ℤ))‖ / (m : ℝ) else 0

private def crossTail (N : ℕ) (s : L2Z) (m : ℕ+) : ℝ :=
  if N < (m : ℕ) then ‖s (m : ℤ)‖ * ‖s (-(m : ℤ))‖ else 0

private theorem positiveLinearTail_summable (N : ℕ) (s : L2Z) :
    Summable (positiveLinearTail N s) := by
  have hm0 (m : ℕ+) : (0 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.zero_le (m : ℕ))
  apply Summable.of_nonneg_of_le (fun m => by
    by_cases hm : N < (m : ℕ)
    · simpa [positiveLinearTail, hm] using
        (div_nonneg (norm_nonneg (s (m : ℤ))) (hm0 m))
    · simp [positiveLinearTail, hm]) (fun m => by
    by_cases hm : N < (m : ℕ)
    · simp [positiveLinearTail, hm]
    · simpa [positiveLinearTail, hm] using
        (div_nonneg (norm_nonneg (s (m : ℤ))) (hm0 m)))
    (reciprocal_linear_summable s)

private theorem negativeLinearTail_summable (N : ℕ) (s : L2Z) :
    Summable (negativeLinearTail N s) := by
  have hm0 (m : ℕ+) : (0 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.zero_le (m : ℕ))
  apply Summable.of_nonneg_of_le (fun m => by
    by_cases hm : N < (m : ℕ)
    · simpa [negativeLinearTail, hm] using
        (div_nonneg (norm_nonneg (s (-(m : ℤ)))) (hm0 m))
    · simp [negativeLinearTail, hm]) (fun m => by
    by_cases hm : N < (m : ℕ)
    · simp [negativeLinearTail, hm]
    · simpa [negativeLinearTail, hm] using
        (div_nonneg (norm_nonneg (s (-(m : ℤ)))) (hm0 m)))
    (reciprocal_negative_linear_summable s)

private theorem crossTail_summable (N : ℕ) (s : L2Z) :
    Summable (crossTail N s) := by
  apply Summable.of_nonneg_of_le (fun m => by
    by_cases hm : N < (m : ℕ)
    · simpa [crossTail, hm] using mul_nonneg (norm_nonneg (s (m : ℤ)))
        (norm_nonneg (s (-(m : ℤ))))
    · simp [crossTail, hm]) (fun m => by
    by_cases hm : N < (m : ℕ)
    · simp [crossTail, hm]
    · simpa [crossTail, hm] using mul_nonneg (norm_nonneg (s (m : ℤ)))
        (norm_nonneg (s (-(m : ℤ)))))
    (paired_cross_summable s)

private theorem positiveLinearTail_tsum_le (N : ℕ) (s : L2Z) :
    ∑' m : ℕ+, positiveLinearTail N s m ≤
      ‖s‖ * Real.sqrt (reciprocalTailSq N) := by
  have hHolder := lp.tsum_mul_le_mul_norm'
    (by rw [Real.holderConjugate_iff]; norm_num)
    (positiveRay s) (reciprocalTailRay N)
  calc
    ∑' m : ℕ+, positiveLinearTail N s m =
        ∑' m : ℕ+, ‖positiveRay s m‖ * ‖reciprocalTailRay N m‖ := by
      apply tsum_congr
      intro m
      by_cases hm : N < (m : ℕ)
      · simp [positiveLinearTail, positiveRay, reciprocalTailRay, hm,
          Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity)),
          div_eq_mul_inv]
      · simp [positiveLinearTail, reciprocalTailRay, hm]
    _ ≤ ‖positiveRay s‖ * ‖reciprocalTailRay N‖ := hHolder
    _ ≤ ‖s‖ * Real.sqrt (reciprocalTailSq N) := by
      rw [reciprocalTailRay_norm]
      exact mul_le_mul_of_nonneg_right (positiveRay_norm_le s)
        (Real.sqrt_nonneg _)

private theorem negativeLinearTail_tsum_le (N : ℕ) (s : L2Z) :
    ∑' m : ℕ+, negativeLinearTail N s m ≤
      ‖s‖ * Real.sqrt (reciprocalTailSq N) := by
  have hHolder := lp.tsum_mul_le_mul_norm'
    (by rw [Real.holderConjugate_iff]; norm_num)
    (negativeRay s) (reciprocalTailRay N)
  calc
    ∑' m : ℕ+, negativeLinearTail N s m =
        ∑' m : ℕ+, ‖negativeRay s m‖ * ‖reciprocalTailRay N m‖ := by
      apply tsum_congr
      intro m
      by_cases hm : N < (m : ℕ)
      · simp [negativeLinearTail, negativeRay, reciprocalTailRay, hm,
          Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity)),
          div_eq_mul_inv]
      · simp [negativeLinearTail, reciprocalTailRay, hm]
    _ ≤ ‖negativeRay s‖ * ‖reciprocalTailRay N‖ := hHolder
    _ ≤ ‖s‖ * Real.sqrt (reciprocalTailSq N) := by
      rw [reciprocalTailRay_norm]
      exact mul_le_mul_of_nonneg_right (negativeRay_norm_le s)
        (Real.sqrt_nonneg _)

private theorem crossTail_tsum_le (N : ℕ) (s : L2Z) :
    ∑' m : ℕ+, crossTail N s m ≤ ‖s‖ * ‖s‖ := by
  have hfull := paired_cross_summable s
  have hle : ∀ m : ℕ+, crossTail N s m ≤
      ‖s (m : ℤ)‖ * ‖s (-(m : ℤ))‖ := by
    intro m
    by_cases hm : N < (m : ℕ)
    · simp [crossTail, hm]
    · simpa [crossTail, hm] using mul_nonneg (norm_nonneg (s (m : ℤ)))
        (norm_nonneg (s (-(m : ℤ))))
  calc
    ∑' m : ℕ+, crossTail N s m ≤
        ∑' m : ℕ+, ‖s (m : ℤ)‖ * ‖s (-(m : ℤ))‖ := by
      exact (crossTail_summable N s).tsum_le_tsum hle hfull
    _ ≤ ‖positiveRay s‖ * ‖negativeRay s‖ := by
      have hHolder := lp.tsum_mul_le_mul_norm'
        (by rw [Real.holderConjugate_iff]; norm_num)
        (positiveRay s) (negativeRay s)
      simpa [positiveRay, negativeRay] using hHolder
    _ ≤ ‖s‖ * ‖s‖ := by
      exact mul_le_mul (positiveRay_norm_le s) (negativeRay_norm_le s)
        (norm_nonneg _) (norm_nonneg _)

private theorem reciprocalTailSq_summable (N : ℕ) :
    Summable (fun m : ℕ+ => if N < (m : ℕ) then 1 / ((m : ℝ) ^ 2) else 0) := by
  apply Summable.of_nonneg_of_le (fun m => by
    by_cases hm : N < (m : ℕ)
    · simpa [hm] using
        (div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (sq_nonneg (m : ℝ)))
    · simp [hm]) (fun m => by
    by_cases hm : N < (m : ℕ)
    · simp [hm]
    · simpa [hm] using
        (div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (sq_nonneg (m : ℝ))))
    reciprocal_sq_summable

private def pairedErrorTail (N : ℕ) (s : L2Z) (lam : ℂ) (m : ℕ+) : ℝ :=
  if N < (m : ℕ) then ‖pairedFactorError s lam m‖ else 0

private theorem pairedErrorTail_summable (N : ℕ) (s : L2Z) (lam : ℂ) :
    Summable (pairedErrorTail N s lam) := by
  apply Summable.of_nonneg_of_le (fun m => by
    by_cases hm : N < (m : ℕ)
    · simpa [pairedErrorTail, hm] using norm_nonneg (pairedFactorError s lam m)
    · simp [pairedErrorTail, hm]) (fun m => by
    by_cases hm : N < (m : ℕ)
    · simp [pairedErrorTail, hm]
    · simpa [pairedErrorTail, hm] using norm_nonneg (pairedFactorError s lam m))
    (paired_product_summable s lam)

private def reciprocalTailTerm (N : ℕ) (m : ℕ+) : ℝ :=
  if N < (m : ℕ) then 1 / ((m : ℝ) ^ 2) else 0

private def pairedErrorTailMajorant (N : ℕ) (s : L2Z) (lam : ℂ) (m : ℕ+) : ℝ :=
  positiveLinearTail N s m + negativeLinearTail N s m +
    crossTail N s m / (((N + 1 : ℕ) : ℝ) ^ 2) +
      (‖lam‖ / ((N + 1 : ℕ) : ℝ)) * positiveLinearTail N s m +
        (‖lam‖ / ((N + 1 : ℕ) : ℝ)) * negativeLinearTail N s m +
          ‖lam‖ ^ 2 * reciprocalTailTerm N m

private theorem pairedErrorTailMajorant_summable (N : ℕ) (s : L2Z) (lam : ℂ) :
    Summable (pairedErrorTailMajorant N s lam) := by
  have hrec := reciprocalTailSq_summable N
  have hrec' : Summable (fun m : ℕ+ => ‖lam‖ ^ 2 * reciprocalTailTerm N m) := by
    apply (hrec.mul_left (‖lam‖ ^ 2)).congr
    intro m
    rfl
  have hpos : Summable (fun m : ℕ+ =>
      (‖lam‖ / ((N + 1 : ℕ) : ℝ)) * positiveLinearTail N s m) :=
    (positiveLinearTail_summable N s).mul_left _
  have hneg : Summable (fun m : ℕ+ =>
      (‖lam‖ / ((N + 1 : ℕ) : ℝ)) * negativeLinearTail N s m) :=
    (negativeLinearTail_summable N s).mul_left _
  have hcross' : Summable (fun m : ℕ+ =>
      crossTail N s m / (((N + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (crossTail_summable N s).mul_left ((((N + 1 : ℕ) : ℝ) ^ 2)⁻¹)
  have hsum := (positiveLinearTail_summable N s).add
    (negativeLinearTail_summable N s) |>.add hcross' |>.add hpos |>.add hneg |>.add hrec'
  apply hsum.congr
  intro m
  simp [pairedErrorTailMajorant, reciprocalTailTerm, add_assoc]

private theorem pairedErrorTailMajorant_pointwise (N : ℕ) (s : L2Z) (lam : ℂ)
    (m : ℕ+) :
    pairedErrorTail N s lam m ≤ pairedErrorTailMajorant N s lam m := by
  by_cases hm : N < (m : ℕ)
  · have hbase := pairedFactorError_norm_le s lam m
    have hcpos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast m.property
    have hNm : (((N + 1 : ℕ) : ℝ)) ≤ (m : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hm
    have hA : 0 ≤ ‖s (m : ℤ)‖ := norm_nonneg _
    have hB : 0 ≤ ‖s (-(m : ℤ))‖ := norm_nonneg _
    have hL : 0 ≤ ‖lam‖ := norm_nonneg _
    have hdenSq : (((N + 1 : ℕ) : ℝ) ^ 2) ≤ (m : ℝ) ^ 2 := by
      nlinarith
    have hlinA : ‖s (m : ℤ)‖ / (m : ℝ) = positiveLinearTail N s m := by
      simp [positiveLinearTail, hm]
    have hlinB : ‖s (-(m : ℤ))‖ / (m : ℝ) = negativeLinearTail N s m := by
      simp [negativeLinearTail, hm]
    have hcross : ‖s (m : ℤ)‖ * ‖s (-(m : ℤ))‖ / ((m : ℝ) ^ 2) ≤
        crossTail N s m / (((N + 1 : ℕ) : ℝ) ^ 2) := by
      simp only [crossTail, if_pos hm]
      exact div_le_div_of_nonneg_left (mul_nonneg hA hB) (by positivity) hdenSq
    have hLA : ‖lam‖ * ‖s (m : ℤ)‖ / ((m : ℝ) ^ 2) ≤
        (‖lam‖ / ((N + 1 : ℕ) : ℝ)) * positiveLinearTail N s m := by
      simp only [positiveLinearTail, if_pos hm]
      have hden : (((N + 1 : ℕ) : ℝ)) * (m : ℝ) ≤ (m : ℝ) ^ 2 := by
        nlinarith [hNm, hmpos]
      calc
        ‖lam‖ * ‖s (m : ℤ)‖ / ((m : ℝ) ^ 2) ≤
            ‖lam‖ * ‖s (m : ℤ)‖ /
              ((((N + 1 : ℕ) : ℝ)) * (m : ℝ)) := by
          exact div_le_div_of_nonneg_left (mul_nonneg hL hA)
            (by positivity) hden
        _ = (‖lam‖ / ((N + 1 : ℕ) : ℝ)) *
              (‖s (m : ℤ)‖ / (m : ℝ)) := by
          field_simp [ne_of_gt hcpos, ne_of_gt hmpos]
    have hLB : ‖lam‖ * ‖s (-(m : ℤ))‖ / ((m : ℝ) ^ 2) ≤
        (‖lam‖ / ((N + 1 : ℕ) : ℝ)) * negativeLinearTail N s m := by
      simp only [negativeLinearTail, if_pos hm]
      have hden : (((N + 1 : ℕ) : ℝ)) * (m : ℝ) ≤ (m : ℝ) ^ 2 := by
        nlinarith [hNm, hmpos]
      calc
        ‖lam‖ * ‖s (-(m : ℤ))‖ / ((m : ℝ) ^ 2) ≤
            ‖lam‖ * ‖s (-(m : ℤ))‖ /
              ((((N + 1 : ℕ) : ℝ)) * (m : ℝ)) := by
          exact div_le_div_of_nonneg_left (mul_nonneg hL hB)
            (by positivity) hden
        _ = (‖lam‖ / ((N + 1 : ℕ) : ℝ)) *
              (‖s (-(m : ℤ))‖ / (m : ℝ)) := by
          field_simp [ne_of_gt hcpos, ne_of_gt hmpos]
    have hLL : ‖lam‖ ^ 2 / ((m : ℝ) ^ 2) =
        ‖lam‖ ^ 2 * reciprocalTailTerm N m := by
      simp [reciprocalTailTerm, hm, div_eq_mul_inv, pow_two]
    rw [pairedErrorTail, if_pos hm]
    rw [pairedErrorTailMajorant, ← hlinA, ← hlinB]
    have hexpand :
        (‖s (m : ℤ)‖ + ‖lam‖) * (‖s (-(m : ℤ))‖ + ‖lam‖) /
          ((m : ℝ) ^ 2) =
          ‖s (m : ℤ)‖ * ‖s (-(m : ℤ))‖ / ((m : ℝ) ^ 2) +
            ‖lam‖ * ‖s (m : ℤ)‖ / ((m : ℝ) ^ 2) +
              ‖lam‖ * ‖s (-(m : ℤ))‖ / ((m : ℝ) ^ 2) +
                ‖lam‖ ^ 2 / ((m : ℝ) ^ 2) := by
      field_simp [ne_of_gt hmpos]
      ring
    rw [hexpand] at hbase
    rw [hLL] at hbase
    rw [← hlinA] at hLA
    rw [← hlinB] at hLB
    linarith
  · simp [pairedErrorTail, pairedErrorTailMajorant, positiveLinearTail,
      negativeLinearTail, crossTail, reciprocalTailTerm, hm]

private theorem pairedErrorTail_tsum_le (N : ℕ) (s : L2Z) (lam : ℂ) :
    ∑' m : ℕ+, pairedErrorTail N s lam m ≤
      2 * ‖s‖ * Real.sqrt (reciprocalTailSq N) +
        (‖s‖ * ‖s‖) / (((N + 1 : ℕ) : ℝ) ^ 2) +
        2 * ‖lam‖ * ‖s‖ * Real.sqrt (reciprocalTailSq N) /
          ((N + 1 : ℕ) : ℝ) +
        ‖lam‖ ^ 2 * reciprocalTailSq N := by
  have hsum := pairedErrorTailMajorant_summable N s lam
  have htail := pairedErrorTail_summable N s lam
  have hmajor := htail.tsum_le_tsum
    (fun m => pairedErrorTailMajorant_pointwise N s lam m) hsum
  have hpos := positiveLinearTail_tsum_le N s
  have hneg := negativeLinearTail_tsum_le N s
  have hcross := crossTail_tsum_le N s
  let f₁ : ℕ+ → ℝ := positiveLinearTail N s
  let f₂ : ℕ+ → ℝ := negativeLinearTail N s
  let f₃ : ℕ+ → ℝ := fun m => crossTail N s m / (((N + 1 : ℕ) : ℝ) ^ 2)
  let c : ℝ := ‖lam‖ / ((N + 1 : ℕ) : ℝ)
  let f₄ : ℕ+ → ℝ := fun m => c * positiveLinearTail N s m
  let f₅ : ℕ+ → ℝ := fun m => c * negativeLinearTail N s m
  let f₆ : ℕ+ → ℝ := fun m => ‖lam‖ ^ 2 * reciprocalTailTerm N m
  have hf₁ : Summable f₁ := positiveLinearTail_summable N s
  have hf₂ : Summable f₂ := negativeLinearTail_summable N s
  have hf₃ : Summable f₃ := by
    apply ((crossTail_summable N s).mul_left
      ((((N + 1 : ℕ) : ℝ) ^ 2)⁻¹)).congr
    intro m
    simp [f₃, div_eq_mul_inv, mul_comm]
  have hf₄ : Summable f₄ := (positiveLinearTail_summable N s).mul_left c
  have hf₅ : Summable f₅ := (negativeLinearTail_summable N s).mul_left c
  have hf₆ : Summable f₆ := by
    apply ((reciprocalTailSq_summable N).mul_left (‖lam‖ ^ 2)).congr
    intro m
    rfl
  have hf₁₂ : Summable (fun m => f₁ m + f₂ m) := hf₁.add hf₂
  have hf₁₂₃ : Summable (fun m => f₁ m + f₂ m + f₃ m) := hf₁₂.add hf₃
  have hf₁₂₃₄ : Summable (fun m => f₁ m + f₂ m + f₃ m + f₄ m) := hf₁₂₃.add hf₄
  have hf₁₂₃₄₅ : Summable (fun m => f₁ m + f₂ m + f₃ m + f₄ m + f₅ m) :=
    hf₁₂₃₄.add hf₅
  have hmajor_sum :
      (∑' m : ℕ+, pairedErrorTailMajorant N s lam m) =
        (∑' m : ℕ+, f₁ m) + (∑' m : ℕ+, f₂ m) +
          (∑' m : ℕ+, f₃ m) + (∑' m : ℕ+, f₄ m) +
            (∑' m : ℕ+, f₅ m) + (∑' m : ℕ+, f₆ m) := by
    change tsum (fun i : ℕ+ => f₁ i + f₂ i + f₃ i + f₄ i + f₅ i + f₆ i) = _
    rw [Summable.tsum_add hf₁₂₃₄₅ hf₆,
      Summable.tsum_add hf₁₂₃₄ hf₅,
      Summable.tsum_add hf₁₂₃ hf₄,
      Summable.tsum_add hf₁₂ hf₃,
      Summable.tsum_add hf₁ hf₂]
  have h₃sum : (∑' m : ℕ+, f₃ m) =
      (((N + 1 : ℕ) : ℝ) ^ 2)⁻¹ * (∑' m : ℕ+, crossTail N s m) := by
    calc
      _ = ∑' m : ℕ+, (((N + 1 : ℕ) : ℝ) ^ 2)⁻¹ * crossTail N s m := by
        apply tsum_congr
        intro m
        simp [f₃, div_eq_mul_inv, mul_comm]
      _ = _ := (crossTail_summable N s).tsum_mul_left _
  have h₄sum : (∑' m : ℕ+, f₄ m) = c * (∑' m : ℕ+, positiveLinearTail N s m) :=
    (positiveLinearTail_summable N s).tsum_mul_left c
  have h₅sum : (∑' m : ℕ+, f₅ m) = c * (∑' m : ℕ+, negativeLinearTail N s m) :=
    (negativeLinearTail_summable N s).tsum_mul_left c
  have h₆sum : (∑' m : ℕ+, f₆ m) = ‖lam‖ ^ 2 * reciprocalTailSq N := by
    calc
      _ = ∑' m : ℕ+, ‖lam‖ ^ 2 * reciprocalTailTerm N m := by
        apply tsum_congr
        intro m
        rfl
      _ = ‖lam‖ ^ 2 * (∑' m : ℕ+, reciprocalTailTerm N m) :=
        (reciprocalTailSq_summable N).tsum_mul_left _
      _ = _ := by rfl
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hc2_nonneg : 0 ≤ (((N + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by positivity
  calc
    ∑' m : ℕ+, pairedErrorTail N s lam m ≤
        ∑' m : ℕ+, pairedErrorTailMajorant N s lam m := hmajor
    _ = (∑' m : ℕ+, f₁ m) + (∑' m : ℕ+, f₂ m) +
          (∑' m : ℕ+, f₃ m) + (∑' m : ℕ+, f₄ m) +
            (∑' m : ℕ+, f₅ m) + (∑' m : ℕ+, f₆ m) := hmajor_sum
    _ ≤ ‖s‖ * Real.sqrt (reciprocalTailSq N) +
          ‖s‖ * Real.sqrt (reciprocalTailSq N) +
          (((N + 1 : ℕ) : ℝ) ^ 2)⁻¹ * (‖s‖ * ‖s‖) +
          c * (‖s‖ * Real.sqrt (reciprocalTailSq N)) +
          c * (‖s‖ * Real.sqrt (reciprocalTailSq N)) +
          ‖lam‖ ^ 2 * reciprocalTailSq N := by
      rw [h₃sum, h₄sum, h₅sum, h₆sum]
      exact add_le_add (add_le_add (add_le_add (add_le_add
        (add_le_add hpos hneg)
        (mul_le_mul_of_nonneg_left hcross hc2_nonneg))
        (mul_le_mul_of_nonneg_left hpos hc_nonneg))
        (mul_le_mul_of_nonneg_left hneg hc_nonneg)) le_rfl
    _ = _ := by
      dsimp [c]
      ring


private def pairedErrorUniformBound (R : ℝ) (N : ℕ) : ℝ :=
  2 * R * Real.sqrt (reciprocalTailSq N) +
    R ^ 2 / (((N + 1 : ℕ) : ℝ) ^ 2) +
      2 * R ^ 2 * Real.sqrt (reciprocalTailSq N) / ((N + 1 : ℕ) : ℝ) +
        R ^ 2 * reciprocalTailSq N

private theorem pairedErrorTail_le_uniform_bound (R : ℝ) (hR : 0 ≤ R)
    (N : ℕ) (s : L2Z) (lam : ℂ) (hs : ‖s‖ ≤ R) (hl : ‖lam‖ ≤ R) :
    ∑' m : ℕ+, pairedErrorTail N s lam m ≤ pairedErrorUniformBound R N := by
  have hT : 0 ≤ reciprocalTailSq N := reciprocalTailSq_nonneg N
  have hroot : 0 ≤ Real.sqrt (reciprocalTailSq N) := Real.sqrt_nonneg _
  have hc : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
  have hs0 : 0 ≤ ‖s‖ := norm_nonneg _
  have hl0 : 0 ≤ ‖lam‖ := norm_nonneg _
  have hs2 : ‖s‖ ^ 2 ≤ R ^ 2 := by nlinarith
  have hsprod : ‖s‖ * ‖s‖ ≤ R ^ 2 := by nlinarith [hs2]
  have hl2 : ‖lam‖ ^ 2 ≤ R ^ 2 := by nlinarith
  have hprod : ‖lam‖ * ‖s‖ ≤ R ^ 2 := by nlinarith
  have hbase := pairedErrorTail_tsum_le N s lam
  unfold pairedErrorUniformBound
  calc
    ∑' m : ℕ+, pairedErrorTail N s lam m ≤
        2 * ‖s‖ * Real.sqrt (reciprocalTailSq N) +
          (‖s‖ * ‖s‖) / (((N + 1 : ℕ) : ℝ) ^ 2) +
          2 * ‖lam‖ * ‖s‖ * Real.sqrt (reciprocalTailSq N) /
            ((N + 1 : ℕ) : ℝ) +
          ‖lam‖ ^ 2 * reciprocalTailSq N := hbase
    _ ≤ 2 * R * Real.sqrt (reciprocalTailSq N) +
          R ^ 2 / (((N + 1 : ℕ) : ℝ) ^ 2) +
          2 * R ^ 2 * Real.sqrt (reciprocalTailSq N) /
            ((N + 1 : ℕ) : ℝ) +
          R ^ 2 * reciprocalTailSq N := by
      apply add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs (by norm_num)) hroot
      · exact div_le_div_of_nonneg_right hsprod (by positivity)
      · apply div_le_div_of_nonneg_right
        · have hstep := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ 2 by norm_num)) hroot
          nlinarith [hstep]
        · positivity
      · exact mul_le_mul_of_nonneg_right hl2 hT

private theorem pairedErrorUniformBound_tendsto (R : ℝ) :
    Tendsto (pairedErrorUniformBound R) atTop (𝓝 0) := by
  have hT := reciprocalTailSq_tendsto_zero
  have hroot : Tendsto (fun N => Real.sqrt (reciprocalTailSq N)) atTop (𝓝 0) := by
    have hcomp := Real.continuous_sqrt.continuousAt.tendsto.comp hT
    simpa only [Function.comp_def, Real.sqrt_zero] using hcomp
  have hinv : Tendsto (fun N : ℕ => 1 / (((N + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hinv2 : Tendsto (fun N : ℕ => 1 / (((N + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
    have hpow := hinv.pow 2
    simpa [div_eq_mul_inv, inv_pow, one_div] using hpow
  have hterm1 : Tendsto (fun N => 2 * R * Real.sqrt (reciprocalTailSq N))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := 2 * R)).mul hroot
  have hterm2 : Tendsto (fun N => R ^ 2 /
      (((N + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x := R ^ 2)).mul hinv2
  have hterm3 : Tendsto (fun N => 2 * R ^ 2 *
      Real.sqrt (reciprocalTailSq N) / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have hprod := hroot.mul hinv
    have hscaled := (tendsto_const_nhds (x := 2 * R ^ 2)).mul hprod
    simpa [div_eq_mul_inv, mul_assoc] using hscaled
  have hterm4 : Tendsto (fun N => R ^ 2 * reciprocalTailSq N) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := R ^ 2)).mul hT
  change Tendsto (fun N =>
    (2 * R * Real.sqrt (reciprocalTailSq N) +
      R ^ 2 / (((N + 1 : ℕ) : ℝ) ^ 2) +
      2 * R ^ 2 * Real.sqrt (reciprocalTailSq N) / ((N + 1 : ℕ) : ℝ) +
      R ^ 2 * reciprocalTailSq N)) atTop (𝓝 0)
  simpa [add_assoc] using (hterm1.add hterm2).add (hterm3.add hterm4)

/-- The paired absolute series has tails tending to zero uniformly on norm-bounded
sets of `(λ,s)`, hence uniformly on every compact subset. -/
theorem paired_product_locally_uniform (R : ℝ) (hR : 0 ≤ R) :
    ∀ (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ (s : L2Z) (lam : ℂ),
      ‖s‖ ≤ R → ‖lam‖ ≤ R →
        (∑' m : ℕ+, if N < (m : ℕ) then ‖pairedFactorError s lam m‖ else 0) < ε := by
  intro ε hε
  have hsmall : ∀ᶠ N : ℕ in atTop, pairedErrorUniformBound R N < ε :=
    (pairedErrorUniformBound_tendsto R).eventually (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
  refine ⟨N, fun s lam hs hl => ?_⟩
  have htail := pairedErrorTail_le_uniform_bound R hR N s lam hs hl
  have hsumid : (∑' m : ℕ+, pairedErrorTail N s lam m) =
      ∑' m : ℕ+, if N < (m : ℕ) then ‖pairedFactorError s lam m‖ else 0 := by
    apply tsum_congr
    intro m
    rfl
  rw [← hsumid]
  exact lt_of_le_of_lt htail (hN N le_rfl)


end NlsGge.Atomic.G2
