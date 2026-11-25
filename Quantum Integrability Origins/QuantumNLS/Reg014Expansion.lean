import QuantumNLS.Reg014Levels
import QuantumNLS.Reg014Identify

/-! REG-014 support: the accepted REG-007 tree expansion of the scalar `A - A_0`, with the
little-oh remainder replaced by an explicit bound whose constant and threshold depend only
on an upper bound `U` for the Fourier-coordinate norm of the field.  The solution used is the
absolutely convergent tree sum, identified uniformly with the ratio solution. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
namespace QuantumNLS.Reg014Expansion
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiExpansions
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.RootH1RatioBounds
open QuantumNLS.TerraMultiRound40ScalarParity QuantumNLS.TerraMultiRound57Collection
open QuantumNLS.TerraMultiRound45TreeSum QuantumNLS.TerraMultiRound45TreeTail
open QuantumNLS.TerraMultiRound45ScalarBound
open QuantumNLS.TerraMultiRound46Fixed QuantumNLS.TerraMultiRound46Radius
open QuantumNLS.TerraMultiRound56LevelCollection QuantumNLS.TerraMultiRound56FiniteRemainder
open QuantumNLS.TerraMultiRound57LevelIdentity QuantumNLS.TerraMultiRound57CollectedPowers
open QuantumNLS.TerraMultiRound59SignedCharges QuantumNLS.TerraMultiRound59RealExpansion
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.Reg014Levels QuantumNLS.Reg014Identify

variable {L : ℝ} [Fact (0 < L)]

/-- The exact (pointwise in `Y`) splitting of the scalar of any element against the finite
tree approximants, the free term, and the finite correlation remainders. -/
theorem exact_split (s : ℕ) (hs : 2 ≤ s) (κ : ℝ) (x r : Ell2) (Y : ℝ) (hY : 0 < Y) :
    scalar L (s - 1 : ℕ) x r -
      (freeScalar (L := L) (s - 1 : ℕ) x Y +
        (∑ n ∈ Finset.Ico 1 s, positiveApprox (L := L) (k := s - 1) κ x n (2 * (s - n) - 1) Y) +
        leadingApprox (L := L) (k := s - 1) κ x s Y) =
    (scalar L (s - 1 : ℕ) x r - scalar L (s - 1 : ℕ) x
      (∑ n ∈ Finset.range (s + 1), treeLevel (Fact.out : 0 < L) (a := ((s - 1 : ℕ) : ℝ))
        (by
          have h : (1 : ℝ) ≤ (s - 1 : ℕ) := by exact_mod_cast (show 1 ≤ s - 1 by omega)
          linarith) (abs_pos.mpr hY.ne') κ x n)) +
    ((∑ n ∈ Finset.Ico 1 s, positiveRemainder (L := L) (k := s - 1) κ x n (2 * (s - n) - 1) Y) +
      leadingRemainder (L := L) (k := s - 1) κ x s Y) := by
  have hk : 1 ≤ s - 1 := by omega
  have ha : (1 : ℝ) / 2 < ((s - 1 : ℕ) : ℝ) := by
    have h : (1 : ℝ) ≤ ((s - 1 : ℕ) : ℝ) := by exact_mod_cast hk
    linarith
  have hY' : 0 < |Y| := abs_pos.mpr hY.ne'
  let f : ℕ → ℂ := fun n => scalar L (s - 1 : ℕ) x
    (treeLevel (Fact.out : 0 < L) ha hY' κ x n)
  have hsplit : (∑ n ∈ Finset.range (s + 1), f n) = f 0 + (∑ n ∈ Finset.Ico 1 s, f n) + f s := by
    rw [Finset.sum_range_succ, ← Finset.sum_range_add_sum_Ico f (show 1 ≤ s by omega)]
    simp
  simp only [freeScalar, hY', dite_true]
  rw [scalar_sum L (Fact.out) ha, hsplit]
  dsimp only [f]
  rw [scalar_level_zero ha hY' κ x]
  simp_rw [positive_level_identity (L := L) hk Y hY' κ x,
    leading_level_identity (L := L) hk Y hY' κ x]
  rw [Finset.sum_sub_distrib]
  abel

omit [Fact (0 < L)] in
/-- The scalar tail of the tree sum after `N` levels. -/
theorem tail_bound {a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (hY : 0 < |Y|) (κ : ℝ) (x : Ell2)
    (N : ℕ) (hq : 4 * (|κ / L| * Cmul L a ^ 2 * ‖x‖ ^ 2 * |Y|⁻¹ ^ 2) ≤ 1 / 2) :
    ‖scalar L a x (∑' n, treeLevel hL ha hY κ x n) -
      scalar L a x (∑ n ∈ Finset.range N, treeLevel hL ha hY κ x n)‖ ≤
      (L * physK L a ^ 2 * ‖x‖) *
        ((‖x‖ * |Y|⁻¹) * (4 * (|κ / L| * Cmul L a ^ 2 * ‖x‖ ^ 2 * |Y|⁻¹ ^ 2)) ^ N * 2) := by
  have hlt : 4 * (|κ / L| * Cmul L a ^ 2 * ‖x‖ ^ 2 * |Y|⁻¹ ^ 2) < 1 := by linarith
  have hs := tree_levels_summable hL ha hY κ x hlt
  have hsplit := hs.sum_add_tsum_nat_add N
  have heq : (∑' n, treeLevel hL ha hY κ x n) -
      ∑ n ∈ Finset.range N, treeLevel hL ha hY κ x n =
      ∑' n, treeLevel hL ha hY κ x (n + N) := by
    rw [← hsplit, add_sub_cancel_left]
  rw [← scalar_sub L hL ha, heq]
  have hb := scalar_norm_le L hL ha x (∑' n, treeLevel hL ha hY κ x (n + N))
  have ht := tree_tail_bound hL ha hY κ x N hlt
  have hpk : 0 ≤ physK L a := physK_nonneg (by linarith)
  have hc : 0 ≤ L * physK L a ^ 2 * ‖x‖ := by positivity
  have hinv : (1 - 4 * (|κ / L| * Cmul L a ^ 2 * ‖x‖ ^ 2 * |Y|⁻¹ ^ 2))⁻¹ ≤ 2 := by
    calc _ ≤ ((1 : ℝ) / 2)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
      _ = 2 := by norm_num
  have hq0 : 0 ≤ 4 * (|κ / L| * Cmul L a ^ 2 * ‖x‖ ^ 2 * |Y|⁻¹ ^ 2) := by positivity
  calc _ ≤ L * (physK L a * ‖x‖ * (physK L a *
        ‖∑' n, treeLevel hL ha hY κ x (n + N)‖)) := hb
    _ = (L * physK L a ^ 2 * ‖x‖) * ‖∑' n, treeLevel hL ha hY κ x (n + N)‖ := by ring
    _ ≤ (L * physK L a ^ 2 * ‖x‖) * ((‖x‖ * |Y|⁻¹) *
        (4 * (|κ / L| * Cmul L a ^ 2 * ‖x‖ ^ 2 * |Y|⁻¹ ^ 2)) ^ N *
        (1 - 4 * (|κ / L| * Cmul L a ^ 2 * ‖x‖ ^ 2 * |Y|⁻¹ ^ 2))⁻¹) :=
      mul_le_mul_of_nonneg_left ht hc
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hc
      apply mul_le_mul_of_nonneg_left hinv
      positivity

/-- **Uniform scalar remainder.** For fixed `s ≥ 2`, `κ > 0` and a bound `U` for the
coordinate norm, the large-`Y` expansion of the real part of the scalar `A - A_0` through
order `Y^{-2s-1}` has remainder bounded by `C Y^{-2s-1}`, for all fields of norm at most `U`
and all `Y ≥ Y₀`; the solution is the ratio solution of the scalar construction. -/
theorem uniform_scalar_remainder (s : ℕ) (hs : 2 ≤ s) (κ : ℝ) (hκ : 0 < κ)
    (U : ℝ) (hU : 0 ≤ U) :
    ∃ C Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ x : Ell2, ‖x‖ ≤ U → ∀ Y : ℝ, Y₀ ≤ Y →
      ∃ (hY : 0 < Y) (hlog : Real.log 3 ≤ Y * L)
        (hsmall : 16 * κ * ‖fieldMap L (s - 1 : ℕ) (Nat.cast_nonneg _) x‖ ^ 2 ≤ Y) (r : Ell2),
        fieldMap L (s - 1 : ℕ) (Nat.cast_nonneg _) r =
          ratioL2 hY hlog hκ.le (fieldMap L (s - 1 : ℕ) (Nat.cast_nonneg _) x) hsmall ∧
        |(scalar L (s - 1 : ℕ) x r - freeScalar (L := L) (s - 1 : ℕ) x Y).re -
          ∑ j ∈ Finset.Icc 1 s, (-1 : ℝ) ^ j *
            retainedR (L := L) s hs κ (physicalToHk (L := L) (s - 1) x) j * Y⁻¹ ^ (2 * j + 1)| ≤
          C * Y⁻¹ ^ (2 * s + 1) := by
  have hk : 1 ≤ s - 1 := by omega
  have ha : (1 : ℝ) / 2 < ((s - 1 : ℕ) : ℝ) := by
    have h : (1 : ℝ) ≤ ((s - 1 : ℕ) : ℝ) := by exact_mod_cast hk
    linarith
  have hL : 0 < L := Fact.out
  set a : ℝ := ((s - 1 : ℕ) : ℝ) with ha_def
  have hCm : 0 ≤ Cmul L a := Real.sqrt_nonneg _
  have hpk : 0 ≤ physK L a := physK_nonneg (by linarith)
  set Q : ℝ := 4 * (|κ / L| * Cmul L a ^ 2 * U ^ 2) with hQ_def
  have hQ0 : 0 ≤ Q := by positivity
  obtain ⟨Yid, hYid1, hid⟩ := uniform_identification L ha κ hκ U hU
  set W : ℝ := max U 1 with hW_def
  have hW1 : 1 ≤ W := le_max_right _ _
  have hUW : ∀ m : ℕ, m ≤ 2 * s + 2 → U ^ m ≤ W ^ (2 * s + 2) := fun m hm =>
    (pow_le_pow_left₀ hU (le_max_left U 1) m).trans (pow_le_pow_right₀ hW1 hm)
  -- constants for the levels
  have hpos : ∀ n ∈ Finset.Ico 1 s, ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : ℝ), 0 ≤ U → ∀ x : Ell2, ‖x‖ ≤ U →
      ∀ Y : ℝ, 0 < Y →
      ‖positiveRemainder (L := L) (k := s - 1) κ x n (2 * (s - n) - 1) Y‖ ≤
        K * U ^ (2 * n + 2) * Y⁻¹ ^ (2 * s + 1) := by
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    obtain ⟨K, hK0, hK⟩ := positive_level_bound (L := L) hk (d := 2 * (s - n) - 1) (by omega) κ n
    refine ⟨K, hK0, fun U hU x hx Y hY => ?_⟩
    have h := hK U hU x hx Y hY
    have he : 2 * n + 1 + (2 * (s - n) - 1 + 1) = 2 * s + 1 := by omega
    rw [he] at h
    exact h
  choose! Kp hKp0 hKp using hpos
  obtain ⟨Kl, hKl0, hKl⟩ := leading_level_bound (L := L) hk κ s
  set Ksum : ℝ := ∑ n ∈ Finset.Ico 1 s, Kp n with hKsum
  have hKsum0 : 0 ≤ Ksum := Finset.sum_nonneg (fun n hn => hKp0 n hn)
  set Ctail : ℝ := 2 * (L * physK L a ^ 2 * U) * (U * Q ^ (s + 1)) with hCtail
  have hCtail0 : 0 ≤ Ctail := by positivity
  refine ⟨Ctail + (Ksum + Kl) * W ^ (2 * s + 2), max (2 * Q + 1) Yid, ?_, ?_⟩
  · exact (le_max_left _ _).trans' (by linarith)
  intro x hx Y hYB
  have hY1 : 1 ≤ Y := by
    have h1 : 2 * Q + 1 ≤ Y := (le_max_left _ _).trans hYB
    linarith
  have hYpos : 0 < Y := by linarith
  have hYid : Yid ≤ Y := (le_max_right _ _).trans hYB
  have hYQ : 2 * Q + 1 ≤ Y := (le_max_left _ _).trans hYB
  have hY' : 0 < |Y| := abs_pos.mpr hYpos.ne'
  have habs : |Y| = Y := abs_of_pos hYpos
  have hYi0 : 0 ≤ Y⁻¹ := inv_nonneg.mpr hYpos.le
  have hYi1 : Y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hY1
  have hxn : 0 ≤ ‖x‖ := norm_nonneg _
  -- smallness of the geometric ratio
  have hq : 4 * (|κ / L| * Cmul L a ^ 2 * ‖x‖ ^ 2 * |Y|⁻¹ ^ 2) ≤ Q * Y⁻¹ ^ 2 := by
    rw [habs, hQ_def]
    have : ‖x‖ ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ hxn hx 2
    have h0 : 0 ≤ |κ / L| * Cmul L a ^ 2 := by positivity
    calc 4 * (|κ / L| * Cmul L a ^ 2 * ‖x‖ ^ 2 * Y⁻¹ ^ 2)
        = 4 * ((|κ / L| * Cmul L a ^ 2) * ‖x‖ ^ 2 * Y⁻¹ ^ 2) := by ring
      _ ≤ 4 * ((|κ / L| * Cmul L a ^ 2) * U ^ 2 * Y⁻¹ ^ 2) := by gcongr
      _ = _ := by ring
  have hQY : Q * Y⁻¹ ^ 2 ≤ 1 / 2 := by
    have h1 : Y⁻¹ ^ 2 ≤ Y⁻¹ := by nlinarith
    have h2 : Q * Y⁻¹ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hYpos]
      linarith
    calc Q * Y⁻¹ ^ 2 ≤ Q * Y⁻¹ := mul_le_mul_of_nonneg_left h1 hQ0
      _ ≤ 1 / 2 := h2
  have hqhalf : 4 * (|κ / L| * Cmul L a ^ 2 * ‖x‖ ^ 2 * |Y|⁻¹ ^ 2) ≤ 1 / 2 := hq.trans hQY
  -- the tree sum
  set r : Ell2 := ∑' n, treeLevel hL ha hY' κ x n with hr_def
  have hfix : physicalT hL ha hY' κ x r = r :=
    tree_sum_fixed hL ha hY' κ x (by linarith)
  have hball : ‖r‖ ≤ 2 * ‖x‖ / |Y| := tree_sum_ball hL ha hY' κ x hqhalf
  rw [habs] at hball
  obtain ⟨hlog, hsmall, hident⟩ := hid Y hYid x r hx hball hYpos hfix
  refine ⟨hYpos, hlog, hsmall, r, hident, ?_⟩
  -- real part and signs
  have hE : (scalar L (s - 1 : ℕ) x r - freeScalar (L := L) (s - 1 : ℕ) x Y).re -
      ∑ j ∈ Finset.Icc 1 s, (-1 : ℝ) ^ j *
        retainedR (L := L) s hs κ (physicalToHk (L := L) (s - 1) x) j * Y⁻¹ ^ (2 * j + 1) =
      (scalar L (s - 1 : ℕ) x r - (freeScalar (L := L) (s - 1 : ℕ) x Y +
        ∑ n ∈ Finset.range (2 * s + 2), (Y⁻¹ ^ n) •
          treeCoefficient (L := L) (k := s - 1) κ x s n)).re := by
    have hsum : ∑ j ∈ Finset.Icc 1 s, (-1 : ℝ) ^ j *
        retainedR (L := L) s hs κ (physicalToHk (L := L) (s - 1) x) j * Y⁻¹ ^ (2 * j + 1) =
        ∑ j ∈ Finset.Icc 1 s, Y⁻¹ ^ (2 * j + 1) *
          (treeCoefficient (L := L) (k := s - 1) κ x s (2 * j + 1)).re := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      rw [odd_coefficient_signed (L := L) s hs κ x j hj'.1 hj'.2]
      ring
    have h1 : (scalar L (s - 1 : ℕ) x r - (freeScalar (L := L) (s - 1 : ℕ) x Y +
        ∑ n ∈ Finset.range (2 * s + 2), (Y⁻¹ ^ n) •
          treeCoefficient (L := L) (k := s - 1) κ x s n)).re =
        (scalar L (s - 1 : ℕ) x r).re - ((freeScalar (L := L) (s - 1 : ℕ) x Y).re +
        (∑ n ∈ Finset.range (2 * s + 2), (Y⁻¹ ^ n) •
          treeCoefficient (L := L) (k := s - 1) κ x s n).re) := by
      simp only [Complex.sub_re, Complex.add_re]
    rw [h1, real_tree_sum L s hs κ hκ x Y, Complex.sub_re, hsum]
    ring
  rw [hE]
  refine (Complex.abs_re_le_norm _).trans ?_
  -- exact split
  have hsplit := exact_split (L := L) s hs κ x r Y hYpos
  have hcol := collect_tree_powers (L := L) (k := s - 1) s hs κ x Y
  have hz : scalar L (s - 1 : ℕ) x r - (freeScalar (L := L) (s - 1 : ℕ) x Y +
        ∑ n ∈ Finset.range (2 * s + 2), (Y⁻¹ ^ n) •
          treeCoefficient (L := L) (k := s - 1) κ x s n) =
      (scalar L (s - 1 : ℕ) x r - scalar L (s - 1 : ℕ) x
        (∑ n ∈ Finset.range (s + 1), treeLevel (Fact.out : 0 < L) (a := ((s - 1 : ℕ) : ℝ)) ha
          hY' κ x n)) +
      ((∑ n ∈ Finset.Ico 1 s, positiveRemainder (L := L) (k := s - 1) κ x n (2 * (s - n) - 1) Y) +
        leadingRemainder (L := L) (k := s - 1) κ x s Y) := by
    rw [← hcol, ← add_assoc]
    exact hsplit
  rw [hz]
  -- bounds on the three pieces
  have hxW : ∀ m : ℕ, m ≤ 2 * s + 2 → ‖x‖ ^ m ≤ W ^ (2 * s + 2) := fun m hm =>
    (pow_le_pow_left₀ hxn hx m).trans (hUW m hm)
  have hYp : Y⁻¹ ^ (2 * s + 3) ≤ Y⁻¹ ^ (2 * s + 1) :=
    pow_le_pow_of_le_one hYi0 hYi1 (by omega)
  have htail : ‖scalar L (s - 1 : ℕ) x r - scalar L (s - 1 : ℕ) x
        (∑ n ∈ Finset.range (s + 1), treeLevel (Fact.out : 0 < L) (a := ((s - 1 : ℕ) : ℝ)) ha
          hY' κ x n)‖ ≤ Ctail * Y⁻¹ ^ (2 * s + 1) := by
    have hb := tail_bound (L := L) hL ha hY' κ x (s + 1) hqhalf
    rw [habs] at hb
    refine hb.trans ?_
    have hq' : 4 * (|κ / L| * Cmul L a ^ 2 * ‖x‖ ^ 2 * Y⁻¹ ^ 2) ≤ Q * Y⁻¹ ^ 2 := by
      rw [habs] at hq; exact hq
    have hq0 : 0 ≤ 4 * (|κ / L| * Cmul L a ^ 2 * ‖x‖ ^ 2 * Y⁻¹ ^ 2) := by positivity
    calc (L * physK L a ^ 2 * ‖x‖) *
          ((‖x‖ * Y⁻¹) * (4 * (|κ / L| * Cmul L a ^ 2 * ‖x‖ ^ 2 * Y⁻¹ ^ 2)) ^ (s + 1) * 2)
        ≤ (L * physK L a ^ 2 * U) * ((U * Y⁻¹) * (Q * Y⁻¹ ^ 2) ^ (s + 1) * 2) := by
          gcongr
      _ = Ctail * Y⁻¹ ^ (2 * s + 3) := by
          rw [hCtail, mul_pow, ← pow_mul]
          ring
      _ ≤ Ctail * Y⁻¹ ^ (2 * s + 1) := mul_le_mul_of_nonneg_left hYp hCtail0
  have hposb : ‖∑ n ∈ Finset.Ico 1 s,
      positiveRemainder (L := L) (k := s - 1) κ x n (2 * (s - n) - 1) Y‖ ≤
      Ksum * W ^ (2 * s + 2) * Y⁻¹ ^ (2 * s + 1) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Finset.Ico 1 s,
          ‖positiveRemainder (L := L) (k := s - 1) κ x n (2 * (s - n) - 1) Y‖
        ≤ ∑ n ∈ Finset.Ico 1 s, Kp n * W ^ (2 * s + 2) * Y⁻¹ ^ (2 * s + 1) := by
          apply Finset.sum_le_sum
          intro n hn
          have hn' := Finset.mem_Ico.mp hn
          refine (hKp n hn U hU x hx Y hYpos).trans ?_
          have h1 : U ^ (2 * n + 2) ≤ W ^ (2 * s + 2) := hUW _ (by omega)
          have h2 := hKp0 n hn
          have h3 : 0 ≤ Y⁻¹ ^ (2 * s + 1) := by positivity
          gcongr
      _ = _ := by rw [hKsum, Finset.sum_mul, Finset.sum_mul]
  have hleadb : ‖leadingRemainder (L := L) (k := s - 1) κ x s Y‖ ≤
      Kl * W ^ (2 * s + 2) * Y⁻¹ ^ (2 * s + 1) := by
    refine (hKl U hU x hx Y hYpos).trans ?_
    have h1 : U ^ (2 * s + 2) ≤ W ^ (2 * s + 2) := hUW _ le_rfl
    have h3 : 0 ≤ Y⁻¹ ^ (2 * s + 1) := by positivity
    gcongr
  calc _ ≤ ‖scalar L (s - 1 : ℕ) x r - scalar L (s - 1 : ℕ) x
        (∑ n ∈ Finset.range (s + 1), treeLevel (Fact.out : 0 < L) (a := ((s - 1 : ℕ) : ℝ)) ha
          hY' κ x n)‖ +
      ‖(∑ n ∈ Finset.Ico 1 s, positiveRemainder (L := L) (k := s - 1) κ x n (2 * (s - n) - 1) Y) +
        leadingRemainder (L := L) (k := s - 1) κ x s Y‖ := norm_add_le _ _
    _ ≤ Ctail * Y⁻¹ ^ (2 * s + 1) + (Ksum * W ^ (2 * s + 2) * Y⁻¹ ^ (2 * s + 1) +
        Kl * W ^ (2 * s + 2) * Y⁻¹ ^ (2 * s + 1)) :=
      add_le_add htail ((norm_add_le _ _).trans (add_le_add hposb hleadb))
    _ = _ := by ring

#print axioms exact_split
#print axioms tail_bound
#print axioms uniform_scalar_remainder
end QuantumNLS.Reg014Expansion
