import NlsGge.ThirdConsultation.Narrative.PGT2M

                                                                                     
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Sobolev38
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.I
open NlsGge.Atomic.I010 (spectralEnergy)
open NlsGge.Atomic.I037
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.Narrative

private theorem m3_gapTerm_const_mul (W : ℝ → ℝ) (κ : ℝ) (u : PhysicalL2) (n : ℤ) :
    gapRemainderTermE02_38 (fun r => κ * W r) u n = κ * gapRemainderTermE02_38 W u n := by
  unfold gapRemainderTermE02_38
  simp_rw [show ∀ x : ℝ, (κ * W (2 * x) - κ * W (2 * Real.pi * n)) *
      actualGapHeightE02_38 u x =
      κ * ((W (2 * x) - W (2 * Real.pi * n)) * actualGapHeightE02_38 u x) by
    intro x; ring]
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem m3_gapTerm_sub (V U : ℝ → ℝ) (hV : Continuous V) (hU : Continuous U)
    (u : PhysicalL2) (n : ℤ) :
    gapRemainderTermE02_38 (fun r => V r - U r) u n =
      gapRemainderTermE02_38 V u n - gapRemainderTermE02_38 U u n := by
  have hVi : IntervalIntegrable
      (fun x : ℝ => (V (2 * x) - V (2 * Real.pi * n)) * actualGapHeightE02_38 u x)
      volume (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    (((hV.comp (continuous_const.mul continuous_id)).sub continuous_const).mul
      (continuous_actualGapHeightE02_38 u)).intervalIntegrable _ _
  have hUi : IntervalIntegrable
      (fun x : ℝ => (U (2 * x) - U (2 * Real.pi * n)) * actualGapHeightE02_38 u x)
      volume (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    (((hU.comp (continuous_const.mul continuous_id)).sub continuous_const).mul
      (continuous_actualGapHeightE02_38 u)).intervalIntegrable _ _
  unfold gapRemainderTermE02_38
  simp_rw [show ∀ x : ℝ, ((V (2 * x) - U (2 * x)) -
      (V (2 * Real.pi * n) - U (2 * Real.pi * n))) * actualGapHeightE02_38 u x =
      (V (2 * x) - V (2 * Real.pi * n)) * actualGapHeightE02_38 u x -
      (U (2 * x) - U (2 * Real.pi * n)) * actualGapHeightE02_38 u x by intro x; ring]
  rw [intervalIntegral.integral_sub hVi hUi]
  ring

/- The following estimates extend the original coefficientwise series argument.
   A is the same factorial-power weight with every numerator equal to one. -/
private theorem m3_bounded_series (p : ℝ) (hp : 1 ≤ p)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    (∀ r : ℝ, Summable (NlsGge.Atomic.I037.factorialPowerTerm p c.val r)) ∧
    ∀ r : ℝ,
      lower * NlsGge.Atomic.I037.factorialPowerWeight p (fun _ => 1) r ≤
        NlsGge.Atomic.I037.factorialPowerWeight p c.val r ∧
      NlsGge.Atomic.I037.factorialPowerWeight p c.val r ≤
        upper * NlsGge.Atomic.I037.factorialPowerWeight p (fun _ => 1) r := by
  have hc0 : ∀ j, 0 ≤ c.val j := fun j => c.property.1.le.trans (c.property.2.2 j).1
  have hterm0 : ∀ (r : ℝ) (j : ℕ),
      0 ≤ NlsGge.Atomic.I037.factorialPowerTerm p c.val r j := by
    intro r j
    unfold NlsGge.Atomic.I037.factorialPowerTerm
    exact div_nonneg (mul_nonneg (hc0 j) (by rw [pow_mul]; positivity))
      (Real.rpow_nonneg (by positivity) _)
  have hlo : ∀ (r : ℝ) (j : ℕ),
      lower * NlsGge.Atomic.I037.factorialPowerTerm p (fun _ => 1) r j ≤
        NlsGge.Atomic.I037.factorialPowerTerm p c.val r j := by
    intro r j
    unfold NlsGge.Atomic.I037.factorialPowerTerm
    simp only [one_mul]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (c.property.2.2 j).1 (by rw [pow_mul]; positivity))
      (Real.rpow_nonneg (by positivity) _)
  have hhi : ∀ (r : ℝ) (j : ℕ),
      NlsGge.Atomic.I037.factorialPowerTerm p c.val r j ≤
        upper * NlsGge.Atomic.I037.factorialPowerTerm p (fun _ => 1) r j := by
    intro r j
    unfold NlsGge.Atomic.I037.factorialPowerTerm
    simp only [one_mul]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (c.property.2.2 j).2 (by rw [pow_mul]; positivity))
      (Real.rpow_nonneg (by positivity) _)
  have h1 : ∀ r : ℝ, Summable (NlsGge.Atomic.I037.factorialPowerTerm p (fun _ => 1) r) :=
    fun r => NlsGge.Atomic.I037.summable_term hp (fun _ => ⟨le_rfl, by norm_num⟩) r
  have hs : ∀ r : ℝ, Summable (NlsGge.Atomic.I037.factorialPowerTerm p c.val r) :=
    fun r => Summable.of_nonneg_of_le (hterm0 r) (hhi r) ((h1 r).mul_left upper)
  refine ⟨hs, fun r => ?_⟩
  constructor
  · change lower * (∑' j, NlsGge.Atomic.I037.factorialPowerTerm p (fun _ => 1) r j) ≤
      ∑' j, NlsGge.Atomic.I037.factorialPowerTerm p c.val r j
    rw [← (h1 r).tsum_mul_left lower]
    exact Summable.tsum_le_tsum (hlo r) ((h1 r).mul_left lower) (hs r)
  · change (∑' j, NlsGge.Atomic.I037.factorialPowerTerm p c.val r j) ≤
      upper * ∑' j, NlsGge.Atomic.I037.factorialPowerTerm p (fun _ => 1) r j
    rw [← (h1 r).tsum_mul_left upper]
    exact Summable.tsum_le_tsum (hhi r) (hs r) ((h1 r).mul_left upper)

private theorem m3_bounded_convex (p : ℝ) (hp : 1 ≤ p)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    ConvexOn ℝ Set.univ (NlsGge.Atomic.I037.factorialPowerWeight p c.val) := by
  have hs := (m3_bounded_series p hp lower upper c).1
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hterm : ∀ j : ℕ,
      NlsGge.Atomic.I037.factorialPowerTerm p c.val (a • x + b • y) j ≤
        a • NlsGge.Atomic.I037.factorialPowerTerm p c.val x j +
          b • NlsGge.Atomic.I037.factorialPowerTerm p c.val y j := by
    intro j
    have hβ : 0 ≤ c.val j / (Nat.factorial j : ℝ) ^ p :=
      div_nonneg (c.property.1.le.trans (c.property.2.2 j).1)
        (Real.rpow_nonneg (by positivity) _)
    have hcv := ((Even.convexOn_pow (n := 2 * j) (even_two_mul j)).smul hβ).2
      (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    have e : ∀ r : ℝ, NlsGge.Atomic.I037.factorialPowerTerm p c.val r j =
        (c.val j / (Nat.factorial j : ℝ) ^ p) • r ^ (2 * j) := by
      intro r
      unfold NlsGge.Atomic.I037.factorialPowerTerm
      rw [smul_eq_mul]
      ring
    rw [e, e, e]
    exact hcv
  unfold NlsGge.Atomic.I037.factorialPowerWeight
  calc ∑' j, NlsGge.Atomic.I037.factorialPowerTerm p c.val (a • x + b • y) j
      ≤ ∑' j, (a • NlsGge.Atomic.I037.factorialPowerTerm p c.val x j +
          b • NlsGge.Atomic.I037.factorialPowerTerm p c.val y j) :=
        Summable.tsum_le_tsum hterm (hs _) (((hs x).mul_left a).add ((hs y).mul_left b))
    _ = a • ∑' j, NlsGge.Atomic.I037.factorialPowerTerm p c.val x j +
        b • ∑' j, NlsGge.Atomic.I037.factorialPowerTerm p c.val y j := by
      simp only [smul_eq_mul]
      rw [((hs x).mul_left a).tsum_add ((hs y).mul_left b), tsum_mul_left, tsum_mul_left]

private theorem m3_bounded_scaled_facts (p : ℝ) (hp : 2 < p)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) (κ : ℝ) (hκ : 0 < κ) :
    let W := fun r : ℝ => κ * NlsGge.Atomic.I037.factorialPowerWeight p c.val r
    let wa := fun n : ℤ => W (2 * Real.pi * (n : ℝ)) * japaneseBracket n ^ (2 / p - 2);
    ContDiff ℝ 2 W ∧ ConvexOn ℝ Set.univ W ∧
      (∀ n : ℤ, 0 < W (2 * Real.pi * (n : ℝ))) ∧ (∀ n : ℤ, 0 ≤ wa n) ∧
      (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PhysicalL2,
        SobolevSquareSummable 1 (physicalFourier u) → ‖physFS38 1 u‖ ≤ B → ∀ n : ℤ,
          |gapRemainderTermE02_38 W u n| ≤ C * wa n * actualGapActionAllE02_38 u n) ∧
      (∀ᵐ z ∂(countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ)))),
        (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
        Summable (fun n : ℤ => wa n * ‖z n‖ ^ 2)) := by
  intro W wa
  have hp1 : 1 ≤ p := by linarith
  have hl : 0 < lower := c.property.1
  have hu : 0 < upper := hl.trans_le c.property.2.1
  let ones : BoundedCoefficients 1 2 :=
    ⟨fun _ => 1, by refine ⟨by norm_num, by norm_num, fun _ => ?_⟩; norm_num⟩
  let d : BoundedCoefficients 1 2 := ⟨fun j => 1 + c.val j / upper, by
    refine ⟨by norm_num, by norm_num, fun j => ?_⟩
    have h0 : 0 ≤ c.val j / upper :=
      div_nonneg (hl.le.trans (c.property.2.2 j).1) hu.le
    have h1 : c.val j / upper ≤ 1 := (div_le_one hu).2 (c.property.2.2 j).2
    constructor <;> linarith⟩
  let A := NlsGge.Atomic.I037.factorialPowerWeight p ones.val
  let D := NlsGge.Atomic.I037.factorialPowerWeight p d.val
  let U := κ * upper
  let L := κ * lower
  have hU : 0 < U := mul_pos hκ hu
  have hL : 0 < L := mul_pos hκ hl
  obtain ⟨hseries, hbounds⟩ := m3_bounded_series p hp1 lower upper c
  have hbase : ∀ r : ℝ, NlsGge.Atomic.I037.factorialPowerWeight p c.val r =
      upper * (D r - A r) := by
    intro r
    have hd := NlsGge.Atomic.I037.summable_term hp1 d.property.2.2 r
    have h1 := NlsGge.Atomic.I037.summable_term hp1 ones.property.2.2 r
    have ht : ∀ j : ℕ,
        upper * (NlsGge.Atomic.I037.factorialPowerTerm p d.val r j -
          NlsGge.Atomic.I037.factorialPowerTerm p ones.val r j) =
            NlsGge.Atomic.I037.factorialPowerTerm p c.val r j := by
      intro j
      dsimp only [d, ones, NlsGge.Atomic.I037.factorialPowerTerm]
      field_simp [hu.ne'] <;> ring
    have hx := (hd.hasSum.sub h1.hasSum).mul_left upper
    exact (hseries r).hasSum.unique (hx.congr_fun (fun j => (ht j).symm))
  have hW : W = fun r : ℝ => U * (D r - A r) := by
    funext r
    dsimp only [W, U]
    rw [hbase r]
    ring
  have hA : ContDiff ℝ 2 A := I038S.contDiff_weight hp1 ones.property.2.2
  have hD : ContDiff ℝ 2 D := I038S.contDiff_weight hp1 d.property.2.2
  have hW2 : ContDiff ℝ 2 W := by
    rw [hW]
    exact ContDiff.mul (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => U)) (ContDiff.sub hD hA)
  have hconv : ConvexOn ℝ Set.univ W := by
    simpa only [smul_eq_mul] using (m3_bounded_convex p hp1 lower upper c).smul hκ.le
  have hApos : ∀ r : ℝ, 0 < A r := fun r =>
    lt_of_lt_of_le zero_lt_one (NlsGge.Atomic.I037.weight_ge_one hp1 ones.property.2.2 r)
  have hDpos : ∀ r : ℝ, 0 < D r := fun r =>
    lt_of_lt_of_le zero_lt_one (NlsGge.Atomic.I037.weight_ge_one hp1 d.property.2.2 r)
  have hD2 : ∀ r : ℝ, D r ≤ 2 * A r := by
    intro r
    have hx := (hbounds r).2
    rw [hbase r] at hx
    have hmul : upper * D r ≤ upper * (2 * A r) := by
      nlinarith only [hx]
    exact le_of_mul_le_mul_left hmul hu
  have hlow : ∀ r : ℝ, L * A r ≤ W r := by
    intro r
    calc L * A r = κ * (lower * A r) := by dsimp only [L]; ring
      _ ≤ κ * NlsGge.Atomic.I037.factorialPowerWeight p c.val r :=
        mul_le_mul_of_nonneg_left (hbounds r).1 hκ.le
      _ = W r := rfl
  have hpos : ∀ r : ℝ, 0 < W r := fun r => lt_of_lt_of_le (mul_pos hL (hApos r)) (hlow r)
  let w : ℤ → ℝ := fun n =>
    U * (D (2 * Real.pi * (n : ℝ)) + A (2 * Real.pi * (n : ℝ))) *
      japaneseBracket n ^ (2 / p - 2)
  have hpow0 : ∀ n : ℤ, 0 ≤ japaneseBracket n ^ (2 / p - 2) := fun n =>
    Real.rpow_nonneg (by unfold japaneseBracket; positivity) _
  have hw0 : ∀ n : ℤ, 0 ≤ w n := fun n =>
    mul_nonneg (mul_nonneg hU.le (add_nonneg (hDpos _).le (hApos _).le)) (hpow0 n)
  have hgap : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PhysicalL2,
      SobolevSquareSummable 1 (physicalFourier u) → ‖physFS38 1 u‖ ≤ B → ∀ n : ℤ,
        |gapRemainderTermE02_38 W u n| ≤ C * w n * actualGapActionAllE02_38 u n := by
    intro B hB
    obtain ⟨CD, hCD, hgD⟩ := I038W.gap_conjunct p hp d B hB
    obtain ⟨CA, hCA, hgA⟩ := I038W.gap_conjunct p hp ones B hB
    refine ⟨CD + CA, add_nonneg hCD hCA, fun u hu hBu n => ?_⟩
    have hlin : gapRemainderTermE02_38 W u n =
        U * (gapRemainderTermE02_38 D u n - gapRemainderTermE02_38 A u n) := by
      rw [hW, m3_gapTerm_const_mul, m3_gapTerm_sub D A hD.continuous hA.continuous]
    have hcoef : CD * D (2 * Real.pi * (n : ℝ)) + CA * A (2 * Real.pi * (n : ℝ)) ≤
        (CD + CA) * (D (2 * Real.pi * (n : ℝ)) + A (2 * Real.pi * (n : ℝ))) := by
      nlinarith only [mul_nonneg hCD (hApos (2 * Real.pi * (n : ℝ))).le,
        mul_nonneg hCA (hDpos (2 * Real.pi * (n : ℝ))).le]
    have hI : 0 ≤ actualGapActionAllE02_38 u n := actualGapAction_nonneg38 u n
    calc |gapRemainderTermE02_38 W u n|
        = U * |gapRemainderTermE02_38 D u n - gapRemainderTermE02_38 A u n| := by
          rw [hlin, abs_mul, abs_of_pos hU]
      _ ≤ U * (|gapRemainderTermE02_38 D u n| + |gapRemainderTermE02_38 A u n|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) hU.le
      _ ≤ U * (CD * D (2 * Real.pi * (n : ℝ)) * actualGapActionAllE02_38 u n *
          japaneseBracket n ^ (2 / p - 2) +
          CA * A (2 * Real.pi * (n : ℝ)) * actualGapActionAllE02_38 u n *
          japaneseBracket n ^ (2 / p - 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add (hgD u hu hBu n) (hgA u hu hBu n)) hU.le
      _ = U * (CD * D (2 * Real.pi * (n : ℝ)) + CA * A (2 * Real.pi * (n : ℝ))) *
          (actualGapActionAllE02_38 u n * japaneseBracket n ^ (2 / p - 2)) := by ring
      _ ≤ U * ((CD + CA) * (D (2 * Real.pi * (n : ℝ)) + A (2 * Real.pi * (n : ℝ)))) *
          (actualGapActionAllE02_38 u n * japaneseBracket n ^ (2 / p - 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef hU.le) (mul_nonneg hI (hpow0 n))
      _ = (CD + CA) * w n * actualGapActionAllE02_38 u n := by dsimp only [w]; ring
  have hsum : Summable (fun n : ℤ => w n / W (2 * Real.pi * (n : ℝ))) := by
    refine Summable.of_nonneg_of_le
      (fun n => div_nonneg (hw0 n) (hpos _).le) (fun n => ?_)
      ((I038W.summable_bracket hp).mul_left (3 * U / L))
    apply (div_le_iff₀ (hpos _)).2
    have hDA : D (2 * Real.pi * (n : ℝ)) + A (2 * Real.pi * (n : ℝ)) ≤
        3 * A (2 * Real.pi * (n : ℝ)) := by linarith only [hD2 (2 * Real.pi * (n : ℝ))]
    calc w n
        ≤ U * (3 * A (2 * Real.pi * (n : ℝ))) * japaneseBracket n ^ (2 / p - 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDA hU.le) (hpow0 n)
      _ = (3 * U / L * japaneseBracket n ^ (2 / p - 2)) *
          (L * A (2 * Real.pi * (n : ℝ))) := by field_simp [hL.ne'] <;> ring
      _ ≤ (3 * U / L * japaneseBracket n ^ (2 / p - 2)) * W (2 * Real.pi * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (hlow _) (mul_nonneg (by positivity) (hpow0 n))
  have hpoly : ∀ r : ℕ, Summable (fun n : ℤ =>
      sobolevWeight38 r n / W (2 * Real.pi * (n : ℝ))) := by
    intro r
    refine Summable.of_nonneg_of_le
      (fun n => div_nonneg (sobolevWeight38_nonneg r n) (hpos _).le) (fun n => ?_)
      ((I038M.rate_poly hp1 ones.property.2.2 r).mul_left L⁻¹)
    calc sobolevWeight38 r n / W (2 * Real.pi * (n : ℝ))
        ≤ sobolevWeight38 r n / (L * A (2 * Real.pi * (n : ℝ))) :=
          div_le_div_of_nonneg_left (sobolevWeight38_nonneg r n) (mul_pos hL (hApos _)) (hlow _)
      _ = L⁻¹ * (sobolevWeight38 r n / A (2 * Real.pi * (n : ℝ))) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  have hwa0 : ∀ n : ℤ, 0 ≤ wa n := fun n => mul_nonneg (hpos _).le (hpow0 n)
  have hwa_le : ∀ n : ℤ, wa n ≤ w n := by
    intro n
    have hle : W (2 * Real.pi * (n : ℝ)) ≤
        U * (D (2 * Real.pi * (n : ℝ)) + A (2 * Real.pi * (n : ℝ))) := by
      rw [hW]
      apply mul_le_mul_of_nonneg_left _ hU.le
      linarith only [(hApos (2 * Real.pi * (n : ℝ))).le]
    exact mul_le_mul_of_nonneg_right hle (hpow0 n)
  have hw_le : ∀ n : ℤ, w n ≤ (3 * U / L) * wa n := by
    intro n
    have hDA : D (2 * Real.pi * (n : ℝ)) + A (2 * Real.pi * (n : ℝ)) ≤
        3 * A (2 * Real.pi * (n : ℝ)) := by linarith only [hD2 (2 * Real.pi * (n : ℝ))]
    calc w n
        ≤ U * (3 * A (2 * Real.pi * (n : ℝ))) * japaneseBracket n ^ (2 / p - 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDA hU.le) (hpow0 n)
      _ = (3 * U / L * japaneseBracket n ^ (2 / p - 2)) *
          (L * A (2 * Real.pi * (n : ℝ))) := by field_simp [hL.ne'] <;> ring
      _ ≤ (3 * U / L * japaneseBracket n ^ (2 / p - 2)) * W (2 * Real.pi * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (hlow _) (mul_nonneg (by positivity) (hpow0 n))
      _ = (3 * U / L) * wa n := by dsimp only [wa]; ring
  have hgapa : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PhysicalL2,
      SobolevSquareSummable 1 (physicalFourier u) → ‖physFS38 1 u‖ ≤ B → ∀ n : ℤ,
        |gapRemainderTermE02_38 W u n| ≤ C * wa n * actualGapActionAllE02_38 u n := by
    intro B hB
    obtain ⟨C, hC, hg⟩ := hgap B hB
    refine ⟨C * (3 * U / L), mul_nonneg hC (by positivity), fun u hu hBu n => ?_⟩
    refine (hg u hu hBu n).trans ?_
    calc C * w n * actualGapActionAllE02_38 u n
        ≤ C * ((3 * U / L) * wa n) * actualGapActionAllE02_38 u n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hw_le n) hC)
            (actualGapAction_nonneg38 u n)
      _ = (C * (3 * U / L)) * wa n * actualGapActionAllE02_38 u n := by ring
  have hΩ : ∀ᵐ z ∂(countableComplexGaussian (fun n : ℤ => W (2 * Real.pi * (n : ℝ)))),
      (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
      Summable (fun n : ℤ => wa n * ‖z n‖ ^ 2) := by
    filter_upwards [I038M.ae_good _ w (fun n => hpos _) hw0 hsum hpoly] with z hz
    refine ⟨hz.1, Summable.of_nonneg_of_le
      (fun n => mul_nonneg (hwa0 n) (sq_nonneg _)) (fun n => ?_) hz.2⟩
    exact mul_le_mul_of_nonneg_right (hwa_le n) (sq_nonneg _)
  exact ⟨hW2, hconv, fun n => hpos _, hwa0, hgapa, hΩ⟩

private theorem m3_hasDerivAt_term (p : ℝ) (c : ℕ → ℝ) (n : ℕ) (y : ℝ) :
    HasDerivAt (fun y => factorialPowerTerm p c y n)
      (c n * (((2 * n : ℕ) : ℝ) * y ^ (2 * n - 1)) / ((Nat.factorial n : ℝ) ^ p)) y := by
  unfold factorialPowerTerm
  exact ((hasDerivAt_pow (2 * n) y).const_mul (c n)).div_const _

private theorem m3_mul_deriv_term (p : ℝ) (c : ℕ → ℝ) (n : ℕ) (y : ℝ) :
    y * (c n * (((2 * n : ℕ) : ℝ) * y ^ (2 * n - 1)) / ((Nat.factorial n : ℝ) ^ p)) =
      2 * ((n : ℝ) * factorialPowerTerm p c y n) := by
  unfold factorialPowerTerm
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
    have hm' : 2 * n - 1 = m := by omega
    rw [hm', hm, pow_succ]
    push_cast
    have h2 : (2 : ℝ) * n = m + 1 := by exact_mod_cast hm
    rw [← h2]
    ring

private theorem m3_summable_deriv_bound (R : ℝ) :
    Summable (fun n : ℕ => 4 * ((n : ℝ) * R ^ (2 * n - 1) / (Nat.factorial n : ℝ))) := by
  refine Summable.mul_left 4 ?_
  rw [← summable_nat_add_iff 1]
  have key : ∀ k : ℕ, (((k + 1 : ℕ) : ℝ) * R ^ (2 * (k + 1) - 1) /
      (Nat.factorial (k + 1) : ℝ)) = R * ((R ^ 2) ^ k / (Nat.factorial k : ℝ)) := by
    intro k
    have h1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have hk : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    rw [h1, Nat.factorial_succ, pow_succ, pow_mul]
    push_cast
    field_simp
  simp only [key]
  exact (Real.summable_pow_div_factorial (R ^ 2)).mul_left R

private theorem m3_hasDerivAt_weight (p : ℝ) (hp : 1 ≤ p)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) (r : ℝ) :
    HasDerivAt (factorialPowerWeight p c.val)
      (∑' n : ℕ, c.val n * (((2 * n : ℕ) : ℝ) * r ^ (2 * n - 1)) /
        ((Nat.factorial n : ℝ) ^ p)) r := by
  set R : ℝ := |r| + 1 with hR
  have hR0 : 0 < R := by positivity
  have hmem : r ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; linarith [abs_nonneg r]
  have h0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R := Metric.mem_ball_self hR0
  have hu : 0 ≤ upper := c.property.1.le.trans c.property.2.1
  have hb := (m3_summable_deriv_bound R).mul_left (upper / 2)
  have hder := hasDerivAt_tsum_of_isPreconnected hb Metric.isOpen_ball
    (convex_ball (0 : ℝ) R).isPreconnected
    (fun n y _ => m3_hasDerivAt_term p c.val n y) ?_ h0
    ((m3_bounded_series p hp lower upper c).1 0) hmem
  · exact hder
  · intro n y hy
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
    have hF : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hFp : 0 < (Nat.factorial n : ℝ) ^ p := Real.rpow_pos_of_pos hF p
    have hF1 : (1 : ℝ) ≤ (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hFle := Real.self_le_rpow_of_one_le hF1 hp
    have hpow : |y| ^ (2 * n - 1) ≤ R ^ (2 * n - 1) := pow_le_pow_left₀ (abs_nonneg y) hy.le _
    have hc0 : 0 ≤ c.val n := c.property.1.le.trans (c.property.2.2 n).1
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_of_pos hFp, abs_pow,
      Nat.abs_cast, abs_of_nonneg hc0]
    have hn0 : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
    calc c.val n * (((2 * n : ℕ) : ℝ) * |y| ^ (2 * n - 1)) / (Nat.factorial n : ℝ) ^ p
        ≤ upper * (((2 * n : ℕ) : ℝ) * R ^ (2 * n - 1)) / (Nat.factorial n : ℝ) ^ p := by
          apply div_le_div_of_nonneg_right _ hFp.le
          exact mul_le_mul (c.property.2.2 n).2 (mul_le_mul_of_nonneg_left hpow hn0)
            (by positivity) hu
      _ ≤ upper * (((2 * n : ℕ) : ℝ) * R ^ (2 * n - 1)) / (Nat.factorial n : ℝ) := by
          apply div_le_div_of_nonneg_left (by positivity) hF hFle
      _ = (upper / 2) * (4 * ((n : ℝ) * R ^ (2 * n - 1) / (Nat.factorial n : ℝ))) := by
          push_cast
          ring

private theorem m3_term_moment (p : ℝ) (lower upper : ℝ)
    (c : BoundedCoefficients lower upper) (r : ℝ) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) ^ p * factorialPowerTerm p c.val r (k + 1) ≤
      (upper / lower) * r ^ 2 * factorialPowerTerm p c.val r k := by
  have hl : 0 < lower := c.property.1
  have hu : 0 < upper := hl.trans_le c.property.2.1
  have hratio : c.val (k + 1) ≤ (upper / lower) * c.val k := by
    calc c.val (k + 1) ≤ upper := (c.property.2.2 (k + 1)).2
      _ = (upper / lower) * lower := by field_simp
      _ ≤ (upper / lower) * c.val k :=
        mul_le_mul_of_nonneg_left (c.property.2.2 k).1 (by positivity)
  unfold factorialPowerTerm
  have hF : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hFp := Real.rpow_pos_of_pos hF p
  have ha : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) ^ p := Real.rpow_pos_of_pos (by positivity) p
  have hfs : ((Nat.factorial (k + 1) : ℕ) : ℝ) ^ p =
      ((k + 1 : ℕ) : ℝ) ^ p * (Nat.factorial k : ℝ) ^ p := by
    rw [Nat.factorial_succ, Nat.cast_mul, Real.mul_rpow (by positivity) hF.le]
  rw [hfs]
  have e1 : ((k + 1 : ℕ) : ℝ) ^ p * (c.val (k + 1) * r ^ (2 * (k + 1)) /
      (((k + 1 : ℕ) : ℝ) ^ p * (Nat.factorial k : ℝ) ^ p)) =
      c.val (k + 1) * (r ^ 2 * r ^ (2 * k)) / (Nat.factorial k : ℝ) ^ p := by
    have he : r ^ (2 * (k + 1)) = r ^ 2 * r ^ (2 * k) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]; ring
    rw [he]
    field_simp
  rw [e1]
  calc c.val (k + 1) * (r ^ 2 * r ^ (2 * k)) / (Nat.factorial k : ℝ) ^ p
      ≤ ((upper / lower) * c.val k) * (r ^ 2 * r ^ (2 * k)) / (Nat.factorial k : ℝ) ^ p := by
        apply div_le_div_of_nonneg_right _ hFp.le
        exact mul_le_mul_of_nonneg_right hratio (by rw [pow_mul]; positivity)
    _ = (upper / lower) * r ^ 2 *
        (c.val k * r ^ (2 * k) / (Nat.factorial k : ℝ) ^ p) := by ring

private theorem m3_logderiv_bound {p r A B D K : ℝ} (hK : 0 ≤ K)
    (hr : 0 < r) (hA : 0 < A) (hD : r * D = 2 * B)
    (hB0 : 0 ≤ B) (hB : B ≤ (K * r ^ 2) ^ (1 / p) * A) :
    0 ≤ D / A ∧ D / A ≤ 2 * K ^ (1 / p) * r ^ (2 / p - 1) := by
  have hD' : D = 2 * B / r := by field_simp; linarith only [hD]
  have hpow : (K * r ^ 2) ^ (1 / p) = K ^ (1 / p) * r ^ (2 / p) := by
    rw [Real.mul_rpow hK (sq_nonneg r)]
    congr 1
    rw [show (r ^ 2 : ℝ) = r ^ (2 : ℝ) by rw [Real.rpow_two], ← Real.rpow_mul hr.le]
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · rw [hD']; positivity
  · rw [hD', Real.rpow_sub_one hr.ne', div_div, div_le_iff₀ (mul_pos hr hA)]
    calc 2 * B ≤ 2 * ((K * r ^ 2) ^ (1 / p) * A) := by linarith only [hB]
      _ = 2 * K ^ (1 / p) * (r ^ (2 / p) / r) * (r * A) := by
        rw [hpow]
        field_simp

/-- The source's sharp ratio-dependent logarithmic-derivative estimate, v2:81,490–496. -/
theorem factorialPower_bounded_coefficients_logDerivative (p : ℝ) (hp : 2 < p)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    (∀ r : ℝ, Summable (NlsGge.Atomic.I037.factorialPowerTerm p c.val r)) ∧
    ∀ r : ℝ, 0 < r →
      0 < NlsGge.Atomic.I037.factorialPowerWeight p c.val r ∧
      DifferentiableAt ℝ (NlsGge.Atomic.I037.factorialPowerWeight p c.val) r ∧
      0 ≤ deriv (NlsGge.Atomic.I037.factorialPowerWeight p c.val) r /
        NlsGge.Atomic.I037.factorialPowerWeight p c.val r ∧
      deriv (NlsGge.Atomic.I037.factorialPowerWeight p c.val) r /
        NlsGge.Atomic.I037.factorialPowerWeight p c.val r ≤
          2 * (upper / lower) ^ (1 / p) * r ^ (2 / p - 1) := by
  have hp1 : 1 ≤ p := by linarith
  have hp' : 1 < p := by linarith
  have hl : 0 < lower := c.property.1
  have hu : 0 < upper := hl.trans_le c.property.2.1
  obtain ⟨hs, hbounds⟩ := m3_bounded_series p hp1 lower upper c
  refine ⟨hs, fun r hr => ?_⟩
  have hA : 0 < factorialPowerWeight p c.val r := by
    have h1 : 0 < factorialPowerWeight p (fun _ => 1) r :=
      lt_of_lt_of_le zero_lt_one (weight_ge_one hp1 (fun _ => ⟨le_rfl, by norm_num⟩) r)
    exact lt_of_lt_of_le (mul_pos hl h1) (hbounds r).1
  have hs0 : ∀ j : ℕ, 0 ≤ factorialPowerTerm p c.val r j := by
    intro j
    unfold factorialPowerTerm
    exact div_nonneg (mul_nonneg (hl.le.trans (c.property.2.2 j).1)
      (by rw [pow_mul]; positivity)) (Real.rpow_nonneg (by positivity) _)
  obtain ⟨hBsum, hB⟩ := core_moment p hp' (factorialPowerTerm p c.val r) hs0 (hs r)
    ((upper / lower) * r ^ 2) (by positivity) (m3_term_moment p lower upper c r)
  have hder := m3_hasDerivAt_weight p hp1 lower upper c r
  have hDsum : Summable (fun n : ℕ => c.val n *
      (((2 * n : ℕ) : ℝ) * r ^ (2 * n - 1)) / ((Nat.factorial n : ℝ) ^ p)) := by
    refine (hBsum.mul_left (2 / r)).congr fun n => ?_
    calc (2 / r) * ((n : ℝ) * factorialPowerTerm p c.val r n)
        = (2 * ((n : ℝ) * factorialPowerTerm p c.val r n)) / r := by ring
      _ = c.val n * (((2 * n : ℕ) : ℝ) * r ^ (2 * n - 1)) /
          ((Nat.factorial n : ℝ) ^ p) :=
        (div_eq_iff hr.ne').2 (by nlinarith only [m3_mul_deriv_term p c.val n r])
  have hD : r * (∑' n : ℕ, c.val n * (((2 * n : ℕ) : ℝ) * r ^ (2 * n - 1)) /
        ((Nat.factorial n : ℝ) ^ p)) =
      2 * ∑' j : ℕ, (j : ℝ) * factorialPowerTerm p c.val r j := by
    rw [← hDsum.tsum_mul_left r, tsum_congr (fun n => m3_mul_deriv_term p c.val n r),
      hBsum.tsum_mul_left 2]
  have hB0 : 0 ≤ ∑' j : ℕ, (j : ℝ) * factorialPowerTerm p c.val r j :=
    tsum_nonneg (fun j => mul_nonneg (Nat.cast_nonneg _) (hs0 j))
  refine ⟨hA, hder.differentiableAt, ?_⟩
  rw [hder.deriv]
  exact m3_logderiv_bound (by positivity) hr hA hD hB0 hB

/-- Full arbitrary-interval finite-gap construction, with the exact source-rate good set. -/
theorem factorialPower_bounded_coefficients_construction (p : ℝ) (hp : 2 < p)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    let W := NlsGge.Atomic.I037.factorialPowerWeight p c.val
    let a := fun n : ℤ => W (2 * Real.pi * (n : ℝ))
    let γ := countableComplexGaussian a
    let Ω := {z : ℤ → ℂ | (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
      Summable (fun n : ℤ => a n * ‖z n‖ ^ 2 * japaneseBracket n ^ (2 / p - 2))}
    Summable (fun n : ℤ => japaneseBracket n ^ (2 / p - 2)) ∧
    MeasurableSet Ω ∧ γ Ω = 1 ∧
    (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : PhysicalL2, SobolevSquareSummable 1 (physicalFourier u) →
        ‖physFS38 1 u‖ ≤ B → ∀ n : ℤ,
          |gapRemainderTermE02_38 W u n| ≤
            C * a n * actualGapActionAllE02_38 u n * japaneseBracket n ^ (2 / p - 2)) ∧
    (∀ z ∈ Ω,
      Summable (fun n : ℤ => |gapRemainderTermE02_38 W (physicalOfSequence z) n|) ∧
      sequenceRemainder W z = remainderForWeight W (physicalOfSequence z) ∧
      0 ≤ remainderForWeight W (physicalOfSequence z)) ∧
    (∀ S : Finset ℤ,
      0 < finiteAbsolutePartition W S ∧
      finiteAbsolutePartition W S ≤ ∏ n : S, Real.pi / a n ∧
      0 < finiteRelativeNormalizer W S ∧ finiteRelativeNormalizer W S ≤ 1 ∧
      finiteRelativeNormalizer W S = finiteAbsolutePartition W S / (∏ n : S, Real.pi / a n) ∧
      finiteGapCoordinateLaw W S = (finiteComplexVolume S).withDensity
        (fun w => ENNReal.ofReal (Real.exp (-spectralEnergy W (finiteGapField S w)) /
          finiteAbsolutePartition W S)) ∧
      IsProbabilityMeasure (finiteGapLaw W S) ∧
      ∀ w : S → ℂ,
        Integrable (fun t : ℝ => W (2 * t) * actualGapHeightE02_38 (finiteGapField S w) t) ∧
        HasSum (fun j : ℕ => c.val j / ((j.factorial : ℝ) ^ p) *
          chargeFn38 (j + 2) j (finiteGapField S w)) (spectralEnergy W (finiteGapField S w))) ∧
    0 < limitNormalizer W ∧ limitNormalizer W ≤ 1 ∧
    IsProbabilityMeasure (weightedSequenceLaw W) ∧ IsProbabilityMeasure (physicalLaw W) ∧
    weightedSequenceLaw W ≪ γ ∧ γ ≪ weightedSequenceLaw W ∧
    (∀ A : Set (ℤ → ℂ), MeasurableSet A →
      weightedSequenceLaw W A ≤ ENNReal.ofReal ((limitNormalizer W)⁻¹) * γ A) ∧
    (∀ᵐ (u : PhysicalL2) ∂physicalLaw W, ∀ r : ℕ, SobolevSquareSummable (r : ℝ) (physicalFourier u)) ∧
    ∀ Λ : ℕ → Finset ℤ, IsExhaustion38 Λ →
      Tendsto (fun N : ℕ => finiteRelativeNormalizer W (Λ N)) atTop (𝓝 (limitNormalizer W)) ∧
      ∀ (r : ℕ) (F : SobolevHilbert (r : ℝ) →ᵇ ℝ),
        Tendsto (fun N : ℕ => ∫ u : PhysicalL2, F (physFS38 r u) ∂finiteGapLaw W (Λ N))
          atTop (𝓝 (∫ u : PhysicalL2, F (physFS38 r u) ∂physicalLaw W)) := by
  intro W a γ Ω
  let Bk := PDE.actualBirkhoffTop38
  have hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z := actual_inverse_eq_physicalOfSequence
  have hfacts := m3_bounded_scaled_facts p hp lower upper c 1 zero_lt_one
  simp only [one_mul] at hfacts
  obtain ⟨hW2, hconv, hpos, hw0, hgap, hΩae⟩ := hfacts
  let w : ℤ → ℝ := fun n => a n * japaneseBracket n ^ (2 / p - 2)
  have hset : Ω = {z : ℤ → ℂ | (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
      Summable (fun n : ℤ => w n * ‖z n‖ ^ 2)} := by
    ext z
    simp only [Set.mem_setOf_eq]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, h2.congr fun n => ?_⟩ <;>
      dsimp only [w] <;> ring
  have hΩm : MeasurableSet Ω := by
    rw [hset]
    exact I038M.measurableSet_good w hw0
  have hΩ1 : γ Ω = 1 := by
    rw [hset]
    exact (prob_compl_eq_zero_iff (I038M.measurableSet_good w hw0)).1 (ae_iff.1 hΩae)
  have homega : ∀ z ∈ Ω,
      Summable (fun n : ℤ => |gapRemainderTermE02_38 W (physicalOfSequence z) n|) ∧
      sequenceRemainder W z = remainderForWeight W (physicalOfSequence z) ∧
      0 ≤ remainderForWeight W (physicalOfSequence z) := by
    intro z hz
    rw [hset] at hz
    have hz1 := (mem_seqSobolev38_iff _ _).2 (hz.1 1)
    obtain ⟨h1, -, -, h0⟩ := I038P.pathwise Bk hB W hW2 hconv w hw0 hgap z hz1 hz.2
      stdExh38 isExhaustion_stdExh38
    exact ⟨h1, max_eq_right h0, h0⟩
  obtain ⟨hZ1, hZ2, hP1, hP2, hac1, hac2, hdens⟩ := I038L.limit_gen Bk hB W hW2.continuous
  have hPm : Measurable physicalOfSequence := by
    rw [show physicalOfSequence = Bk.cleanΦinv from (funext hB).symm]
    exact Bk.measurable_cleanΦinv
  have hall : ∀ᵐ (u : PhysicalL2) ∂physicalLaw W, ∀ r : ℕ,
      SobolevSquareSummable (r : ℝ) (physicalFourier u) := by
    unfold physicalLaw
    rw [ae_map_iff hPm.aemeasurable I038L.measurableSet_allSobolev_phys]
    refine hac1.ae_le ?_
    filter_upwards [hΩae] with z hz r
    rw [← hB z]
    exact Bk.sobolev_cleanΦinv38 r z ((mem_seqSobolev38_iff _ _).2 (hz.1 r))
  refine ⟨I038W.summable_bracket hp, hΩm, hΩ1, ?_, homega, ?_,
    hZ1, hZ2, hP1, hP2, hac1, hac2, hdens, hall,
    fun Λ hΛ => I038K.weak_gen Bk hB W hW2 hconv w hw0 hgap hΩae Λ hΛ⟩
  · intro B hBd
    obtain ⟨C, hC, hg⟩ := hgap B hBd
    refine ⟨C, hC, fun u hu hBu n => (hg u hu hBu n).trans (le_of_eq ?_)⟩
    ring
  · intro S
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := I038B.block Bk hB W hW2 hconv hpos S
    refine ⟨b1, b2, b3, b4, b5, b6, b7, fun v => ⟨b8 v, ?_⟩⟩
    have hcoeff : ∀ j : ℕ, 0 ≤ c.val j / ((j.factorial : ℝ) ^ p) := by
      intro j
      exact div_nonneg (c.property.1.le.trans (c.property.2.2 j).1)
        (Real.rpow_nonneg (by positivity) _)
    have hseries : ∀ r : ℝ, HasSum
        (fun j : ℕ => c.val j / ((j.factorial : ℝ) ^ p) * r ^ (2 * j)) (W r) := by
      intro r
      have hs := ((m3_bounded_series p (show 1 ≤ p by linarith) lower upper c).1 r).hasSum
      refine hs.congr_fun fun j => ?_
      unfold NlsGge.Atomic.I037.factorialPowerTerm
      ring
    have hu : ∀ m : ℕ, SobolevSquareSummable (m : ℝ) (physicalFourier (finiteGapField S v)) := by
      intro m
      rw [I017C.field_eq_proj Bk hB S v]
      exact Bk.sobolev_cleanΦinv38 m _ (finiteSupport_mem_seqSobolev38 _ _ (finite_support_projFin38 S _))
    exact I038C.hasSum_charge W _ hcoeff hseries _ hu (b8 v)

/-- The field-law singularity assertion at v2:425, in the standing/scaled p>2 class. -/
theorem factorialPower_bounded_scaled_field_laws_mutuallySingular
    (p : ℝ) (hp : 2 < p) (lower upper : ℝ)
    (c : BoundedCoefficients lower upper) (κ : ℝ) (hκ : 0 < κ) :
    let W := fun r : ℝ => κ * NlsGge.Atomic.I037.factorialPowerWeight p c.val r
    ∀ S : Finset ℤ, (finiteGapLaw W S).MutuallySingular (physicalLaw W) := by
  intro W
  let Bk := PDE.actualBirkhoffTop38
  have hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z := actual_inverse_eq_physicalOfSequence
  obtain ⟨hW2, -, hq, -, -, hΩ⟩ := m3_bounded_scaled_facts p hp lower upper c κ hκ
  have hPm : Measurable physicalOfSequence := by
    rw [show physicalOfSequence = Bk.cleanΦinv from (funext hB).symm]
    exact Bk.measurable_cleanΦinv
  obtain ⟨-, -, -, -, hac, -, -⟩ := I038L.limit_gen Bk hB W hW2.continuous
  have hA := I027C.measurableSet_actions_pos
  have hpos : ∀ᵐ u ∂physicalLaw W, ∀ n : ℤ, 0 < actualGapActionAllE02_38 u n := by
    unfold physicalLaw
    rw [ae_map_iff hPm.aemeasurable hA]
    refine hac.ae_le ?_
    filter_upwards [hΩ, I027C.coord_ne_zero_ae _ hq] with z hz hz0
    intro n
    have hz1 : z ∈ seqSobolev38 ((1 : ℕ) : ℝ) := (mem_seqSobolev38_iff _ _).2 (hz.1 1)
    rw [← hB, Bk.action_cleanΦinv38 z hz1 n]
    exact pow_pos (norm_pos_iff.2 (hz0 n)) 2
  intro S
  refine ⟨{u : PhysicalL2 | ∀ n : ℤ, 0 < actualGapActionAllE02_38 u n}, hA, ?_, ae_iff.1 hpos⟩
  unfold finiteGapLaw
  rw [Measure.map_apply ((I017C.field_eq38 Bk hB S) ▸ Bk.measurable_finiteGapField38 S) hA]
  have hempty : finiteGapField S ⁻¹' {u : PhysicalL2 | ∀ n : ℤ, 0 < actualGapActionAllE02_38 u n} = ∅ := by
    ext v
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall, not_lt]
    obtain ⟨n, -, hn⟩ := (Set.infinite_univ.diff S.finite_toSet).nonempty
    have hnS : n ∉ S := hn
    have hz1 : extZero38 S v ∈ seqSobolev38 ((1 : ℕ) : ℝ) := by
      have h := finiteSupport_mem_seqSobolev38 ((1 : ℕ) : ℝ) _
        (finite_support_projFin38 S (extZero38 S v))
      rwa [projFin38_extZero38] at h
    refine ⟨n, ?_⟩
    show actualGapActionAllE02_38 (physicalOfSequence (extZero38 S v)) n ≤ 0
    rw [← hB, Bk.action_cleanΦinv38 _ hz1 n, extZero38_apply_of_not_mem v hnS, norm_zero]
    norm_num
  rw [hempty, measure_empty]

end NlsGge.ThirdConsultation.Narrative
