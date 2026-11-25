import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.lpHolder

/-! # G6-008: quadratic radii of paired real Cartesian coordinates

The source `ell2_r` space is a pair of real `ell2` sequences.  `PiLp 2` fixes
its Hilbert pair norm: the square of the norm is the sum of the two component
squared norms.  This is the unscaled Cartesian pair `(x,y)`; its physical
complex representative `(x - I*y)/sqrt 2` is a separate normalization.
-/

set_option autoImplicit false
noncomputable section

open scoped ENNReal BigOperators

namespace NlsGge.Atomic.G6008

/-- The literal paired-real `ell2_r` carrier: Boolean true/false are `x` and `y`. -/
abbrev CartesianL2 := PiLp 2 (fun _ : Bool => lp (fun _ : ℤ => ℝ) 2)

/-- The raw coordinate action/radius sequence `((x_n)^2 + (y_n)^2)/2`. -/
def coordinateRadiiSeq (z : CartesianL2) : ℤ → ℝ :=
  fun n => ((z true n) ^ 2 + (z false n) ^ 2) / 2

private lemma coordinateRadiiSeq_nonneg (z : CartesianL2) (n : ℤ) :
    0 ≤ coordinateRadiiSeq z n := by
  apply div_nonneg
  · exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · norm_num

private lemma norm_coordinateRadiiSeq (z : CartesianL2) (n : ℤ) :
    ‖coordinateRadiiSeq z n‖ =
      ((‖z true n‖ ^ 2 + ‖z false n‖ ^ 2) / 2) := by
  rw [Real.norm_of_nonneg (coordinateRadiiSeq_nonneg z n)]
  simp only [coordinateRadiiSeq, Real.norm_eq_abs, sq_abs]

/-- The radii sequence belongs to the actual real `ell1` carrier. -/
theorem coordinateRadiiSeq_mem_l1 (z : CartesianL2) :
    Memℓp (coordinateRadiiSeq z) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  have hx : Summable (fun n : ℤ => ‖z true n‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp (z true)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hy : Summable (fun n : ℤ => ‖z false n‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp (z false)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hxy := (hx.add hy).mul_left (1 / 2 : ℝ)
  apply hxy.congr
  intro n
  simp only [ENNReal.toReal_one, Real.rpow_one, norm_coordinateRadiiSeq]
  ring

/-- The radius map with codomain the genuine real `ell1` sequence space. -/
def coordinateRadii (z : CartesianL2) : lp (fun _ : ℤ => ℝ) 1 :=
  ⟨coordinateRadiiSeq z, coordinateRadiiSeq_mem_l1 z⟩

@[simp] theorem coordinateRadii_apply (z : CartesianL2) (n : ℤ) :
    coordinateRadii z n = ((z true n) ^ 2 + (z false n) ^ 2) / 2 := rfl

/-- Squared Hilbert norm of the paired source coordinates. -/
theorem cartesianL2_norm_sq (z : CartesianL2) :
    ‖z‖ ^ 2 = ‖z true‖ ^ 2 + ‖z false‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_bool]

private theorem pair_cauchy_schwarz (z w : CartesianL2) :
    ‖(z + w) true‖ * ‖(z - w) true‖ +
      ‖(z + w) false‖ * ‖(z - w) false‖ ≤ ‖z + w‖ * ‖z - w‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset Bool)
    (fun b => ‖(z + w) b‖) (fun b => ‖(z - w) b‖)
  rw [Fintype.sum_bool] at h
  rw [← PiLp.norm_eq_of_L2 (z + w), ← PiLp.norm_eq_of_L2 (z - w)] at h
  exact h

private theorem coordinateRadiiSeq_diff_bound (z w : CartesianL2) (n : ℤ) :
    ‖coordinateRadiiSeq z n - coordinateRadiiSeq w n‖ ≤
      (‖(z + w) true n‖ * ‖(z - w) true n‖ +
        ‖(z + w) false n‖ * ‖(z - w) false n‖) / 2 := by
  have hfactor : coordinateRadiiSeq z n - coordinateRadiiSeq w n =
      ((z + w) true n * ((z - w) true n) +
        (z + w) false n * ((z - w) false n)) / 2 := by
    simp only [coordinateRadiiSeq, PiLp.add_apply, PiLp.sub_apply,
      lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hfactor]
  calc
    ‖(((z + w) true n * ((z - w) true n) +
        (z + w) false n * ((z - w) false n)) / 2 : ℝ)‖
        = (1 / 2 : ℝ) *
          ‖(z + w) true n * ((z - w) true n) +
            (z + w) false n * ((z - w) false n)‖ := by
          rw [show ((z + w) true n * ((z - w) true n) +
              (z + w) false n * ((z - w) false n)) / 2 =
              (1 / 2 : ℝ) * ((z + w) true n * ((z - w) true n) +
                (z + w) false n * ((z - w) false n)) by ring,
            norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ (1 / 2 : ℝ) *
          (‖(z + w) true n * ((z - w) true n)‖ +
            ‖(z + w) false n * ((z - w) false n)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = (‖(z + w) true n‖ * ‖(z - w) true n‖ +
          ‖(z + w) false n‖ * ‖(z - w) false n‖) / 2 := by
        rw [norm_mul, norm_mul]
        ring

/-- Exact source-normalized local Lipschitz estimate for the paired-real radii map. -/
theorem coordinateRadii_lipschitz_bound (z w : CartesianL2) :
    ‖coordinateRadii z - coordinateRadii w‖ ≤
      (‖z‖ + ‖w‖) * ‖z - w‖ / 2 := by
  have hpq : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]
    norm_num
  let zp := z + w
  let zm := z - w
  let hT : Summable (fun n : ℤ => ‖zp true n‖ * ‖zm true n‖) :=
    lp.summable_mul hpq (zp true) (zm true)
  let hF : Summable (fun n : ℤ => ‖zp false n‖ * ‖zm false n‖) :=
    lp.summable_mul hpq (zp false) (zm false)
  have hMaj : Summable (fun n : ℤ =>
      (‖zp true n‖ * ‖zm true n‖ + ‖zp false n‖ * ‖zm false n‖) / 2) := by
    convert (hT.add hF).mul_left (1 / 2 : ℝ) using 1
    ext n
    ring
  have hDiff : Summable (fun n : ℤ => ‖(coordinateRadii z - coordinateRadii w) n‖) :=
    by
      simpa only [ENNReal.toReal_one, Real.rpow_one] using
        (lp.memℓp (coordinateRadii z - coordinateRadii w)).summable
          (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  have hsum :
      (∑' n : ℤ, ‖(coordinateRadii z - coordinateRadii w) n‖) ≤
        ∑' n : ℤ, (‖zp true n‖ * ‖zm true n‖ +
          ‖zp false n‖ * ‖zm false n‖) / 2 :=
    Summable.tsum_le_tsum (fun n => by
      change ‖coordinateRadiiSeq z n - coordinateRadiiSeq w n‖ ≤
        (‖(z + w) true n‖ * ‖(z - w) true n‖ +
          ‖(z + w) false n‖ * ‖(z - w) false n‖) / 2
      exact coordinateRadiiSeq_diff_bound z w n)
      hDiff hMaj
  have hTsum := lp.tsum_mul_le_mul_norm' hpq (zp true) (zm true)
  have hFsum := lp.tsum_mul_le_mul_norm' hpq (zp false) (zm false)
  have hmajor_sum :
      (∑' n : ℤ, (‖zp true n‖ * ‖zm true n‖ +
        ‖zp false n‖ * ‖zm false n‖) / 2) ≤
          (‖zp true‖ * ‖zm true‖ + ‖zp false‖ * ‖zm false‖) / 2 := by
    calc
      (∑' n : ℤ, (‖zp true n‖ * ‖zm true n‖ +
          ‖zp false n‖ * ‖zm false n‖) / 2) =
          (1 / 2 : ℝ) *
            ((∑' n : ℤ, ‖zp true n‖ * ‖zm true n‖) +
              ∑' n : ℤ, ‖zp false n‖ * ‖zm false n‖) := by
        calc
          _ = ∑' n : ℤ, (1 / 2 : ℝ) *
              (‖zp true n‖ * ‖zm true n‖ + ‖zp false n‖ * ‖zm false n‖) := by
            congr 1
            funext n
            ring
          _ = (1 / 2 : ℝ) *
              ∑' n : ℤ, (‖zp true n‖ * ‖zm true n‖ +
                ‖zp false n‖ * ‖zm false n‖) := tsum_mul_left
          _ = (1 / 2 : ℝ) *
              ((∑' n : ℤ, ‖zp true n‖ * ‖zm true n‖) +
                ∑' n : ℤ, ‖zp false n‖ * ‖zm false n‖) := by
            rw [hT.tsum_add hF]
      _ ≤ (1 / 2 : ℝ) *
            (‖zp true‖ * ‖zm true‖ + ‖zp false‖ * ‖zm false‖) :=
          mul_le_mul_of_nonneg_left (add_le_add hTsum hFsum) (by norm_num)
      _ = _ := by ring
  have hpair := pair_cauchy_schwarz z w
  have hbound :
      (∑' n : ℤ, ‖(coordinateRadii z - coordinateRadii w) n‖) ≤
        (‖zp‖ * ‖zm‖) / 2 := hsum.trans (hmajor_sum.trans (by
          simpa [zp, zm] using (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 hpair))
  have hnorm : ‖coordinateRadii z - coordinateRadii w‖ =
      ∑' n : ℤ, ‖(coordinateRadii z - coordinateRadii w) n‖ := by
    simpa only [ENNReal.toReal_one, one_div, inv_one, Real.rpow_one] using
      (lp.norm_eq_tsum_rpow (p := (1 : ℝ≥0∞))
        (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
        (coordinateRadii z - coordinateRadii w))
  rw [hnorm]
  calc
    (∑' n : ℤ, ‖(coordinateRadii z - coordinateRadii w) n‖) ≤
        (‖zp‖ * ‖zm‖) / 2 := hbound
    _ ≤ ((‖z‖ + ‖w‖) * ‖z - w‖) / 2 := by
        dsimp [zp, zm]
        gcongr
        exact norm_add_le z w

/-- Continuity of the source-normalized radius map into `ell1`. -/
theorem continuous_coordinateRadii : Continuous coordinateRadii := by
  refine continuous_iff_continuousAt.2 fun z₀ => ?_
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min 1 (ε / (‖z₀‖ + 1)), by positivity, fun z hz => ?_⟩
  rw [dist_eq_norm] at hz ⊢
  have hz₁ : ‖z - z₀‖ < 1 := lt_of_lt_of_le hz (min_le_left _ _)
  have hz₂ : ‖z - z₀‖ < ε / (‖z₀‖ + 1) := lt_of_lt_of_le hz (min_le_right _ _)
  have hznorm : ‖z‖ ≤ ‖z₀‖ + 1 := by
    have htri : ‖z‖ ≤ ‖z₀‖ + ‖z - z₀‖ := by
      calc
        ‖z‖ = ‖z₀ + (z - z₀)‖ :=
          congrArg norm (by abel : z = z₀ + (z - z₀))
        _ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_add_le z₀ (z - z₀)
    linarith
  have hfactor : (‖z‖ + ‖z₀‖) / 2 ≤ ‖z₀‖ + 1 := by
    linarith
  calc
    ‖coordinateRadii z - coordinateRadii z₀‖ ≤
        (‖z‖ + ‖z₀‖) * ‖z - z₀‖ / 2 := coordinateRadii_lipschitz_bound z z₀
    _ = ((‖z‖ + ‖z₀‖) / 2) * ‖z - z₀‖ := by ring
    _ ≤ (‖z₀‖ + 1) * ‖z - z₀‖ :=
      mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
    _ < (‖z₀‖ + 1) * (ε / (‖z₀‖ + 1)) :=
      mul_lt_mul_of_pos_left hz₂ (by positivity)
    _ = ε := by field_simp

end NlsGge.Atomic.G6008
