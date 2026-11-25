import Mathlib
import NlsGge.GK38.PairPotential

/- KSPS-008 support (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/Perturbed008Support.lean.
   Parseval for moment coefficients (Mathlib tsum_sq_fourierCoeffOn), exp-series interchange, and an
   l2 Minkowski inequality for series of sequences. No hypothesis beyond the stated ones. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace NlsGge.ThirdConsultation.KSPS008Support

/-- the k-th moment Fourier-type coefficient -/
def bco (F : ℝ → ℂ) (x : ℝ) (k : ℕ) (n : ℤ) : ℂ :=
  ∫ t in (0 : ℝ)..x,
    Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * ((x - 2 * t : ℝ) : ℂ)) *
      (((x - 2 * t : ℝ) : ℂ) ^ k * F t)

def hfun (F : ℝ → ℂ) (x : ℝ) (k : ℕ) : ℝ → ℂ :=
  Set.indicator (Set.Iic x) (fun t => ((x - 2 * t : ℝ) : ℂ) ^ k * F t)

theorem norm_hfun_le (F : ℝ → ℂ) {x : ℝ} (hx1 : x ≤ 1) (k : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖hfun F x k t‖ ≤ ‖F t‖ := by
  unfold hfun
  by_cases h : t ≤ x
  · rw [Set.indicator_of_mem (by exact h)]
    have hs : ‖((x - 2 * t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [ht.1, ht.2]
    rw [norm_mul, norm_pow]
    calc ‖((x - 2 * t : ℝ) : ℂ)‖ ^ k * ‖F t‖ ≤ 1 * ‖F t‖ := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hs
      _ = ‖F t‖ := one_mul _
  · rw [Set.indicator_of_notMem (by exact h)]
    simp

theorem bco_eq_fourierCoeffOn (F : ℝ → ℂ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) (n : ℤ) :
    bco F x k n = Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * (x : ℂ)) *
      fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) (hfun F x k) n := by
  rw [fourierCoeffOn_eq_integral]
  have key : ∀ t : ℝ, fourier (-n) (t : AddCircle ((1 : ℝ) - 0)) • hfun F x k t =
      Set.indicator (Set.Iic x) (fun t : ℝ => fourier (-n) (t : AddCircle ((1 : ℝ) - 0)) •
        (((x - 2 * t : ℝ) : ℂ) ^ k * F t)) t := by
    intro t
    unfold hfun
    by_cases h : t ≤ x
    · simp [Set.indicator_of_mem (show t ∈ Set.Iic x from h)]
    · simp [Set.indicator_of_notMem (show t ∉ Set.Iic x from h)]
  simp_rw [key]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have hset : Set.Iic x ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioc 0 x := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hx1⟩
  rw [hset, bco, intervalIntegral.integral_of_le hx0]
  simp only [one_div, smul_eq_mul, sub_zero, inv_one, one_smul]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
  rw [fourier_coe_apply]
  have he : Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * ((x - 2 * t : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * (x : ℂ)) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((-n : ℤ) : ℂ) * (t : ℂ) / (((1 : ℝ) - 0 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

theorem norm_phase (n : ℤ) (x : ℝ) :
    ‖Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem bco_sq_summable_le (F : ℝ → ℂ) (hFm : AEStronglyMeasurable F volume)
    (hF2 : IntervalIntegrable (fun t => ‖F t‖ ^ 2) volume 0 1)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    Summable (fun n : ℤ => ‖bco F x k n‖ ^ 2) ∧
      ∑' n : ℤ, ‖bco F x k n‖ ^ 2 ≤ ∫ t in (0 : ℝ)..1, ‖F t‖ ^ 2 := by
  have hF2' : Integrable (fun t => ‖F t‖ ^ 2) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp hF2
  have hFL : MemLp F 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm hFm.restrict).mpr hF2'
  have hhm : AEStronglyMeasurable (hfun F x k) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    unfold hfun
    refine AEStronglyMeasurable.indicator ?_ measurableSet_Iic
    exact (Continuous.aestronglyMeasurable (by fun_prop)).mul hFm.restrict
  have hhL : MemLp (hfun F x k) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    refine MemLp.of_le hFL hhm ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioc
      (fun t ht => norm_hfun_le F hx1 k ⟨ht.1.le, ht.2⟩)
  have H := hasSum_sq_fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) hhL
  have hnorm : ∀ n : ℤ, ‖bco F x k n‖ =
      ‖fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) (hfun F x k) n‖ := by
    intro n
    rw [bco_eq_fourierCoeffOn F hx0 hx1 k n, norm_mul, norm_phase, one_mul]
  simp_rw [hnorm]
  refine ⟨H.summable, ?_⟩
  rw [H.tsum_eq]
  have hhI : IntervalIntegrable (fun t => ‖hfun F x k t‖ ^ 2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      ((memLp_two_iff_integrable_sq_norm hhm).mp hhL)
  simp only [sub_zero, inv_one, one_smul]
  refine intervalIntegral.integral_mono_on (by norm_num) hhI hF2 (fun t ht => ?_)
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_hfun_le F hx1 k ht) 2

theorem norm_sreal_le {x t : ℝ} (hx : 0 ≤ x) (ht : t ∈ Set.Ioc (0 : ℝ) x) :
    ‖((x - 2 * t : ℝ) : ℂ)‖ ≤ x := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [ht.1, ht.2]

theorem integrableOn_Ioc_of_cont (F : ℝ → ℂ) (hFi : IntervalIntegrable F volume 0 1)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (c : ℝ → ℂ) (hc : Continuous c) :
    Integrable (fun t => c t * F t) (volume.restrict (Set.Ioc (0 : ℝ) x)) := by
  have h1 : IntervalIntegrable F volume 0 x := hFi.mono_set (by
    rw [Set.uIcc_of_le hx0, Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc le_rfl hx1)
  have h2 := h1.continuousOn_mul (g := c) hc.continuousOn
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx0).mp h2

theorem pert_hasSum (F : ℝ → ℂ) (hFi : IntervalIntegrable F volume 0 1)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (a : ℂ) (n : ℤ) :
    HasSum (fun k : ℕ => (Complex.I * a) ^ k / (k.factorial : ℂ) * bco F x k n)
      (∫ t in (0 : ℝ)..x,
        Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ) + a) * ((x - 2 * t : ℝ) : ℂ)) * F t) := by
  set G : ℕ → ℝ → ℂ := fun k t =>
    (Complex.I * a) ^ k / (k.factorial : ℂ) *
      (Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * ((x - 2 * t : ℝ) : ℂ)) *
        (((x - 2 * t : ℝ) : ℂ) ^ k * F t)) with hG
  have hGint : ∀ k, Integrable (G k) (volume.restrict (Set.Ioc (0 : ℝ) x)) := by
    intro k
    have := (integrableOn_Ioc_of_cont F hFi hx0 hx1
      (fun t => (Complex.I * a) ^ k / (k.factorial : ℂ) *
        (Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * ((x - 2 * t : ℝ) : ℂ)) *
          ((x - 2 * t : ℝ) : ℂ) ^ k)) (by fun_prop))
    refine this.congr (Filter.Eventually.of_forall (fun t => ?_))
    simp only [hG]; ring
  have hFn : Integrable (fun t => ‖F t‖) (volume.restrict (Set.Ioc (0 : ℝ) x)) := by
    have := integrableOn_Ioc_of_cont F hFi hx0 hx1 (fun _ => 1) continuous_const
    simpa using this.norm
  have hsum : Summable (fun k => ∫ t in Set.Ioc (0 : ℝ) x, ‖G k t‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun t => norm_nonneg _))
      (fun k => ?_) ((Real.summable_pow_div_factorial (‖a‖ * x)).mul_right
        (∫ t in Set.Ioc (0 : ℝ) x, ‖F t‖))
    have hb : ∀ t ∈ Set.Ioc (0 : ℝ) x, ‖G k t‖ ≤
        (‖a‖ * x) ^ k / (k.factorial : ℝ) * ‖F t‖ := by
      intro t ht
      have he : (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * ((x - 2 * t : ℝ) : ℂ)).re = 0 := by
        simp
      have e : ‖G k t‖ = ‖a‖ ^ k / (k.factorial : ℝ) *
          (‖((x - 2 * t : ℝ) : ℂ)‖ ^ k * ‖F t‖) := by
        simp only [hG, norm_mul, norm_div, norm_pow, Complex.norm_I, one_mul,
          Complex.norm_natCast, Complex.norm_exp, he, Real.exp_zero]
      have hs := norm_sreal_le hx0 ht
      have hsk : ‖((x - 2 * t : ℝ) : ℂ)‖ ^ k * ‖F t‖ ≤ x ^ k * ‖F t‖ := by
        gcongr
      rw [e]
      calc ‖a‖ ^ k / (k.factorial : ℝ) * (‖((x - 2 * t : ℝ) : ℂ)‖ ^ k * ‖F t‖)
          ≤ ‖a‖ ^ k / (k.factorial : ℝ) * (x ^ k * ‖F t‖) := by gcongr
        _ = (‖a‖ * x) ^ k / (k.factorial : ℝ) * ‖F t‖ := by rw [mul_pow]; ring
    calc ∫ t in Set.Ioc (0 : ℝ) x, ‖G k t‖
        ≤ ∫ t in Set.Ioc (0 : ℝ) x, (‖a‖ * x) ^ k / (k.factorial : ℝ) * ‖F t‖ :=
          setIntegral_mono_on (hGint k).norm (hFn.const_mul _) measurableSet_Ioc hb
      _ = _ := integral_const_mul _ _
  have hH := hasSum_integral_of_summable_integral_norm hGint hsum
  have hpt : ∀ t : ℝ, ∑' k, G k t =
      Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ) + a) * ((x - 2 * t : ℝ) : ℂ)) * F t := by
    intro t
    have h1 := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ)
      (Complex.I * a * ((x - 2 * t : ℝ) : ℂ)))
    rw [← Complex.exp_eq_exp_ℂ] at h1
    have h2 := (h1.mul_left (Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) *
      ((x - 2 * t : ℝ) : ℂ)) * F t))
    have h3 : (fun k : ℕ => G k t) = fun k : ℕ =>
        Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * ((x - 2 * t : ℝ) : ℂ)) * F t *
          ((Complex.I * a * ((x - 2 * t : ℝ) : ℂ)) ^ k / (k.factorial : ℂ)) := by
      funext k
      simp only [hG]
      rw [mul_pow, mul_pow]
      ring
    rw [h3, h2.tsum_eq, mul_assoc, mul_comm (F t), ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp_rw [hpt] at hH
  rw [intervalIntegral.integral_of_le hx0]
  convert hH using 2 with k
  rw [bco, intervalIntegral.integral_of_le hx0, integral_const_mul]



theorem memlp_two_of_summable (v : ℤ → ℂ) (hv : Summable (fun n : ℤ => ‖v n‖ ^ 2)) :
    Memℓp v 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  simpa using hv

theorem lp_two_norm_sq (u : lp (fun _ : ℤ => ℂ) 2) :
    HasSum (fun n : ℤ => ‖u n‖ ^ 2) (‖u‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) u
  simpa using h

theorem minkowski_series (v : ℕ → ℤ → ℂ) (B : ℕ → ℝ) (S : ℤ → ℂ)
    (hsum : ∀ k, Summable (fun n : ℤ => ‖v k n‖ ^ 2))
    (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ k, ∑' n : ℤ, ‖v k n‖ ^ 2 ≤ B k ^ 2)
    (hBs : Summable B)
    (hS : ∀ n, HasSum (fun k => v k n) (S n)) :
    Summable (fun n : ℤ => ‖S n‖ ^ 2) ∧ ∑' n : ℤ, ‖S n‖ ^ 2 ≤ (∑' k, B k) ^ 2 := by
  let u : ℕ → lp (fun _ : ℤ => ℂ) 2 := fun k => ⟨v k, memlp_two_of_summable _ (hsum k)⟩
  have hu_apply : ∀ k n, u k n = v k n := fun k n => rfl
  have hnorm : ∀ k, ‖u k‖ ≤ B k := by
    intro k
    have h1 := (lp_two_norm_sq (u k)).tsum_eq
    have h2 : ‖u k‖ ^ 2 ≤ B k ^ 2 := by
      rw [← h1]; simpa [hu_apply] using hB k
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (hB0 k) (by norm_num : (2 : ℕ) ≠ 0)).mp h2
  have hus : Summable (fun k => ‖u k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hnorm hBs
  have hus' : Summable u := hus.of_norm
  set T := ∑' k, u k with hT
  have hTs : HasSum u T := hus'.hasSum
  have hcoord : ∀ n, HasSum (fun k => v k n) (T n) := by
    intro n
    let ev : lp (fun _ : ℤ => ℂ) 2 →+ ℂ :=
      { toFun := fun f => f n, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have hcont : Continuous ev :=
      AddMonoidHomClass.continuous_of_bound ev 1 (fun f => by
        show ‖f n‖ ≤ 1 * ‖f‖
        rw [one_mul]
        exact lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) f n)
    exact hTs.map ev hcont
  have hST : ∀ n, S n = T n := fun n => (hS n).unique (hcoord n)
  have hTn := lp_two_norm_sq T
  have hbound : ‖T‖ ≤ ∑' k, B k :=
    (norm_tsum_le_tsum_norm hus).trans (Summable.tsum_le_tsum hnorm hus hBs)
  refine ⟨?_, ?_⟩
  · simp_rw [hST]; exact hTn.summable
  · simp_rw [hST]
    rw [hTn.tsum_eq]
    exact pow_le_pow_left₀ (norm_nonneg _) hbound 2


theorem exp_sub_one_hasSum (a : ℝ) :
    HasSum (fun k : ℕ => a ^ (k + 1) / ((k + 1).factorial : ℝ)) (Real.exp a - 1) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) a
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := (hasSum_nat_add_iff' 1).mpr h
  simpa using h2

theorem pert_weighted (F : ℝ → ℂ) (hFm : AEStronglyMeasurable F volume)
    (hFi : IntervalIntegrable F volume 0 1)
    (hF2 : IntervalIntegrable (fun t => ‖F t‖ ^ 2) volume 0 1)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {a : ℝ} (ha : 0 ≤ a)
    (w : ℤ → ℝ) (hw : ∀ n, 1 ≤ w n) (α : ℤ → ℂ) (hα : ∀ n, ‖α n‖ * w n ≤ a) :
    Summable (fun n : ℤ => w n ^ 2 * ‖∫ t in (0 : ℝ)..x,
        (Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ) + α n) * ((x - 2 * t : ℝ) : ℂ)) -
          Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ) * ((x - 2 * t : ℝ) : ℂ))) *
            F t‖ ^ 2) ∧
    ∑' n : ℤ, w n ^ 2 * ‖∫ t in (0 : ℝ)..x,
        (Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ) + α n) * ((x - 2 * t : ℝ) : ℂ)) -
          Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ) * ((x - 2 * t : ℝ) : ℂ))) *
            F t‖ ^ 2 ≤ Real.exp (2 * a) * ∫ t in (0 : ℝ)..1, ‖F t‖ ^ 2 := by
  set I2 : ℝ := ∫ t in (0 : ℝ)..1, ‖F t‖ ^ 2 with hI2
  have hI2nn : 0 ≤ I2 := intervalIntegral.integral_nonneg (by norm_num) (fun t _ => by positivity)
  set c : ℤ → ℂ := fun n => ∫ t in (0 : ℝ)..x,
        (Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ) + α n) * ((x - 2 * t : ℝ) : ℂ)) -
          Complex.exp (Complex.I * (n : ℂ) * (Real.pi : ℂ) * ((x - 2 * t : ℝ) : ℂ))) *
            F t with hc
  have hαa : ∀ n, ‖α n‖ ≤ a := fun n => by
    have := hα n; have := hw n
    nlinarith [norm_nonneg (α n)]
  let v : ℕ → ℤ → ℂ := fun k n =>
    (w n : ℂ) * ((Complex.I * α n) ^ (k + 1) / ((k + 1).factorial : ℂ) * bco F x (k + 1) n)
  have hvnorm : ∀ k n, ‖v k n‖ ≤ a ^ (k + 1) / ((k + 1).factorial : ℝ) * ‖bco F x (k + 1) n‖ := by
    intro k n
    simp only [v, norm_mul, norm_div, norm_pow, Complex.norm_I, one_mul, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs]
    have hw0 : 0 ≤ w n := (zero_le_one.trans (hw n))
    rw [abs_of_nonneg hw0]
    have hk : w n * ‖α n‖ ^ (k + 1) ≤ a ^ (k + 1) := by
      rw [pow_succ']
      calc w n * (‖α n‖ * ‖α n‖ ^ k) = (‖α n‖ * w n) * ‖α n‖ ^ k := by ring
        _ ≤ a * a ^ k := by
          gcongr
          · exact hα n
          · exact hαa n
        _ = a ^ (k + 1) := by ring
    have hfac : (0 : ℝ) < ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    calc w n * (‖α n‖ ^ (k + 1) / ((k + 1).factorial : ℝ) * ‖bco F x (k + 1) n‖)
        = (w n * ‖α n‖ ^ (k + 1)) / ((k + 1).factorial : ℝ) * ‖bco F x (k + 1) n‖ := by ring
      _ ≤ a ^ (k + 1) / ((k + 1).factorial : ℝ) * ‖bco F x (k + 1) n‖ := by gcongr
  have hbco := fun k => bco_sq_summable_le F hFm hF2 hx0 hx1 k
  have hsq : ∀ k n, ‖v k n‖ ^ 2 ≤
      (a ^ (k + 1) / ((k + 1).factorial : ℝ)) ^ 2 * ‖bco F x (k + 1) n‖ ^ 2 := by
    intro k n
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hvnorm k n) 2
  have hsum : ∀ k, Summable (fun n : ℤ => ‖v k n‖ ^ 2) := fun k =>
    Summable.of_nonneg_of_le (fun n => by positivity) (hsq k)
      ((hbco (k + 1)).1.mul_left _)
  set B : ℕ → ℝ := fun k => a ^ (k + 1) / ((k + 1).factorial : ℝ) * Real.sqrt I2 with hB
  have hB0 : ∀ k, 0 ≤ B k := fun k => by simp only [hB]; positivity
  have hBk : ∀ k, ∑' n : ℤ, ‖v k n‖ ^ 2 ≤ B k ^ 2 := by
    intro k
    calc ∑' n : ℤ, ‖v k n‖ ^ 2
        ≤ ∑' n : ℤ, (a ^ (k + 1) / ((k + 1).factorial : ℝ)) ^ 2 * ‖bco F x (k + 1) n‖ ^ 2 :=
          Summable.tsum_le_tsum (hsq k) (hsum k) ((hbco (k + 1)).1.mul_left _)
      _ = (a ^ (k + 1) / ((k + 1).factorial : ℝ)) ^ 2 * ∑' n : ℤ, ‖bco F x (k + 1) n‖ ^ 2 :=
          tsum_mul_left
      _ ≤ (a ^ (k + 1) / ((k + 1).factorial : ℝ)) ^ 2 * I2 := by
          gcongr
          exact (hbco (k + 1)).2
      _ = B k ^ 2 := by
          simp only [hB]; rw [mul_pow, Real.sq_sqrt hI2nn]
  have hexp := exp_sub_one_hasSum a
  have hBs : HasSum B (Real.sqrt I2 * (Real.exp a - 1)) := by
    have := hexp.mul_right (Real.sqrt I2)
    simp only [hB]
    rw [mul_comm (Real.sqrt I2)]
    exact this
  have hS : ∀ n, HasSum (fun k => v k n) ((w n : ℂ) * c n) := by
    intro n
    have H := pert_hasSum F hFi hx0 hx1 (α n) n
    have H1 := (hasSum_nat_add_iff' 1).mpr H
    have H2 := H1.mul_left (w n : ℂ)
    have ii : ∀ cc : ℝ → ℂ, Continuous cc →
        IntervalIntegrable (fun t => cc t * F t) volume 0 x := fun cc hcc =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hx0).mpr
        (integrableOn_Ioc_of_cont F hFi hx0 hx1 cc hcc)
    have i1 := ii (fun t => Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ) + α n) *
      ((x - 2 * t : ℝ) : ℂ))) (by fun_prop)
    have i2 := ii (fun t => Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) *
      ((x - 2 * t : ℝ) : ℂ)) * ((x - 2 * t : ℝ) : ℂ) ^ 0) (by fun_prop)
    have i2' : IntervalIntegrable (fun t => Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) *
      ((x - 2 * t : ℝ) : ℂ)) * (((x - 2 * t : ℝ) : ℂ) ^ 0 * F t)) volume 0 x := by
      refine i2.congr (fun t _ => ?_)
      exact mul_assoc _ _ _
    have hcn : c n = (∫ t in (0 : ℝ)..x, Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ) + α n) *
      ((x - 2 * t : ℝ) : ℂ)) * F t) - bco F x 0 n := by
      simp only [hc]
      rw [bco, ← intervalIntegral.integral_sub i1 i2']
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      rw [show Complex.I * (n : ℂ) * (Real.pi : ℂ) * ((x - 2 * t : ℝ) : ℂ) =
        Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * ((x - 2 * t : ℝ) : ℂ) by ring]
      ring
    rw [hcn]
    convert H2 using 2
    simp
  obtain ⟨hs1, hs2⟩ := minkowski_series v B (fun n => (w n : ℂ) * c n) hsum hB0 hBk hBs.summable hS
  have hnorm : ∀ n, ‖(w n : ℂ) * c n‖ ^ 2 = w n ^ 2 * ‖c n‖ ^ 2 := by
    intro n
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hnorm] at hs1 hs2
  refine ⟨hs1, hs2.trans ?_⟩
  rw [hBs.tsum_eq, mul_pow, Real.sq_sqrt hI2nn, mul_comm]
  gcongr
  have h1 : Real.exp a - 1 ≤ Real.exp a := by linarith
  have h0 : 0 ≤ Real.exp a - 1 := by
    have := Real.add_one_le_exp a; linarith
  calc (Real.exp a - 1) ^ 2 ≤ (Real.exp a) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = Real.exp (2 * a) := by rw [← Real.exp_nat_mul]; norm_num

end NlsGge.ThirdConsultation.KSPS008Support
