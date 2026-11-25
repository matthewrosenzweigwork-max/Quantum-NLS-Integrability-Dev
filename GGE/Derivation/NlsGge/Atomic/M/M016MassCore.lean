import Mathlib
import NlsGge.GK38.PairPotential


/- M016 MASS CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/M/M016MassCore.lean, namespace NlsGge.ThirdConsultation.M016MassAux. Supporting leaves (c) and (d) of
   the N=0 bilinear-mass support `M.discriminant_imaginary_bilinear_mass` (Pro R16 §1.3, proof §4); no packet increment.
   * `pairW t s r`: helper (supporting) definition of the §4 triangular kernel after division by e^t:
     e^{-2t(s-r)} for r ≤ s, e^{-2t(1+s-r)} for s < r (the full periodic convolution kernel on [0,1]²).
   * rowSum / colSum: exact row and column integrals (1-e^{-2t})/(2t).
   * schur_bound (real), Q_norm_le (complex): leaf (c), A_t ≤ (1-e^{-2t})/(2t)·‖u‖₂‖v‖₂ ≤ M/(2t).
     ROUTE NOTE: Schur test (row/column sums + weighted AM-GM) instead of §4's Young + Cauchy–Schwarz; same bound,
     same kernel L¹ norm. Recorded for review.
   * mass_limit: leaf (d), 2t·P_t → ∫₀¹ u v for u, v ∈ L²(0,1); mass_limit_cover: the same for the actual period-one
     representatives coverRep38 φ.1, coverRep38 φ.2 (= potRepFst38/potRepSnd38 by definition).
     ROUTE NOTE: §4 proves (d) by L² continuity of translation with a δ-split of the kernel. Here the same limit is proved
     by density of bounded continuous functions in L² (Mathlib MemLp.exists_boundedContinuous_eLpNorm_sub_le), the
     uniform bound (c), and pointwise concentration of the kernel at r = s⁻ (substitution + dominated convergence),
     with the wrap-around piece O(e^{-2ts}). Different local argument for the same lemma; recorded for review.
   No hypothesis beyond u, v ∈ L²(0,1); no reality restriction or conjugation. Mirror lane-checked in full. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology intervalIntegral

namespace NlsGge.ThirdConsultation.M016MassAux

/-- Helper kernel (Pro R16 §4, after division by `e^t`): `e^{-2t(s-r)}` for `r ≤ s` and
`e^{-2t(1+s-r)}` for `s < r`; together the full periodic convolution kernel on `[0,1]²`. -/
def pairW (t s r : ℝ) : ℝ :=
  if r ≤ s then Real.exp (-(2 * t * (s - r))) else Real.exp (-(2 * t * (1 + s - r)))

theorem pairW_pos (t s r : ℝ) : 0 < pairW t s r := by
  unfold pairW; split_ifs <;> exact Real.exp_pos _

theorem pairW_le_one {t s r : ℝ} (ht : 0 ≤ t) (hs : s ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1) :
    pairW t s r ≤ 1 := by
  unfold pairW
  split_ifs with h
  · rw [Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg (by linarith) (by linarith)
  · rw [Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg (by linarith) (by linarith [hs.1, hr.2])

theorem measurable_pairW (t : ℝ) : Measurable (fun p : ℝ × ℝ => pairW t p.1 p.2) := by
  unfold pairW
  exact Measurable.ite (measurableSet_le measurable_snd measurable_fst) (by fun_prop) (by fun_prop)

theorem ae_ne_point (x : ℝ) : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ x := by
  rw [ae_iff]; simp

/-! ### Explicit exponential integrals -/

theorem int_exp_left (t s : ℝ) (ht : 0 < t) :
    ∫ r in (0 : ℝ)..s, Real.exp (-(2 * t * (s - r))) = (1 - Real.exp (-(2 * t * s))) / (2 * t) := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) s, HasDerivAt (fun r => Real.exp (-(2 * t * (s - r))) / (2 * t))
      (Real.exp (-(2 * t * (s - x)))) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => -(2 * t * (s - r))) (2 * t) x := by
      have := ((hasDerivAt_id x).const_mul (2 * t)).sub_const (2 * t * s)
      convert this using 1
      · funext y; simp only [id]; ring
      · ring
    convert (h1.exp).div_const (2 * t) using 1
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous fun x : ℝ =>
    Real.exp (-(2 * t * (s - x)))).intervalIntegrable _ _)]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, sub_zero]
  ring

theorem int_exp_right (t s : ℝ) (ht : 0 < t) :
    ∫ r in s..1, Real.exp (-(2 * t * (1 + s - r))) =
      (Real.exp (-(2 * t * s)) - Real.exp (-(2 * t))) / (2 * t) := by
  have hd : ∀ x ∈ uIcc s 1, HasDerivAt (fun r => Real.exp (-(2 * t * (1 + s - r))) / (2 * t))
      (Real.exp (-(2 * t * (1 + s - x)))) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => -(2 * t * (1 + s - r))) (2 * t) x := by
      have := ((hasDerivAt_id x).const_mul (2 * t)).sub_const (2 * t * (1 + s))
      convert this using 1
      · funext y; simp only [id]; ring
      · ring
    convert (h1.exp).div_const (2 * t) using 1
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous fun x : ℝ =>
    Real.exp (-(2 * t * (1 + s - x)))).intervalIntegrable _ _)]
  simp only [add_sub_cancel_left, add_sub_cancel_right, mul_one]
  ring

theorem int_exp_left_col (t r : ℝ) (ht : 0 < t) :
    ∫ s in (0 : ℝ)..r, Real.exp (-(2 * t * (1 + s - r))) =
      (Real.exp (-(2 * t * (1 - r))) - Real.exp (-(2 * t))) / (2 * t) := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) r, HasDerivAt (fun s => -Real.exp (-(2 * t * (1 + s - r))) / (2 * t))
      (Real.exp (-(2 * t * (1 + x - r)))) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => -(2 * t * (1 + s - r))) (-(2 * t)) x := by
      have := ((hasDerivAt_id x).const_mul (-(2 * t))).sub_const (2 * t * (1 - r))
      convert this using 1
      · funext y; simp only [id]; ring
      · ring
    convert ((h1.exp).neg).div_const (2 * t) using 1
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous fun x : ℝ =>
    Real.exp (-(2 * t * (1 + x - r)))).intervalIntegrable _ _)]
  have e1 : (1 : ℝ) + r - r = 1 := by ring
  have e2 : (1 : ℝ) + 0 - r = 1 - r := by ring
  rw [e1, e2, mul_one]
  ring

theorem int_exp_right_col (t r : ℝ) (ht : 0 < t) :
    ∫ s in r..1, Real.exp (-(2 * t * (s - r))) =
      (1 - Real.exp (-(2 * t * (1 - r)))) / (2 * t) := by
  have hd : ∀ x ∈ uIcc r 1, HasDerivAt (fun s => -Real.exp (-(2 * t * (s - r))) / (2 * t))
      (Real.exp (-(2 * t * (x - r)))) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => -(2 * t * (s - r))) (-(2 * t)) x := by
      have := ((hasDerivAt_id x).const_mul (-(2 * t))).add_const (2 * t * r)
      convert this using 1
      · funext y; simp only [id]; ring
      · ring
    convert ((h1.exp).neg).div_const (2 * t) using 1
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous fun x : ℝ =>
    Real.exp (-(2 * t * (x - r)))).intervalIntegrable _ _)]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero]
  ring

/-! ### Interval integrability and the row/column sums -/

theorem intervalIntegrable_pairW_r (t s : ℝ) (ht : 0 ≤ t) (hs : s ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun r => pairW t s r) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    ((measurable_pairW t).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_)
  rw [Real.norm_of_nonneg (pairW_pos t s r).le]
  exact pairW_le_one ht hs (Ioc_subset_Icc_self hr)

theorem intervalIntegrable_pairW_s (t r : ℝ) (ht : 0 ≤ t) (hr : r ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s => pairW t s r) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    ((measurable_pairW t).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_)
  rw [Real.norm_of_nonneg (pairW_pos t s r).le]
  exact pairW_le_one ht (Ioc_subset_Icc_self hs) hr

/-- Row sums: `∫₀¹ w(s,r) dr = (1-e^{-2t})/(2t)` for every `s ∈ [0,1]`. -/
theorem rowSum (t s : ℝ) (ht : 0 < t) (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫ r in (0 : ℝ)..1, pairW t s r = (1 - Real.exp (-(2 * t))) / (2 * t) := by
  have hII := intervalIntegrable_pairW_r t s ht.le hs
  have h1 : IntervalIntegrable (fun r => pairW t s r) volume 0 s :=
    hII.mono_set (uIcc_subset_uIcc (left_mem_uIcc) (by rw [uIcc_of_le zero_le_one]; exact hs))
  have h2 : IntervalIntegrable (fun r => pairW t s r) volume s 1 :=
    hII.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le zero_le_one]; exact hs) right_mem_uIcc)
  rw [← integral_add_adjacent_intervals h1 h2]
  have e1 : ∫ r in (0 : ℝ)..s, pairW t s r = ∫ r in (0 : ℝ)..s, Real.exp (-(2 * t * (s - r))) :=
    integral_congr fun r hr => by
      rw [uIcc_of_le hs.1] at hr
      show pairW t s r = _
      simp only [pairW, hr.2, ↓reduceIte]
  have e2 : ∫ r in s..1, pairW t s r = ∫ r in s..1, Real.exp (-(2 * t * (1 + s - r))) :=
    integral_congr_ae (Eventually.of_forall fun r hr => by
      rw [uIoc_of_le hs.2] at hr
      simp only [pairW, not_le.2 hr.1, ↓reduceIte])
  rw [e1, e2, int_exp_left t s ht, int_exp_right t s ht]
  ring

/-- Column sums: `∫₀¹ w(s,r) ds = (1-e^{-2t})/(2t)` for every `r ∈ [0,1]`. -/
theorem colSum (t r : ℝ) (ht : 0 < t) (hr : r ∈ Icc (0 : ℝ) 1) :
    ∫ s in (0 : ℝ)..1, pairW t s r = (1 - Real.exp (-(2 * t))) / (2 * t) := by
  have hII := intervalIntegrable_pairW_s t r ht.le hr
  have h1 : IntervalIntegrable (fun s => pairW t s r) volume 0 r :=
    hII.mono_set (uIcc_subset_uIcc (left_mem_uIcc) (by rw [uIcc_of_le zero_le_one]; exact hr))
  have h2 : IntervalIntegrable (fun s => pairW t s r) volume r 1 :=
    hII.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le zero_le_one]; exact hr) right_mem_uIcc)
  rw [← integral_add_adjacent_intervals h1 h2]
  have e1 : ∫ s in (0 : ℝ)..r, pairW t s r = ∫ s in (0 : ℝ)..r, Real.exp (-(2 * t * (1 + s - r))) :=
    integral_congr_ae ((ae_ne_point r).mono fun s hne hs => by
      rw [uIoc_of_le hr.1] at hs
      simp only [pairW, not_le.2 (lt_of_le_of_ne hs.2 hne), ↓reduceIte])
  have e2 : ∫ s in r..1, pairW t s r = ∫ s in r..1, Real.exp (-(2 * t * (s - r))) :=
    integral_congr_ae (Eventually.of_forall fun s hs => by
      rw [uIoc_of_le hr.2] at hs
      simp only [pairW, hs.1.le, ↓reduceIte])
  rw [e1, e2, int_exp_left_col t r ht, int_exp_right_col t r ht]
  ring

end NlsGge.ThirdConsultation.M016MassAux

namespace NlsGge.ThirdConsultation.M016MassAux

/-- Optimizing the weighted AM-GM bound over `ε > 0`. -/
theorem le_of_forall_amgm {L c X Y : ℝ} (hc : 0 ≤ c) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : ∀ ε : ℝ, 0 < ε → L ≤ c * (ε * X + Y / ε) / 2) :
    L ≤ c * (Real.sqrt X * Real.sqrt Y) := by
  rcases eq_or_lt_of_le hX with hX0 | hXp
  · subst hX0
    rw [Real.sqrt_zero, zero_mul, mul_zero]
    refine le_of_forall_pos_lt_add fun η hη => ?_
    have hε : 0 < (c * Y + 1) / η := by positivity
    have h1 := h _ hε
    have h2 : c * ((c * Y + 1) / η * 0 + Y / ((c * Y + 1) / η)) / 2 ≤ η / 2 := by
      rw [mul_zero, zero_add, div_div_eq_mul_div, div_le_div_iff_of_pos_right two_pos,
        mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hc hY]
    linarith
  rcases eq_or_lt_of_le hY with hY0 | hYp
  · subst hY0
    rw [Real.sqrt_zero, mul_zero, mul_zero]
    refine le_of_forall_pos_lt_add fun η hη => ?_
    have hε : 0 < η / (c * X + 1) := by positivity
    have h1 := h _ hε
    have h2 : c * (η / (c * X + 1) * X + 0 / (η / (c * X + 1))) / 2 ≤ η / 2 := by
      rw [zero_div, add_zero, div_le_div_iff_of_pos_right two_pos, div_mul_eq_mul_div,
        mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hc hX]
    linarith
  · have hsX := Real.sqrt_pos.2 hXp
    have hsY := Real.sqrt_pos.2 hYp
    have h1 := h (Real.sqrt Y / Real.sqrt X) (div_pos hsY hsX)
    have hXs : X = Real.sqrt X * Real.sqrt X := (Real.mul_self_sqrt hX).symm
    have hYs : Y = Real.sqrt Y * Real.sqrt Y := (Real.mul_self_sqrt hY).symm
    have h2 : c * (Real.sqrt Y / Real.sqrt X * X + Y / (Real.sqrt Y / Real.sqrt X)) / 2 =
        c * (Real.sqrt X * Real.sqrt Y) := by
      rw [hXs, hYs]
      rw [Real.sqrt_mul_self (Real.sqrt_nonneg X), Real.sqrt_mul_self (Real.sqrt_nonneg Y)]
      field_simp
      ring
    linarith

/-- **Leaf (c), Schur bound.** For real `a, b ∈ L²(0,1)`,
`∫∫ w(s,r) a(s) b(r) ≤ (1-e^{-2t})/(2t) · ‖a‖₂ ‖b‖₂` (`A_t ≤ M/(2t)` in Pro R16 §4). -/
theorem schur_bound (t : ℝ) (ht : 0 < t) {a b : ℝ → ℝ}
    (ha : MemLp a 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hb : MemLp b 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    ∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1, pairW t s r * a s * b r ≤
      (1 - Real.exp (-(2 * t))) / (2 * t) *
        (Real.sqrt (∫ s in Ioc (0 : ℝ) 1, a s ^ 2) * Real.sqrt (∫ r in Ioc (0 : ℝ) 1, b r ^ 2)) := by
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hμ
  set c : ℝ := (1 - Real.exp (-(2 * t))) / (2 * t) with hcdef
  have hc0 : 0 ≤ c := div_nonneg (sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith)))
    (by linarith)
  have ha1 : Integrable a μ := ha.integrable one_le_two
  have hb1 : Integrable b μ := hb.integrable one_le_two
  have ha2 : Integrable (fun s => a s ^ 2) μ := ha.integrable_sq
  have hb2 : Integrable (fun r => b r ^ 2) μ := hb.integrable_sq
  have hprod : μ.prod μ = (volume.prod volume).restrict (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :=
    Measure.prod_restrict _ _
  have hW_ae : ∀ᵐ p ∂(μ.prod μ), ‖pairW t p.1 p.2‖ ≤ 1 := by
    rw [hprod]
    refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) fun p hp => ?_
    rw [Real.norm_of_nonneg (pairW_pos _ _ _).le]
    exact pairW_le_one ht.le (Ioc_subset_Icc_self hp.1) (Ioc_subset_Icc_self hp.2)
  have hWm : AEStronglyMeasurable (fun p : ℝ × ℝ => pairW t p.1 p.2) (μ.prod μ) :=
    (measurable_pairW t).aestronglyMeasurable
  have hIab : Integrable (fun p : ℝ × ℝ => pairW t p.1 p.2 * (a p.1 * b p.2)) (μ.prod μ) :=
    (ha1.mul_prod hb1).bdd_mul hWm hW_ae
  have hIa : Integrable (fun p : ℝ × ℝ => pairW t p.1 p.2 * (a p.1 ^ 2 * 1)) (μ.prod μ) :=
    (ha2.mul_prod (integrable_const (1 : ℝ))).bdd_mul hWm hW_ae
  have hIb : Integrable (fun p : ℝ × ℝ => pairW t p.1 p.2 * (1 * b p.2 ^ 2)) (μ.prod μ) :=
    ((integrable_const (1 : ℝ)).mul_prod hb2).bdd_mul hWm hW_ae
  -- row and column sums as set integrals
  have hrow : ∀ s ∈ Ioc (0 : ℝ) 1, ∫ r, pairW t s r ∂μ = c := fun s hs => by
    rw [hμ, ← intervalIntegral.integral_of_le zero_le_one]
    exact rowSum t s ht (Ioc_subset_Icc_self hs)
  have hcol : ∀ r ∈ Ioc (0 : ℝ) 1, ∫ s, pairW t s r ∂μ = c := fun r hr => by
    rw [hμ, ← intervalIntegral.integral_of_le zero_le_one]
    exact colSum t r ht (Ioc_subset_Icc_self hr)
  have hXa : ∫ p, pairW t p.1 p.2 * (a p.1 ^ 2 * 1) ∂(μ.prod μ) = c * ∫ s, a s ^ 2 ∂μ := by
    rw [integral_prod _ hIa, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    simp only [mul_one]
    rw [MeasureTheory.integral_mul_const, hrow s hs, mul_comm]
  have hXb : ∫ p, pairW t p.1 p.2 * (1 * b p.2 ^ 2) ∂(μ.prod μ) = c * ∫ r, b r ^ 2 ∂μ := by
    rw [integral_prod_symm _ hIb, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    simp only [one_mul]
    rw [MeasureTheory.integral_mul_const, hcol r hr, mul_comm]
  have hL : (∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1, pairW t s r * a s * b r) =
      ∫ p, pairW t p.1 p.2 * (a p.1 * b p.2) ∂(μ.prod μ) := by
    rw [integral_prod _ hIab]
    exact integral_congr_ae (Eventually.of_forall fun s => integral_congr_ae
      (Eventually.of_forall fun r => by simp only [mul_assoc]))
  rw [hL]
  refine le_of_forall_amgm hc0 (integral_nonneg fun s => sq_nonneg (a s))
    (integral_nonneg fun r => sq_nonneg (b r)) fun ε hε => ?_
  calc ∫ p, pairW t p.1 p.2 * (a p.1 * b p.2) ∂(μ.prod μ)
      ≤ ∫ p, (ε / 2 * (pairW t p.1 p.2 * (a p.1 ^ 2 * 1)) +
          1 / (2 * ε) * (pairW t p.1 p.2 * (1 * b p.2 ^ 2))) ∂(μ.prod μ) := by
        refine integral_mono hIab ((hIa.const_mul _).add (hIb.const_mul _)) fun p => ?_
        have hw := (pairW_pos t p.1 p.2).le
        have key : a p.1 * b p.2 ≤ ε / 2 * a p.1 ^ 2 + 1 / (2 * ε) * b p.2 ^ 2 := by
          have : ε / 2 * a p.1 ^ 2 + 1 / (2 * ε) * b p.2 ^ 2 - a p.1 * b p.2 =
              (ε * a p.1 - b p.2) ^ 2 / (2 * ε) := by
            field_simp; ring
          have : 0 ≤ (ε * a p.1 - b p.2) ^ 2 / (2 * ε) := by positivity
          linarith
        have := mul_le_mul_of_nonneg_left key hw
        simp only [mul_one, one_mul]
        nlinarith [this]
    _ = ε / 2 * (c * ∫ s, a s ^ 2 ∂μ) + 1 / (2 * ε) * (c * ∫ r, b r ^ 2 ∂μ) := by
        rw [integral_add (hIa.const_mul _) (hIb.const_mul _), MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul, hXa, hXb]
    _ = c * (ε * (∫ s in Ioc (0 : ℝ) 1, a s ^ 2) + (∫ r in Ioc (0 : ℝ) 1, b r ^ 2) / ε) / 2 := by
        field_simp
        ring

end NlsGge.ThirdConsultation.M016MassAux

namespace NlsGge.ThirdConsultation.M016MassAux

/-- Left piece of the kernel average: `2t ∫₀ˢ e^{-2t(s-r)} g(r) dr → g(s)` for continuous bounded `g`, `s > 0`. -/
theorem left_conc (g : ℝ → ℂ) (hg : Continuous g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) {s : ℝ}
    (hs : 0 < s) :
    Tendsto (fun t : ℝ => ((2 * t : ℝ) : ℂ) *
      ∫ r in (0 : ℝ)..s, (Real.exp (-(2 * t * (s - r))) : ℂ) * g r) atTop (𝓝 (g s)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set h : ℝ → ℝ → ℂ := fun t x => (Real.exp (-x) : ℂ) * g (s - x / (2 * t)) with hh
  have hhc : ∀ t, Continuous (h t) := fun t =>
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).mul
      (hg.comp (continuous_const.sub (continuous_id.div_const _)))
  have hrep : ∀ t : ℝ, 0 < t → ((2 * t : ℝ) : ℂ) *
      ∫ r in (0 : ℝ)..s, (Real.exp (-(2 * t * (s - r))) : ℂ) * g r =
      ∫ x in Ioi (0 : ℝ), (Iic (2 * t * s)).indicator (h t) x := by
    intro t ht
    have h2t : (2 * t : ℝ) ≠ 0 := by positivity
    have e1 : ∫ r in (0 : ℝ)..s, (Real.exp (-(2 * t * (s - r))) : ℂ) * g r =
        ∫ σ in (0 : ℝ)..s, (Real.exp (-(2 * t * σ)) : ℂ) * g (s - σ) := by
      have := intervalIntegral.integral_comp_sub_left
        (fun σ : ℝ => (Real.exp (-(2 * t * σ)) : ℂ) * g (s - σ)) (a := 0) (b := s) s
      simp only [sub_sub_cancel, sub_self, sub_zero] at this
      exact this
    have e2 : ∫ σ in (0 : ℝ)..s, (Real.exp (-(2 * t * σ)) : ℂ) * g (s - σ) =
        (2 * t)⁻¹ • ∫ x in (0 : ℝ)..(2 * t * s), h t x := by
      have := intervalIntegral.integral_comp_mul_left (h t) (a := 0) (b := s) h2t
      rw [mul_zero] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun σ _ => ?_
      simp only [hh]
      rw [mul_div_cancel_left₀ σ h2t]
    have e3 : ∫ x in (0 : ℝ)..(2 * t * s), h t x =
        ∫ x in Ioi (0 : ℝ), (Iic (2 * t * s)).indicator (h t) x := by
      rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic,
        intervalIntegral.integral_of_le (by positivity)]
    rw [e1, e2, e3, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ h2t,
      Complex.ofReal_one, one_mul]
  have hlim : Tendsto (fun t : ℝ => ∫ x in Ioi (0 : ℝ), (Iic (2 * t * s)).indicator (h t) x)
      atTop (𝓝 (∫ x in Ioi (0 : ℝ), (Real.exp (-x) : ℂ) * g s)) := by
    have hint : Integrable (fun x : ℝ => B * Real.exp (-x)) (volume.restrict (Ioi (0 : ℝ))) := by
      have := (exp_neg_integrableOn_Ioi 0 one_pos).const_mul B
      simpa only [neg_mul, one_mul] using this
    refine tendsto_integral_filter_of_dominated_convergence (fun x => B * Real.exp (-x))
      (Eventually.of_forall fun t => ((hhc t).aestronglyMeasurable.indicator measurableSet_Iic))
      (Eventually.of_forall fun t => Eventually.of_forall fun x => ?_) hint
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
    · refine le_trans (norm_indicator_le_norm_self (h t) x) ?_
      simp only [hh, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hB _) (Real.exp_pos _).le
    · have hev : ∀ᶠ t in atTop, (Iic (2 * t * s)).indicator (h t) x = h t x := by
        filter_upwards [eventually_ge_atTop (x / (2 * s))] with t ht
        have : x ≤ 2 * t * s := by
          rw [div_le_iff₀ (by positivity)] at ht
          linarith
        exact indicator_of_mem (show x ∈ Iic (2 * t * s) from this) (h t)
      refine Tendsto.congr' (EventuallyEq.symm hev) ?_
      have h0 : Tendsto (fun t : ℝ => x / (2 * t)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop two_pos)
      have h1 : Tendsto (fun t : ℝ => s - x / (2 * t)) atTop (𝓝 s) := by
        simpa using (tendsto_const_nhds (x := s)).sub h0
      exact tendsto_const_nhds.mul ((hg.tendsto s).comp h1)
  have hval : ∫ x in Ioi (0 : ℝ), (Real.exp (-x) : ℂ) * g s = g s := by
    rw [MeasureTheory.integral_mul_const, integral_complex_ofReal, integral_exp_neg_Ioi_zero,
      Complex.ofReal_one, one_mul]
  rw [hval] at hlim
  exact hlim.congr' ((eventually_gt_atTop 0).mono fun t ht => (hrep t ht).symm)

/-- Right (wrap-around) piece: `2t ∫ₛ¹ e^{-2t(1+s-r)} g(r) dr → 0` for `0 < s ≤ 1`. -/
theorem right_small (g : ℝ → ℂ) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Tendsto (fun t : ℝ => ((2 * t : ℝ) : ℂ) *
      ∫ r in s..1, (Real.exp (-(2 * t * (1 + s - r))) : ℂ) * g r) atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hdec : Tendsto (fun t : ℝ => B * Real.exp (-(2 * t * s))) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => 2 * t * s) atTop atTop :=
      (tendsto_id.const_mul_atTop two_pos).atTop_mul_const hs
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp this).const_mul B
  refine squeeze_zero_norm' ?_ hdec
  filter_upwards [eventually_gt_atTop 0] with t ht
  have hI : ‖∫ r in s..1, (Real.exp (-(2 * t * (1 + s - r))) : ℂ) * g r‖ ≤
      ∫ r in s..1, B * Real.exp (-(2 * t * (1 + s - r))) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hs1 (Eventually.of_forall fun r _ => ?_)
      ((by fun_prop : Continuous fun r : ℝ => B * Real.exp (-(2 * t * (1 + s - r)))).intervalIntegrable _ _)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB r) (Real.exp_pos _).le
  rw [intervalIntegral.integral_const_mul, int_exp_right t s ht] at hI
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc 2 * t * ‖∫ r in s..1, (Real.exp (-(2 * t * (1 + s - r))) : ℂ) * g r‖
      ≤ 2 * t * (B * ((Real.exp (-(2 * t * s)) - Real.exp (-(2 * t))) / (2 * t))) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = B * (Real.exp (-(2 * t * s)) - Real.exp (-(2 * t))) := by field_simp
    _ ≤ B * Real.exp (-(2 * t * s)) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.exp_pos (-(2 * t))]) hB0

theorem intervalIntegrable_pairW_mul (t s : ℝ) (ht : 0 ≤ t) (hs : s ∈ Icc (0 : ℝ) 1)
    (g : ℝ → ℂ) (hg : Continuous g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    IntervalIntegrable (fun r => (pairW t s r : ℂ) * g r) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := B) measure_Ioc_lt_top.ne
    ((Complex.measurable_ofReal.comp ((measurable_pairW t).comp
      (measurable_const.prodMk measurable_id))).mul hg.measurable).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pairW_pos t s r).le]
  calc pairW t s r * ‖g r‖ ≤ 1 * B :=
        mul_le_mul (pairW_le_one ht hs (Ioc_subset_Icc_self hr)) (hB r) (norm_nonneg _) zero_le_one
    _ = B := one_mul B

/-- **Pointwise concentration.** For `s ∈ (0,1]`: `2t ∫₀¹ w(s,r) g(r) dr → g(s)`. -/
theorem pointwise_conc (g : ℝ → ℂ) (hg : Continuous g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) :
    Tendsto (fun t : ℝ => ((2 * t : ℝ) : ℂ) * ∫ r in (0 : ℝ)..1, (pairW t s r : ℂ) * g r)
      atTop (𝓝 (g s)) := by
  have hsI : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
  have hsum := (left_conc g hg hB hs.1).add (right_small g hB hs.1 hs.2)
  rw [add_zero] at hsum
  refine hsum.congr' ((eventually_gt_atTop 0).mono fun t ht => ?_)
  beta_reduce
  have hII := intervalIntegrable_pairW_mul t s ht.le hsI g hg hB
  have h1 := hII.mono_set (uIcc_subset_uIcc left_mem_uIcc (by rw [uIcc_of_le zero_le_one]; exact hsI))
  have h2 := hII.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le zero_le_one]; exact hsI) right_mem_uIcc)
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, mul_add]
  have e1 : ∫ r in (0 : ℝ)..s, (pairW t s r : ℂ) * g r =
      ∫ r in (0 : ℝ)..s, (Real.exp (-(2 * t * (s - r))) : ℂ) * g r :=
    intervalIntegral.integral_congr fun r hr => by
      rw [uIcc_of_le hsI.1] at hr
      simp only [pairW, hr.2, ↓reduceIte]
  have e2 : ∫ r in s..1, (pairW t s r : ℂ) * g r =
      ∫ r in s..1, (Real.exp (-(2 * t * (1 + s - r))) : ℂ) * g r :=
    intervalIntegral.integral_congr_ae (Eventually.of_forall fun r hr => by
      rw [uIoc_of_le hsI.2] at hr
      simp only [pairW, not_le.2 hr.1, ↓reduceIte])
  rw [e1, e2]

end NlsGge.ThirdConsultation.M016MassAux

namespace NlsGge.ThirdConsultation.M016MassAux

/-- Cauchy–Schwarz on `(0,1]`, from the same AM-GM optimization. -/
theorem cs_bound {f h : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hh : MemLp h 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    ∫ s in Ioc (0 : ℝ) 1, ‖f s‖ * ‖h s‖ ≤
      Real.sqrt (∫ s in Ioc (0 : ℝ) 1, ‖f s‖ ^ 2) * Real.sqrt (∫ s in Ioc (0 : ℝ) 1, ‖h s‖ ^ 2) := by
  have hf2 := hf.norm.integrable_sq
  have hh2 := hh.norm.integrable_sq
  have hint : Integrable (fun s => ‖f s‖ * ‖h s‖) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    refine Integrable.mono' ((hf2.add hh2).div_const 2) (hf.aestronglyMeasurable.norm.mul hh.aestronglyMeasurable.norm)
      (Eventually.of_forall fun s => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖f s‖ - ‖h s‖)]
  have := le_of_forall_amgm (L := ∫ s in Ioc (0 : ℝ) 1, ‖f s‖ * ‖h s‖) (c := 1) zero_le_one
    (integral_nonneg fun s => sq_nonneg ‖f s‖) (integral_nonneg fun s => sq_nonneg ‖h s‖)
    (fun ε hε => by
      calc ∫ s in Ioc (0 : ℝ) 1, ‖f s‖ * ‖h s‖
          ≤ ∫ s in Ioc (0 : ℝ) 1, (ε / 2 * ‖f s‖ ^ 2 + 1 / (2 * ε) * ‖h s‖ ^ 2) := by
            refine integral_mono hint ((hf2.const_mul _).add (hh2.const_mul _)) fun s => ?_
            have : ε / 2 * ‖f s‖ ^ 2 + 1 / (2 * ε) * ‖h s‖ ^ 2 - ‖f s‖ * ‖h s‖ =
                (ε * ‖f s‖ - ‖h s‖) ^ 2 / (2 * ε) := by field_simp; ring
            have : 0 ≤ (ε * ‖f s‖ - ‖h s‖) ^ 2 / (2 * ε) := by positivity
            simp only
            linarith
        _ = 1 * (ε * (∫ s in Ioc (0 : ℝ) 1, ‖f s‖ ^ 2) + (∫ s in Ioc (0 : ℝ) 1, ‖h s‖ ^ 2) / ε) / 2 := by
            rw [integral_add (hf2.const_mul _) (hh2.const_mul _), MeasureTheory.integral_const_mul,
              MeasureTheory.integral_const_mul]
            field_simp)
  rwa [one_mul] at this

/-- The double integral as a product-measure integral. -/
theorem Q_eq_prod (t : ℝ) (ht : 0 ≤ t) {u h : ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hh : MemLp h 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    Integrable (fun p : ℝ × ℝ => (pairW t p.1 p.2 : ℂ) * (u p.1 * h p.2))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) ∧
    (∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1, (pairW t s r : ℂ) * u s * h r) =
      ∫ p, (pairW t p.1 p.2 : ℂ) * (u p.1 * h p.2)
        ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have hprod : μ.prod μ = (volume.prod volume).restrict (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) :=
    Measure.prod_restrict _ _
  have hW_ae : ∀ᵐ p ∂(μ.prod μ), ‖(pairW t p.1 p.2 : ℂ)‖ ≤ 1 := by
    rw [hprod]
    refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) fun p hp => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (pairW_pos _ _ _).le]
    exact pairW_le_one ht (Ioc_subset_Icc_self hp.1) (Ioc_subset_Icc_self hp.2)
  have hI : Integrable (fun p : ℝ × ℝ => (pairW t p.1 p.2 : ℂ) * (u p.1 * h p.2)) (μ.prod μ) :=
    ((hu.integrable one_le_two).mul_prod (hh.integrable one_le_two)).bdd_mul
      (Complex.measurable_ofReal.comp (measurable_pairW t)).aestronglyMeasurable hW_ae
  refine ⟨hI, ?_⟩
  rw [integral_prod _ hI]
  exact integral_congr_ae (Eventually.of_forall fun s => integral_congr_ae
    (Eventually.of_forall fun r => by simp only [mul_assoc]))

/-- **Leaf (c), complex form.** `‖∫∫ w u(s) h(r)‖ ≤ (1-e^{-2t})/(2t) ‖u‖₂ ‖h‖₂`. -/
theorem Q_norm_le (t : ℝ) (ht : 0 < t) {u h : ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hh : MemLp h 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    ‖∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1, (pairW t s r : ℂ) * u s * h r‖ ≤
      (1 - Real.exp (-(2 * t))) / (2 * t) *
        (Real.sqrt (∫ s in Ioc (0 : ℝ) 1, ‖u s‖ ^ 2) * Real.sqrt (∫ r in Ioc (0 : ℝ) 1, ‖h r‖ ^ 2)) := by
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  obtain ⟨hI, hQ⟩ := Q_eq_prod t ht.le hu hh
  rw [hQ]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  have hreal : ∫ p, ‖(pairW t p.1 p.2 : ℂ) * (u p.1 * h p.2)‖ ∂(μ.prod μ) =
      ∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1, pairW t s r * ‖u s‖ * ‖h r‖ := by
    rw [integral_prod _ hI.norm]
    exact integral_congr_ae (Eventually.of_forall fun s => integral_congr_ae
      (Eventually.of_forall fun r => by
        simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pairW_pos t s r).le, mul_assoc]))
  rw [hreal]
  exact schur_bound t ht hu.norm hh.norm

/-- Linearity in the second function. -/
theorem Q_sub (t : ℝ) (ht : 0 ≤ t) {u v g : ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hv : MemLp v 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    (∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1, (pairW t s r : ℂ) * u s * (v - g) r) =
      (∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1, (pairW t s r : ℂ) * u s * v r) -
        ∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1, (pairW t s r : ℂ) * u s * g r := by
  obtain ⟨hIvg, hQvg⟩ := Q_eq_prod t ht hu (hv.sub hg)
  obtain ⟨hIv, hQv⟩ := Q_eq_prod t ht hu hv
  obtain ⟨hIg, hQg⟩ := Q_eq_prod t ht hu hg
  rw [hQvg, hQv, hQg, ← integral_sub hIv hIg]
  exact integral_congr_ae (Eventually.of_forall fun p => by simp only [Pi.sub_apply]; ring)

/-- Continuous bounded second function: `2t ∫∫ w u(s) g(r) → ∫ u g`. -/
theorem cont_limit {u : ℝ → ℂ} (hu : MemLp u 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (g : ℝ → ℂ) (hg : Continuous g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) :
    Tendsto (fun t : ℝ => ((2 * t : ℝ) : ℂ) *
      ∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1, (pairW t s r : ℂ) * u s * g r)
      atTop (𝓝 (∫ s in Ioc (0 : ℝ) 1, u s * g s)) := by
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hμ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hu1 : Integrable u μ := hu.integrable one_le_two
  set G : ℝ → ℝ → ℂ := fun t s => ((2 * t : ℝ) : ℂ) * ∫ r, (pairW t s r : ℂ) * g r ∂μ with hG
  have hGm : ∀ t, StronglyMeasurable (G t) := fun t => by
    have hm : StronglyMeasurable (Function.uncurry fun s r => (pairW t s r : ℂ) * g r) :=
      ((Complex.measurable_ofReal.comp (measurable_pairW t)).mul
        (hg.measurable.comp measurable_snd)).stronglyMeasurable
    exact stronglyMeasurable_const.mul hm.integral_prod_right
  have hrep : ∀ t : ℝ, ((2 * t : ℝ) : ℂ) *
      (∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1, (pairW t s r : ℂ) * u s * g r) =
      ∫ s, u s * G t s ∂μ := by
    intro t
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [hG]
    have : ∫ r, (pairW t s r : ℂ) * u s * g r ∂μ = u s * ∫ r, (pairW t s r : ℂ) * g r ∂μ := by
      rw [← MeasureTheory.integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun r => by ring)
    rw [this]; ring
  have hlim : Tendsto (fun t => ∫ s, u s * G t s ∂μ) atTop (𝓝 (∫ s, u s * g s ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun s => ‖u s‖ * B)
      (Eventually.of_forall fun t => hu1.aestronglyMeasurable.mul (hGm t).aestronglyMeasurable)
      ((eventually_gt_atTop 0).mono fun t ht =>
        ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_)
      (hu1.norm.mul_const B) (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_)
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hsI : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
      have hint : Integrable (fun r => B * pairW t s r) μ := by
        have := (intervalIntegrable_pairW_r t s ht.le hsI).1
        exact this.const_mul B
      have hnb : ‖∫ r, (pairW t s r : ℂ) * g r ∂μ‖ ≤ ∫ r, B * pairW t s r ∂μ :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall fun r => by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pairW_pos t s r).le, mul_comm]
          exact mul_le_mul_of_nonneg_right (hB r) (pairW_pos t s r).le)
      have hrs : ∫ r, pairW t s r ∂μ = (1 - Real.exp (-(2 * t))) / (2 * t) := by
        rw [hμ, ← intervalIntegral.integral_of_le zero_le_one]
        exact rowSum t s ht hsI
      rw [MeasureTheory.integral_const_mul, hrs] at hnb
      simp only [hG]
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc 2 * t * ‖∫ r, (pairW t s r : ℂ) * g r ∂μ‖
          ≤ 2 * t * (B * ((1 - Real.exp (-(2 * t))) / (2 * t))) :=
            mul_le_mul_of_nonneg_left hnb (by positivity)
        _ = B * (1 - Real.exp (-(2 * t))) := by field_simp
        _ ≤ B := by nlinarith [Real.exp_pos (-(2 * t))]
    · have hc := pointwise_conc g hg hB hs
      have hc' : Tendsto (fun t => G t s) atTop (𝓝 (g s)) := by
        refine hc.congr' (Eventually.of_forall fun t => ?_)
        simp only [hG, hμ, intervalIntegral.integral_of_le zero_le_one]
      exact tendsto_const_nhds.mul hc'
  exact hlim.congr' (Eventually.of_forall fun t => (hrep t).symm)

/-- `‖f‖₂` from `eLpNorm`. -/
theorem sqrt_le_of_eLpNorm_le {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    {δ : ℝ} (hδ : 0 ≤ δ) (h : eLpNorm f 2 (volume.restrict (Ioc (0 : ℝ) 1)) ≤ ENNReal.ofReal δ) :
    Real.sqrt (∫ s in Ioc (0 : ℝ) 1, ‖f s‖ ^ 2) ≤ δ := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.ofReal_le_ofReal_iff hδ] at h
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rwa [Real.sqrt_eq_rpow, ← inv_eq_one_div]

/-- **Leaf (d).** `2t ∫∫ w(s,r) u(s) v(r) → ∫₀¹ u v` for `u, v ∈ L²(0,1)`. -/
theorem mass_limit {u v : ℝ → ℂ} (hu : MemLp u 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hv : MemLp v 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    Tendsto (fun t : ℝ => ((2 * t : ℝ) : ℂ) *
      ∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1, (pairW t s r : ℂ) * u s * v r)
      atTop (𝓝 (∫ s in Ioc (0 : ℝ) 1, u s * v s)) := by
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hμ
  set Cu : ℝ := Real.sqrt (∫ s in Ioc (0 : ℝ) 1, ‖u s‖ ^ 2) with hCu
  have hCu0 : 0 ≤ Cu := Real.sqrt_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / (4 * (Cu + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨g, hgδ, hgm⟩ := hv.exists_boundedContinuous_eLpNorm_sub_le ENNReal.ofNat_ne_top
    (ENNReal.ofReal_pos.2 hδ0).ne'
  have hvg : Real.sqrt (∫ s in Ioc (0 : ℝ) 1, ‖(v - (g : ℝ → ℂ)) s‖ ^ 2) ≤ δ :=
    sqrt_le_of_eLpNorm_le (hv.sub hgm) hδ0.le hgδ
  have hcl := cont_limit hu (g : ℝ → ℂ) g.continuous (fun x => g.norm_coe_le_norm x)
  rw [Metric.tendsto_atTop] at hcl
  obtain ⟨T, hT⟩ := hcl (ε / 2) (by positivity)
  refine ⟨max T 1, fun t htT => ?_⟩
  have ht : 0 < t := lt_of_lt_of_le one_pos (le_of_max_le_right htT)
  have h1 := hT t (le_of_max_le_left htT)
  -- error from replacing v by g in the double integral
  have h2 : ‖((2 * t : ℝ) : ℂ) *
      ∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1, (pairW t s r : ℂ) * u s * (v - (g : ℝ → ℂ)) r‖ ≤
      Cu * δ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hq := Q_norm_le t ht hu (hv.sub hgm)
    calc 2 * t * ‖∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1,
          (pairW t s r : ℂ) * u s * (v - (g : ℝ → ℂ)) r‖
        ≤ 2 * t * ((1 - Real.exp (-(2 * t))) / (2 * t) *
          (Cu * Real.sqrt (∫ r in Ioc (0 : ℝ) 1, ‖(v - (g : ℝ → ℂ)) r‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = (1 - Real.exp (-(2 * t))) *
          (Cu * Real.sqrt (∫ r in Ioc (0 : ℝ) 1, ‖(v - (g : ℝ → ℂ)) r‖ ^ 2)) := by field_simp
      _ ≤ 1 * (Cu * δ) := by
          refine mul_le_mul (by linarith [Real.exp_pos (-(2 * t))])
            (mul_le_mul_of_nonneg_left hvg hCu0) (by positivity) zero_le_one
      _ = Cu * δ := one_mul _
  -- error from replacing v by g in the limit
  have h3 : ‖(∫ s in Ioc (0 : ℝ) 1, u s * (g : ℝ → ℂ) s) - ∫ s in Ioc (0 : ℝ) 1, u s * v s‖ ≤
      Cu * δ := by
    have hug : Integrable (fun s => u s * (g : ℝ → ℂ) s) μ :=
      (hu.integrable one_le_two).mul_bdd hgm.aestronglyMeasurable (Eventually.of_forall fun x => g.norm_coe_le_norm x)
    have huv : Integrable (fun s => ‖u s‖ * ‖(v - (g : ℝ → ℂ)) s‖) μ := by
      refine Integrable.mono' ((hu.norm.integrable_sq.add (hv.sub hgm).norm.integrable_sq).div_const 2)
        (hu.aestronglyMeasurable.norm.mul (hv.sub hgm).aestronglyMeasurable.norm) (Eventually.of_forall fun s => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (‖u s‖ - ‖(v - (g : ℝ → ℂ)) s‖)]
    have hu_v : Integrable (fun s => u s * v s) μ := by
      refine Integrable.mono' ((hu.norm.integrable_sq.add hv.norm.integrable_sq).div_const 2)
        (hu.aestronglyMeasurable.mul hv.aestronglyMeasurable) (Eventually.of_forall fun s => ?_)
      rw [norm_mul]
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (‖u s‖ - ‖v s‖), norm_nonneg (u s), norm_nonneg (v s)]
    rw [← integral_sub hug hu_v]
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    calc ∫ s in Ioc (0 : ℝ) 1, ‖u s * (g : ℝ → ℂ) s - u s * v s‖
        = ∫ s in Ioc (0 : ℝ) 1, ‖u s‖ * ‖(v - (g : ℝ → ℂ)) s‖ := by
          refine integral_congr_ae (Eventually.of_forall fun s => ?_)
          simp only [Pi.sub_apply]
          rw [← mul_sub, norm_mul, ← norm_neg (v s - _), neg_sub]
      _ ≤ Cu * Real.sqrt (∫ s in Ioc (0 : ℝ) 1, ‖(v - (g : ℝ → ℂ)) s‖ ^ 2) := cs_bound hu (hv.sub hgm)
      _ ≤ Cu * δ := mul_le_mul_of_nonneg_left hvg hCu0
  have hQ := Q_sub t ht.le hu hv hgm
  have hCδ : Cu * δ ≤ ε / 4 := by
    rw [hδ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  rw [dist_eq_norm] at h1 ⊢
  have heq : ((2 * t : ℝ) : ℂ) *
        (∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1, (pairW t s r : ℂ) * u s * v r) -
      ∫ s in Ioc (0 : ℝ) 1, u s * v s =
      (((2 * t : ℝ) : ℂ) *
          (∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1, (pairW t s r : ℂ) * u s * (g : ℝ → ℂ) r) -
        ∫ s in Ioc (0 : ℝ) 1, u s * (g : ℝ → ℂ) s) +
      ((2 * t : ℝ) : ℂ) *
        (∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1, (pairW t s r : ℂ) * u s * (v - (g : ℝ → ℂ)) r) +
      ((∫ s in Ioc (0 : ℝ) 1, u s * (g : ℝ → ℂ) s) - ∫ s in Ioc (0 : ℝ) 1, u s * v s) := by
    rw [hQ]; ring
  rw [heq]
  calc _ ≤ _ := norm_add₃_le
    _ < ε / 2 + Cu * δ + Cu * δ := by linarith
    _ ≤ ε := by linarith

end NlsGge.ThirdConsultation.M016MassAux

namespace NlsGge.ThirdConsultation.M016MassAux

/-- The period-one cover representatives are `L²(0,1)`. -/
theorem memLp_coverRep38 (f : NlsGge.Pilot.PhysicalL2) :
    MemLp (NlsGge.GK38.coverRep38 f) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (memLp_two_iff_integrable_sq_norm
    (NlsGge.GK38.intervalIntegrable_coverRep38_one f).1.aestronglyMeasurable).2
    (NlsGge.GK38.intervalIntegrable_coverRep38_sq_one f).1

/-- **Leaf (d) for the potential representatives** (`potRepFst38 φ = coverRep38 φ.1` by definition):
`2t ∫∫ w(s,r) φ₁(s) φ₂(r) → ∫₀¹ φ₁ φ₂`, the bilinear mass of Pro R16 §1.3. -/
theorem mass_limit_cover (f g : NlsGge.Pilot.PhysicalL2) :
    Tendsto (fun t : ℝ => ((2 * t : ℝ) : ℂ) *
      ∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1,
        (pairW t s r : ℂ) * NlsGge.GK38.coverRep38 f s * NlsGge.GK38.coverRep38 g r)
      atTop (𝓝 (∫ x in (0 : ℝ)..1, NlsGge.GK38.coverRep38 f x * NlsGge.GK38.coverRep38 g x)) := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact mass_limit (memLp_coverRep38 f) (memLp_coverRep38 g)

end NlsGge.ThirdConsultation.M016MassAux
