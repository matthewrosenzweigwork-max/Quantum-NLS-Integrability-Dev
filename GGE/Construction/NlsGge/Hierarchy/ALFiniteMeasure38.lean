import NlsGge.Hierarchy.ALFullEnergy38
import NlsGge.Hierarchy.ALGaussianNormalizer38
import NlsGge.Hierarchy.ALFloquetSummary38
import NlsGge.Hierarchy.ALMomentsBridge38
/-! # L02c / L03b: the finite AL canonical measure `η_h` (D:thm:ALfinite l.1956-1977)

* `alPartition_bounds38`: the Liouville integrand `1_𝔻^L e^{-E_{W,h}} ∏(1-|α_j|²)⁻¹` is measurable and
  integrable and `0 < 𝒵_h ≤ (πh/β₀)^L` (`D:eq:ALZupper`), via `E ≥ β₀M_d/h`, a product
  (`integral_fintype_prod_eq_prod`) and the polar-coordinates disk integral `π/s`.
* `alGaussianNormalizer_bundled38`: L03 identity as an equation of finite positive reals; `f_h`
  measurable, integrable against `γ_h` (NOT bounded by 1 for the full weight), `0 < Z_h`.
* `alEta_invariant38`: `η_h` is a probability measure invariant under the `H_d` flow
  (conservation of `E` from `alK_const38`, Liouville invariance from `alLiouville_lintegral_flow38`). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik
open MeasureTheory Set

section Meas
variable {L : ℕ} [NeZero L]

omit [NeZero L] in
theorem meas_alPartial38 (k : ℕ) (i j : Fin 2) :
    Measurable (fun p : (ZMod L → ℂ) × ℝ =>
      alPartial38 p.1 (Complex.exp ((p.2 : ℂ) * Complex.I)) k i j) := by
  induction k generalizing i j with
  | zero => simp only [alPartial38]; exact measurable_const
  | succ k ih =>
    simp only [alPartial38, Matrix.mul_apply, Fin.sum_univ_two]
    have ht : ∀ a b : Fin 2, Measurable (fun p : (ZMod L → ℂ) × ℝ =>
        alTransfer38 (p.1 (k : ZMod L)) (Complex.exp ((p.2 : ℂ) * Complex.I)) a b) := by
      intro a b
      have e1 : Measurable fun p : (ZMod L → ℂ) × ℝ => (p.1 (k : ZMod L)) :=
        (measurable_pi_apply _).comp measurable_fst
      have e2 : Measurable fun p : (ZMod L → ℂ) × ℝ => Complex.exp ((p.2 : ℂ) * Complex.I) := by
        fun_prop
      fin_cases a <;> fin_cases b <;> simp [alTransfer38] <;> fun_prop
    exact ((ht i 0).mul (ih 0 j)).add ((ht i 1).mul (ih 1 j))

omit [NeZero L] in
theorem meas_alKappa38 :
    Measurable (fun p : (ZMod L → ℂ) × ℝ => alKappa38 p.1 p.2) := by
  unfold alKappa38 alMonodromy38
  have htr : Measurable (fun p : (ZMod L → ℂ) × ℝ =>
      Matrix.trace (alPartial38 p.1 (Complex.exp ((p.2 : ℂ) * Complex.I)) L)) := by
    simp only [Matrix.trace_fin_two]
    exact (meas_alPartial38 L 0 0).add (meas_alPartial38 L 1 1)
  have : Measurable (fun p : (ZMod L → ℂ) × ℝ => max 1
      ‖Matrix.trace (alPartial38 p.1 (Complex.exp ((p.2 : ℂ) * Complex.I)) L) / 2‖) :=
    measurable_const.max (htr.div_const 2).norm
  refine measurable_const.mul ?_
  unfold Real.arcosh
  fun_prop


/-- Spectral formula for `K_j` as a total function of `α` (equal to `alMomentK38` on the disk). -/
def alKspec38 (α : ZMod L → ℂ) (j : ℕ) : ℝ :=
  (L / Real.pi) * ∫ θ in (0:ℝ)..(2 * Real.pi), (2 - 2 * Real.cos (2 * θ)) ^ j * alKappa38 α θ

theorem alKspec_eq38 {α : ZMod L → ℂ} (hα : IsALField38 α) (j : ℕ) :
    alKspec38 α j = alMomentK38 α j := (alMomentK38_spectral hα j).symm

theorem meas_alKspec38 (j : ℕ) : Measurable (fun α : ZMod L → ℂ => alKspec38 α j) := by
  unfold alKspec38
  refine measurable_const.mul ?_
  have hm : Measurable (fun p : (ZMod L → ℂ) × ℝ =>
      (2 - 2 * Real.cos (2 * p.2)) ^ j * alKappa38 p.1 p.2) := by
    have := meas_alKappa38 (L := L)
    fun_prop
  have := (hm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ).restrict (Ioc 0 (2 * Real.pi)))).measurable
  simp_rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  exact this

open Classical in
/-- The energy, totalized by `0` off the disk. -/
def alEnergyInd38 (c : ℕ → ℝ) (h : ℝ) (α : ZMod L → ℂ) : ℝ :=
  if IsALField38 α then alEnergy38 c h α else 0

theorem meas_alEnergyInd38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : 0 < h) :
    Measurable (alEnergyInd38 (L := L) c h) := by
  classical
  set Et : (ZMod L → ℂ) → ℝ := fun α => (∑' j : ℕ, ENNReal.ofReal
    (NlsGge.coefficient c j * ((h⁻¹) ^ (2 * j + 1) * alKspec38 α j))).toReal with hEt
  have hEtm : Measurable Et := by
    refine (Measurable.tsum fun j => ?_).ennreal_toReal
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_const.mul (meas_alKspec38 j)))
  have : alEnergyInd38 (L := L) c h = fun α => if IsALField38 α then Et α else 0 := by
    funext α
    unfold alEnergyInd38
    by_cases hα : IsALField38 α
    · simp only [hα, ite_true]
      have e1 : ∀ j, NlsGge.coefficient c j * ((h⁻¹) ^ (2 * j + 1) * alKspec38 α j) =
          alEnergyTerm38 c h α j := by
        intro j; rw [alKspec_eq38 hα]; rfl
      simp only [hEt, e1]
      rw [← ENNReal.ofReal_tsum_of_nonneg (alEnergyTerm38_nonneg hc hα hh)
        (alEnergy38_summable hc hα hh), ENNReal.toReal_ofReal (tsum_nonneg (alEnergyTerm38_nonneg hc hα hh))]
      rfl
    · simp [hα]
  rw [this]
  exact Measurable.ite (measurableSet_alDisk38 (L := L)) hEtm measurable_const

open Classical in
/-- The Liouville integrand of `𝒵_h` (verbatim the integrand of `alPartition38`). -/
def alIntegrand38 (c : ℕ → ℝ) (h : ℝ) (α : ZMod L → ℂ) : ℝ :=
  if IsALField38 α then Real.exp (-alEnergy38 c h α) * ∏ j, (1 - ‖α j‖ ^ 2)⁻¹ else 0

theorem meas_alIntegrand38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : 0 < h) :
    Measurable (alIntegrand38 (L := L) c h) := by
  classical
  have hm := meas_alEnergyInd38 (L := L) hc hh
  have hprod : Measurable (fun α : ZMod L → ℂ => ∏ j, (1 - ‖α j‖ ^ 2)⁻¹) := by
    refine Finset.measurable_prod _ fun j _ => ?_
    have : Measurable fun α : ZMod L → ℂ => ‖α j‖ := (measurable_pi_apply j).norm
    fun_prop
  have : alIntegrand38 (L := L) c h = fun α => if IsALField38 α then
      Real.exp (-alEnergyInd38 c h α) * ∏ j, (1 - ‖α j‖ ^ 2)⁻¹ else 0 := by
    funext α
    unfold alIntegrand38 alEnergyInd38
    by_cases hα : IsALField38 α <;> simp [hα]
  rw [this]
  exact Measurable.ite (measurableSet_alDisk38 (L := L))
    ((hm.neg.exp).mul hprod) measurable_const

end Meas

/-- radial profile of the disk integrand -/
def diskProf38 (s : ℝ) (r : ℝ) : ℝ := if r < 1 then (1 - r ^ 2) ^ (s - 1) else 0

theorem diskRad_integral38 {s : ℝ} (hs : 0 < s) :
    ∫ y in Ioo (0:ℝ) 1, y * (1 - y ^ 2) ^ (s - 1) = 1 / (2 * s) := by
  have hP : ∀ y ∈ Ioo (0:ℝ) 1, HasDerivAt (fun y : ℝ => -((1 - y ^ 2) ^ s) / (2 * s))
      (y * (1 - y ^ 2) ^ (s - 1)) y := by
    intro y hy
    have h1 : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
    have h2 : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * y)) y := by
      simpa using ((hasDerivAt_pow 2 y).const_sub 1)
    have h3 := (h2.rpow_const (p := s) (Or.inl h1.ne')).neg.div_const (2 * s)
    convert h3 using 1
    field_simp
  have hc : ContinuousOn (fun y : ℝ => -((1 - y ^ 2) ^ s) / (2 * s)) (Icc 0 1) := by
    refine Continuous.continuousOn ?_
    have := Real.continuous_rpow_const hs.le
    fun_prop
  have hint : IntervalIntegrable (fun y : ℝ => y * (1 - y ^ 2) ^ (s - 1)) volume 0 1 := by
    refine intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := fun y : ℝ => -((1 - y ^ 2) ^ s) / (2 * s)) (by simpa using hc) ?_ ?_
    · simpa using hP
    · intro y hy
      simp only [min_eq_left zero_le_one, max_eq_right zero_le_one] at hy
      have h1 : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
      have := Real.rpow_nonneg h1.le (s - 1)
      exact mul_nonneg hy.1.le this
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (zero_le_one' ℝ) hc hP hint
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, this]
  simp [Real.zero_rpow hs.ne']
  field_simp
  

theorem diskRad_integrable38 {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun y : ℝ => y * (1 - y ^ 2) ^ (s - 1)) (Ioo (0:ℝ) 1) := by
  have hP : ∀ y ∈ Ioo (0:ℝ) 1, HasDerivAt (fun y : ℝ => -((1 - y ^ 2) ^ s) / (2 * s))
      (y * (1 - y ^ 2) ^ (s - 1)) y := by
    intro y hy
    have h1 : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
    have h2 : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * y)) y := by
      simpa using ((hasDerivAt_pow 2 y).const_sub 1)
    have h3 := (h2.rpow_const (p := s) (Or.inl h1.ne')).neg.div_const (2 * s)
    convert h3 using 1
    field_simp
  have hc : ContinuousOn (fun y : ℝ => -((1 - y ^ 2) ^ s) / (2 * s)) (Icc 0 1) := by
    refine Continuous.continuousOn ?_
    have := Real.continuous_rpow_const hs.le
    fun_prop
  have := intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := fun y : ℝ => -((1 - y ^ 2) ^ s) / (2 * s)) (a := 0) (b := 1) (by simpa using hc) (by simpa using hP) (by
      intro y hy
      simp only [min_eq_left zero_le_one, max_eq_right zero_le_one] at hy
      have h1 : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
      exact mul_nonneg hy.1.le (Real.rpow_nonneg h1.le (s - 1)))
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 this

theorem diskProf_integrable38 {s : ℝ} (hs : 0 < s) :
    Integrable (fun z : ℂ => diskProf38 s ‖z‖) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ), Complex.finrank_real_complex]
  have h := diskRad_integrable38 hs
  have : IntegrableOn (fun y : ℝ => y ^ (2 - 1) • diskProf38 s y) (Ioo 0 1) := by
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioo
    simp [diskProf38, hy.2]
  have h0 : IntegrableOn (fun y : ℝ => y ^ (2 - 1) • diskProf38 s y) (Ici 1) := by
    refine (integrableOn_zero).congr_fun (fun y hy => ?_) measurableSet_Ici
    have hy' : 1 ≤ y := hy
    simp [diskProf38, not_lt.2 hy']
  have : IntegrableOn (fun y : ℝ => y ^ (2 - 1) • diskProf38 s y) (Ioo 0 1 ∪ Ici 1) := this.union h0
  refine this.mono_set ?_
  intro y hy
  rcases lt_or_ge y 1 with h1 | h1
  · exact Or.inl ⟨hy, h1⟩
  · exact Or.inr h1

theorem diskProf_integral38 {s : ℝ} (hs : 0 < s) :
    ∫ z : ℂ, diskProf38 s ‖z‖ = Real.pi / s := by
  rw [integral_fun_norm_addHaar (volume : Measure ℂ), Complex.finrank_real_complex]
  have h1 : ∫ y in Ioi (0:ℝ), y ^ (2 - 1) • diskProf38 s y = ∫ y in Ioo (0:ℝ) 1, y * (1 - y ^ 2) ^ (s - 1) := by
    refine ((setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (f := fun y : ℝ => y ^ (2 - 1) • diskProf38 s y) (s := Ioo (0:ℝ) 1) measurableSet_Ioi
      (fun y hy => hy.1) ?_)).trans ?_
    · intro y hy
      have : ¬ y < 1 := fun h => hy.2 ⟨hy.1, h⟩
      simp [diskProf38, this]
    · refine setIntegral_congr_fun measurableSet_Ioo (fun y hy => ?_)
      simp [diskProf38, hy.2]
  rw [h1, diskRad_integral38 hs]
  have hv : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real]
  rw [hv]
  simp only [smul_eq_mul, nsmul_eq_mul]
  push_cast
  field_simp


section Bound
variable {L : ℕ} [NeZero L]

theorem diskProf_nonneg38 (s : ℝ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ diskProf38 s r := by
  unfold diskProf38
  split_ifs with h
  · exact Real.rpow_nonneg (by nlinarith) _
  · exact le_rfl

theorem alIntegrand_nonneg38 (c : ℕ → ℝ) (h : ℝ) (α : ZMod L → ℂ) : 0 ≤ alIntegrand38 c h α := by
  classical
  unfold alIntegrand38
  split_ifs with hα
  · refine mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun j _ => inv_nonneg.2 ?_)
    have := hα j; nlinarith [norm_nonneg (α j)]
  · exact le_rfl

theorem alIntegrand_le38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : 0 < h) (α : ZMod L → ℂ) :
    alIntegrand38 c h α ≤ ∏ j, diskProf38 (c 0 / h) ‖α j‖ := by
  classical
  by_cases hα : IsALField38 α
  · have hpos : ∀ j, 0 < 1 - ‖α j‖ ^ 2 := fun j => by
      have := hα j; nlinarith [norm_nonneg (α j)]
    have hs := (alEnergy38_sandwich hc hα hh).1
    have e1 : Real.exp (-alEnergy38 c h α) ≤ ∏ j, (1 - ‖α j‖ ^ 2) ^ (c 0 / h) := by
      calc Real.exp (-alEnergy38 c h α) ≤ Real.exp (-(c 0 / h * alMass38 L α)) := by
            apply Real.exp_le_exp.2
            have : c 0 * alMass38 L α / h = c 0 / h * alMass38 L α := by ring
            linarith
        _ = ∏ j, (1 - ‖α j‖ ^ 2) ^ (c 0 / h) := by
            unfold alMass38
            rw [show -(c 0 / h * -∑ j : ZMod L, Real.log (1 - ‖α j‖ ^ 2)) =
              ∑ j : ZMod L, Real.log (1 - ‖α j‖ ^ 2) * (c 0 / h) by
                rw [mul_neg, neg_neg, Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ => by ring, Real.exp_sum]
            exact Finset.prod_congr rfl fun j _ => (Real.rpow_def_of_pos (hpos j) _).symm
    unfold alIntegrand38
    simp only [hα, ite_true]
    have e2 : ∏ j, diskProf38 (c 0 / h) ‖α j‖ =
        ∏ j, (1 - ‖α j‖ ^ 2) ^ (c 0 / h) * (1 - ‖α j‖ ^ 2)⁻¹ := by
      refine Finset.prod_congr rfl fun j _ => ?_
      have : ‖α j‖ < 1 := hα j
      simp only [diskProf38, this, ite_true]
      rw [Real.rpow_sub_one (hpos j).ne', div_eq_mul_inv]
    rw [e2, Finset.prod_mul_distrib]
    exact mul_le_mul_of_nonneg_right e1 (Finset.prod_nonneg fun j _ => (inv_pos.2 (hpos j)).le)
  · rw [show alIntegrand38 c h α = 0 by unfold alIntegrand38; simp [hα]]
    exact Finset.prod_nonneg fun j _ => diskProf_nonneg38 _ (norm_nonneg _)

theorem alIntegrand_integrable38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : 0 < h) :
    Integrable (alIntegrand38 (L := L) c h) := by
  have hs : 0 < c 0 / h := div_pos (lt_of_lt_of_le hc.1 (hc.2.2 0).1) hh
  have hG : Integrable (fun α : ZMod L → ℂ => ∏ j, diskProf38 (c 0 / h) ‖α j‖)
      (Measure.pi fun _ : ZMod L => (volume : Measure ℂ)) :=
    Integrable.fintype_prod (fun j => diskProf_integrable38 hs)
  refine Integrable.mono' hG (meas_alIntegrand38 hc hh).aestronglyMeasurable
    (Filter.Eventually.of_forall fun α => ?_)
  rw [Real.norm_of_nonneg (alIntegrand_nonneg38 c h α)]
  exact alIntegrand_le38 hc hh α

theorem alPartition_bounds38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : 0 < h) :
    Integrable (alIntegrand38 (L := L) c h) ∧
    (∫⁻ α, ENNReal.ofReal (alIntegrand38 (L := L) c h α)) < ⊤ ∧
    0 < alPartition38 L c h ∧ alPartition38 L c h ≤ (Real.pi * h / c 0) ^ L := by
  have hs : 0 < c 0 / h := div_pos (lt_of_lt_of_le hc.1 (hc.2.2 0).1) hh
  have hint := alIntegrand_integrable38 (L := L) hc hh
  have hpart : alPartition38 L c h = ∫ α, alIntegrand38 (L := L) c h α := rfl
  refine ⟨hint, hint.lintegral_lt_top, ?_, ?_⟩
  · rw [hpart, integral_pos_iff_support_of_nonneg (alIntegrand_nonneg38 c h) hint]
    have hsupp : Function.support (alIntegrand38 (L := L) c h) = alDisk38 L := by
      classical
      ext α
      simp only [Function.mem_support, ne_eq, alDisk38, Set.mem_ofPred_eq]
      unfold alIntegrand38
      by_cases hα : IsALField38 α
      · simp only [hα, ite_true, iff_true]
        refine mul_ne_zero (Real.exp_pos _).ne' (Finset.prod_ne_zero_iff.2 fun j _ => inv_ne_zero ?_)
        have := hα j; nlinarith [norm_nonneg (α j)]
      · simp [hα]
    rw [hsupp]
    refine (isOpen_alDisk38 (L := L)).measure_pos _ ⟨0, fun j => by simp⟩
  · have hG : Integrable (fun α : ZMod L → ℂ => ∏ j, diskProf38 (c 0 / h) ‖α j‖)
        (Measure.pi fun _ : ZMod L => (volume : Measure ℂ)) :=
      Integrable.fintype_prod (fun j => diskProf_integrable38 hs)
    rw [hpart]
    calc ∫ α, alIntegrand38 (L := L) c h α ≤ ∫ α : ZMod L → ℂ, ∏ j, diskProf38 (c 0 / h) ‖α j‖ :=
          integral_mono hint hG (alIntegrand_le38 hc hh)
      _ = ∏ j : ZMod L, ∫ z : ℂ, diskProf38 (c 0 / h) ‖z‖ :=
          integral_fintype_prod_eq_prod (fun (j : ZMod L) (z : ℂ) => diskProf38 (c 0 / h) ‖z‖)
      _ = (Real.pi * h / c 0) ^ L := by
          simp only [diskProf_integral38 hs, Finset.prod_const, Finset.card_univ, ZMod.card]
          congr 1
          have : c 0 ≠ 0 := (lt_of_lt_of_le hc.1 (hc.2.2 0).1).ne'
          field_simp

end Bound

section Gaussian
open NlsGge.Measure ProbabilityTheory
variable {L : ℕ} [NeZero L]

/-- Pointwise factorisation of the Liouville integrand in Fourier coordinates (as in L03). -/
theorem alIntegrand_synth38 (c : ℕ → ℝ) (h : ℝ) (û : ZMod L → ℂ) :
    alIntegrand38 c h (ZMod.dft.symm û) =
      Real.exp (-∑ k : ZMod L, alRate38 c h k.valMinAbs * ‖û k‖ ^ 2) * alReweight38 c h û := by
  classical
  unfold alIntegrand38 alReweight38
  by_cases hα : IsALField38 (ZMod.dft.symm û)
  · simp only [hα, ite_true]
    rw [← exp_alMass38 hα, ← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold alRemainder38; ring
  · simp only [hα, ite_true, mul_zero]
    simp [hα]

theorem measurable_synth38 : Measurable (fun û : ZMod L → ℂ => ZMod.dft.symm û) :=
  (LinearMap.continuous_of_finiteDimensional
    (ZMod.dft.symm : (ZMod L → ℂ) ≃ₗ[ℂ] (ZMod L → ℂ)).toLinearMap).measurable

theorem meas_alReweight38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : 0 < h) :
    Measurable (alReweight38 (L := L) c h) := by
  classical
  have hs := measurable_synth38 (L := L)
  have hE := (meas_alEnergyInd38 (L := L) hc hh).comp hs
  have hM := (measurable_alMass38 (L := L)).comp hs
  have hQ : Measurable (fun û : ZMod L → ℂ => ∑ k : ZMod L, alRate38 c h k.valMinAbs * ‖û k‖ ^ 2) := by
    refine Finset.measurable_sum _ fun k _ => measurable_const.mul ?_
    have : Measurable fun û : ZMod L → ℂ => ‖û k‖ := (measurable_pi_apply k).norm
    fun_prop
  have : alReweight38 (L := L) c h = fun û => if IsALField38 (ZMod.dft.symm û) then
      Real.exp (-(alEnergyInd38 c h (ZMod.dft.symm û) - alMass38 L (ZMod.dft.symm û) -
        ∑ k : ZMod L, alRate38 c h k.valMinAbs * ‖û k‖ ^ 2)) else 0 := by
    funext û
    unfold alReweight38 alRemainder38 alEnergyInd38
    by_cases hα : IsALField38 (ZMod.dft.symm û) <;> simp [hα]
  rw [this]
  exact Measurable.ite (hs measurableSet_alDisk38) (((hE.sub hM).sub hQ).neg.exp) measurable_const

theorem integrable_alIntegrand_synth38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : 0 < h) :
    Integrable (fun û : ZMod L → ℂ => alIntegrand38 c h (ZMod.dft.symm û)) := by
  have hme : MeasurableEmbedding (synthR38 (L := L)) :=
    (synthR38 (L := L)).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hI : Integrable (alIntegrand38 (L := L) c h)
      (Measure.map (synthR38 (L := L)) (volume : Measure (ZMod L → ℂ))) := by
    rw [map_synth_volume38]
    exact (alIntegrand_integrable38 hc hh).smul_measure ENNReal.ofReal_ne_top
  exact hme.integrable_map_iff.1 hI

/-- **(L03b)** `f_h` is measurable and integrable against `γ_h` (it is *not* bounded by `1` for the
full weight: by `D:prop:negativeAL` it exceeds `1` near plane waves; integrability follows from
that of the Liouville integrand). -/
theorem integrable_alReweight38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : 0 < h)
    (ha : ∀ ν : ℤ, 0 < alRate38 c h ν) :
    Integrable (alReweight38 (L := L) c h) (alGauss38 (L := L) c h) := by
  unfold alGauss38
  rw [pi_complexGaussian_eq38 (fun k : ZMod L => alRate38 c h k.valMinAbs) (fun k => ha _)]
  have hmeas : Measurable (fun x : ZMod L → ℂ =>
      (∏ k : ZMod L, gDens38 (alRate38 c h k.valMinAbs) (x k)).toNNReal) := by
    refine Measurable.real_toNNReal (Finset.measurable_prod _ fun k _ => ?_)
    exact (gDens_meas38 _).comp (measurable_pi_apply k)
  refine (integrable_withDensity_iff_integrable_smul hmeas).2 ?_
  have hΦ := (integrable_alIntegrand_synth38 (L := L) hc hh).const_mul
    (∏ k : ZMod L, alRate38 c h k.valMinAbs / Real.pi)
  refine hΦ.congr (Filter.Eventually.of_forall fun x => ?_)
  have hp : ∏ k : ZMod L, gDens38 (alRate38 c h k.valMinAbs) (x k) =
      (∏ k : ZMod L, alRate38 c h k.valMinAbs / Real.pi) *
        Real.exp (-∑ k : ZMod L, alRate38 c h k.valMinAbs * ‖x k‖ ^ 2) := by
    unfold gDens38
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    congr 2
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h0 : 0 ≤ ∏ k : ZMod L, gDens38 (alRate38 c h k.valMinAbs) (x k) :=
    Finset.prod_nonneg fun k _ => gDens_nonneg38 (ha _) _
  beta_reduce
  rw [alIntegrand_synth38]
  show _ = ((∏ k : ZMod L, gDens38 (alRate38 c h k.valMinAbs) (x k)).toNNReal : ℝ) * _
  rw [Real.coe_toNNReal _ h0, hp]
  ring


/-- **(L03b) bundled corollary of `alGaussianNormalizer38`**: for `h = 1/L`, `L > 1/lo`, the
Liouville integrand is integrable, `0 < 𝒵_h ≤ (πh/β₀)^L`, `f_h` is integrable against `γ_h`,
`0 < Z_h`, the Gaussian prefactor is positive and `𝒵_h = h^L ∏_k (π/a_{h,k}) Z_h`, an equation
between finite positive reals. -/
theorem alGaussianNormalizer_bundled38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : h = (L : ℝ)⁻¹)
    (hL : lo⁻¹ < (L : ℝ)) :
    Integrable (alIntegrand38 (L := L) c h) ∧
    0 < alPartition38 L c h ∧ alPartition38 L c h ≤ (Real.pi * h / c 0) ^ L ∧
    Measurable (alReweight38 (L := L) c h) ∧
    Integrable (alReweight38 (L := L) c h) (alGauss38 (L := L) c h) ∧
    0 < h ^ L * ∏ k : ZMod L, Real.pi / alRate38 c h k.valMinAbs ∧
    0 < alZ38 (L := L) c h ∧
    alPartition38 L c h =
      h ^ L * (∏ k : ZMod L, Real.pi / alRate38 c h k.valMinAbs) * alZ38 (L := L) c h ∧
    alZ38 (L := L) c h ≤
      (Real.pi * h / c 0) ^ L / (h ^ L * ∏ k : ZMod L, Real.pi / alRate38 c h k.valMinAbs) := by
  have hL0 : (0:ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh0 : 0 < h := by rw [hh]; positivity
  have ha := alRate38_pos_of_mesh38 hc hh hL
  obtain ⟨hint, -, hpos, hle⟩ := alPartition_bounds38 (L := L) hc hh0
  have hP : 0 < h ^ L * ∏ k : ZMod L, Real.pi / alRate38 c h k.valMinAbs :=
    mul_pos (pow_pos hh0 _) (Finset.prod_pos fun k _ => div_pos Real.pi_pos (ha _))
  have hid := alGaussianNormalizer38 (L := L) c hh ha
  have hZ : 0 < alZ38 (L := L) c h := by
    by_contra hZ
    push Not at hZ
    have := mul_nonpos_of_nonneg_of_nonpos hP.le hZ
    linarith
  refine ⟨hint, hpos, hle, meas_alReweight38 hc hh0, integrable_alReweight38 hc hh0 ha, hP, hZ,
    by rw [hid], ?_⟩
  rw [le_div_iff₀ hP]
  calc alZ38 (L := L) c h * (h ^ L * ∏ k : ZMod L, Real.pi / alRate38 c h k.valMinAbs)
      = alPartition38 L c h := by rw [hid]; ring
    _ ≤ _ := hle

end Gaussian

section Invariance
open NlsGge.HierarchyRiccati.Core
variable {L : ℕ} [NeZero L]

/-- Conservation of the full energy along the `H_d` (Ablowitz-Ladik) flow, from the
conservation of every `K_j` (`alK_const38`). -/
theorem alEnergy_flow38 (c : ℕ → ℝ) (h : ℝ) (s : ℝ) (α : ZMod L → ℂ) :
    alEnergy38 c h (alFlow38 alHd s α) = alEnergy38 c h α := by
  by_cases hα : α ∈ alDisk38 L
  · have hγ : ∀ t ∈ (Set.univ : Set ℝ), IsALField38 (alFlow38 alHd t α) ∧
        HasDerivAt (fun t => alFlow38 alHd t α) (alX38 alHd (alFlow38 alHd t α)) t :=
      fun t _ => ⟨alFlow_mem38 alHd_contDiffOn38 alBracket_mass_alHd38 hα t,
        alFlow_hasDerivAt38 alHd_contDiffOn38 alBracket_mass_alHd38 hα t⟩
    have hK : ∀ j, alK38 (alFlow38 alHd s α) j = alK38 α j := by
      intro j
      have := alK_const38 (U := Set.univ) isOpen_univ isPreconnected_univ
        (γ := fun t => alFlow38 alHd t α) hγ (Set.mem_univ s) (Set.mem_univ 0) j
      simpa [alFlow_zero38 alHd_contDiffOn38 alBracket_mass_alHd38] using this
    unfold alEnergy38
    refine tsum_congr fun j => ?_
    unfold alEnergyTerm38 alQ38
    rw [show alMomentK38 (alFlow38 alHd s α) j = alK38 (alFlow38 alHd s α) j from rfl,
      show alMomentK38 α j = alK38 α j from rfl, hK]
  · rw [alFlow_of_not_mem38 alHd s hα]

theorem alEnergyInd_flow38 (c : ℕ → ℝ) (h : ℝ) (s : ℝ) (α : ZMod L → ℂ) :
    alEnergyInd38 c h (alFlow38 alHd s α) = alEnergyInd38 c h α := by
  classical
  by_cases hα : α ∈ alDisk38 L
  · have h1 : IsALField38 α := hα
    have h2 : IsALField38 (alFlow38 alHd s α) := alFlow_mem38 alHd_contDiffOn38 alBracket_mass_alHd38 hα s
    unfold alEnergyInd38
    simp only [h1, h2, ite_true]
    exact alEnergy_flow38 c h s α
  · rw [alFlow_of_not_mem38 alHd s hα]

/-- The energy-weighted Liouville measure `e^{-E_{W,h}} ∏ d²α_j/(1-|α_j|²)` (on the open polydisk;
`alEnergyInd38` agrees with `alEnergy38` there). -/
def alWeighted38 (L : ℕ) [NeZero L] (c : ℕ → ℝ) (h : ℝ) : Measure (ZMod L → ℂ) :=
  (alLiouvilleMeasure38 L).withDensity fun α => ENNReal.ofReal (Real.exp (-alEnergyInd38 c h α))

/-- The normalised canonical measure `η_h = 𝒵_h⁻¹ e^{-E_{W,h}} ∏ d²α_j/(1-|α_j|²)`
(`D:eq:ALfullmeasure`). -/
def alEta38 (L : ℕ) [NeZero L] (c : ℕ → ℝ) (h : ℝ) : Measure (ZMod L → ℂ) :=
  ENNReal.ofReal (alPartition38 L c h)⁻¹ • alWeighted38 L c h

theorem measurable_alRho38 : Measurable (alRho38 (L := L)) := by
  unfold alRho38
  refine Finset.measurable_prod _ fun j _ => ?_
  have : Measurable fun α : ZMod L → ℂ => ‖α j‖ := (measurable_pi_apply j).norm
  fun_prop

theorem alWeighted_univ38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : 0 < h) :
    alWeighted38 L c h Set.univ = ENNReal.ofReal (alPartition38 L c h) := by
  classical
  have hint := alIntegrand_integrable38 (L := L) hc hh
  have hE := meas_alEnergyInd38 (L := L) hc hh
  unfold alWeighted38 alLiouvilleMeasure38
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_withDensity_eq_lintegral_mul _
      (f := fun α => ENNReal.ofReal (alRho38 α))
      (ENNReal.measurable_ofReal.comp measurable_alRho38)
      (g := fun α => ENNReal.ofReal (Real.exp (-alEnergyInd38 c h α)))
      (ENNReal.measurable_ofReal.comp hE.neg.exp)]
  have hpart : alPartition38 L c h = ∫ α, alIntegrand38 (L := L) c h α := rfl
  rw [hpart, ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (alIntegrand_nonneg38 c h))]
  have hsupp : Function.support (fun α => ENNReal.ofReal (alIntegrand38 (L := L) c h α)) ⊆
      alDisk38 L := by
    intro α hα
    by_contra hn
    apply hα
    have : alIntegrand38 (L := L) c h α = 0 := by
      unfold alIntegrand38; simp [show ¬ IsALField38 α from hn]
    simp [this]
  rw [← setLIntegral_eq_of_support_subset hsupp]
  refine setLIntegral_congr_fun measurableSet_alDisk38 fun α hα => ?_
  have h1 : IsALField38 α := hα
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (by exact (Finset.prod_nonneg fun j _ => inv_nonneg.2 (by
    have := h1 j; nlinarith [norm_nonneg (α j)])))]
  unfold alIntegrand38 alEnergyInd38
  simp only [h1, ite_true]
  rw [mul_comm]; rfl

theorem isProbabilityMeasure_alEta38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : 0 < h) :
    IsProbabilityMeasure (alEta38 L c h) := by
  have hpos := (alPartition_bounds38 (L := L) hc hh).2.2.1
  refine ⟨?_⟩
  unfold alEta38
  rw [Measure.smul_apply, alWeighted_univ38 hc hh, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity),
    inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one]

/-- **Invariance of the weighted Liouville measure** under the `H_d` flow. -/
theorem alWeighted_invariant38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : 0 < h) (s : ℝ) :
    (alWeighted38 L c h).map (alFlow38 alHd s) = alWeighted38 L c h := by
  classical
  obtain ⟨hm, -⟩ := alLiouville_preimage38 (alHd_contDiffOn38 (L := L)) alBracket_mass_alHd38 s
  have hw : Measurable fun α : ZMod L → ℂ => ENNReal.ofReal (Real.exp (-alEnergyInd38 c h α)) :=
    ENNReal.measurable_ofReal.comp (meas_alEnergyInd38 hc hh).neg.exp
  refine Measure.ext fun A hA => ?_
  unfold alWeighted38
  rw [Measure.map_apply hm hA, withDensity_apply _ (hm hA), withDensity_apply _ hA,
    ← lintegral_indicator (hm hA), ← lintegral_indicator hA]
  rw [← alLiouville_lintegral_flow38 (alHd_contDiffOn38 (L := L)) alBracket_mass_alHd38 s
    (hw.indicator hA)]
  refine lintegral_congr fun α => ?_
  by_cases hx : alFlow38 alHd s α ∈ A
  · rw [Set.indicator_of_mem (show α ∈ alFlow38 alHd s ⁻¹' A from hx), Set.indicator_of_mem hx,
      alEnergyInd_flow38]
  · rw [Set.indicator_of_notMem (show α ∉ alFlow38 alHd s ⁻¹' A from hx),
      Set.indicator_of_notMem hx]

/-- **(L02c) Invariance of `η_h`** under the Ablowitz-Ladik (`H_d`) flow, every `s ∈ ℝ`. -/
theorem alEta_invariant38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : 0 < h) (s : ℝ) :
    (alEta38 L c h).map (alFlow38 alHd s) = alEta38 L c h := by
  unfold alEta38
  rw [Measure.map_smul, alWeighted_invariant38 hc hh s]
  exact (alLiouville_preimage38 (alHd_contDiffOn38 (L := L)) alBracket_mass_alHd38 s).1.aemeasurable

end Invariance


#check @alPartition_bounds38
#check @alGaussianNormalizer_bundled38
#check @integrable_alReweight38
#check @meas_alReweight38
#check @alEnergy_flow38
#check @alWeighted_univ38
#check @isProbabilityMeasure_alEta38
#check @alEta_invariant38
#print axioms alPartition_bounds38
#print axioms alGaussianNormalizer_bundled38
#print axioms integrable_alReweight38
#print axioms alEnergy_flow38
#print axioms alWeighted_univ38
#print axioms isProbabilityMeasure_alEta38
#print axioms alEta_invariant38

end NlsGge.AblowitzLadik
end
