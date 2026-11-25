import NlsGge.Hierarchy.FourierTilt38
import NlsGge.Hierarchy.UniformPartitionBound38
import NlsGge.Hierarchy.FullEnergySpectralIdentification38
import NlsGge.Hierarchy.RiccatiQ4FiniteProjectionH1AndH2MatchingThird
import NlsGge.Spectral.ActualTraceFormulaQ024E02_38

/-!
# NEW-F08 (v2 `F:eq:unnormexp`, `F:eq:unnormtail`): unnormalized exponential `H²` moment

With `δ = c₋/64`, `G = Q₀ + Q₄` and `Φ_N(z) = ‖P_N U‖²_{h²} = Σ_{|n|≤N} (1+n²)² |z_n|²`:
* `G ≥ (1/2) Φ_N` on the plane (positive `Q₄` form);
* `E_{γ_N}[f_N^F e^{η Φ_N}] ≤ C` with `η = δ/2`, `C` depending only on `c₋, c₊`;
* tail `E[f_N^F 1_{‖P_N U‖_{h²} > R}] ≤ C e^{-η R²}` for `R ≥ 0`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot NlsGge.Measure MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

/-- `‖P_N U‖²_{h²} = Σ_{|n|≤N} (1+n²)² |z_n|²` (source convention `⟨n⟩^{2r}`, `r = 2`). -/
def planeH2NormSq38 (N : ℕ) (z : FourierPlane N) : ℝ :=
  ∑ i : Fin (2 * N + 1), (1 + (modeIndex N i : ℝ) ^ 2) ^ 2 * ‖z i‖ ^ 2

/-- `‖P_N U‖_{h²}`. -/
def planeH2Norm38 (N : ℕ) (z : FourierPlane N) : ℝ := Real.sqrt (planeH2NormSq38 N z)

theorem planeH2NormSq38_nonneg (N : ℕ) (z : FourierPlane N) : 0 ≤ planeH2NormSq38 N z :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem continuous_planeH2NormSq38 (N : ℕ) : Continuous (planeH2NormSq38 N) := by
  unfold planeH2NormSq38
  fun_prop

/-- Pointwise: `‖u''‖² + 2‖u‖⁶ + 8‖u‖²‖u'‖² + 2 Re(u² ū'²) ≥ ‖u''‖²`. -/
theorem q4_density_ge38 (a b c : ℂ) :
    ‖c‖ ^ 2 ≤ ‖c‖ ^ 2 + 2 * ‖a‖ ^ 6 + 8 * ‖a‖ ^ 2 * ‖b‖ ^ 2 + 2 * (a ^ 2 * (star b) ^ 2).re := by
  have h1 : |(a ^ 2 * (star b) ^ 2).re| ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_pow, norm_pow, norm_star]
  have h2 := neg_abs_le (a ^ 2 * (star b) ^ 2).re
  have h3 : 0 ≤ ‖a‖ ^ 6 := by positivity
  have h4 : 0 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by positivity
  nlinarith

/-- `Q₄ ≥ ‖u''‖²_{L²}` on the plane. -/
theorem localCharge38_two_ge38 (N : ℕ) (z : FourierPlane N) :
    ∑ i : Fin (2 * N + 1), (2 * Real.pi * (modeIndex N i : ℝ)) ^ 4 * ‖z i‖ ^ 2 ≤
      localCharge38 (planeReal N z) 2 := by
  have hU := planeReal_smooth38 N z
  have hper := planeReal_periodic N z
  have hform := NlsGge.SpectralFoundations.complexQ4_local_formula_Q024 _ hU hper
  have hk : ∀ k : ℕ, Continuous (iteratedDeriv k (planeReal N z)) := fun k => by
    rw [iteratedDeriv_eq_iterate]; exact (hU.iterate_deriv k).continuous
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  simp only [iteratedDeriv_zero, iteratedDeriv_one] at h0 h1
  have hnorm : (∫ x in (0:ℝ)..1, ‖iteratedDeriv 2 (planeReal N z) x‖ ^ 2) =
      ∑ i : Fin (2 * N + 1), (2 * Real.pi * (modeIndex N i : ℝ)) ^ 4 * ‖z i‖ ^ 2 := by
    rw [NlsGge.HierarchyRiccati.finitePlaneSecondDerivative_intervalIntegral_eq_L2Norm,
      planeL2_norm_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [derivativePlane, norm_mul]
    have e4 : ∀ t : ℝ, |t| ^ 4 = t ^ 4 := fun t => by
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
    have e : ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ * ‖Complex.I‖ * ‖((modeIndex N i : ℤ) : ℂ)‖ =
        |2 * Real.pi * (modeIndex N i : ℝ)| := by
      simp [abs_mul, abs_of_pos Real.pi_pos]
    rw [e, ← e4]
    ring
  rw [← hnorm]
  unfold localCharge38
  rw [hform]
  refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ fun x _ => ?_
  · exact (by have := h2; fun_prop : Continuous fun x => ‖iteratedDeriv 2 (planeReal N z) x‖ ^ 2).intervalIntegrable _ _
  · exact (by have := h2; fun_prop : Continuous fun x => ‖iteratedDeriv 2 (planeReal N z) x‖ ^ 2
        + 2 * ‖planeReal N z x‖ ^ 6 + 8 * ‖planeReal N z x‖ ^ 2 * ‖deriv (planeReal N z) x‖ ^ 2
        + 2 * ((planeReal N z) x ^ 2 * (star (deriv (planeReal N z) x)) ^ 2).re).intervalIntegrable _ _
  · exact q4_density_ge38 _ _ _

/-- `G = Q₀ + Q₄ ≥ (1/2) ‖P_N U‖²_{h²}` on the plane. -/
theorem tiltG38_ge_half_h2 (N : ℕ) (z : FourierPlane N) :
    planeH2NormSq38 N z / 2 ≤ tiltG38 N z := by
  unfold tiltG38
  rw [localCharge38_zero_plane N z]
  have h4 := localCharge38_two_ge38 N z
  unfold planeH2NormSq38
  rw [Finset.sum_div]
  have : ∑ i : Fin (2 * N + 1), (1 + (modeIndex N i : ℝ) ^ 2) ^ 2 * ‖z i‖ ^ 2 / 2 ≤
      ∑ i : Fin (2 * N + 1), ‖z i‖ ^ 2 +
        ∑ i : Fin (2 * N + 1), (2 * Real.pi * (modeIndex N i : ℝ)) ^ 4 * ‖z i‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    set n : ℝ := (modeIndex N i : ℝ)
    have hπ : (3:ℝ) < Real.pi := Real.pi_gt_three
    have hn : n ^ 4 ≤ (2 * Real.pi * n) ^ 4 := by
      rw [mul_pow, mul_comm]
      have : (1:ℝ) ≤ (2 * Real.pi) ^ 4 := one_le_pow₀ (by linarith)
      nlinarith [pow_nonneg (sq_nonneg n) 2, show n ^ 4 = (n ^ 2) ^ 2 by ring]
    have hz : 0 ≤ ‖z i‖ ^ 2 := by positivity
    have e : (1 + n ^ 2) ^ 2 / 2 ≤ 1 + n ^ 4 := by nlinarith [sq_nonneg (n ^ 2 - 1)]
    calc (1 + n ^ 2) ^ 2 * ‖z i‖ ^ 2 / 2 = (1 + n ^ 2) ^ 2 / 2 * ‖z i‖ ^ 2 := by ring
      _ ≤ (1 + n ^ 4) * ‖z i‖ ^ 2 := mul_le_mul_of_nonneg_right e hz
      _ ≤ _ := by nlinarith
  linarith

open NlsGge.AblowitzLadik (alTiltFactor_bounds38 abs_log_factor_le38 deficit_le_majorant38
  alTiltMajorant38 summable_alTiltMajorant38 alTiltFactor38)

/-- Uniform positive lower bound for `D_{δ,N}`, `δ = c₋/64`: it depends only on `c₋`
(the `log`-majorant of the factors is `c`-free), so it is uniform in the admitted sequence. -/
theorem tiltD_uniform_lower38 (lo up : ℝ) (hl : 0 < lo) (_hlu : lo ≤ up) :
    ∃ d : ℝ, 0 < d ∧ ∀ (c : BoundedCoefficients lo up) (N : ℕ),
      d ≤ tiltD38 c.val (lo / 64) N := by
  classical
  set δ : ℝ := lo / 64 with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hM0 : ∀ ν : ℤ, 0 ≤ alTiltMajorant38 lo δ ν := fun ν => by
    unfold alTiltMajorant38
    have : (0:ℝ) ≤ 324 * δ / lo * (1 / (ν : ℝ) ^ 2) := by positivity
    have h2 : (0:ℝ) ≤ (if ν = 0 then 1 / 4 else 0) := by split_ifs <;> norm_num
    linarith
  set S : ℝ := ∑' ν : ℤ, 2 * alTiltMajorant38 lo δ ν with hS
  have hsumm : Summable fun ν : ℤ => 2 * alTiltMajorant38 lo δ ν :=
    (summable_alTiltMajorant38 lo δ).mul_left 2
  refine ⟨Real.exp (-S), Real.exp_pos _, fun c N => ?_⟩
  have hc := c.property
  set f0 : ℤ → ℝ := fun k => alTiltFactor38 c.val δ (2 * Real.pi * k) 0 with hf0
  have hf0pos : ∀ k, 0 < f0 k := fun k => by
    have := (alTiltFactor_bounds38 hc hδ0 le_rfl (h := 0) (by positivity) (2 * Real.pi * k)).1
    linarith
  have hlogb : ∀ ν : ℤ, |Real.log (f0 ν)| ≤ 2 * alTiltMajorant38 lo δ ν := by
    intro ν
    have h1 := abs_log_factor_le38 hc hδ0 le_rfl (h := 0) (by positivity) (2 * Real.pi * ν)
    have hw : 4 * |(ν : ℝ)| ≤ |2 * Real.pi * (ν : ℝ)| := by
      rw [abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]
      have := Real.pi_gt_three
      nlinarith [abs_nonneg (ν : ℝ)]
    have h2 := deficit_le_majorant38 hc hδ0 le_rfl (h := 0) (by positivity) (ν := ν) hw
    exact h1.trans (by linarith)
  have hprod : tiltD38 c.val δ N = ∏ ν ∈ Finset.Icc (-(N : ℤ)) N, f0 ν := by
    rw [tiltD38_eq_factors c δ N]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [hf0, alTiltFactor38]
  have hlog : Real.log (tiltD38 c.val δ N) = ∑ ν ∈ Finset.Icc (-(N : ℤ)) N, Real.log (f0 ν) := by
    rw [hprod, Real.log_prod]
    exact fun ν _ => (hf0pos ν).ne'
  have hDpos : 0 < tiltD38 c.val δ N := by
    rw [hprod]; exact Finset.prod_pos fun ν _ => hf0pos ν
  have hge : -S ≤ Real.log (tiltD38 c.val δ N) := by
    rw [hlog]
    have h1 : ∑ ν ∈ Finset.Icc (-(N : ℤ)) N, |Real.log (f0 ν)| ≤
        ∑ ν ∈ Finset.Icc (-(N : ℤ)) N, 2 * alTiltMajorant38 lo δ ν :=
      Finset.sum_le_sum fun ν _ => hlogb ν
    have h2 := hsumm.sum_le_tsum (Finset.Icc (-(N : ℤ)) N) (fun ν _ => by
      have := hM0 ν; linarith)
    have h3 : -∑ ν ∈ Finset.Icc (-(N : ℤ)) N, |Real.log (f0 ν)| ≤
        ∑ ν ∈ Finset.Icc (-(N : ℤ)) N, Real.log (f0 ν) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun ν _ => neg_abs_le _
    linarith
  calc Real.exp (-S) ≤ Real.exp (Real.log (tiltD38 c.val δ N)) := Real.exp_le_exp.2 hge
    _ = _ := Real.exp_log hDpos

/-- **NEW-F08 / `F:eq:unnormexp`.** For `0 < c₋ ≤ c₊` there are `η > 0` (namely `c₋/128`) and `C`,
depending only on `c₋, c₊`, such that for every admitted `c` and every `N`,
`f_N^F e^{η ‖P_N U‖²_{h²}}` is `γ_N`-integrable with integral `≤ C`. -/
theorem exponentialH2Moment38 (lo up : ℝ) (hl : 0 < lo) (hlu : lo ≤ up) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ (c : BoundedCoefficients lo up) (N : ℕ),
      Integrable (fun z => fFourier38 c N z * Real.exp (η * planeH2NormSq38 N z))
        (fullWeightFourierGaussian N c.val) ∧
      ∫ z, fFourier38 c N z * Real.exp (η * planeH2NormSq38 N z)
        ∂(fullWeightFourierGaussian N c.val) ≤ C := by
  obtain ⟨d, hd, hdl⟩ := tiltD_uniform_lower38 lo up hl hlu
  obtain ⟨Z, hZ, hZb⟩ := uniformRelativePartition_bound38 (3 * lo / 4) up (by linarith)
    (by linarith)
  refine ⟨lo / 128, Z / d, by positivity, by positivity, fun c N => ?_⟩
  have hδ0 : (0:ℝ) ≤ lo / 64 := by positivity
  obtain ⟨c', hc', hid⟩ := fourierTilt_identity_admitted38 c hδ0 le_rfl N
  have hint := integrable_fFourier_tilt38 c c' (lo / 64) hc' N
  have hmeas : Continuous fun z : FourierPlane N =>
      fFourier38 c N z * Real.exp (lo / 128 * planeH2NormSq38 N z) := by
    unfold fFourier38
    have := continuous_fullEnergy38 c N
    have := continuous_planeH2NormSq38 N
    fun_prop
  have hle : ∀ z, fFourier38 c N z * Real.exp (lo / 128 * planeH2NormSq38 N z) ≤
      fFourier38 c N z * Real.exp (lo / 64 * tiltG38 N z) := fun z => by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    have := tiltG38_ge_half_h2 N z
    nlinarith
  have hnn : ∀ z, 0 ≤ fFourier38 c N z * Real.exp (lo / 128 * planeH2NormSq38 N z) :=
    fun z => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hI : Integrable (fun z => fFourier38 c N z * Real.exp (lo / 128 * planeH2NormSq38 N z))
      (fullWeightFourierGaussian N c.val) :=
    hint.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn z)]; exact hle z)
  refine ⟨hI, ?_⟩
  calc _ ≤ ∫ z, fFourier38 c N z * Real.exp (lo / 64 * tiltG38 N z)
        ∂(fullWeightFourierGaussian N c.val) := integral_mono hI hint hle
    _ = (tiltD38 c.val (lo / 64) N)⁻¹ * relativePartition38 c' N := hid
    _ ≤ d⁻¹ * Z := by
      have hDp := tiltD38_pos c c' (lo / 64) hc' N
      have h1 : (tiltD38 c.val (lo / 64) N)⁻¹ ≤ d⁻¹ := inv_anti₀ hd (hdl c N)
      have h2 := hZb c' N
      have hZp : 0 ≤ relativePartition38 c' N := by
        unfold relativePartition38 fullPartition38
        refine div_nonneg (integral_nonneg fun z => (Real.exp_pos _).le) (freeNormalizer38_pos c' N).le
      exact mul_le_mul h1 h2 hZp (inv_nonneg.2 hd.le)
    _ = Z / d := by ring

/-- **NEW-F08 / `F:eq:unnormexp` and `F:eq:unnormtail` together.** The same `η, C` (depending only
on `c₋, c₊`, chosen before `c, N, R`) give the exponential moment and, for every `R ≥ 0`, the
tail bound `∫_{‖P_N U‖_{h²} > R} f_N^F dγ_N ≤ C e^{-η R²}`. -/
theorem exponentialH2MomentTail38 (lo up : ℝ) (hl : 0 < lo) (hlu : lo ≤ up) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ (c : BoundedCoefficients lo up) (N : ℕ),
      (Integrable (fun z => fFourier38 c N z * Real.exp (η * planeH2NormSq38 N z))
          (fullWeightFourierGaussian N c.val) ∧
        ∫ z, fFourier38 c N z * Real.exp (η * planeH2NormSq38 N z)
          ∂(fullWeightFourierGaussian N c.val) ≤ C) ∧
      ∀ R : ℝ, 0 ≤ R →
        IntegrableOn (fFourier38 c N) {z | R < planeH2Norm38 N z}
          (fullWeightFourierGaussian N c.val) ∧
        ∫ z in {z | R < planeH2Norm38 N z}, fFourier38 c N z
          ∂(fullWeightFourierGaussian N c.val) ≤ C * Real.exp (-(η * R ^ 2)) := by
  obtain ⟨η, C, hη, hC, hmom⟩ := exponentialH2Moment38 lo up hl hlu
  refine ⟨η, C, hη, hC, fun c N => ⟨hmom c N, fun R hR => ?_⟩⟩
  obtain ⟨hI, hb⟩ := hmom c N
  set μ := fullWeightFourierGaussian N c.val
  have hfc : Continuous (fFourier38 c N) := by
    unfold fFourier38
    have := continuous_fullEnergy38 c N
    fun_prop
  have hf0 : ∀ z, 0 ≤ fFourier38 c N z := fun z => (Real.exp_pos _).le
  have hdom : ∀ z, fFourier38 c N z ≤
      fFourier38 c N z * Real.exp (η * planeH2NormSq38 N z) := fun z => by
    have : 1 ≤ Real.exp (η * planeH2NormSq38 N z) :=
      Real.one_le_exp (mul_nonneg hη.le (planeH2NormSq38_nonneg N z))
    nlinarith [hf0 z]
  have hfint : Integrable (fFourier38 c N) μ :=
    hI.mono' hfc.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]; exact hdom z)
  have hset : MeasurableSet {z : FourierPlane N | R < planeH2Norm38 N z} :=
    (isOpen_lt continuous_const (Real.continuous_sqrt.comp (continuous_planeH2NormSq38 N))).measurableSet
  refine ⟨hfint.integrableOn, ?_⟩
  have hg : Integrable (fun z => Real.exp (-(η * R ^ 2)) *
      (fFourier38 c N z * Real.exp (η * planeH2NormSq38 N z))) μ := hI.const_mul _
  calc ∫ z in {z | R < planeH2Norm38 N z}, fFourier38 c N z ∂μ
      ≤ ∫ z in {z | R < planeH2Norm38 N z}, Real.exp (-(η * R ^ 2)) *
          (fFourier38 c N z * Real.exp (η * planeH2NormSq38 N z)) ∂μ := by
        refine setIntegral_mono_on hfint.integrableOn hg.integrableOn hset fun z hz => ?_
        have hz' : R ^ 2 ≤ planeH2NormSq38 N z := by
          have h1 : R < Real.sqrt (planeH2NormSq38 N z) := hz
          have := (Real.lt_sqrt hR).1 h1
          exact this.le
        have h2 : 1 ≤ Real.exp (-(η * R ^ 2)) * Real.exp (η * planeH2NormSq38 N z) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by nlinarith)
        calc fFourier38 c N z ≤ fFourier38 c N z *
              (Real.exp (-(η * R ^ 2)) * Real.exp (η * planeH2NormSq38 N z)) := by
                nlinarith [hf0 z]
          _ = _ := by ring
    _ ≤ ∫ z, Real.exp (-(η * R ^ 2)) *
          (fFourier38 c N z * Real.exp (η * planeH2NormSq38 N z)) ∂μ :=
        setIntegral_le_integral hg (Filter.Eventually.of_forall fun z =>
          mul_nonneg (Real.exp_pos _).le (mul_nonneg (hf0 z) (Real.exp_pos _).le))
    _ = Real.exp (-(η * R ^ 2)) * ∫ z, fFourier38 c N z *
          Real.exp (η * planeH2NormSq38 N z) ∂μ := integral_const_mul _ _
    _ ≤ Real.exp (-(η * R ^ 2)) * C := mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by ring

end NlsGge.HierarchyRiccati.Core

end
