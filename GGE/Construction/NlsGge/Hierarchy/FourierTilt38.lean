import NlsGge.Hierarchy.RelativePartition38
import NlsGge.Hierarchy.ALTilt38

/-!
# W13 (v2 `F:eq:tilt`, `F:eq:Dlimit`): the exact finite-dimensional reduced-weight Gaussian tilt

On the Fourier plane `ℂ^{2N+1}` (modes `n = -N..N`, including `n = 0`), with
* `a_n = W(2πn) = fullWeightRate c n`, `γ_N = fullWeightFourierGaussian N c` (density
  `∏ (a_n/π) e^{-a_n|z_n|²}`),
* `f_N^F(z) = exp(-E_W(z) + Σ a_n |z_n|²)` (`fFourier38`),
* `G(z) = Q_0 + Q_4 = localCharge38 · 0 + localCharge38 · 2` (`tiltG38`),
* `W̃ = W - δ(1 + r⁴)`, coefficient numerators `c̃_0 = c_0 - δ`, `c̃_2 = c_2 - 16 δ`
  (`NlsGge.AblowitzLadik.alTiltCoeff38`), `ã_n = W̃(2πn)`,
* `D_{δ,N} = ∏_{|n|≤N} ã_n/a_n` (`tiltD38`),

the identity is `E_{γ_N}[f_N^F e^{δ G}] = D_{δ,N}⁻¹ Z_N(W̃)` with `Z_N = relativePartition38`,
and `D_{δ,N} → D_δ > 0`.  The determinant has exponent one (complex coordinates).
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot NlsGge.Measure MeasureTheory Filter Topology
open NlsGge.AblowitzLadik (alTiltCoeff38 alTiltCoeff_admitted38 weight_tilt38
  alTiltFactor38 alTiltFactor_bounds38 abs_log_factor_le38 deficit_le_majorant38
  alTiltMajorant38 summable_alTiltMajorant38)

/-- `G = Q_0 + Q_4` on the Fourier plane (`localCharge38 · j = Q_{2j}`). -/
def tiltG38 (N : ℕ) (z : FourierPlane N) : ℝ :=
  localCharge38 (planeReal N z) 0 + localCharge38 (planeReal N z) 2

/-- `f_N^F(z) = exp(-E_W(z) + Σ_{|n|≤N} a_n |z_n|²)`. -/
def fFourier38 {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) (z : FourierPlane N) : ℝ :=
  Real.exp (-fullEnergy38 c N z +
    ∑ i : Fin (2 * N + 1), fullWeightRate c.val (modeIndex N i) * ‖z i‖ ^ 2)

/-- `D_{δ,N} = ∏_{|n|≤N} ã_n / a_n`, with `ã_n = W̃(2πn)`. -/
def tiltD38 (c : ℕ → ℝ) (δ : ℝ) (N : ℕ) : ℝ :=
  ∏ i : Fin (2 * N + 1),
    (fullWeightRate (alTiltCoeff38 c δ) (modeIndex N i) / fullWeightRate c (modeIndex N i))

theorem prod_modeIndex38 (N : ℕ) (f : ℤ → ℝ) :
    ∏ i : Fin (2 * N + 1), f (modeIndex N i) = ∏ ν ∈ Finset.Icc (-(N : ℤ)) N, f ν := by
  refine Finset.prod_bij (fun i _ => modeIndex N i) (fun i _ => ?_) (fun i _ j _ h =>
    modeIndex_injective N h) (fun ν hν => ?_) (fun _ _ => rfl)
  · exact Finset.mem_Icc.2 (modeIndex_bounds N i)
  · obtain ⟨i, hi⟩ := modeIndex_covers N ν (Finset.mem_Icc.1 hν).1 (Finset.mem_Icc.1 hν).2
    exact ⟨i, Finset.mem_univ _, hi⟩

/-- Exact linearity of the full energy in the coefficients: `E_{W̃} = E_W - δ G`. -/
theorem fullEnergy38_tilt {lo up lo' up' : ℝ} (c : BoundedCoefficients lo up)
    (c' : BoundedCoefficients lo' up') (δ : ℝ) (hc' : c'.val = alTiltCoeff38 c.val δ)
    (N : ℕ) (z : FourierPlane N) :
    fullEnergy38 c' N z = fullEnergy38 c N z - δ * tiltG38 N z := by
  have hs := fullEnergy38_summable c N z
  have h0 : HasSum (fun j : ℕ => if j = 0 then δ * localCharge38 (planeReal N z) 0 else 0)
      (δ * localCharge38 (planeReal N z) 0) := by
    simpa using hasSum_ite_eq (0 : ℕ) (δ * localCharge38 (planeReal N z) 0)
  have h2 : HasSum (fun j : ℕ => if j = 2 then δ * localCharge38 (planeReal N z) 2 else 0)
      (δ * localCharge38 (planeReal N z) 2) := by
    simpa using hasSum_ite_eq (2 : ℕ) (δ * localCharge38 (planeReal N z) 2)
  have hsum := (hs.hasSum.sub h0).sub h2
  have e : (fun j : ℕ => c'.val j / ((j.factorial : ℝ)) ^ 4 * localCharge38 (planeReal N z) j) =
      fun j => c.val j / ((j.factorial : ℝ)) ^ 4 * localCharge38 (planeReal N z) j
        - (if j = 0 then δ * localCharge38 (planeReal N z) 0 else 0)
        - (if j = 2 then δ * localCharge38 (planeReal N z) 2 else 0) := by
    funext j
    rw [hc']
    unfold alTiltCoeff38
    by_cases h0 : j = 0
    · subst h0; simp; ring
    · by_cases h2 : j = 2
      · subst h2; simp [Nat.factorial]; ring
      · simp [h0, h2]
  unfold fullEnergy38 tiltG38
  rw [e, hsum.tsum_eq]
  ring

/-- Each factor of `D_{δ,N}` is `1 - δ(1+ω⁴)/a_n`, `ω = 2πn`. -/
theorem tiltD38_eq_factors {lo up : ℝ} (c : BoundedCoefficients lo up) (δ : ℝ) (N : ℕ) :
    tiltD38 c.val δ N = ∏ ν ∈ Finset.Icc (-(N : ℤ)) N,
      (1 - δ * (1 + (2 * Real.pi * ν) ^ 4) / NlsGge.Weights.weight c.val (2 * Real.pi * ν)) := by
  unfold tiltD38
  rw [prod_modeIndex38 N (fun ν => fullWeightRate (alTiltCoeff38 c.val δ) ν /
    fullWeightRate c.val ν)]
  refine Finset.prod_congr rfl fun ν _ => ?_
  have hpos := fullWeightRate_pos38 c ν
  unfold fullWeightRate at hpos ⊢
  rw [weight_tilt38 c.property]
  field_simp

theorem tiltD38_pos {lo up : ℝ} (c : BoundedCoefficients lo up) {lo' up' : ℝ}
    (c' : BoundedCoefficients lo' up') (δ : ℝ) (hc' : c'.val = alTiltCoeff38 c.val δ)
    (N : ℕ) : 0 < tiltD38 c.val δ N := by
  unfold tiltD38
  rw [← hc']
  exact Finset.prod_pos fun i _ =>
    div_pos (fullWeightRate_pos38 c' _) (fullWeightRate_pos38 c _)

/-- Integrability (before any Bochner identity) of `f_N^F e^{δG}` against the Gaussian `γ_N`,
and the Lebesgue-density form. -/
theorem fFourier_tilt_pointwise38 {lo up lo' up' : ℝ} (c : BoundedCoefficients lo up)
    (c' : BoundedCoefficients lo' up') (δ : ℝ) (hc' : c'.val = alTiltCoeff38 c.val δ)
    (N : ℕ) (z : FourierPlane N) :
    (∏ i, (fullWeightRate c.val (modeIndex N i) / Real.pi) *
        Real.exp (-fullWeightRate c.val (modeIndex N i) * ‖z i‖ ^ 2)) *
      (fFourier38 c N z * Real.exp (δ * tiltG38 N z)) =
    (∏ i, fullWeightRate c.val (modeIndex N i) / Real.pi) * Real.exp (-fullEnergy38 c' N z) := by
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, fullEnergy38_tilt c c' δ hc']
  unfold fFourier38
  have e : ∑ i : Fin (2 * N + 1), -fullWeightRate c.val (modeIndex N i) * ‖z i‖ ^ 2 =
      -∑ i : Fin (2 * N + 1), fullWeightRate c.val (modeIndex N i) * ‖z i‖ ^ 2 := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  have : Real.exp (-∑ i : Fin (2 * N + 1), fullWeightRate c.val (modeIndex N i) * ‖z i‖ ^ 2) *
      (Real.exp (-fullEnergy38 c N z +
        ∑ i : Fin (2 * N + 1), fullWeightRate c.val (modeIndex N i) * ‖z i‖ ^ 2) *
        Real.exp (δ * tiltG38 N z)) = Real.exp (-(fullEnergy38 c N z - δ * tiltG38 N z)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [← this]; ring

theorem integrable_fFourier_tilt38 {lo up lo' up' : ℝ} (c : BoundedCoefficients lo up)
    (c' : BoundedCoefficients lo' up') (δ : ℝ) (hc' : c'.val = alTiltCoeff38 c.val δ)
    (N : ℕ) :
    Integrable (fun z => fFourier38 c N z * Real.exp (δ * tiltG38 N z))
      (fullWeightFourierGaussian N c.val) := by
  have hlo := c.property.1
  have hden := fullWeightFourierGaussian_density lo up c.val hlo (fun j => (c.property.2.2 j).1)
    (fun j => (c.property.2.2 j).2) N
  have hpos : ∀ z : FourierPlane N, 0 ≤ ∏ i, (fullWeightRate c.val (modeIndex N i) / Real.pi) *
      Real.exp (-fullWeightRate c.val (modeIndex N i) * ‖z i‖ ^ 2) := fun z =>
    Finset.prod_nonneg fun i _ => mul_nonneg
      (div_nonneg (fullWeightRate_pos38 c _).le Real.pi_pos.le) (Real.exp_pos _).le
  rw [hden]
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop) (Filter.Eventually.of_forall
    fun _ => ENNReal.ofReal_lt_top)]
  have : (fun z : FourierPlane N => (ENNReal.ofReal (∏ i, (fullWeightRate c.val (modeIndex N i) /
      Real.pi) * Real.exp (-fullWeightRate c.val (modeIndex N i) * ‖z i‖ ^ 2))).toReal •
      (fFourier38 c N z * Real.exp (δ * tiltG38 N z))) =
      fun z => (∏ i, fullWeightRate c.val (modeIndex N i) / Real.pi) *
        Real.exp (-fullEnergy38 c' N z) := by
    funext z
    rw [ENNReal.toReal_ofReal (hpos z), smul_eq_mul]
    exact fFourier_tilt_pointwise38 c c' δ hc' N z
  rw [this]
  exact (integrable_exp_neg_fullEnergy38 c' N).const_mul _

/-- **`F:eq:tilt`.**  If `c̃ = alTiltCoeff38 c δ` is an admitted coefficient sequence (any
`BoundedCoefficients lo' up'` structure on it), then
`E_{γ_N}[f_N^F e^{δ G}] = D_{δ,N}⁻¹ Z_N(W̃)`. -/
theorem fourierTilt_identity38 {lo up lo' up' : ℝ} (c : BoundedCoefficients lo up)
    (c' : BoundedCoefficients lo' up') (δ : ℝ) (hc' : c'.val = alTiltCoeff38 c.val δ)
    (N : ℕ) :
    ∫ z, fFourier38 c N z * Real.exp (δ * tiltG38 N z) ∂(fullWeightFourierGaussian N c.val) =
      (tiltD38 c.val δ N)⁻¹ * relativePartition38 c' N := by
  have hlo := c.property.1
  have hden := fullWeightFourierGaussian_density lo up c.val hlo (fun j => (c.property.2.2 j).1)
    (fun j => (c.property.2.2 j).2) N
  have hnn : ∀ z : FourierPlane N, 0 ≤ ∏ i, (fullWeightRate c.val (modeIndex N i) / Real.pi) *
      Real.exp (-fullWeightRate c.val (modeIndex N i) * ‖z i‖ ^ 2) := fun z =>
    Finset.prod_nonneg fun i _ => mul_nonneg
      (div_nonneg (fullWeightRate_pos38 c _).le Real.pi_pos.le) (Real.exp_pos _).le
  rw [hden, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have : (fun z : FourierPlane N => (ENNReal.ofReal (∏ i, (fullWeightRate c.val (modeIndex N i) /
      Real.pi) * Real.exp (-fullWeightRate c.val (modeIndex N i) * ‖z i‖ ^ 2))).toReal •
      (fFourier38 c N z * Real.exp (δ * tiltG38 N z))) =
      fun z => (∏ i, fullWeightRate c.val (modeIndex N i) / Real.pi) *
        Real.exp (-fullEnergy38 c' N z) := by
    funext z
    rw [ENNReal.toReal_ofReal (hnn z), smul_eq_mul]
    exact fFourier_tilt_pointwise38 c c' δ hc' N z
  rw [this, integral_const_mul]
  change _ * fullPartition38 c' N = _
  unfold relativePartition38 tiltD38
  rw [← hc']
  have hP : ∀ i : Fin (2 * N + 1), (fullWeightRate c.val (modeIndex N i) / Real.pi) =
      (fullWeightRate c'.val (modeIndex N i) / fullWeightRate c.val (modeIndex N i))⁻¹
        / (Real.pi / fullWeightRate c'.val (modeIndex N i)) := fun i => by
    have h1 := (fullWeightRate_pos38 c (modeIndex N i)).ne'
    have h2 := (fullWeightRate_pos38 c' (modeIndex N i)).ne'
    have h3 := Real.pi_pos.ne'
    field_simp
  have hfree : freeNormalizer38 c' N =
      ∏ i : Fin (2 * N + 1), (Real.pi / fullWeightRate c'.val (modeIndex N i)) := rfl
  have hD : ∏ i : Fin (2 * N + 1), (fullWeightRate c'.val (modeIndex N i) /
      fullWeightRate c.val (modeIndex N i)) ≠ 0 :=
    (Finset.prod_pos fun i _ => div_pos (fullWeightRate_pos38 c' _)
      (fullWeightRate_pos38 c _)).ne'
  rw [Finset.prod_congr rfl fun i _ => hP i, Finset.prod_div_distrib, Finset.prod_inv_distrib, ← hfree]
  field_simp

/-- Admitted-class form: for `0 ≤ δ ≤ c₋/64` the tilted numerators lie in `[3c₋/4, c₊]`. -/
theorem fourierTilt_identity_admitted38 {lo up : ℝ} (c : BoundedCoefficients lo up) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ lo / 64) (N : ℕ) :
    ∃ c' : BoundedCoefficients (3 * lo / 4) up, c'.val = alTiltCoeff38 c.val δ ∧
      ∫ z, fFourier38 c N z * Real.exp (δ * tiltG38 N z) ∂(fullWeightFourierGaussian N c.val) =
        (tiltD38 c.val δ N)⁻¹ * relativePartition38 c' N := by
  refine ⟨⟨alTiltCoeff38 c.val δ, alTiltCoeff_admitted38 c.property hδ0 hδ⟩, rfl, ?_⟩
  exact fourierTilt_identity38 c _ δ rfl N

/-- General range `0 ≤ δ < min(β₀, β₂) = min(c₀, c₂/16)`: the tilted sequence is admitted for
some positive lower bound `lo'`. -/
theorem alTiltCoeff_admitted_general38 {lo up : ℝ} (c : BoundedCoefficients lo up) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (h0 : δ < c.val 0) (h2 : 16 * δ < c.val 2) :
    ∃ lo' : ℝ, 0 < lo' ∧ lo' ≤ up ∧ NlsGge.Pilot.AdmittedCoefficients lo' up (alTiltCoeff38 c.val δ) := by
  obtain ⟨hlo, hlu, hb⟩ := c.property
  set lo' := min lo (min (c.val 0 - δ) (c.val 2 - 16 * δ)) with hl'
  have hpos : 0 < lo' := lt_min hlo (lt_min (by linarith) (by linarith))
  have hle : lo' ≤ lo := min_le_left _ _
  have h02 : lo' ≤ c.val 0 - δ := (min_le_right _ _).trans (min_le_left _ _)
  have h22 : lo' ≤ c.val 2 - 16 * δ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨lo', hpos, by linarith, hpos, by linarith, fun j => ?_⟩
  have := hb j
  unfold alTiltCoeff38
  by_cases hj0 : j = 0
  · subst hj0; simp; constructor <;> linarith [this.1, this.2]
  · by_cases hj2 : j = 2
    · subst hj2; simp; constructor <;> linarith [this.1, this.2]
    · simp [hj0, hj2]; constructor <;> linarith [this.1, this.2]

/-- `F:eq:tilt` on the full source range `0 ≤ δ < min(β₀, β₂)`, `β₀ = c₀`, `β₂ = c₂/16`. -/
theorem fourierTilt_identity_general38 {lo up : ℝ} (c : BoundedCoefficients lo up) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (h0 : δ < c.val 0) (h2 : 16 * δ < c.val 2) (N : ℕ) :
    ∃ (lo' : ℝ) (c' : BoundedCoefficients lo' up), c'.val = alTiltCoeff38 c.val δ ∧
      ∫ z, fFourier38 c N z * Real.exp (δ * tiltG38 N z) ∂(fullWeightFourierGaussian N c.val) =
        (tiltD38 c.val δ N)⁻¹ * relativePartition38 c' N := by
  obtain ⟨lo', _, _, hadm⟩ := alTiltCoeff_admitted_general38 c hδ0 h0 h2
  exact ⟨lo', ⟨_, hadm⟩, rfl, fourierTilt_identity38 c _ δ rfl N⟩

/-- Convergence `D_{δ,N} → D_δ > 0` (`F:eq:Dlimit`), `D_δ = ∏_{n∈ℤ}(1 - δ(1+(2πn)⁴)/a_n)`. -/
theorem tiltD_tendsto38 {lo up : ℝ} (c : BoundedCoefficients lo up) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ lo / 64) :
    ∃ Dδ : ℝ, 0 < Dδ ∧
      HasProd (fun k : ℤ => 1 - δ * (1 + (2 * Real.pi * k) ^ 4) /
        NlsGge.Weights.weight c.val (2 * Real.pi * k)) Dδ ∧
      Tendsto (fun N : ℕ => tiltD38 c.val δ N) atTop (𝓝 Dδ) := by
  classical
  have hc := c.property
  have hlo := hc.1
  set f0 : ℤ → ℝ := fun k => alTiltFactor38 c.val δ (2 * Real.pi * k) 0 with hf0
  have hf0pos : ∀ k, 0 < f0 k := fun k => by
    have := (alTiltFactor_bounds38 hc hδ0 hδ (h := 0) (by positivity) (2 * Real.pi * k)).1
    linarith
  have hlim_bound : ∀ ν : ℤ, ‖Real.log (f0 ν)‖ ≤ 2 * alTiltMajorant38 lo δ ν := by
    intro ν
    have h1 := abs_log_factor_le38 hc hδ0 hδ (h := 0) (by positivity) (2 * Real.pi * ν)
    have h2 := deficit_le_majorant38 hc hδ0 hδ (h := 0) (by positivity) (ν := ν)
      (ω := 2 * Real.pi * ν) (by
        rw [abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]
        have := Real.pi_gt_three
        nlinarith [abs_nonneg (ν : ℝ)])
    rw [Real.norm_eq_abs]
    exact h1.trans (by linarith)
  have hsumm : Summable fun ν => Real.log (f0 ν) :=
    Summable.of_norm_bounded ((summable_alTiltMajorant38 lo δ).mul_left 2) hlim_bound
  have hHas := Real.hasProd_of_hasSum_log hf0pos hsumm.hasSum
  have e : f0 = fun k : ℤ => 1 - δ * (1 + (2 * Real.pi * k) ^ 4) /
      NlsGge.Weights.weight c.val (2 * Real.pi * k) := by
    funext k; simp [hf0, alTiltFactor38]
  rw [e] at hHas
  refine ⟨_, Real.exp_pos _, hHas, ?_⟩
  have hwin : Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) N) atTop atTop := by
    refine Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun x => ?_)
    · exact Finset.Icc_subset_Icc (by omega) (by omega)
    · exact ⟨x.natAbs, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩
  have hT : Tendsto (fun s : Finset ℤ => ∏ b ∈ s, (1 - δ * (1 + (2 * Real.pi * (b : ℝ)) ^ 4) /
      NlsGge.Weights.weight c.val (2 * Real.pi * (b : ℝ)))) atTop _ := hHas
  exact (hT.comp hwin).congr fun N => (tiltD38_eq_factors c δ N).symm

end NlsGge.HierarchyRiccati.Core

end
