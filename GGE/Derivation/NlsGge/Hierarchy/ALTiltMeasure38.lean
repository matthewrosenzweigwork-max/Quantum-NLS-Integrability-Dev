import NlsGge.Hierarchy.ALTilt38
import NlsGge.Hierarchy.ALFiniteMeasure38

/-!
# L12b: the exact lattice tilt against the measure `η_h` (`D:eq:ALtilt`, v2 l.2374-2397)

* `alTiltIntegral_eq_integral_eta38`: bridge from the Lebesgue-density integral `alTiltIntegral38`
  to `∫ e^{δ G_h} dη_h^W` for the measure `alEta38`, with integrability.
* `alTilt_identity_bundled38`: `D:eq:ALtilt` with finiteness/positivity of everything.
* `alTilt_H2_moment_conditional38`: **conditional** (L12.06): the relative partition bounds
  are explicit unproved hypotheses (`ALRelPartitionBounds38`); they are NOT claimed to hold.
-/

namespace NlsGge.AblowitzLadik

open MeasureTheory Filter Topology

section Bridge

variable {L : ℕ} [NeZero L] {lo up : ℝ} {c : ℕ → ℝ}

/-- `alWeighted38` is the Lebesgue measure with density `ofReal (alIntegrand38 c h)`. -/
theorem alWeighted_eq_withDensity38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ}
    (hh : 0 < h) :
    alWeighted38 L c h =
      (volume : Measure (ZMod L → ℂ)).withDensity fun α => ENNReal.ofReal (alIntegrand38 c h α) := by
  classical
  have hE := meas_alEnergyInd38 (L := L) hc hh
  have hρ : Measurable fun α : ZMod L → ℂ => ENNReal.ofReal (alRho38 α) :=
    ENNReal.measurable_ofReal.comp measurable_alRho38
  have hg : Measurable fun α : ZMod L → ℂ => ENNReal.ofReal (Real.exp (-alEnergyInd38 c h α)) :=
    ENNReal.measurable_ofReal.comp hE.neg.exp
  have hfun : (fun α : ZMod L → ℂ => ENNReal.ofReal (alIntegrand38 c h α)) =
      (alDisk38 L).indicator (fun α => ENNReal.ofReal (alRho38 α) *
        ENNReal.ofReal (Real.exp (-alEnergyInd38 c h α))) := by
    funext α
    by_cases hα : IsALField38 α
    · have hm : α ∈ alDisk38 L := hα
      rw [Set.indicator_of_mem hm, ← ENNReal.ofReal_mul]
      · unfold alIntegrand38 alEnergyInd38
        simp only [hα, ite_true]
        rw [mul_comm]; rfl
      · exact Finset.prod_nonneg fun j _ => inv_nonneg.2 (by
          have := hα j; nlinarith [norm_nonneg (α j)])
    · have hm : α ∉ alDisk38 L := hα
      rw [Set.indicator_of_notMem hm]
      unfold alIntegrand38; simp [hα]
  rw [hfun, withDensity_indicator measurableSet_alDisk38]
  unfold alWeighted38 alLiouvilleMeasure38
  exact (withDensity_mul (volume.restrict (alDisk38 L)) hρ hg).symm

/-- Pointwise: `alIntegrand38 c h α · e^{δ G_h(α)} = alIntegrand38 c̃ h α`. -/
theorem alIntegrand_tilt38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ lo / 64) {h : ℝ} (hh : 0 < h) (α : ZMod L → ℂ) :
    alIntegrand38 c h α * Real.exp (δ * alTiltG38 h α) =
      alIntegrand38 (alTiltCoeff38 c δ) h α := by
  classical
  by_cases hα : IsALField38 α
  · unfold alIntegrand38
    simp only [hα, ite_true]
    rw [alEnergy_tilt38 hc hδ0 hδ hα hh, mul_right_comm, ← Real.exp_add]
    congr 2; ring
  · unfold alIntegrand38; simp [hα]

/-- **Bridge.** For `0 ≤ δ ≤ lo/64`, `h > 0`, `W` in the class:
`e^{δ G_h}` is `η_h`-integrable, and `alTiltIntegral38 = ∫ e^{δ G_h} dη_h`; moreover both equal
`𝒵_h(W)⁻¹ 𝒵_h(W̃)`. -/
theorem alTiltIntegral_eq_integral_eta38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ lo / 64) {h : ℝ} (hh : 0 < h) :
    Integrable (fun α : ZMod L → ℂ => Real.exp (δ * alTiltG38 h α)) (alEta38 L c h) ∧
    ∫ α, Real.exp (δ * alTiltG38 h α) ∂(alEta38 L c h) = alTiltIntegral38 L c h δ ∧
    alTiltIntegral38 L c h δ =
      (alPartition38 L c h)⁻¹ * alPartition38 L (alTiltCoeff38 c δ) h := by
  have hc' := alTiltCoeff_admitted38 hc hδ0 hδ
  obtain ⟨-, -, hZpos, -⟩ := alPartition_bounds38 (L := L) hc hh
  obtain ⟨hint', -, -, -⟩ := alPartition_bounds38 (L := L) hc' hh
  have hai : Measurable (alIntegrand38 (L := L) c h) := meas_alIntegrand38 hc hh
  have hdens : Measurable fun α : ZMod L → ℂ => ENNReal.ofReal (alIntegrand38 c h α) :=
    ENNReal.measurable_ofReal.comp hai
  have hlt : ∀ᵐ α ∂(volume : Measure (ZMod L → ℂ)), ENNReal.ofReal (alIntegrand38 c h α) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hsm : (fun α : ZMod L → ℂ => (ENNReal.ofReal (alIntegrand38 c h α)).toReal •
      Real.exp (δ * alTiltG38 h α)) = alIntegrand38 (alTiltCoeff38 c δ) h := by
    funext α
    rw [ENNReal.toReal_ofReal (alIntegrand_nonneg38 c h α), smul_eq_mul,
      alIntegrand_tilt38 hc hδ0 hδ hh]
  have hW : Integrable (fun α : ZMod L → ℂ => Real.exp (δ * alTiltG38 h α)) (alWeighted38 L c h) := by
    rw [alWeighted_eq_withDensity38 hc hh, integrable_withDensity_iff_integrable_smul' hdens hlt, hsm]
    exact hint'
  have hWint : ∫ α, Real.exp (δ * alTiltG38 h α) ∂(alWeighted38 L c h) =
      alPartition38 L (alTiltCoeff38 c δ) h := by
    rw [alWeighted_eq_withDensity38 hc hh, integral_withDensity_eq_integral_toReal_smul hdens hlt, hsm]
    rfl
  have hEta : alEta38 L c h = ENNReal.ofReal (alPartition38 L c h)⁻¹ • alWeighted38 L c h := rfl
  have hid := alTiltIntegral_eq_partition38 L hc hδ0 hδ hh
  refine ⟨?_, ?_, hid⟩
  · rw [hEta]; exact hW.smul_measure ENNReal.ofReal_ne_top
  · rw [hEta, integral_smul_measure, hWint, ENNReal.toReal_ofReal (inv_nonneg.2 hZpos.le), hid,
      smul_eq_mul]

end Bridge

section Bundled

variable {lo up : ℝ} {c : ℕ → ℝ}

/-- **`D:eq:ALtilt`, bundled.** Under the mesh hypotheses (`L = 2N+1`, `h = 1/L`,
`(3lo/4)⁻¹ < L`, `0 ≤ δ ≤ lo/64`): `e^{δ G_h}` is `η_h`-integrable; `Z_h(W)` and `Z_h(W̃)` are
positive (finite reals, with the explicit upper bounds from `alGaussianNormalizer_bundled38`);
`D_{δ,h} > 0`; and `∫ e^{δ G_h} dη_h = D_{δ,h}⁻¹ Z_h(W̃)/Z_h(W)`. -/
theorem alTilt_identity_bundled38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) (N : ℕ)
    {h δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ lo / 64) (hh : h = ((2 * N + 1 : ℕ) : ℝ)⁻¹)
    (hN : (3 * lo / 4)⁻¹ < ((2 * N + 1 : ℕ) : ℝ)) :
    Integrable (fun α : ZMod (2 * N + 1) → ℂ => Real.exp (δ * alTiltG38 h α))
        (alEta38 (2 * N + 1) c h) ∧
    (0 < alZ38 (L := 2 * N + 1) c h ∧
      alZ38 (L := 2 * N + 1) c h ≤ (Real.pi * h / c 0) ^ (2 * N + 1) /
        (h ^ (2 * N + 1) * ∏ k : ZMod (2 * N + 1), Real.pi / alRate38 c h k.valMinAbs)) ∧
    (0 < alZ38 (L := 2 * N + 1) (alTiltCoeff38 c δ) h ∧
      alZ38 (L := 2 * N + 1) (alTiltCoeff38 c δ) h ≤
        (Real.pi * h / alTiltCoeff38 c δ 0) ^ (2 * N + 1) /
        (h ^ (2 * N + 1) * ∏ k : ZMod (2 * N + 1),
          Real.pi / alRate38 (alTiltCoeff38 c δ) h k.valMinAbs)) ∧
    0 < alTiltD38 c h δ N ∧
    ∫ α, Real.exp (δ * alTiltG38 h α) ∂(alEta38 (2 * N + 1) c h) =
      (alTiltD38 c h δ N)⁻¹ *
        (alZ38 (L := 2 * N + 1) (alTiltCoeff38 c δ) h / alZ38 (L := 2 * N + 1) c h) := by
  have hc' := alTiltCoeff_admitted38 hc hδ0 hδ
  have hh0 : 0 < h := by rw [hh]; positivity
  have hlo' : lo⁻¹ < ((2 * N + 1 : ℕ) : ℝ) := by
    refine lt_of_le_of_lt ?_ hN
    have := hc.1
    exact inv_anti₀ (by positivity) (by linarith)
  have ha := alRate38_pos_of_mesh38 hc hh hlo'
  obtain ⟨hI, hEq, -⟩ := alTiltIntegral_eq_integral_eta38 (L := 2 * N + 1) hc hδ0 hδ hh0
  have b1 := alGaussianNormalizer_bundled38 (L := 2 * N + 1) hc hh hlo'
  have b2 := alGaussianNormalizer_bundled38 (L := 2 * N + 1) hc' hh hN
  have hD : 0 < alTiltD38 c h δ N := by
    rw [alTiltD_eq_prod38 hc δ h N ha]
    exact Finset.prod_pos fun ν _ => div_pos (alRate38_pos_of_mesh38 hc' hh hN ν) (ha ν)
  refine ⟨hI, ⟨b1.2.2.2.2.2.2.1, b1.2.2.2.2.2.2.2.2⟩, ⟨b2.2.2.2.2.2.2.1, b2.2.2.2.2.2.2.2.2⟩, hD, ?_⟩
  rw [hEq]
  exact alTilt_identity38 hc N hδ0 hδ hh hN

end Bundled

section Conditional

variable {lo up : ℝ} {c : ℕ → ℝ}

/-- **Explicit, unproved hypothesis (L12.06).**  Uniform-in-small-`h` upper and lower relative
partition bounds at the nearby weights: for the lattice meshes `h_N = 1/(2N+1)`, `N ≥ N₀`,
`A ≤ Z_h(W̃)/Z_h(W) ≤ B` with `0 < A`. v2 l.2395: "upper and lower relative partition bounds at
the nearby weights"; the paper says these are NOT supplied by the Fourier theorem. This is only
a hypothesis; nothing here asserts it holds. -/
def ALRelPartitionBounds38 (c : ℕ → ℝ) (δ A B : ℝ) (N₀ : ℕ) : Prop :=
  0 < A ∧ ∀ N : ℕ, N₀ ≤ N →
    A ≤ alZ38 (L := 2 * N + 1) (alTiltCoeff38 c δ) (alMesh38 N) /
          alZ38 (L := 2 * N + 1) c (alMesh38 N) ∧
    alZ38 (L := 2 * N + 1) (alTiltCoeff38 c δ) (alMesh38 N) /
          alZ38 (L := 2 * N + 1) c (alMesh38 N) ≤ B

theorem measurable_alH2Sq38 {L : ℕ} [NeZero L] : Measurable (alH2Sq38 (L := L)) := by
  unfold alH2Sq38
  refine Finset.measurable_sum _ fun k _ => ?_
  refine measurable_const.mul ?_
  have : Measurable fun α : ZMod L → ℂ => ZMod.dft α k := by
    simp only [ZMod.dft_apply]
    refine Finset.measurable_sum _ fun j _ => ?_
    have hj : Measurable fun α : ZMod L → ℂ => α j := measurable_pi_apply j
    simp only [smul_eq_mul]
    exact measurable_const.mul hj
  exact this.norm.pow_const 2

/-- **CONDITIONAL (L12.06).**  Assume the unproved uniform relative partition bounds
`ALRelPartitionBounds38 c δ A B N₀` (hypothesis, not a theorem about the lattice model). Then
there are `κ > 0`, `C` and `N₁` such that for all `N ≥ N₁`, with `h = 1/(2N+1)`,
`∫ exp(δ κ ‖𝓘_h(α/h)‖²_{H²}) dη_h ≤ C` (and the integrand is integrable). Constants: `κ` from
`alG_H2_lower_exists38`, `C = 2 B / D_δ` with `D_δ > 0` from `alTiltD_tendsto38`. -/
theorem alTilt_H2_moment_conditional38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ lo / 64) {A B : ℝ} {N₀ : ℕ}
    (hrel : ALRelPartitionBounds38 c δ A B N₀) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ C : ℝ, ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      Integrable (fun α : ZMod (2 * N + 1) → ℂ => Real.exp (δ * (κ * alH2Sq38 α)))
        (alEta38 (2 * N + 1) c (alMesh38 N)) ∧
      ∫ α, Real.exp (δ * (κ * alH2Sq38 α)) ∂(alEta38 (2 * N + 1) c (alMesh38 N)) ≤ C := by
  obtain ⟨κ, hκ, hG⟩ := alG_H2_lower_exists38
  obtain ⟨Dδ, hDδ, -, hlim⟩ := alTiltD_tendsto38 hc hδ0 hδ
  have hev : ∀ᶠ N in atTop, Dδ / 2 < alTiltD38 c (alMesh38 N) δ N :=
    hlim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 hev
  obtain ⟨hA, hbd⟩ := hrel
  have hlo := hc.1
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt ((3 * lo / 4)⁻¹)
  refine ⟨κ, hκ, 2 / Dδ * B, max (max N₀ N₂) (max N₃ 1), fun N hN => ?_⟩
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN3 : N₃ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN1 : 1 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hNL : (3 * lo / 4)⁻¹ < ((2 * N + 1 : ℕ) : ℝ) := by
    refine lt_of_lt_of_le hN₃ ?_
    have : (N₃ : ℝ) ≤ N := by exact_mod_cast hN3
    push_cast; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  have hh : alMesh38 N = ((2 * N + 1 : ℕ) : ℝ)⁻¹ := rfl
  have hh0 : 0 < alMesh38 N := alMesh_pos38 N
  obtain ⟨hI, -, -, hD, hEq⟩ :=
    alTilt_identity_bundled38 hc N hδ0 hδ hh hNL
  have hc' := alTiltCoeff_admitted38 hc hδ0 hδ
  obtain ⟨hI2, hEq2, -⟩ := alTiltIntegral_eq_integral_eta38 (L := 2 * N + 1) hc hδ0 hδ hh0
  have hDlow := hN₂ N hN2
  have hZ := hbd N hN0
  have hLge : 3 ≤ 2 * N + 1 := by omega
  -- the eta-measure lives on the disk
  have hnull : alEta38 (2 * N + 1) c (alMesh38 N) (alDisk38 (2 * N + 1))ᶜ = 0 := by
    unfold alEta38
    rw [Measure.smul_apply, alWeighted_eq_withDensity38 hc hh0,
      withDensity_apply _ (measurableSet_alDisk38).compl]
    have : ∫⁻ α in (alDisk38 (2 * N + 1))ᶜ, ENNReal.ofReal
        (alIntegrand38 (L := 2 * N + 1) c (alMesh38 N) α) = 0 := by
      rw [setLIntegral_congr_fun (measurableSet_alDisk38).compl (g := fun _ => 0)]
      · simp
      · intro α hα
        have : ¬ IsALField38 α := hα
        simp [alIntegrand38, this]
    rw [this]; simp
  have hae : ∀ᵐ α ∂(alEta38 (2 * N + 1) c (alMesh38 N)), α ∈ alDisk38 (2 * N + 1) := by
    have := (measure_eq_zero_iff_ae_notMem (μ := alEta38 (2 * N + 1) c (alMesh38 N))
      (s := (alDisk38 (2 * N + 1))ᶜ)).1 hnull
    filter_upwards [this] with α hα
    simpa using hα
  have hle : ∀ᵐ α ∂(alEta38 (2 * N + 1) c (alMesh38 N)),
      Real.exp (δ * (κ * alH2Sq38 α)) ≤ Real.exp (δ * alTiltG38 (alMesh38 N) α) := by
    filter_upwards [hae] with α hα
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
      (hG (2 * N + 1) hLge hα hh) hδ0)
  have hmeas : Measurable fun α : ZMod (2 * N + 1) → ℂ => Real.exp (δ * (κ * alH2Sq38 α)) :=
    (measurable_const.mul (measurable_const.mul measurable_alH2Sq38)).exp
  have hint : Integrable (fun α : ZMod (2 * N + 1) → ℂ => Real.exp (δ * (κ * alH2Sq38 α)))
      (alEta38 (2 * N + 1) c (alMesh38 N)) :=
    hI.mono' hmeas.aestronglyMeasurable (by
      filter_upwards [hle] with α hα
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact hα)
  refine ⟨hint, ?_⟩
  calc ∫ α, Real.exp (δ * (κ * alH2Sq38 α)) ∂(alEta38 (2 * N + 1) c (alMesh38 N))
      ≤ ∫ α, Real.exp (δ * alTiltG38 (alMesh38 N) α) ∂(alEta38 (2 * N + 1) c (alMesh38 N)) :=
        integral_mono_ae hint hI hle
    _ = (alTiltD38 c (alMesh38 N) δ N)⁻¹ *
        (alZ38 (L := 2 * N + 1) (alTiltCoeff38 c δ) (alMesh38 N) /
          alZ38 (L := 2 * N + 1) c (alMesh38 N)) := hEq
    _ ≤ 2 / Dδ * B := by
        have hr : 0 ≤ alZ38 (L := 2 * N + 1) (alTiltCoeff38 c δ) (alMesh38 N) /
            alZ38 (L := 2 * N + 1) c (alMesh38 N) := le_trans hA.le hZ.1
        have hDi : (alTiltD38 c (alMesh38 N) δ N)⁻¹ ≤ 2 / Dδ := by
          rw [inv_eq_one_div, div_le_div_iff₀ hD hDδ]; linarith
        exact mul_le_mul hDi hZ.2 hr (by positivity)

end Conditional

end NlsGge.AblowitzLadik
