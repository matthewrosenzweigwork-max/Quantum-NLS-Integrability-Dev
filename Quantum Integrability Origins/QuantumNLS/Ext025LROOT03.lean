import Mathlib

/-!
# EXT-025 layer A: contract theorem for FIN-EXT025-ROOT-03 (REPAIRED text)

Exact source text: `implementation/ops/contracts/OWNER_CONTRACT_REPAIRS_2026-11-16.md`
(sha256 7af859909fd84fa7...; section "FIN-EXT025-ROOT-03 (corrected) -- Schur bound").
The historical record in FINAL_EXTERNAL_THEOREM_INSTANCES.json (sha256
82876b0400535292c74c814f70269d4dea6778fb05d4d3066b73e8a3d0d13782) is not edited.

* Hypotheses: `μ`, `ν` SFinite measures (covering Lebesgue measure on intervals and boxes,
  counting measure, normalized Haar on tori); `K` is `(μ⊗ν)`-measurable with
  `∫|K(x,y)| dν(y) ≤ A` for every `x` and `∫|K(x,y)| dμ(x) ≤ B` for every `y`.
* Conclusion: the induced `L²` operator has norm at most `√(A B)`.
* Original application wrapper (descriptive): for `A = 0` or `B = 0` the operator is zero.

Lean reading.  Two measure spaces `X`, `Y` with `SFinite` measures; the kernel `K : X × Y → ℂ` is
`AEStronglyMeasurable` for `μ.prod ν` (the weakest reading of "(μ⊗ν)-measurable"; in particular
it covers every `Measurable K`).  The bounds are the printed ones, for every `x`, resp. every `y`,
stated with lower Lebesgue integrals of `‖K‖ₑ` (so no integrability premise is smuggled in).
`A, B` are finite nonnegative reals.  The "induced `L²` operator" `L²(ν) → L²(μ)` is
expressed by its defining formula: `T g` is a.e. the function `x ↦ ∫ K(x,y) g(y) dν(y)`,
whose integrand is a.e. integrable.  Conclusions: existence of `T` as a bounded `ℂ`-linear
map, `‖T‖ ≤ √(A B)`, uniqueness of an operator with that formula, and `T = 0` when `A = 0`
or `B = 0`.  No weaker (single-space, finite-measure, equal-bound) surrogate is used.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace QuantumNLS.Ext025L

universe u v

/-- Weighted Cauchy-Schwarz for nonnegative extended integrals. -/
theorem schur_cs {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) (k u : Y → ℝ≥0∞)
    (hk : Measurable k) (hu : Measurable u) :
    (∫⁻ y, k y * u y ∂ν) ^ 2 ≤ (∫⁻ y, k y ∂ν) * ∫⁻ y, k y * u y ^ 2 ∂ν := by
  have sqsq : ∀ a b : ℝ≥0∞, (a ^ (1 / (2:ℝ)) * b ^ (1 / (2:ℝ))) ^ 2 = a * b := by
    intro a b
    rw [mul_pow, ← ENNReal.rpow_natCast (a ^ (1 / (2:ℝ))),
      ← ENNReal.rpow_natCast (b ^ (1 / (2:ℝ))), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    norm_num
  set m := ν.withDensity k with hm
  have h1 : ∫⁻ y, k y * u y ∂ν = ∫⁻ y, u y ∂m :=
    (lintegral_withDensity_eq_lintegral_mul ν hk hu).symm
  have h2 : ∫⁻ y, k y ∂ν = ∫⁻ y, (1 : ℝ≥0∞) ∂m := by
    have := lintegral_withDensity_eq_lintegral_mul ν hk (measurable_const (a := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one] at this
    exact this.symm
  have h3 : ∫⁻ y, k y * u y ^ 2 ∂ν = ∫⁻ y, u y ^ 2 ∂m := by
    have := lintegral_withDensity_eq_lintegral_mul ν hk (hu.pow_const 2)
    simp only [Pi.mul_apply] at this
    exact this.symm
  rw [h1, h2, h3]
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq m Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ≥0∞)) (g := u) measurable_const.aemeasurable hu.aemeasurable
  simp only [Pi.mul_apply, one_mul, ENNReal.rpow_two, one_pow] at H
  calc (∫⁻ y, u y ∂m) ^ 2
      ≤ ((∫⁻ y, (1:ℝ≥0∞) ∂m) ^ (1 / (2:ℝ)) * (∫⁻ y, u y ^ 2 ∂m) ^ (1 / (2:ℝ))) ^ 2 :=
        pow_le_pow_left' H 2
    _ = _ := sqsq _ _

theorem schur_eL2 {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) (g : Y → ℂ)
    (hg : AEStronglyMeasurable g ν) :
    eLpNorm g 2 ν = (∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν) ^ (1 / (2:ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

theorem schur_memLp2 {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) (g : Y → ℂ)
    (hg : AEStronglyMeasurable g ν) (h : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν < ∞) : MemLp g 2 ν := by
  show eLpNorm g 2 ν < ∞
  rw [schur_eL2 ν g hg]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne

/-- The core `L²` estimate for a measurable kernel and almost-everywhere row/column bounds. -/
theorem schur_core {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    (ν : Measure Y) [SFinite μ] [SFinite ν] (K : X × Y → ℂ) (hK : Measurable K) (A B : ℝ≥0)
    (hrow : ∀ᵐ x ∂μ, ∫⁻ y, ‖K (x, y)‖ₑ ∂ν ≤ A) (hcol : ∀ᵐ y ∂ν, ∫⁻ x, ‖K (x, y)‖ₑ ∂μ ≤ B)
    (g : Y → ℂ) (hg : Measurable g) :
    ∫⁻ x, (∫⁻ y, ‖K (x, y)‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 ∂μ ≤ (A * B : ℝ≥0∞) * ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν := by
  have hkm : Measurable fun z : X × Y => ‖K z‖ₑ := hK.enorm
  have hsec : ∀ x, Measurable fun y => ‖K (x, y)‖ₑ := fun x =>
    hkm.comp (measurable_const.prodMk measurable_id)
  have hu : Measurable fun y => ‖g y‖ₑ := hg.enorm
  have s2 : ∀ x, (∫⁻ y, ‖K (x, y)‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 ≤
      (∫⁻ y, ‖K (x, y)‖ₑ ∂ν) * ∫⁻ y, ‖K (x, y)‖ₑ * ‖g y‖ₑ ^ 2 ∂ν := fun x =>
    schur_cs ν _ _ (hsec x) hu
  have s3 : ∫⁻ x, (∫⁻ y, ‖K (x, y)‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 ∂μ ≤
      ∫⁻ x, (A : ℝ≥0∞) * ∫⁻ y, ‖K (x, y)‖ₑ * ‖g y‖ₑ ^ 2 ∂ν ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hrow] with x hx
    exact (s2 x).trans (by gcongr)
  have hmeas2 : Measurable fun z : X × Y => ‖K z‖ₑ * ‖g z.2‖ₑ ^ 2 :=
    hkm.mul ((hu.comp measurable_snd).pow_const 2)
  have s4 : ∫⁻ x, ∫⁻ y, ‖K (x, y)‖ₑ * ‖g y‖ₑ ^ 2 ∂ν ∂μ =
      ∫⁻ y, (∫⁻ x, ‖K (x, y)‖ₑ ∂μ) * ‖g y‖ₑ ^ 2 ∂ν := by
    rw [lintegral_lintegral_swap hmeas2.aemeasurable]
    refine lintegral_congr fun y => ?_
    have hm : Measurable fun x => ‖K (x, y)‖ₑ := hkm.comp (measurable_id.prodMk measurable_const)
    exact lintegral_mul_const _ hm
  have s5 : ∫⁻ y, (∫⁻ x, ‖K (x, y)‖ₑ ∂μ) * ‖g y‖ₑ ^ 2 ∂ν ≤
      ∫⁻ y, (B : ℝ≥0∞) * ‖g y‖ₑ ^ 2 ∂ν := by
    refine lintegral_mono_ae ?_
    filter_upwards [hcol] with y hy
    gcongr
  calc _ ≤ _ := s3
    _ = (A : ℝ≥0∞) * ∫⁻ x, ∫⁻ y, ‖K (x, y)‖ₑ * ‖g y‖ₑ ^ 2 ∂ν ∂μ :=
        lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ (A : ℝ≥0∞) * ((B : ℝ≥0∞) * ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν) := by
      rw [s4]; gcongr; refine s5.trans ?_
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    _ = _ := by ring

/-- The `L²(ν) → L²(μ)` operator of a measurable kernel (a.e. row/column bounds). -/
theorem schur_meas {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    (ν : Measure Y) [SFinite μ] [SFinite ν] (K : X × Y → ℂ) (hK : Measurable K) (A B : ℝ≥0)
    (hrow : ∀ᵐ x ∂μ, ∫⁻ y, ‖K (x, y)‖ₑ ∂ν ≤ A) (hcol : ∀ᵐ y ∂ν, ∫⁻ x, ‖K (x, y)‖ₑ ∂μ ≤ B) :
    ∃ T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ, ‖T‖ ≤ ((NNReal.sqrt (A * B) : ℝ≥0) : ℝ) ∧
      ∀ g : Lp ℂ 2 ν, (∀ᵐ x ∂μ, Integrable (fun y => K (x, y) * g y) ν) ∧
        (T g : X → ℂ) =ᵐ[μ] fun x => ∫ y, K (x, y) * g y ∂ν := by
  have hkm : Measurable fun z : X × Y => ‖K z‖ₑ := hK.enorm
  have hgm : ∀ g : Lp ℂ 2 ν, Measurable (g : Y → ℂ) :=
    fun g => (Lp.stronglyMeasurable g).measurable
  have hgI : ∀ g : Lp ℂ 2 ν, ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν < ∞ := fun g => by
    have h1 := schur_eL2 ν g (Lp.aestronglyMeasurable g)
    have h2 : eLpNorm g 2 ν < ∞ := Lp.eLpNorm_lt_top g
    rw [h1] at h2
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc] at h2
    simp at h2
  have hHint : ∀ g : Lp ℂ 2 ν, ∫⁻ x, (∫⁻ y, ‖K (x, y)‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 ∂μ ≤
      (A * B : ℝ≥0∞) * ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν :=
    fun g => schur_core μ ν K hK A B hrow hcol g (hgm g)
  have hHfin : ∀ g : Lp ℂ 2 ν, ∫⁻ x, (∫⁻ y, ‖K (x, y)‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 ∂μ < ∞ := fun g =>
    (hHint g).trans_lt (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top) (hgI g))
  have hF : ∀ g : Lp ℂ 2 ν, ∀ᵐ x ∂μ, Integrable (fun y => K (x, y) * g y) ν := by
    intro g
    have hfin : ∀ᵐ x ∂μ, (∫⁻ y, ‖K (x, y)‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 < ∞ := by
      refine ae_lt_top' ?_ (hHfin g).ne
      exact ((Measurable.lintegral_prod_right' (f := fun z : X × Y => ‖K z‖ₑ * ‖g z.2‖ₑ)
        (hkm.mul ((hgm g).enorm.comp measurable_snd)))).pow_const 2 |>.aemeasurable
    filter_upwards [hfin] with x hx
    refine ⟨((hK.comp (measurable_const.prodMk measurable_id)).mul
      (hgm g)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp only [enorm_mul]
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc] at hx
    simp at hx
  let F : Lp ℂ 2 ν → X → ℂ := fun g x => ∫ y, K (x, y) * g y ∂ν
  have hFm : ∀ g, AEStronglyMeasurable (F g) μ := by
    intro g
    have : AEStronglyMeasurable (fun z : X × Y => K z * g z.2) (μ.prod ν) :=
      hK.aestronglyMeasurable.mul
        ((Lp.aestronglyMeasurable g).comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_snd)
    exact this.integral_prod_right'
  have hFbound : ∀ g, ∫⁻ x, ‖F g x‖ₑ ^ 2 ∂μ ≤ (A * B : ℝ≥0∞) * ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν := by
    intro g
    refine le_trans (lintegral_mono fun x => ?_) (hHint g)
    refine pow_le_pow_left' ((enorm_integral_le_lintegral_enorm _).trans ?_) 2
    simp only [enorm_mul, le_refl]
  have hmem : ∀ g, MemLp (F g) 2 μ := fun g => schur_memLp2 μ _ (hFm g)
    ((hFbound g).trans_lt (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top) (hgI g)))
  have hadd : ∀ g₁ g₂, F (g₁ + g₂) =ᵐ[μ] F g₁ + F g₂ := by
    intro g₁ g₂
    filter_upwards [hF g₁, hF g₂] with x h1 h2
    have : ∀ᵐ y ∂ν, K (x, y) * (↑↑(g₁ + g₂) : Y → ℂ) y = K (x, y) * g₁ y + K (x, y) * g₂ y := by
      filter_upwards [Lp.coeFn_add g₁ g₂] with y hy
      rw [hy, Pi.add_apply, mul_add]
    simp only [F, Pi.add_apply]
    rw [integral_congr_ae this, integral_add h1 h2]
  have hsmul : ∀ (c : ℂ) g, F (c • g) =ᵐ[μ] c • F g := by
    intro c g
    refine Filter.Eventually.of_forall fun x => ?_
    have : ∀ᵐ y ∂ν, K (x, y) * (↑↑(c • g) : Y → ℂ) y = c * (K (x, y) * g y) := by
      filter_upwards [Lp.coeFn_smul c g] with y hy
      rw [hy, Pi.smul_apply, smul_eq_mul]; ring
    simp only [F, Pi.smul_apply, smul_eq_mul]
    rw [integral_congr_ae this, integral_const_mul]
  let Tlin : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun g => (hmem g).toLp (F g)
      map_add' := fun g₁ g₂ => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (hadd g₁ g₂)
      map_smul' := fun c g => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (hsmul c g) }
  have hnorm : ∀ g, ‖Tlin g‖ ≤ ((NNReal.sqrt (A * B) : ℝ≥0) : ℝ) * ‖g‖ := by
    intro g
    have e1 : ‖Tlin g‖ = (eLpNorm (F g) 2 μ).toReal := Lp.norm_toLp (F g) (hmem g)
    have e2 : ‖g‖ = (eLpNorm g 2 ν).toReal := Lp.norm_def g
    have hle : eLpNorm (F g) 2 μ ≤ (NNReal.sqrt (A * B) : ℝ≥0∞) * eLpNorm g 2 ν := by
      rw [schur_eL2 μ _ (hFm g), schur_eL2 ν g (Lp.aestronglyMeasurable g)]
      have hC : ((NNReal.sqrt (A * B) : ℝ≥0) : ℝ≥0∞) = (A * B : ℝ≥0∞) ^ (1 / (2:ℝ)) := by
        rw [NNReal.sqrt_eq_rpow, ENNReal.coe_rpow_of_nonneg _ (by norm_num : (0:ℝ) ≤ 1 / 2)]
        simp
      rw [hC, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      exact ENNReal.rpow_le_rpow (hFbound g) (by norm_num)
    rw [e1, e2]
    have hfin : (NNReal.sqrt (A * B) : ℝ≥0∞) * eLpNorm g 2 ν ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_lt_top g).ne
    have := ENNReal.toReal_mono hfin hle
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal] at this
  refine ⟨Tlin.mkContinuous _ hnorm,
    LinearMap.mkContinuous_norm_le _ (NNReal.coe_nonneg _) hnorm, fun g => ⟨hF g, ?_⟩⟩
  exact (hmem g).coeFn_toLp

/-- FIN-EXT025-ROOT-03 (corrected) as a Lean theorem. -/
theorem contract_ROOT03 :
    ∀ (X : Type u) (Y : Type v) [MeasurableSpace X] [MeasurableSpace Y]
      (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (K : X × Y → ℂ),
      AEStronglyMeasurable K (μ.prod ν) → ∀ (A B : ℝ), 0 ≤ A → 0 ≤ B →
      (∀ x, ∫⁻ y, ‖K (x, y)‖ₑ ∂ν ≤ ENNReal.ofReal A) →
      (∀ y, ∫⁻ x, ‖K (x, y)‖ₑ ∂μ ≤ ENNReal.ofReal B) →
      ∃ T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ, ‖T‖ ≤ Real.sqrt (A * B) ∧
        (∀ g : Lp ℂ 2 ν, (∀ᵐ x ∂μ, Integrable (fun y => K (x, y) * g y) ν) ∧
          (T g : X → ℂ) =ᵐ[μ] fun x => ∫ y, K (x, y) * g y ∂ν) ∧
        (∀ T' : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ,
          (∀ g : Lp ℂ 2 ν, (T' g : X → ℂ) =ᵐ[μ] fun x => ∫ y, K (x, y) * g y ∂ν) → T' = T) ∧
        ((A = 0 ∨ B = 0) → T = 0) := by
  intro X Y _ _ μ ν _ _ K hK A B hA hB hrow hcol
  have hKm : AEMeasurable K (μ.prod ν) := hK.aemeasurable
  set K' := hKm.mk K with hK'
  have hK'm : Measurable K' := hKm.measurable_mk
  have hae : K =ᵐ[μ.prod ν] K' := hKm.ae_eq_mk
  have hkk : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, K (x, y) = K' (x, y) := Measure.ae_ae_of_ae_prod hae
  have hkk2 : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, K (x, y) = K' (x, y) := by
    have hs : (fun z : Y × X => K z.swap) =ᵐ[ν.prod μ] fun z => K' z.swap :=
      (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae_eq_comp hae
    exact Measure.ae_ae_of_ae_prod hs
  have hrow' : ∀ᵐ x ∂μ, ∫⁻ y, ‖K' (x, y)‖ₑ ∂ν ≤ (A.toNNReal : ℝ≥0∞) := by
    filter_upwards [hkk] with x hx
    have : ∫⁻ y, ‖K (x, y)‖ₑ ∂ν = ∫⁻ y, ‖K' (x, y)‖ₑ ∂ν :=
      lintegral_congr_ae (hx.mono fun y hy => by simp only [hy])
    rw [← this]
    exact hrow x
  have hcol' : ∀ᵐ y ∂ν, ∫⁻ x, ‖K' (x, y)‖ₑ ∂μ ≤ (B.toNNReal : ℝ≥0∞) := by
    filter_upwards [hkk2] with y hy
    have : ∫⁻ x, ‖K (x, y)‖ₑ ∂μ = ∫⁻ x, ‖K' (x, y)‖ₑ ∂μ :=
      lintegral_congr_ae (hy.mono fun x hx => by simp only [hx])
    rw [← this]
    exact hcol y
  obtain ⟨T, hTn, hT⟩ := schur_meas μ ν K' hK'm A.toNNReal B.toNNReal hrow' hcol'
  have hspec : ∀ g : Lp ℂ 2 ν, (∀ᵐ x ∂μ, Integrable (fun y => K (x, y) * g y) ν) ∧
      (T g : X → ℂ) =ᵐ[μ] fun x => ∫ y, K (x, y) * g y ∂ν := by
    intro g
    obtain ⟨hI, hEq⟩ := hT g
    refine ⟨?_, ?_⟩
    · filter_upwards [hI, hkk] with x h1 h2
      refine h1.congr ?_
      filter_upwards [h2] with y hy
      rw [hy]
    · filter_upwards [hEq, hkk] with x h1 h2
      rw [h1]
      exact integral_congr_ae (by filter_upwards [h2] with y hy; rw [hy])
  have hnorm : ‖T‖ ≤ Real.sqrt (A * B) := by
    refine hTn.trans_eq ?_
    rw [Real.coe_sqrt, NNReal.coe_mul, Real.coe_toNNReal _ hA, Real.coe_toNNReal _ hB]
  refine ⟨T, hnorm, hspec, ?_, ?_⟩
  · intro T' hT'
    ext1 g
    refine Lp.ext ?_
    filter_upwards [hT' g, (hspec g).2] with x h1 h2
    rw [h1, h2]
  · intro hz
    have h0 : Real.sqrt (A * B) = 0 := by
      rcases hz with h | h <;> simp [h]
    rw [h0] at hnorm
    exact norm_le_zero_iff.mp hnorm

end QuantumNLS.Ext025L

#print axioms QuantumNLS.Ext025L.contract_ROOT03
