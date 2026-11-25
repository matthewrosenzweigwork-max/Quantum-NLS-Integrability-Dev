import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB13Local

/-! # Track B, contracts 18–19 (step 3): the cubic `L⁴ → L^{4/3}` is real-analytic

* `hmulL p q r`: the pointwise product `Lᵖ × L^q → L^r` (Hölder triple) as a real continuous bilinear
  map of norm `≤ 1`;
* `cjL p`: complex conjugation on `Lᵖ` as a real continuous linear map;
* `Ncub_eq`: `N f = 2 • ((f · conj f) · f)`, hence `analyticOnNhd_Ncub` (Mathlib
  `ContinuousLinearMap.analyticAt_bilinear`).
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Filter Topology NlsGge.Pilot
open scoped ENNReal NNReal ComplexConjugate

/-- Hölder exponents `1/4 + 1/4 = 1/2`. -/
instance holderTriple_four_four_two : ENNReal.HolderTriple 4 4 2 := by
  constructor
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by simp
  rw [h2, h4, ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_inv_of_pos (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

section Holder

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The pointwise product of an `Lᵖ` and an `L^q` function in `L^r`. -/
def hmulF (p q r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] [p.HolderTriple q r]
    (f : Lp ℂ p μ) (g : Lp ℂ q μ) : Lp ℂ r μ :=
  ((Lp.memLp f).mul (Lp.memLp g)).toLp _

variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] [p.HolderTriple q r]

theorem hmulF_coeFn (f : Lp ℂ p μ) (g : Lp ℂ q μ) :
    (hmulF p q r f g : α → ℂ) =ᵐ[μ] (f : α → ℂ) * (g : α → ℂ) :=
  MemLp.coeFn_toLp _

theorem hmulF_norm (f : Lp ℂ p μ) (g : Lp ℂ q μ) : ‖hmulF p q r f g‖ ≤ ‖f‖ * ‖g‖ := by
  have h : ‖hmulF p q r f g‖ₑ ≤ ‖f‖ₑ * ‖g‖ₑ := by
    rw [Lp.enorm_def, eLpNorm_congr_ae (hmulF_coeFn f g), Lp.enorm_def, Lp.enorm_def]
    exact eLpNorm_smul_le_mul_eLpNorm (Lp.aestronglyMeasurable f) (Lp.aestronglyMeasurable g)
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top enorm_ne_top) h
  rwa [ENNReal.toReal_mul, toReal_enorm, toReal_enorm, toReal_enorm] at h2

/-- The product as a real continuous bilinear map. -/
def hmulL (p q r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] [p.HolderTriple q r] :
    Lp ℂ p μ →L[ℝ] Lp ℂ q μ →L[ℝ] Lp ℂ r μ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (hmulF p q r)
      (fun f₁ f₂ g => Lp.ext (by
        filter_upwards [hmulF_coeFn (r := r) (f₁ + f₂) g, hmulF_coeFn (r := r) f₁ g,
          hmulF_coeFn (r := r) f₂ g, Lp.coeFn_add f₁ f₂,
          Lp.coeFn_add (hmulF p q r f₁ g) (hmulF p q r f₂ g)] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3]
        simp only [Pi.mul_apply, h4, Pi.add_apply, add_mul]))
      (fun c f g => Lp.ext (by
        filter_upwards [hmulF_coeFn (r := r) (c • f) g, hmulF_coeFn (r := r) f g,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (hmulF p q r f g)] with x h1 h2 h3 h4
        rw [h1, h4, Pi.smul_apply, h2]
        simp only [Pi.mul_apply, h3, Pi.smul_apply, smul_mul_assoc]))
      (fun f g₁ g₂ => Lp.ext (by
        filter_upwards [hmulF_coeFn (r := r) f (g₁ + g₂), hmulF_coeFn (r := r) f g₁,
          hmulF_coeFn (r := r) f g₂, Lp.coeFn_add g₁ g₂,
          Lp.coeFn_add (hmulF p q r f g₁) (hmulF p q r f g₂)] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3]
        simp only [Pi.mul_apply, h4, Pi.add_apply, mul_add]))
      (fun c f g => Lp.ext (by
        filter_upwards [hmulF_coeFn (r := r) f (c • g), hmulF_coeFn (r := r) f g,
          Lp.coeFn_smul c g, Lp.coeFn_smul c (hmulF p q r f g)] with x h1 h2 h3 h4
        rw [h1, h4, Pi.smul_apply, h2]
        simp only [Pi.mul_apply, h3, Pi.smul_apply, mul_smul_comm])))
    1 (fun f g => by
      rw [one_mul]
      exact hmulF_norm f g)

theorem hmulL_apply (f : Lp ℂ p μ) (g : Lp ℂ q μ) : hmulL p q r f g = hmulF p q r f g := rfl

end Holder

section Conj

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Complex conjugation on `Lᵖ`. -/
def cjF (p : ℝ≥0∞) (f : Lp ℂ p μ) : Lp ℂ p μ :=
  (memLp_conj_fun (Lp.memLp f)).toLp fun x => conj (f x)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
theorem cjF_coeFn (f : Lp ℂ p μ) : (cjF p f : α → ℂ) =ᵐ[μ] fun x => conj (f x) :=
  MemLp.coeFn_toLp _

omit [Fact (1 ≤ p)] in
theorem cjF_norm (f : Lp ℂ p μ) : ‖cjF p f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (cjF_coeFn f)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono_ae
    (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
    (Eventually.of_forall fun x => le_of_eq (Complex.norm_conj _)))

/-- Complex conjugation as a real continuous linear map. -/
def cjL (p : ℝ≥0∞) [Fact (1 ≤ p)] : Lp ℂ p μ →L[ℝ] Lp ℂ p μ :=
  LinearMap.mkContinuous
    { toFun := cjF p
      map_add' := fun f g => Lp.ext (by
        filter_upwards [cjF_coeFn (f + g), cjF_coeFn f, cjF_coeFn g, Lp.coeFn_add f g,
          Lp.coeFn_add (cjF p f) (cjF p g)] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3, h4, Pi.add_apply, map_add])
      map_smul' := fun c f => Lp.ext (by
        filter_upwards [cjF_coeFn (c • f), cjF_coeFn f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (cjF p f)] with x h1 h2 h3 h4
        rw [RingHom.id_apply, h1, h4, h3]
        simp only [Pi.smul_apply, h2, Complex.real_smul, map_mul, Complex.conj_ofReal]) }
    1 (fun f => by rw [one_mul]; exact cjF_norm f)

theorem cjL_apply (f : Lp ℂ p μ) : cjL p f = cjF p f := rfl

end Conj

/-! ### The cubic -/

attribute [local instance] isProbabilityMeasure_spatialMeasure

theorem Ncub_eq (δ : ℝ) (f : Lp ℂ 4 (slabMeasure δ)) :
    Ncub δ f = (2 : ℝ) • hmulL 2 4 (4 / 3) (hmulL 4 4 2 f (cjL 4 f)) f := by
  refine Lp.ext ?_
  filter_upwards [Ncub_coeFn f, Lp.coeFn_smul (2 : ℝ) (hmulL 2 4 (4 / 3) (hmulL 4 4 2 f (cjL 4 f)) f),
    hmulF_coeFn (r := 4 / 3) (hmulL 4 4 2 f (cjL 4 f)) f, hmulF_coeFn (r := 2) f (cjL 4 f),
    cjF_coeFn (p := 4) f] with x h1 h2 h3 h4 h5
  rw [h1, h2, Pi.smul_apply, hmulL_apply, h3, Pi.mul_apply, hmulL_apply, h4, Pi.mul_apply,
    cjL_apply, h5]
  simp only [cubF, cubicNL]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.real_smul]
  push_cast
  ring

theorem analyticOnNhd_Ncub (δ : ℝ) : AnalyticOnNhd ℝ (Ncub δ) Set.univ := by
  intro f₀ _
  set B1 := (hmulL 4 4 2 : Lp ℂ 4 (slabMeasure δ) →L[ℝ] Lp ℂ 4 (slabMeasure δ) →L[ℝ]
    Lp ℂ 2 (slabMeasure δ))
  set B2 := (hmulL 2 4 (4 / 3) : Lp ℂ 2 (slabMeasure δ) →L[ℝ] Lp ℂ 4 (slabMeasure δ) →L[ℝ]
    Lp ℂ (4 / 3) (slabMeasure δ))
  set C := (cjL 4 : Lp ℂ 4 (slabMeasure δ) →L[ℝ] Lp ℂ 4 (slabMeasure δ))
  have e : Ncub δ = fun f => (2 : ℝ) • B2 (B1 f (C f)) f := funext (Ncub_eq δ)
  rw [e]
  have h1 : AnalyticAt ℝ (fun f => B1 f (C f)) f₀ :=
    AnalyticAt.comp (g := fun x : Lp ℂ 4 (slabMeasure δ) × Lp ℂ 4 (slabMeasure δ) => B1 x.1 x.2)
      (f := fun f => (f, C f)) (x := f₀) (B1.analyticAt_bilinear _)
      (analyticAt_id.prod (C.analyticAt f₀))
  have h2 : AnalyticAt ℝ (fun f => B2 (B1 f (C f)) f) f₀ :=
    AnalyticAt.comp (g := fun x : Lp ℂ 2 (slabMeasure δ) × Lp ℂ 4 (slabMeasure δ) => B2 x.1 x.2)
      (f := fun f => (B1 f (C f), f)) (x := f₀) (B2.analyticAt_bilinear _) (h1.prod analyticAt_id)
  exact AnalyticAt.comp (g := ((2 : ℝ) • ContinuousLinearMap.id ℝ (Lp ℂ (4 / 3) (slabMeasure δ))))
    (f := fun f => B2 (B1 f (C f)) f) (x := f₀) (ContinuousLinearMap.analyticAt _ _) h2

end LiebLiniger.FixedPeriod.ALLS.PdeB
