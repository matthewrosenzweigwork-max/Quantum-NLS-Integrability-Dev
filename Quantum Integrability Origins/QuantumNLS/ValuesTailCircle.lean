import Mathlib

/-!
# R-CB4CC6EE (`values:lem:tail`), B1: circle representation of the Cauchy-power kernel and the Born bias

Generic support module (imports Mathlib only). With `c = R i`, radius `r = R/2`, and
`kern c k t = (c - t)^{-(k+1)}` for real `t`, Cauchy's formula gives (`t` outside the closed disk, since `Im c = R > r`)

  `kern c k t = (2πi)^{-1} (-1)^k ∮_{|z-c|=r} (z-c)^{-(k+1)} (z-t)^{-1} dz`.

Averaging over a countable index `a` (probability weights `β`, probability laws `ρ a` on `ℝ`), Fubini on
`ρ a × dθ` and on `β × dθ` gives, with the Born-averaged Cauchy transform `H(z) = ∫ cauchy (ρ a) z dβ(a)`,

  `∫ a, ∫ t, kern c k t ∂(ρ a) ∂β = (2πi)^{-1} (-1)^k ∫_{θ∈(0,2π]} deriv(circleMap) θ · ((z-c)^{-(k+1)} H(z))|_{z = circleMap θ} dθ`.

If `|H(z) - cauchy μ z| ≤ B/(Im z)^2` on `Im z ≥ R/2`, then
`|∫ a, ∫ t, kern c k t ∂(ρ a) ∂β - ∫ t, kern c k t ∂μ| ≤ 2^{k+2} B / R^{k+2}`.

Nothing here uses hypotheses beyond the printed data; no analysis beyond Mathlib's Cauchy formula
`DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul` and Fubini. Nothing here is accepted.
-/

namespace QuantumNLS.ValuesTailCircle

open MeasureTheory Complex Metric Set Filter Topology

noncomputable section

/-- Cauchy transform of a measure on `ℝ` (same convention as `CauchyUniqueness.cauchyTransform`). -/
def cauchy (ρ : Measure ℝ) (z : ℂ) : ℂ := ∫ t : ℝ, (z - (t : ℂ))⁻¹ ∂ρ

/-- The kernel `(c - t)^{-(k+1)}` at a real point `t`. -/
def kern (c : ℂ) (k : ℕ) (t : ℝ) : ℂ := ((c - (t : ℂ)) ^ (k + 1))⁻¹

/-- `(z - c)^{-(k+1)}`. -/
def gf (c : ℂ) (k : ℕ) (z : ℂ) : ℂ := 1 / (z - c) ^ (k + 1)

/-- The circle integrand at real `t` and parameter `θ`, for the circle `C(c, r)`. -/
def Psi (c : ℂ) (r : ℝ) (k : ℕ) (t : ℝ) (θ : ℝ) : ℂ :=
  deriv (circleMap c r) θ * (gf c k (circleMap c r θ) * (circleMap c r θ - (t : ℂ))⁻¹)

/-- The parameter interval measure `dθ` on `(0, 2π]`. -/
abbrev nu : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))

instance nu_finite : IsFiniteMeasure nu :=
  ⟨by rw [nu, Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩

lemma circleIntegral_eq_Ioc (f : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    circleIntegral f c r = ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), deriv (circleMap c r) θ * f (circleMap c r θ) := by
  unfold circleIntegral
  rw [intervalIntegral.integral_of_le (by positivity)]
  simp only [smul_eq_mul]

lemma iter_inv_formula (t : ℂ) (k : ℕ) (z : ℂ) (hz : z ≠ t) :
    iteratedDeriv k (fun w : ℂ => (w - t)⁻¹) z =
      ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ((z - t) ^ (k + 1))⁻¹ := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (fun w : ℂ => (w - t)⁻¹) =ᶠ[𝓝 z]
        fun w => ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ((w - t) ^ (k + 1))⁻¹ := by
      have hopen : {w : ℂ | w ≠ t} ∈ 𝓝 z := isOpen_ne.mem_nhds hz
      filter_upwards [hopen] with w hw
      exact ih w hw
    rw [hev.deriv_eq]
    have hne : z - t ≠ 0 := sub_ne_zero.2 hz
    have h1 : HasDerivAt (fun w : ℂ => (w - t) ^ (k + 1)) (((k + 1 : ℕ) : ℂ) * (z - t) ^ k) z := by
      have := (hasDerivAt_pow (k + 1) (z - t)).comp_sub_const z t
      simpa using this
    have h2 := (h1.inv (pow_ne_zero _ hne)).const_mul ((-1 : ℂ) ^ k * (k.factorial : ℂ))
    refine h2.deriv.trans ?_
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- Cauchy's formula for the kernel at a point outside the closed disk. -/
lemma circle_kernel (c : ℂ) {r : ℝ} (hr : 0 < r) {t : ℂ} (ht : t ∉ closedBall c r) (k : ℕ) :
    circleIntegral (fun z : ℂ => gf c k z * (z - t)⁻¹) c r =
      (2 * Real.pi * I) * ((-1 : ℂ) ^ k) * ((c - t) ^ (k + 1))⁻¹ := by
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => (w - t)⁻¹) (closedBall c r) := by
    intro w hw
    have hwt : w - t ≠ 0 := sub_ne_zero.2 (fun h => ht (h ▸ hw))
    exact ((differentiableAt_id.sub_const t).inv hwt).differentiableWithinAt
  have hct : c ≠ t := fun h => ht (h ▸ mem_closedBall_self hr.le)
  have key := DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul hr k hdiff
  rw [iter_inv_formula t k c hct] at key
  have hfact : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  have hgf : (fun z : ℂ => gf c k z * (z - t)⁻¹) =
      fun z => (1 / (z - c) ^ (k + 1)) • (fun w : ℂ => (w - t)⁻¹) z := by
    funext z
    simp [gf, smul_eq_mul]
  rw [hgf, key]
  simp only [smul_eq_mul]
  field_simp

lemma circleMap_im_ge (R : ℝ) (hR : 0 < R) (θ : ℝ) :
    R / 2 ≤ (circleMap ((R : ℂ) * I) (R / 2) θ).im := by
  have h1 : circleMap ((R : ℂ) * I) (R / 2) θ - (R : ℂ) * I = circleMap 0 (R / 2) θ :=
    circleMap_sub_center _ _ _
  have h2 : |(circleMap 0 (R / 2) θ).im| ≤ R / 2 := by
    have := Complex.abs_im_le_norm (circleMap 0 (R / 2) θ)
    rw [norm_circleMap_zero, abs_of_pos (show (0 : ℝ) < R / 2 by linarith)] at this
    exact this
  have h3 := congrArg Complex.im h1
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_add, add_zero, sub_zero] at h3
  have h4 := abs_le.1 h2
  linarith [h4.1, h4.2]

lemma real_not_mem_closedBall (R : ℝ) (hR : 0 < R) (t : ℝ) :
    (t : ℂ) ∉ closedBall ((R : ℂ) * I) (R / 2) := by
  intro h
  rw [mem_closedBall, dist_eq_norm] at h
  have h1 := Complex.abs_im_le_norm ((t : ℂ) - (R : ℂ) * I)
  have h2 : ((t : ℂ) - (R : ℂ) * I).im = -R := by simp
  rw [h2, abs_neg, abs_of_pos hR] at h1
  linarith

lemma inv_norm_le (R : ℝ) (hR : 0 < R) (z : ℂ) (hz : R / 2 ≤ z.im) (t : ℝ) :
    ‖(z - (t : ℂ))⁻¹‖ ≤ (R / 2)⁻¹ := by
  have hle : R / 2 ≤ ‖z - (t : ℂ)‖ := by
    have h1 := Complex.abs_im_le_norm (z - (t : ℂ))
    have h2 : (z - (t : ℂ)).im = z.im := by simp
    rw [h2] at h1
    linarith [le_abs_self z.im]
  rw [norm_inv]
  exact inv_anti₀ (by linarith) hle

lemma cauchy_norm_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (R : ℝ) (hR : 0 < R) (z : ℂ)
    (hz : R / 2 ≤ z.im) : ‖cauchy ρ z‖ ≤ (R / 2)⁻¹ := by
  unfold cauchy
  have := norm_integral_le_of_norm_le_const (μ := ρ) (f := fun t : ℝ => (z - (t : ℂ))⁻¹) (C := (R / 2)⁻¹)
    (ae_of_all _ (fun t => inv_norm_le R hR z hz t))
  simpa using this

/-- The uniform bound `M(R,k) = r · r^{-(k+1)} · r^{-1}` with `r = R/2`. -/
def Mbd (R : ℝ) (k : ℕ) : ℝ := (R / 2) * ((R / 2) ^ (k + 1))⁻¹ * (R / 2)⁻¹

lemma deriv_norm (R : ℝ) (hR : 0 < R) (θ : ℝ) :
    ‖deriv (circleMap ((R : ℂ) * I) (R / 2)) θ‖ = R / 2 := by
  rw [deriv_circleMap, norm_mul, norm_circleMap_zero, norm_I, mul_one, abs_of_pos (show (0 : ℝ) < R / 2 by linarith)]

lemma gf_norm (R : ℝ) (hR : 0 < R) (k : ℕ) (θ : ℝ) :
    ‖gf ((R : ℂ) * I) k (circleMap ((R : ℂ) * I) (R / 2) θ)‖ = ((R / 2) ^ (k + 1))⁻¹ := by
  unfold gf
  rw [norm_div, norm_one, norm_pow, circleMap_sub_center, norm_circleMap_zero,
    abs_of_pos (by linarith : (0 : ℝ) < R / 2), one_div]

lemma Psi_norm_le (R : ℝ) (hR : 0 < R) (k : ℕ) (t : ℝ) (θ : ℝ) :
    ‖Psi ((R : ℂ) * I) (R / 2) k t θ‖ ≤ Mbd R k := by
  unfold Psi Mbd
  have hz := inv_norm_le R hR (circleMap ((R : ℂ) * I) (R / 2) θ) (circleMap_im_ge R hR θ) t
  rw [norm_mul, norm_mul, deriv_norm R hR, gf_norm R hR k]
  rw [mul_assoc (R / 2)]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hz (inv_nonneg.2 (pow_nonneg (by linarith) _))) (by linarith)

lemma cauchy_measurable (ρ : Measure ℝ) [IsFiniteMeasure ρ] : Measurable (cauchy ρ) := by
  have hf : StronglyMeasurable (fun p : ℂ × ℝ => (p.1 - (p.2 : ℂ))⁻¹) :=
    (by fun_prop : Measurable (fun p : ℂ × ℝ => (p.1 - (p.2 : ℂ))⁻¹)).stronglyMeasurable
  exact (hf.integral_prod_right' (ν := ρ)).measurable

lemma Psi_measurable (R : ℝ) (k : ℕ) :
    Measurable (fun p : ℝ × ℝ => Psi ((R : ℂ) * I) (R / 2) k p.1 p.2) := by
  unfold Psi gf
  simp only [deriv_circleMap]
  have hc : Continuous (fun θ : ℝ => circleMap ((R : ℂ) * I) (R / 2) θ) := continuous_circleMap _ _
  have hc0 : Continuous (fun θ : ℝ => circleMap 0 (R / 2) θ) := continuous_circleMap _ _
  fun_prop

lemma Psi_integrable (R : ℝ) (hR : 0 < R) (k : ℕ) (ν' : Measure ℝ) [IsFiniteMeasure ν'] :
    Integrable (fun p : ℝ × ℝ => Psi ((R : ℂ) * I) (R / 2) k p.1 p.2) (ν'.prod nu) :=
  Integrable.mono' (integrable_const (Mbd R k)) (Psi_measurable R k).aestronglyMeasurable
    (ae_of_all _ (fun p => Psi_norm_le R hR k p.1 p.2))

/-- The Born-averaged parameter integrand `F a θ = deriv · (gf · cauchy (ρ a))` at `z = circleMap θ`. -/
def Fa {α : Type*} (ρ : α → Measure ℝ) (R : ℝ) (k : ℕ) (a : α) (θ : ℝ) : ℂ :=
  deriv (circleMap ((R : ℂ) * I) (R / 2)) θ *
    (gf ((R : ℂ) * I) k (circleMap ((R : ℂ) * I) (R / 2) θ) *
      cauchy (ρ a) (circleMap ((R : ℂ) * I) (R / 2) θ))

lemma Fa_integrable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (β : Measure α) [IsProbabilityMeasure β] (ρ : α → Measure ℝ) [∀ a, IsProbabilityMeasure (ρ a)]
    {R : ℝ} (hR : 0 < R) (k : ℕ) :
    Integrable (fun p : α × ℝ => Fa ρ R k p.1 p.2) (β.prod nu) := by
  have hmeas : Measurable (fun p : α × ℝ => Fa ρ R k p.1 p.2) := by
    have h' : Measurable (fun q : ℝ × α => Fa ρ R k q.2 q.1) := by
      apply measurable_from_prod_countable_left
      intro a
      unfold Fa gf
      simp only [deriv_circleMap]
      have hcont : Measurable (fun θ : ℝ => cauchy (ρ a) (circleMap ((R : ℂ) * I) (R / 2) θ)) :=
        (cauchy_measurable (ρ a)).comp (continuous_circleMap _ _).measurable
      have hc : Measurable (fun θ : ℝ => circleMap ((R : ℂ) * I) (R / 2) θ) :=
        (continuous_circleMap _ _).measurable
      fun_prop
    exact h'.comp measurable_swap
  refine Integrable.mono' (integrable_const (Mbd R k)) hmeas.aestronglyMeasurable
    (ae_of_all _ (fun p => ?_))
  unfold Fa
  rw [norm_mul, norm_mul, deriv_norm R hR, gf_norm R hR k]
  have hz := cauchy_norm_le (ρ p.1) R hR (circleMap ((R : ℂ) * I) (R / 2) p.2)
    (circleMap_im_ge R hR p.2)
  unfold Mbd
  rw [mul_assoc (R / 2)]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hz (inv_nonneg.2 (pow_nonneg (by linarith) _))) (by linarith)

lemma kern_eq (R : ℝ) (hR : 0 < R) (k : ℕ) (t : ℝ) :
    kern ((R : ℂ) * I) k t = (2 * Real.pi * I)⁻¹ * (-1 : ℂ) ^ k *
      ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), Psi ((R : ℂ) * I) (R / 2) k t θ := by
  have h := circle_kernel ((R : ℂ) * I) (r := R / 2) (by linarith) (real_not_mem_closedBall R hR t) k
  rw [circleIntegral_eq_Ioc] at h
  have h2 : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), Psi ((R : ℂ) * I) (R / 2) k t θ =
      (2 * Real.pi * I) * ((-1 : ℂ) ^ k) * kern ((R : ℂ) * I) k t := h
  rw [h2]
  have hs : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; norm_num
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2pi : (2 * Real.pi * I : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hpi) I_ne_zero
  have key : (2 * Real.pi * I)⁻¹ * (-1 : ℂ) ^ k * ((2 * Real.pi * I) * (-1 : ℂ) ^ k * kern ((R : ℂ) * I) k t)
      = ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * kern ((R : ℂ) * I) k t * ((2 * Real.pi * I)⁻¹ * (2 * Real.pi * I)) := by
    ring
  rw [key, hs, inv_mul_cancel₀ h2pi, one_mul, mul_one]

lemma Fa_integral {α : Type*} [MeasurableSpace α] (β : Measure α) (ρ : α → Measure ℝ) (R : ℝ) (k : ℕ) (θ : ℝ) :
    (∫ a, Fa ρ R k a θ ∂β) = deriv (circleMap ((R : ℂ) * I) (R / 2)) θ *
      (gf ((R : ℂ) * I) k (circleMap ((R : ℂ) * I) (R / 2) θ) *
        ∫ a, cauchy (ρ a) (circleMap ((R : ℂ) * I) (R / 2) θ) ∂β) := by
  unfold Fa
  rw [integral_const_mul, integral_const_mul]

/-- **Born identity.** For a countable index with probability weights `β` and laws `ρ a`. -/
theorem born_identity {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (β : Measure α) [IsProbabilityMeasure β] (ρ : α → Measure ℝ) [∀ a, IsProbabilityMeasure (ρ a)]
    {R : ℝ} (hR : 0 < R) (k : ℕ) :
    (∫ a, (∫ t : ℝ, kern ((R : ℂ) * I) k t ∂(ρ a)) ∂β) =
      (2 * Real.pi * I)⁻¹ * (-1 : ℂ) ^ k *
        ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ∫ a, Fa ρ R k a θ ∂β := by
  have hA : ∀ a, (∫ t : ℝ, kern ((R : ℂ) * I) k t ∂(ρ a)) =
      (2 * Real.pi * I)⁻¹ * (-1 : ℂ) ^ k * ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), Fa ρ R k a θ := by
    intro a
    calc (∫ t : ℝ, kern ((R : ℂ) * I) k t ∂(ρ a))
        = ∫ t : ℝ, ((2 * Real.pi * I)⁻¹ * (-1 : ℂ) ^ k *
            ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), Psi ((R : ℂ) * I) (R / 2) k t θ) ∂(ρ a) :=
          integral_congr_ae (ae_of_all _ (fun t => kern_eq R hR k t))
      _ = (2 * Real.pi * I)⁻¹ * (-1 : ℂ) ^ k *
            ∫ t : ℝ, (∫ θ in Ioc (0 : ℝ) (2 * Real.pi), Psi ((R : ℂ) * I) (R / 2) k t θ) ∂(ρ a) :=
          integral_const_mul _ _
      _ = (2 * Real.pi * I)⁻¹ * (-1 : ℂ) ^ k *
            ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ∫ t : ℝ, Psi ((R : ℂ) * I) (R / 2) k t θ ∂(ρ a) := by
          congr 1
          exact integral_integral_swap (f := fun t θ => Psi ((R : ℂ) * I) (R / 2) k t θ)
            (Psi_integrable R hR k (ρ a))
      _ = (2 * Real.pi * I)⁻¹ * (-1 : ℂ) ^ k *
            ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), Fa ρ R k a θ := by
          congr 1
          refine integral_congr_ae (ae_of_all _ (fun θ => ?_))
          unfold Psi Fa cauchy
          dsimp only
          rw [integral_const_mul, integral_const_mul]
  calc (∫ a, (∫ t : ℝ, kern ((R : ℂ) * I) k t ∂(ρ a)) ∂β)
      = ∫ a, ((2 * Real.pi * I)⁻¹ * (-1 : ℂ) ^ k *
          ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), Fa ρ R k a θ) ∂β :=
        integral_congr_ae (ae_of_all _ hA)
    _ = (2 * Real.pi * I)⁻¹ * (-1 : ℂ) ^ k *
          ∫ a, (∫ θ in Ioc (0 : ℝ) (2 * Real.pi), Fa ρ R k a θ) ∂β := integral_const_mul _ _
    _ = (2 * Real.pi * I)⁻¹ * (-1 : ℂ) ^ k *
          ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ∫ a, Fa ρ R k a θ ∂β := by
        congr 1
        exact integral_integral_swap (f := fun a θ => Fa ρ R k a θ) (Fa_integrable β ρ hR k)

/-- **Born bias bound.** If `|H(z) - cauchy μ z| ≤ B/(Im z)^2` on `Im z ≥ R/2`, then the kernel bias is
`≤ 2^{k+2} B / R^{k+2}`. -/
theorem born_bias {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (β : Measure α) [IsProbabilityMeasure β] (ρ : α → Measure ℝ) [∀ a, IsProbabilityMeasure (ρ a)]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B) (k : ℕ)
    (hD : ∀ z : ℂ, R / 2 ≤ z.im → ‖(∫ a, cauchy (ρ a) z ∂β) - cauchy μ z‖ ≤ B / z.im ^ 2) :
    ‖(∫ a, (∫ t : ℝ, kern ((R : ℂ) * I) k t ∂(ρ a)) ∂β) - ∫ t : ℝ, kern ((R : ℂ) * I) k t ∂μ‖ ≤
      2 ^ (k + 2) * B / R ^ (k + 2) := by
  have hL := born_identity β ρ hR k
  have hμ := born_identity (Measure.dirac ()) (fun _ : Unit => μ) hR k
  have hμL : (∫ a : Unit, (∫ t : ℝ, kern ((R : ℂ) * I) k t ∂μ) ∂(Measure.dirac ())) =
      ∫ t : ℝ, kern ((R : ℂ) * I) k t ∂μ := by simp
  rw [hμL] at hμ
  have hint1 : Integrable (fun θ : ℝ => ∫ a, Fa ρ R k a θ ∂β) nu :=
    (Fa_integrable β ρ hR k).integral_prod_right
  have hint2 : Integrable (fun θ : ℝ => ∫ u : Unit, Fa (fun _ : Unit => μ) R k u θ ∂(Measure.dirac ())) nu :=
    (Fa_integrable (Measure.dirac ()) (fun _ : Unit => μ) hR k).integral_prod_right
  have hfin : (∫ a, (∫ t : ℝ, kern ((R : ℂ) * I) k t ∂(ρ a)) ∂β) - ∫ t : ℝ, kern ((R : ℂ) * I) k t ∂μ =
      (2 * Real.pi * I)⁻¹ * (-1 : ℂ) ^ k *
        ∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
          ((∫ a, Fa ρ R k a θ ∂β) - ∫ u : Unit, Fa (fun _ : Unit => μ) R k u θ ∂(Measure.dirac ())) := by
    rw [hL, hμ, integral_sub hint1 hint2, mul_sub]
  have hpt : ∀ θ : ℝ, ‖(∫ a, Fa ρ R k a θ ∂β) -
      ∫ u : Unit, Fa (fun _ : Unit => μ) R k u θ ∂(Measure.dirac ())‖ ≤
        (R / 2) * ((R / 2) ^ (k + 1))⁻¹ * (B / (R / 2) ^ 2) := by
    intro θ
    have e1 := Fa_integral β ρ R k θ
    have e2 : (∫ u : Unit, Fa (fun _ : Unit => μ) R k u θ ∂(Measure.dirac ())) =
        deriv (circleMap ((R : ℂ) * I) (R / 2)) θ *
          (gf ((R : ℂ) * I) k (circleMap ((R : ℂ) * I) (R / 2) θ) *
            cauchy μ (circleMap ((R : ℂ) * I) (R / 2) θ)) := by
      simp [Fa]
    have e3 : (∫ a, Fa ρ R k a θ ∂β) -
        (∫ u : Unit, Fa (fun _ : Unit => μ) R k u θ ∂(Measure.dirac ())) =
        deriv (circleMap ((R : ℂ) * I) (R / 2)) θ *
          (gf ((R : ℂ) * I) k (circleMap ((R : ℂ) * I) (R / 2) θ) *
            ((∫ a, cauchy (ρ a) (circleMap ((R : ℂ) * I) (R / 2) θ) ∂β) -
              cauchy μ (circleMap ((R : ℂ) * I) (R / 2) θ))) := by
      rw [e1, e2]
      ring
    rw [e3, norm_mul, norm_mul, deriv_norm R hR, gf_norm R hR k]
    have hD' := hD _ (circleMap_im_ge R hR θ)
    have hle : B / (circleMap ((R : ℂ) * I) (R / 2) θ).im ^ 2 ≤ B / (R / 2) ^ 2 :=
      div_le_div_of_nonneg_left hB (by positivity)
        (pow_le_pow_left₀ (by linarith) (circleMap_im_ge R hR θ) 2)
    rw [mul_assoc]
    have hr0 : (0 : ℝ) ≤ R / 2 := by linarith
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hD'.trans hle) (inv_nonneg.2 (pow_nonneg hr0 (k + 1)))) hr0
  have hνr : nu.real Set.univ = 2 * Real.pi := by
    simp only [Measure.real, nu, Measure.restrict_apply_univ, Real.volume_Ioc]
    rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hbd := norm_integral_le_of_norm_le_const (μ := nu)
    (f := fun θ : ℝ => (∫ a, Fa ρ R k a θ ∂β) -
      ∫ u : Unit, Fa (fun _ : Unit => μ) R k u θ ∂(Measure.dirac ()))
    (C := (R / 2) * ((R / 2) ^ (k + 1))⁻¹ * (B / (R / 2) ^ 2)) (ae_of_all _ hpt)
  rw [hνr] at hbd
  have hκ : ‖(2 * Real.pi * I)⁻¹ * (-1 : ℂ) ^ k‖ = (2 * Real.pi)⁻¹ := by
    simp [norm_mul, norm_inv, Real.pi_pos.le, abs_of_pos Real.pi_pos]
  rw [hfin, norm_mul, hκ]
  have hR0 : R ≠ 0 := hR.ne'
  have hpi0 : Real.pi ≠ 0 := Real.pi_pos.ne'
  have gen : ∀ s : ℝ, s ≠ 0 → s * (s ^ (k + 1))⁻¹ * (B / s ^ 2) = B / s ^ (k + 2) := by
    intro s hs
    field_simp
    ring
  have hR2 : R / 2 ≠ 0 := (div_pos hR two_pos).ne'
  calc (2 * Real.pi)⁻¹ * ‖∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
          ((∫ a, Fa ρ R k a θ ∂β) - ∫ u : Unit, Fa (fun _ : Unit => μ) R k u θ ∂(Measure.dirac ()))‖
      ≤ (2 * Real.pi)⁻¹ * (((R / 2) * ((R / 2) ^ (k + 1))⁻¹ * (B / (R / 2) ^ 2)) * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = (2 * Real.pi)⁻¹ * (B / (R / 2) ^ (k + 2) * (2 * Real.pi)) := by
        rw [gen (R / 2) hR2]
    _ = B / (R / 2) ^ (k + 2) := by
        field_simp
    _ = 2 ^ (k + 2) * B / R ^ (k + 2) := by
        rw [div_pow, div_div_eq_mul_div]
        ring

end

#print axioms QuantumNLS.ValuesTailCircle.circle_kernel
#print axioms QuantumNLS.ValuesTailCircle.born_identity
#print axioms QuantumNLS.ValuesTailCircle.born_bias

end QuantumNLS.ValuesTailCircle
