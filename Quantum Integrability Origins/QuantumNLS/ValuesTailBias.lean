import Mathlib
import QuantumNLS.ValuesConcentration
import QuantumNLS.ValuesTailCircle
import QuantumNLS.ValuesTailPartialFraction
import QuantumNLS.ValuesTailMarkov

/-!
# R-CB4CC6EE (`values:lem:tail`), B3: the Born-averaged filter bias

Step B3 of the barycentric tail lemma `values:lem:tail`. With the printed rational filter
`F_{p,R}(t) = (t^2/(t^2+R^2))^p` (`ValuesTailMarkov.filterF`), the partial-fraction representation
`ValuesTailPartialFraction.pf_transport` and the Born-kernel bias bound `ValuesTailCircle.born_bias`,
the Born average of the empirical measures satisfies, for `R ≥ 2 η₀`, `η₀ = max (4κ) (log 16 / L)`,

  `| E ∫ F_{p,R} dL_N - ∫ F_{p,R} dμ | ≤ D / (N R)`,

with `D` depending only on `p, κ, L` (not on `N`, `R`, the unit profile `u`, or `μ`).

Ingredients: `ValuesConcentration.values_concentration` (part 2, bias on `Im z ≥ η₀`, accepted read-only),
the frozen partial fractions and the frozen Cauchy-kernel bias. Only the sign convention
`(R (t - R i)^{-1})^{a+1} = (-R)^{a+1} (R i - t)^{-(a+1)}` and the conjugation
`kern (-R i) = conj (kern (R i))` for real `t` are used. Nothing here is accepted; review pending.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Complex ComplexConjugate
open QuantumNLS.ValuesTailCircle
open QuantumNLS.ValuesTailMarkov (filterF)

namespace QuantumNLS.ValuesTailBias

section Generic

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [DiscreteMeasurableSpace α]

/-- The lower-centre kernel is the conjugate of the upper-centre kernel at real `t`. -/
lemma kern_neg_conj (R : ℝ) (k : ℕ) (t : ℝ) :
    kern (-((R : ℂ) * Complex.I)) k t = conj (kern ((R : ℂ) * Complex.I) k t) := by
  have h : conj ((R : ℂ) * Complex.I - (t : ℂ)) = -((R : ℂ) * Complex.I) - (t : ℂ) := by
    simp only [map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  unfold kern
  rw [map_inv₀, map_pow, h]

lemma norm_sub_ge {c : ℂ} {R : ℝ} (him : |c.im| = R) (t : ℝ) : R ≤ ‖c - (t : ℂ)‖ := by
  have h1 := Complex.abs_im_le_norm (c - (t : ℂ))
  have h2 : (c - (t : ℂ)).im = c.im := by simp
  rw [h2, him] at h1
  exact h1

lemma kern_norm_le {c : ℂ} {R : ℝ} (hR : 0 < R) (him : |c.im| = R) (k : ℕ) (t : ℝ) :
    ‖kern c k t‖ ≤ (R ^ (k + 1))⁻¹ := by
  have hpow : R ^ (k + 1) ≤ ‖c - (t : ℂ)‖ ^ (k + 1) :=
    pow_le_pow_left₀ hR.le (norm_sub_ge him t) (k + 1)
  unfold kern
  rw [norm_inv, norm_pow]
  exact inv_anti₀ (pow_pos hR _) hpow

lemma kern_integrable {c : ℂ} {R : ℝ} (hR : 0 < R) (him : |c.im| = R) (k : ℕ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] : Integrable (fun t : ℝ => kern c k t) ν := by
  have hne : ∀ t : ℝ, c - (t : ℂ) ≠ 0 := by
    intro t h
    have h1 := norm_sub_ge him t
    rw [h, norm_zero] at h1
    linarith
  have hcont : Continuous (fun t : ℝ => kern c k t) := by
    unfold kern
    exact ((continuous_const.sub Complex.continuous_ofReal).pow (k + 1)).inv₀
      (fun t => pow_ne_zero _ (hne t))
  exact Integrable.of_bound (C := (R ^ (k + 1))⁻¹) hcont.aestronglyMeasurable
    (ae_of_all _ (fun t => kern_norm_le hR him k t))

lemma integral_kern_norm_le {c : ℂ} {R : ℝ} (hR : 0 < R) (him : |c.im| = R) (k : ℕ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ‖∫ t : ℝ, kern c k t ∂ν‖ ≤ (R ^ (k + 1))⁻¹ := by
  have h := norm_integral_le_of_norm_le_const (μ := ν) (f := fun t : ℝ => kern c k t)
    (C := (R ^ (k + 1))⁻¹) (ae_of_all _ (fun t => kern_norm_le hR him k t))
  simpa using h

lemma integrable_of_bdd {M : ℝ} (β : Measure α) [IsFiniteMeasure β] (g : α → ℂ)
    (hg : ∀ a, ‖g a‖ ≤ M) : Integrable g β :=
  Integrable.of_bound (C := M) Measurable.of_discrete.aestronglyMeasurable (ae_of_all _ hg)

/-- Integral of `1 + Σ_c w_c (cα_c g⁺_c + cβ_c g⁻_c)` over a probability measure. -/
lemma integral_sum_form {γ : Type*} [MeasurableSpace γ] (ν : Measure γ) [IsProbabilityMeasure ν]
    (p : ℕ) (w cα cβ : ℕ → ℂ) (gp gm : ℕ → γ → ℂ)
    (hgp : ∀ c, Integrable (gp c) ν) (hgm : ∀ c, Integrable (gm c) ν) :
    ∫ x, (1 + ∑ c ∈ Finset.range p, w c * (cα c * gp c x + cβ c * gm c x)) ∂ν =
      1 + ∑ c ∈ Finset.range p, w c * (cα c * ∫ x, gp c x ∂ν + cβ c * ∫ x, gm c x ∂ν) := by
  have hterm : ∀ c ∈ Finset.range p,
      Integrable (fun x => w c * (cα c * gp c x + cβ c * gm c x)) ν :=
    fun c _ => (((hgp c).const_mul (cα c)).add ((hgm c).const_mul (cβ c))).const_mul (w c)
  have hS : Integrable (fun x => ∑ c ∈ Finset.range p, w c * (cα c * gp c x + cβ c * gm c x)) ν :=
    integrable_finsetSum _ hterm
  rw [integral_add (integrable_const _) hS, integral_const, integral_finsetSum _ hterm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [integral_const_mul, integral_add ((hgp c).const_mul (cα c)) ((hgm c).const_mul (cβ c)),
      integral_const_mul, integral_const_mul]

/-- The Markov filter as a combination of the two Cauchy-type kernels (scale `R`, real `t`). -/
lemma pf_kernel_form {R : ℝ} (p : ℕ) (cα cβ : ℕ → ℂ)
    (hpf : ∀ t : ℝ, ((t ^ 2 / (t ^ 2 + R ^ 2) : ℝ) : ℂ) ^ p - 1 =
      ∑ a ∈ Finset.range p, (cα a * ((R : ℂ) * ((t : ℂ) - (R : ℂ) * Complex.I)⁻¹) ^ (a + 1) +
        cβ a * ((R : ℂ) * ((t : ℂ) + (R : ℂ) * Complex.I)⁻¹) ^ (a + 1)))
    (t : ℝ) :
    ((t ^ 2 / (t ^ 2 + R ^ 2) : ℝ) : ℂ) ^ p =
      1 + ∑ a ∈ Finset.range p, (-(R : ℂ)) ^ (a + 1) *
        (cα a * kern ((R : ℂ) * Complex.I) a t + cβ a * kern (-((R : ℂ) * Complex.I)) a t) := by
  have e1 : ∀ a : ℕ, ((R : ℂ) * ((t : ℂ) - (R : ℂ) * Complex.I)⁻¹) ^ (a + 1) =
      (-(R : ℂ)) ^ (a + 1) * kern ((R : ℂ) * Complex.I) a t := by
    intro a
    have h : (R : ℂ) * ((t : ℂ) - (R : ℂ) * Complex.I)⁻¹ =
        (-(R : ℂ)) * ((R : ℂ) * Complex.I - (t : ℂ))⁻¹ := by
      rw [show (t : ℂ) - (R : ℂ) * Complex.I = -((R : ℂ) * Complex.I - (t : ℂ)) by ring, inv_neg]
      ring
    unfold kern
    rw [h, mul_pow, inv_pow]
  have e2 : ∀ a : ℕ, ((R : ℂ) * ((t : ℂ) + (R : ℂ) * Complex.I)⁻¹) ^ (a + 1) =
      (-(R : ℂ)) ^ (a + 1) * kern (-((R : ℂ) * Complex.I)) a t := by
    intro a
    have h : (R : ℂ) * ((t : ℂ) + (R : ℂ) * Complex.I)⁻¹ =
        (-(R : ℂ)) * (-((R : ℂ) * Complex.I) - (t : ℂ))⁻¹ := by
      rw [show (t : ℂ) + (R : ℂ) * Complex.I = -(-((R : ℂ) * Complex.I) - (t : ℂ)) by ring,
        inv_neg]
      ring
    unfold kern
    rw [h, mul_pow, inv_pow]
  have hsum : ∑ a ∈ Finset.range p, (cα a * ((R : ℂ) * ((t : ℂ) - (R : ℂ) * Complex.I)⁻¹) ^ (a + 1) +
        cβ a * ((R : ℂ) * ((t : ℂ) + (R : ℂ) * Complex.I)⁻¹) ^ (a + 1)) =
      ∑ a ∈ Finset.range p, (-(R : ℂ)) ^ (a + 1) *
        (cα a * kern ((R : ℂ) * Complex.I) a t + cβ a * kern (-((R : ℂ) * Complex.I)) a t) :=
    Finset.sum_congr rfl (fun a _ => by rw [e1 a, e2 a]; ring)
  have h0 := hpf t
  rw [sub_eq_iff_eq_add] at h0
  rw [h0, hsum]
  ring

lemma filter_cast_eq (p : ℕ) (R t : ℝ) :
    ((filterF p R t : ℝ) : ℂ) = ((t ^ 2 / (t ^ 2 + R ^ 2) : ℝ) : ℂ) ^ p := by
  unfold filterF
  rw [Complex.ofReal_pow]

/-- **Born-averaged filter bias (generic).** For a countable Born index `α` with probability
weights `β`, laws `ρ a`, a limit law `μ`, and the Born-kernel bias hypothesis `hD`, the Born-averaged
complex filter `F_{p,R}` has bias at most `(Σ_c (‖cα_c‖+‖cβ_c‖) 2^{c+2}) · B/R`. -/
theorem born_filter_core (β : Measure α) [IsProbabilityMeasure β] (ρ : α → Measure ℝ)
    [∀ a, IsProbabilityMeasure (ρ a)] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B) (p : ℕ) (cα cβ : ℕ → ℂ)
    (hpf : ∀ t : ℝ, ((t ^ 2 / (t ^ 2 + R ^ 2) : ℝ) : ℂ) ^ p - 1 =
      ∑ a ∈ Finset.range p, (cα a * ((R : ℂ) * ((t : ℂ) - (R : ℂ) * Complex.I)⁻¹) ^ (a + 1) +
        cβ a * ((R : ℂ) * ((t : ℂ) + (R : ℂ) * Complex.I)⁻¹) ^ (a + 1)))
    (hD : ∀ z : ℂ, R / 2 ≤ z.im → ‖(∫ a, cauchy (ρ a) z ∂β) - cauchy μ z‖ ≤ B / z.im ^ 2) :
    ‖(∫ a, (∫ t : ℝ, ((filterF p R t : ℝ) : ℂ) ∂(ρ a)) ∂β) -
        ∫ t : ℝ, ((filterF p R t : ℝ) : ℂ) ∂μ‖ ≤
      (∑ c ∈ Finset.range p, (‖cα c‖ + ‖cβ c‖) * 2 ^ (c + 2)) * (B / R) := by
  have hI : |((R : ℂ) * Complex.I).im| = R := by simp [abs_of_pos hR]
  have hI' : |(-((R : ℂ) * Complex.I)).im| = R := by simp [abs_of_pos hR]
  have hF : ∀ t : ℝ, ((filterF p R t : ℝ) : ℂ) = 1 + ∑ c ∈ Finset.range p,
      (-(R : ℂ)) ^ (c + 1) * (cα c * kern ((R : ℂ) * Complex.I) c t +
        cβ c * kern (-((R : ℂ) * Complex.I)) c t) := by
    intro t
    rw [filter_cast_eq]
    exact pf_kernel_form (R := R) p cα cβ hpf t
  have hA : ∀ a : α, (∫ t : ℝ, ((filterF p R t : ℝ) : ℂ) ∂(ρ a)) = 1 + ∑ c ∈ Finset.range p,
      (-(R : ℂ)) ^ (c + 1) * (cα c * (∫ t : ℝ, kern ((R : ℂ) * Complex.I) c t ∂(ρ a)) +
        cβ c * (∫ t : ℝ, kern (-((R : ℂ) * Complex.I)) c t ∂(ρ a))) := by
    intro a
    simp only [hF]
    exact integral_sum_form (ρ a) p (fun c => (-(R : ℂ)) ^ (c + 1)) cα cβ
      (fun c t => kern ((R : ℂ) * Complex.I) c t) (fun c t => kern (-((R : ℂ) * Complex.I)) c t)
      (fun c => kern_integrable hR hI c (ρ a)) (fun c => kern_integrable hR hI' c (ρ a))
  have hMu : (∫ t : ℝ, ((filterF p R t : ℝ) : ℂ) ∂μ) = 1 + ∑ c ∈ Finset.range p,
      (-(R : ℂ)) ^ (c + 1) * (cα c * (∫ t : ℝ, kern ((R : ℂ) * Complex.I) c t ∂μ) +
        cβ c * (∫ t : ℝ, kern (-((R : ℂ) * Complex.I)) c t ∂μ)) := by
    simp only [hF]
    exact integral_sum_form μ p (fun c => (-(R : ℂ)) ^ (c + 1)) cα cβ
      (fun c t => kern ((R : ℂ) * Complex.I) c t) (fun c t => kern (-((R : ℂ) * Complex.I)) c t)
      (fun c => kern_integrable hR hI c μ) (fun c => kern_integrable hR hI' c μ)
  have hBav : (∫ a, (∫ t : ℝ, ((filterF p R t : ℝ) : ℂ) ∂(ρ a)) ∂β) = 1 + ∑ c ∈ Finset.range p,
      (-(R : ℂ)) ^ (c + 1) * (cα c * (∫ a, ∫ t : ℝ, kern ((R : ℂ) * Complex.I) c t ∂(ρ a) ∂β) +
        cβ c * (∫ a, ∫ t : ℝ, kern (-((R : ℂ) * Complex.I)) c t ∂(ρ a) ∂β)) := by
    simp only [hA]
    exact integral_sum_form β p (fun c => (-(R : ℂ)) ^ (c + 1)) cα cβ
      (fun c a => ∫ t : ℝ, kern ((R : ℂ) * Complex.I) c t ∂(ρ a))
      (fun c a => ∫ t : ℝ, kern (-((R : ℂ) * Complex.I)) c t ∂(ρ a))
      (fun c => integrable_of_bdd (M := (R ^ (c + 1))⁻¹) β
        (fun a => ∫ t : ℝ, kern ((R : ℂ) * Complex.I) c t ∂(ρ a))
        (fun a => integral_kern_norm_le hR hI c (ρ a)))
      (fun c => integrable_of_bdd (M := (R ^ (c + 1))⁻¹) β
        (fun a => ∫ t : ℝ, kern (-((R : ℂ) * Complex.I)) c t ∂(ρ a))
        (fun a => integral_kern_norm_le hR hI' c (ρ a)))
  obtain ⟨Dp, hDp⟩ : ∃ Dp : ℕ → ℂ, ∀ c, Dp c =
      (∫ a, ∫ t : ℝ, kern ((R : ℂ) * Complex.I) c t ∂(ρ a) ∂β) -
        ∫ t : ℝ, kern ((R : ℂ) * Complex.I) c t ∂μ := ⟨_, fun c => rfl⟩
  obtain ⟨Dm, hDm⟩ : ∃ Dm : ℕ → ℂ, ∀ c, Dm c =
      (∫ a, ∫ t : ℝ, kern (-((R : ℂ) * Complex.I)) c t ∂(ρ a) ∂β) -
        ∫ t : ℝ, kern (-((R : ℂ) * Complex.I)) c t ∂μ := ⟨_, fun c => rfl⟩
  have e : ∀ X Y : ℂ, (1 + X) - (1 + Y) = X - Y := fun X Y => by ring
  have hkey : (∫ a, (∫ t : ℝ, ((filterF p R t : ℝ) : ℂ) ∂(ρ a)) ∂β) -
      ∫ t : ℝ, ((filterF p R t : ℝ) : ℂ) ∂μ =
      ∑ c ∈ Finset.range p, (-(R : ℂ)) ^ (c + 1) * (cα c * Dp c + cβ c * Dm c) := by
    rw [hBav, hMu, e, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hDp c, hDm c]
    ring
  have hneg : ∀ c, Dm c = conj (Dp c) := by
    intro c
    rw [hDm c, hDp c]
    simp only [kern_neg_conj, integral_conj, map_sub]
  have hDp_bd : ∀ c : ℕ, ‖Dp c‖ ≤ 2 ^ (c + 2) * B / R ^ (c + 2) := by
    intro c
    rw [hDp c]
    exact born_bias β ρ μ hR hB c hD
  have hDm_bd : ∀ c : ℕ, ‖Dm c‖ ≤ 2 ^ (c + 2) * B / R ^ (c + 2) := by
    intro c
    rw [hneg c, Complex.norm_conj]
    exact hDp_bd c
  have hterm : ∀ c ∈ Finset.range p, ‖(-(R : ℂ)) ^ (c + 1) * (cα c * Dp c + cβ c * Dm c)‖ ≤
      ((‖cα c‖ + ‖cβ c‖) * 2 ^ (c + 2)) * (B / R) := by
    intro c _
    have hw : ‖(-(R : ℂ)) ^ (c + 1)‖ = R ^ (c + 1) := by
      rw [norm_pow, norm_neg, Complex.norm_real, Real.norm_of_nonneg hR.le]
    have h1 : ‖cα c * Dp c + cβ c * Dm c‖ ≤
        (‖cα c‖ + ‖cβ c‖) * (2 ^ (c + 2) * B / R ^ (c + 2)) := by
      calc ‖cα c * Dp c + cβ c * Dm c‖ ≤ ‖cα c * Dp c‖ + ‖cβ c * Dm c‖ := norm_add_le _ _
        _ = ‖cα c‖ * ‖Dp c‖ + ‖cβ c‖ * ‖Dm c‖ := by rw [norm_mul, norm_mul]
        _ ≤ ‖cα c‖ * (2 ^ (c + 2) * B / R ^ (c + 2)) + ‖cβ c‖ * (2 ^ (c + 2) * B / R ^ (c + 2)) :=
            add_le_add (mul_le_mul_of_nonneg_left (hDp_bd c) (norm_nonneg _))
              (mul_le_mul_of_nonneg_left (hDm_bd c) (norm_nonneg _))
        _ = (‖cα c‖ + ‖cβ c‖) * (2 ^ (c + 2) * B / R ^ (c + 2)) := by ring
    have hid : R ^ (c + 1) * ((‖cα c‖ + ‖cβ c‖) * (2 ^ (c + 2) * B / R ^ (c + 2))) =
        ((‖cα c‖ + ‖cβ c‖) * 2 ^ (c + 2)) * (B / R) := by
      have hRne : R ≠ 0 := hR.ne'
      have hpow : R ^ (c + 2) = R ^ (c + 1) * R := by ring
      rw [hpow]
      first
        | (field_simp; ring)
        | field_simp
    rw [norm_mul, hw]
    calc R ^ (c + 1) * ‖cα c * Dp c + cβ c * Dm c‖
        ≤ R ^ (c + 1) * ((‖cα c‖ + ‖cβ c‖) * (2 ^ (c + 2) * B / R ^ (c + 2))) :=
          mul_le_mul_of_nonneg_left h1 (pow_pos hR _).le
      _ = ((‖cα c‖ + ‖cβ c‖) * 2 ^ (c + 2)) * (B / R) := hid
  calc ‖(∫ a, (∫ t : ℝ, ((filterF p R t : ℝ) : ℂ) ∂(ρ a)) ∂β) -
        ∫ t : ℝ, ((filterF p R t : ℝ) : ℂ) ∂μ‖
      = ‖∑ c ∈ Finset.range p, (-(R : ℂ)) ^ (c + 1) * (cα c * Dp c + cβ c * Dm c)‖ := by
        rw [hkey]
    _ ≤ ∑ c ∈ Finset.range p, ‖(-(R : ℂ)) ^ (c + 1) * (cα c * Dp c + cβ c * Dm c)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ c ∈ Finset.range p, ((‖cα c‖ + ‖cβ c‖) * 2 ^ (c + 2)) * (B / R) :=
        Finset.sum_le_sum hterm
    _ = (∑ c ∈ Finset.range p, (‖cα c‖ + ‖cβ c‖) * 2 ^ (c + 2)) * (B / R) := by
        rw [Finset.sum_mul]

end Generic

/-- The empirical rapidity measure `ν_N(m)` as a `Measure ℝ` (transparent wrapper). -/
def empMeas (L κ : ℝ) (N : ℕ) (m : QuantumNLS.BetheLabels.MArr N) : Measure ℝ :=
  ((QuantumNLS.BulkResponseActual.empiricalProb L κ N m : ProbabilityMeasure ℝ) : Measure ℝ)

instance empMeas_isProbabilityMeasure (L κ : ℝ) (N : ℕ) (m : QuantumNLS.BetheLabels.MArr N) :
    IsProbabilityMeasure (empMeas L κ N m) := by
  unfold empMeas
  infer_instance

section Instance

variable {L : ℝ} [Fact (0 < L)]

/-- **B3: Born-averaged filter bias.** For `N ≥ 1`, any unit profile `u`, any limiting measure `μ`
and `R ≥ 2 η₀` with `η₀ = max (4κ) (log 16 / L)`:
`|E ∫F_{p,R} dν_N - ∫F_{p,R} dμ| ≤ D/(N R)`, where `E` is the Born average over `bornMeasure`. -/
theorem born_filter_bias {κ : ℝ} (hκ : 0 < κ) (p : ℕ) :
    ∃ D : ℝ, ∀ (N : ℕ) (hN : 0 < N) (u : QuantumNLS.PhysicalTensor.L2T L) (hu : ‖u‖ = 1)
      (μ : ProbabilityMeasure ℝ),
      QuantumNLS.BulkResponseActual.IsLimitingRapidityMeasure L κ hκ u hu μ →
      ∀ R : ℝ, 2 * max (4 * κ) (Real.log 16 / L) ≤ R →
        |(∫ m : QuantumNLS.BetheLabels.MArr N,
            ∫ t : ℝ, filterF p R t ∂(empMeas L κ N m)
            ∂(QuantumNLS.EmpiricalRapidity.bornMeasure
                (QuantumNLS.BulkResponseActual.physBasis L hκ N) u hu)) -
          ∫ t : ℝ, filterF p R t ∂((μ : ProbabilityMeasure ℝ) : Measure ℝ)| ≤ D / (N * R) := by
  obtain ⟨cα, cβ, hpf⟩ := QuantumNLS.ValuesTailPartialFraction.pf_transport p
  refine ⟨max QuantumNLS.RootMeasureConcentrationSharp.Csharp (|QuantumNLS.Prop017Bias.Cg| * κ) *
    ∑ c ∈ Finset.range p, (‖cα c‖ + ‖cβ c‖) * 2 ^ (c + 2), ?_⟩
  intro N hN u hu μ hμ R hR2
  have hVC := QuantumNLS.ValuesConcentration.values_concentration (L := L) hκ (le_refl κ)
  have hCpos : 0 < max QuantumNLS.RootMeasureConcentrationSharp.Csharp
      (|QuantumNLS.Prop017Bias.Cg| * κ) := hVC.2.1
  have hη : 0 < max (4 * κ) (Real.log 16 / L) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hR : 0 < R := by linarith
  have hB : 0 ≤ max QuantumNLS.RootMeasureConcentrationSharp.Csharp
      (|QuantumNLS.Prop017Bias.Cg| * κ) / (N : ℝ) :=
    div_nonneg hCpos.le (Nat.cast_nonneg N)
  obtain ⟨β, hβ⟩ : ∃ β : Measure (QuantumNLS.BetheLabels.MArr N),
      β = QuantumNLS.EmpiricalRapidity.bornMeasure
        (QuantumNLS.BulkResponseActual.physBasis L hκ N) u hu := ⟨_, rfl⟩
  have hβP : IsProbabilityMeasure β := by
    rw [hβ]
    infer_instance
  rw [← hβ]
  have hcore := born_filter_core (R := R) (B := max QuantumNLS.RootMeasureConcentrationSharp.Csharp
      (|QuantumNLS.Prop017Bias.Cg| * κ) / (N : ℝ)) β (empMeas L κ N) (μ : Measure ℝ) hR hB p cα cβ
    (fun t => hpf R hR t) (fun z hz => by
      have hz' : max (4 * κ) (Real.log 16 / L) ≤ z.im := by linarith
      have h := (hVC.2.2 N hN u hu μ hμ z hz').2
      rw [hβ, div_div]
      exact h)
  have key : ∀ x y : ℝ, |x - y| = ‖(x : ℂ) - (y : ℂ)‖ := fun x y => by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hc1 : ((∫ m : QuantumNLS.BetheLabels.MArr N, ∫ t : ℝ, filterF p R t ∂(empMeas L κ N m) ∂β :
      ℝ) : ℂ) = ∫ m : QuantumNLS.BetheLabels.MArr N, ∫ t : ℝ,
        ((filterF p R t : ℝ) : ℂ) ∂(empMeas L κ N m) ∂β := by
    simp only [integral_complex_ofReal]
  have hc2 : ((∫ t : ℝ, filterF p R t ∂((μ : ProbabilityMeasure ℝ) : Measure ℝ) : ℝ) : ℂ) =
      ∫ t : ℝ, ((filterF p R t : ℝ) : ℂ) ∂((μ : ProbabilityMeasure ℝ) : Measure ℝ) := by
    rw [integral_complex_ofReal]
  rw [key, hc1, hc2]
  exact hcore.trans (le_of_eq (by ring))

end Instance

end QuantumNLS.ValuesTailBias

#print axioms QuantumNLS.ValuesTailBias.kern_neg_conj
#print axioms QuantumNLS.ValuesTailBias.born_filter_core
#print axioms QuantumNLS.ValuesTailBias.born_filter_bias
