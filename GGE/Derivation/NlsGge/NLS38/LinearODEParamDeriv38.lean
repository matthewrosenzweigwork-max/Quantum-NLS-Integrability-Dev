import Mathlib
import NlsGge.Analysis.ODEFlowDeriv38
import NlsGge.NLS38.LinearODEParamDeriv38a

/-!
# Parameter derivative of a linear ODE (38, B2)

For `Ψ' = A Ψ` in the `x` variable with `A` depending `C¹` on a parameter `t`, the derivative
`E = ∂ₜ Ψ` exists and solves the variational equation `E' = A E + (∂ₜ A) Ψ`, `E(0) = 0`.

The core argument is carried out in an arbitrary real Banach algebra `𝔸` (instantiated at
`Matrix (Fin 2) (Fin 2) ℂ` with the Frobenius norm at the end): the remainder
`r = Ψ(·,t₀+h) - Ψ(·,t₀) - h E(·,t₀)` satisfies `r(0) = 0` and `‖r'‖ ≤ M ‖r‖ + o(h)` uniformly
on `[0, T]`, and `NlsGge.ODEFlowDeriv38.gronwall_rem38` gives `‖r‖ = o(h)`.  Negative `x` is
reduced to positive `x` by the reflection `x ↦ -x`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open Set Filter Topology
open scoped Matrix Matrix.Norms.Frobenius

namespace NlsGge.NLS38

section Banach

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The augmented linear operator `(p, q) ↦ (a p, b p + a q)` on `𝔸 × 𝔸`, encoding the system
`Ψ' = A Ψ`, `E' = A E + B Ψ`. -/
def augLin38 (a b : 𝔸) : (𝔸 × 𝔸) →L[ℝ] (𝔸 × 𝔸) :=
  ((ContinuousLinearMap.mul ℝ 𝔸 a).comp (ContinuousLinearMap.fst ℝ 𝔸 𝔸)).prod
    ((ContinuousLinearMap.mul ℝ 𝔸 b).comp (ContinuousLinearMap.fst ℝ 𝔸 𝔸) +
      (ContinuousLinearMap.mul ℝ 𝔸 a).comp (ContinuousLinearMap.snd ℝ 𝔸 𝔸))

lemma augLin38_apply (a b : 𝔸) (p : 𝔸 × 𝔸) :
    augLin38 a b p = (a * p.1, b * p.1 + a * p.2) := rfl

lemma continuous_augLin38 {X : Type*} [TopologicalSpace X] {a b : X → 𝔸} (ha : Continuous a)
    (hb : Continuous b) : Continuous fun x => augLin38 (a x) (b x) := by
  have hm : ∀ {c : X → 𝔸}, Continuous c →
      Continuous fun x => (ContinuousLinearMap.mul ℝ 𝔸 (c x)) :=
    fun hc => (ContinuousLinearMap.mul ℝ 𝔸).continuous.comp hc
  have h1 : Continuous fun x => (ContinuousLinearMap.mul ℝ 𝔸 (a x)).comp
      (ContinuousLinearMap.fst ℝ 𝔸 𝔸) := (hm ha).clm_comp continuous_const
  have h2 : Continuous fun x => (ContinuousLinearMap.mul ℝ 𝔸 (b x)).comp
      (ContinuousLinearMap.fst ℝ 𝔸 𝔸) := (hm hb).clm_comp continuous_const
  have h3 : Continuous fun x => (ContinuousLinearMap.mul ℝ 𝔸 (a x)).comp
      (ContinuousLinearMap.snd ℝ 𝔸 𝔸) := (hm ha).clm_comp continuous_const
  exact (ContinuousLinearMap.prodL ℝ (𝕜 := ℝ) (E := 𝔸 × 𝔸) (F := 𝔸) (G := 𝔸)).continuous.comp (h1.prodMk (h2.add h3))

/-- Existence of a fundamental solution `Ψ' = A Ψ`, `Ψ(0,t) = 1`, for each parameter `t`. -/
theorem exists_fundamental_banach38 (A : ℝ → ℝ → 𝔸) (hA : Continuous (Function.uncurry A)) :
    ∃ Ψ : ℝ → ℝ → 𝔸, (∀ t, Ψ 0 t = 1) ∧
      ∀ x t, HasDerivAt (fun y => Ψ y t) (A x t * Ψ x t) x := by
  have h : ∀ t : ℝ, ∃ D : ℝ → 𝔸, D 0 = 1 ∧ ∀ x, HasDerivAt D (A x t * D x) x := fun t =>
    exists_global_lin38 (fun x => ContinuousLinearMap.mul ℝ 𝔸 (A x t))
      ((ContinuousLinearMap.mul ℝ 𝔸).continuous.comp
        (hA.comp (continuous_id.prodMk continuous_const))) 1
  choose D hD0 hD using h
  exact ⟨fun x t => D t x, hD0, fun x t => hD t x⟩

/-- Uniqueness for `Z' = A Z`, `Z 0 = 0` (single parameter value). -/
theorem linear_ode_unique_banach38 (A : ℝ → 𝔸) (hA : Continuous A) {Z : ℝ → 𝔸} (h0 : Z 0 = 0)
    (hZ : ∀ x, HasDerivAt Z (A x * Z x) x) : ∀ x, Z x = 0 := by
  have := lin_unique38 (fun x => ContinuousLinearMap.mul ℝ 𝔸 (A x))
    ((ContinuousLinearMap.mul ℝ 𝔸).continuous.comp hA) (D₁ := Z) (D₂ := fun _ => 0)
    hZ (fun x => by simpa using hasDerivAt_const x (0 : 𝔸)) (by simpa using h0)
  intro x
  exact congrFun this x

/-- The candidate derivative `E`: solution of the variational equation. -/
theorem exists_variational_banach38 (A At : ℝ → ℝ → 𝔸) (hA : Continuous (Function.uncurry A))
    (hAt : Continuous (Function.uncurry At)) (Ψ : ℝ → ℝ → 𝔸) (h0 : ∀ t, Ψ 0 t = 1)
    (hΨ : ∀ x t, HasDerivAt (fun y => Ψ y t) (A x t * Ψ x t) x) :
    ∃ E : ℝ → ℝ → 𝔸, (∀ t, E 0 t = 0) ∧
      ∀ x t, HasDerivAt (fun y => E y t) (A x t * E x t + At x t * Ψ x t) x := by
  have h : ∀ t : ℝ, ∃ D : ℝ → 𝔸 × 𝔸, D 0 = (1, 0) ∧
      ∀ x, HasDerivAt D (augLin38 (A x t) (At x t) (D x)) x := fun t =>
    exists_global_lin38 (fun x => augLin38 (A x t) (At x t))
      (continuous_augLin38 (hA.comp (continuous_id.prodMk continuous_const))
        (hAt.comp (continuous_id.prodMk continuous_const))) (1, 0)
  choose D hD0 hD using h
  have hP : ∀ t, (fun x => (D t x).1) = fun x => Ψ x t := fun t => by
    refine lin_unique38 (fun x => ContinuousLinearMap.mul ℝ 𝔸 (A x t))
      ((ContinuousLinearMap.mul ℝ 𝔸).continuous.comp
        (hA.comp (continuous_id.prodMk continuous_const))) (fun x => ?_) (fun x => ?_) ?_
    · exact (hD t x).fst
    · exact hΨ x t
    · simp [hD0, h0]
  refine ⟨fun x t => (D t x).2, fun t => by simp [hD0], fun x t => ?_⟩
  have h2 := (ContinuousLinearMap.snd ℝ 𝔸 𝔸).hasFDerivAt.comp_hasDerivAt x (hD t x)
  have h3 : (D t x).1 = Ψ x t := congrFun (hP t) x
  simpa [augLin38_apply, h3, Function.comp_def, add_comm] using h2

/-- Forward (`x₀ ≥ 0`) core estimate. -/
theorem param_deriv_fwd38 (A At : ℝ → ℝ → 𝔸) (hA : Continuous (Function.uncurry A))
    (hAt : Continuous (Function.uncurry At))
    (hdt : ∀ x t, HasDerivAt (fun s => A x s) (At x t) t)
    (Ψ E : ℝ → ℝ → 𝔸) (h0 : ∀ t, Ψ 0 t = 1)
    (hΨ : ∀ x t, HasDerivAt (fun y => Ψ y t) (A x t * Ψ x t) x)
    (hE0 : ∀ t, E 0 t = 0)
    (hE : ∀ x t, HasDerivAt (fun y => E y t) (A x t * E x t + At x t * Ψ x t) x)
    {T : ℝ} (hT : 0 ≤ T) (t₀ : ℝ) :
    HasDerivAt (fun s => Ψ T s) (E T t₀) t₀ := by
  have hK : IsCompact (Icc (0 : ℝ) T ×ˢ Icc (t₀ - 1) (t₀ + 1)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨MA, hMA⟩ := hK.exists_bound_of_continuousOn hA.continuousOn
  obtain ⟨MB, hMB⟩ := hK.exists_bound_of_continuousOn hAt.continuousOn
  obtain ⟨ME, hME⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (f := fun x => E x t₀) (fun x _ => (hE x t₀).continuousAt.continuousWithinAt)
  set a : ℝ := max MA 0 with ha
  set b : ℝ := max MB 0 with hb
  set e : ℝ := max ME 0 with he
  have ha0 : 0 ≤ a := le_max_right _ _
  have hb0 : 0 ≤ b := le_max_right _ _
  have he0 : 0 ≤ e := le_max_right _ _
  have hAb : ∀ x ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (t₀ - 1) (t₀ + 1), ‖A x s‖ ≤ a := fun x hx s hs =>
    (hMA (x, s) ⟨hx, hs⟩).trans (le_max_left _ _)
  have hBb : ∀ x ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (t₀ - 1) (t₀ + 1), ‖At x s‖ ≤ b := fun x hx s hs =>
    (hMB (x, s) ⟨hx, hs⟩).trans (le_max_left _ _)
  have hEb : ∀ x ∈ Icc (0 : ℝ) T, ‖E x t₀‖ ≤ e := fun x hx =>
    (hME x hx).trans (le_max_left _ _)
  -- uniform bound for `Ψ`
  set n1 : ℝ := ‖(1 : 𝔸)‖ with hn1
  set Bp : ℝ := a * n1 * T * Real.exp (a * T) + n1 with hBp
  have hBp0 : 0 ≤ Bp := by positivity
  have hPsi : ∀ s ∈ Icc (t₀ - 1) (t₀ + 1), ∀ x ∈ Icc (0 : ℝ) T, ‖Ψ x s‖ ≤ Bp := by
    intro s hs x hx
    have hg := NlsGge.ODEFlowDeriv38.gronwall_rem38 (E := 𝔸) (r := fun y => Ψ y s - 1)
      (r' := fun y => A y s * Ψ y s) hT ha0 (mul_nonneg ha0 (norm_nonneg _))
      (by simp [h0]) (fun y _ => ((hΨ y s).sub_const 1).hasDerivWithinAt)
      (fun y hy => by
        have h1 : A y s * Ψ y s = A y s * (Ψ y s - 1) + A y s * 1 := by
          rw [mul_sub]; abel
        rw [h1]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (hAb y hy s hs) (norm_nonneg _))
        · exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (hAb y hy s hs) (norm_nonneg _))) x hx
    have : ‖Ψ x s‖ ≤ ‖Ψ x s - 1‖ + n1 := by
      have := norm_add_le (Ψ x s - 1) 1
      simpa [hn1] using this
    refine this.trans ?_
    rw [hBp]
    have := hg
    linarith
  -- uniform continuity of `At`
  have huc := hK.uniformContinuousOn_of_continuous hAt.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set W : ℝ := T * Real.exp ((a + b) * T) with hW
  have hW0 : 0 ≤ W := by positivity
  set ε : ℝ := c / (2 * (Bp * W + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨δ, hδ, hδε⟩ := huc ε hε0
  set ρ : ℝ := c / (2 * (b * e * W + 1)) with hρ
  have hρ0 : 0 < ρ := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (lt_min (lt_min hδ one_pos) hρ0)] with h hh
  have hh' : |h| < min (min δ 1) ρ := by simpa [Real.dist_eq] using hh
  have hhδ : |h| < δ := lt_of_lt_of_le hh' ((min_le_left _ _).trans (min_le_left _ _))
  have hh1 : |h| < 1 := lt_of_lt_of_le hh' ((min_le_left _ _).trans (min_le_right _ _))
  have hhρ : |h| < ρ := lt_of_lt_of_le hh' (min_le_right _ _)
  have hs_mem : ∀ s, |s - t₀| < 1 → s ∈ Icc (t₀ - 1) (t₀ + 1) := fun s hs =>
    ⟨by linarith [(abs_lt.1 hs).1], by linarith [(abs_lt.1 hs).2]⟩
  have hth : t₀ + h ∈ Icc (t₀ - 1) (t₀ + 1) := hs_mem _ (by simpa using hh1)
  have ht0 : t₀ ∈ Icc (t₀ - 1) (t₀ + 1) := ⟨by linarith, by linarith⟩
  -- mean-value estimate for `A`
  have hMV : ∀ x ∈ Icc (0 : ℝ) T, ‖A x (t₀ + h) - A x t₀ - h • At x t₀‖ ≤ ε * |h| := by
    intro x hx
    have hconv := convex_ball t₀ (min δ 1)
    have hφ : ∀ s ∈ Metric.ball t₀ (min δ 1),
        HasDerivWithinAt (fun s => A x s - s • At x t₀) (At x s - At x t₀)
          (Metric.ball t₀ (min δ 1)) s := fun s _ => by
      exact ((hdt x s).sub ((hasDerivAt_id s).smul_const (At x t₀))).hasDerivWithinAt.congr_deriv
        (by simp)
    have hbd : ∀ s ∈ Metric.ball t₀ (min δ 1), ‖At x s - At x t₀‖ ≤ ε := by
      intro s hs
      have hs' : |s - t₀| < min δ 1 := by simpa [Real.dist_eq] using hs
      have hs1 : |s - t₀| < 1 := lt_of_lt_of_le hs' (min_le_right _ _)
      have hsδ : |s - t₀| < δ := lt_of_lt_of_le hs' (min_le_left _ _)
      have := hδε (x, s) ⟨hx, hs_mem s hs1⟩ (x, t₀) ⟨hx, ht0⟩
        (by rw [Prod.dist_eq]; simpa [Real.dist_eq] using hsδ)
      rw [dist_eq_norm] at this
      exact this.le
    have hm1 : t₀ ∈ Metric.ball t₀ (min δ 1) := Metric.mem_ball_self (lt_min hδ one_pos)
    have hm2 : t₀ + h ∈ Metric.ball t₀ (min δ 1) := by
      rw [Metric.mem_ball, Real.dist_eq]; simpa using lt_min hhδ hh1
    have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hφ hbd hm1 hm2
    have e1 : A x (t₀ + h) - (t₀ + h) • At x t₀ - (A x t₀ - t₀ • At x t₀) =
        A x (t₀ + h) - A x t₀ - h • At x t₀ := by
      rw [add_smul]; abel
    simpa [e1] using this
  -- Grönwall
  set r : ℝ → 𝔸 := fun x => Ψ x (t₀ + h) - Ψ x t₀ - h • E x t₀ with hr
  set r' : ℝ → 𝔸 := fun x => A x (t₀ + h) * Ψ x (t₀ + h) - A x t₀ * Ψ x t₀ -
    h • (A x t₀ * E x t₀ + At x t₀ * Ψ x t₀) with hr'
  have hrd : ∀ x ∈ Icc (0 : ℝ) T, HasDerivWithinAt r (r' x) (Icc 0 T) x := fun x _ =>
    (((hΨ x (t₀ + h)).sub (hΨ x t₀)).sub ((hE x t₀).const_smul h)).hasDerivWithinAt
  have hr0 : r 0 = 0 := by simp [hr, h0, hE0]
  have hrb : ∀ x ∈ Icc (0 : ℝ) T,
      ‖r' x‖ ≤ (a + b) * ‖r x‖ + |h| * (ε * Bp + |h| * (b * e)) := by
    intro x hx
    have e1 : r' x = A x t₀ * r x + (A x (t₀ + h) - A x t₀ - h • At x t₀) * Ψ x (t₀ + h) +
        h • (At x t₀ * (r x + h • E x t₀)) := by
      simp only [hr', hr]
      simp only [mul_sub, sub_mul, mul_add, smul_sub, smul_add, mul_smul_comm,
        smul_mul_assoc]
      abel
    rw [e1]
    have t1 : ‖A x t₀ * r x‖ ≤ a * ‖r x‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hAb x hx t₀ ht0) (norm_nonneg _))
    have t2 : ‖(A x (t₀ + h) - A x t₀ - h • At x t₀) * Ψ x (t₀ + h)‖ ≤ ε * |h| * Bp :=
      (norm_mul_le _ _).trans (mul_le_mul (hMV x hx) (hPsi _ hth x hx) (norm_nonneg _)
        (by positivity))
    have t3 : ‖h • (At x t₀ * (r x + h • E x t₀))‖ ≤ |h| * (b * (‖r x‖ + |h| * e)) := by
      rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans ?_) (abs_nonneg _)
      refine mul_le_mul (hBb x hx t₀ ht0) ((norm_add_le _ _).trans ?_) (norm_nonneg _) hb0
      rw [norm_smul, Real.norm_eq_abs]
      have := mul_le_mul_of_nonneg_left (hEb x hx) (abs_nonneg h)
      linarith
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) t3).trans ?_)
    have hr_nn := norm_nonneg (r x)
    have habs := abs_nonneg h
    nlinarith [mul_nonneg habs hr_nn, mul_le_mul_of_nonneg_right hh1.le hr_nn,
      mul_nonneg hb0 habs, mul_nonneg (mul_nonneg hb0 habs) habs]
  have hgr := NlsGge.ODEFlowDeriv38.gronwall_rem38 (E := 𝔸) (r := r) (r' := r') hT
    (by positivity) (by positivity) hr0 hrd hrb T ⟨hT, le_rfl⟩
  have hfin : ‖r T‖ ≤ c * ‖h‖ := by
    refine hgr.trans ?_
    rw [Real.norm_eq_abs]
    have hε1 : ε * (Bp * W) ≤ c / 2 := by
      rw [hε, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg hBp0 hW0]
    have hρ1 : |h| * (b * e * W) ≤ c / 2 := by
      calc |h| * (b * e * W) ≤ ρ * (b * e * W) := by gcongr
        _ ≤ c / 2 := by
          rw [hρ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_nonneg (mul_nonneg hb0 he0) hW0]
    have : |h| * (ε * Bp + |h| * (b * e)) * T * Real.exp ((a + b) * T)
        = |h| * (ε * (Bp * W) + |h| * (b * e * W)) := by rw [hW]; ring
    rw [this]
    calc |h| * (ε * (Bp * W) + |h| * (b * e * W)) ≤ |h| * (c / 2 + c / 2) := by gcongr
      _ = c * |h| := by ring
  simpa [hr] using hfin

end Banach

section Matrix2

/-- The parameter derivative of the fundamental matrix of a linear ODE with `C¹` parameter
dependence.  Statement as in the plan (B2), proved in the Frobenius-normed Banach algebra. -/
theorem hasDerivAt_param_linearODE
    (A At : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : Continuous (Function.uncurry A)) (hAt : Continuous (Function.uncurry At))
    (hdt : ∀ x t, HasDerivAt (fun s => A x s) (At x t) t)
    (Ψ : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ) (h0 : ∀ t, Ψ 0 t = 1)
    (hΨ : ∀ x t, HasDerivAt (fun y => Ψ y t) (A x t * Ψ x t) x) :
    ∃ E : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ x t, HasDerivAt (fun s => Ψ x s) (E x t) t) ∧ (∀ t, E 0 t = 0) ∧
      ∀ x t, HasDerivAt (fun y => E y t) (A x t * E x t + At x t * Ψ x t) x := by
  obtain ⟨E, hE0, hE⟩ := exists_variational_banach38 A At hA hAt Ψ h0 hΨ
  refine ⟨E, fun x t => ?_, hE0, hE⟩
  rcases le_total 0 x with hx | hx
  · exact param_deriv_fwd38 A At hA hAt hdt Ψ E h0 hΨ hE0 hE hx t
  · -- reflection `x ↦ -x`
    have key := param_deriv_fwd38 (fun y s => -A (-y) s) (fun y s => -At (-y) s)
      (by
        have : Continuous (fun p : ℝ × ℝ => A (-p.1) p.2) :=
          hA.comp (continuous_neg.comp continuous_fst |>.prodMk continuous_snd)
        exact this.neg)
      (by
        have : Continuous (fun p : ℝ × ℝ => At (-p.1) p.2) :=
          hAt.comp (continuous_neg.comp continuous_fst |>.prodMk continuous_snd)
        exact this.neg)
      (fun y s => (hdt (-y) s).neg) (fun y s => Ψ (-y) s) (fun y s => E (-y) s)
      (by simpa using h0) (fun y s => by
        have := (hΨ (-y) s).scomp y (hasDerivAt_neg y)
        exact this.congr_deriv (by simp))
      (by simpa using hE0) (fun y s => by
        have := (hE (-y) s).scomp y (hasDerivAt_neg y)
        exact this.congr_deriv (by simp [neg_mul]))
      (T := -x) (by linarith) t
    simp only [neg_neg] at key
    exact key

/-- Existence of the fundamental matrix, for each parameter `t`. -/
theorem exists_fundamental (A : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : Continuous (Function.uncurry A)) :
    ∃ Ψ : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ, (∀ t, Ψ 0 t = 1) ∧
      ∀ x t, HasDerivAt (fun y => Ψ y t) (A x t * Ψ x t) x :=
  exists_fundamental_banach38 A hA

/-- Uniqueness: `Z' = A Z`, `Z(0) = 0` forces `Z = 0` on `ℝ`. -/
theorem linear_ode_unique (A : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : Continuous (Function.uncurry A)) (t : ℝ) (Z : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (h0 : Z 0 = 0) (hZ : ∀ x, HasDerivAt Z (A x t * Z x) x) : ∀ x, Z x = 0 :=
  linear_ode_unique_banach38 (fun x => A x t) (hA.comp (continuous_id.prodMk continuous_const)) h0 hZ

end Matrix2

end NlsGge.NLS38
