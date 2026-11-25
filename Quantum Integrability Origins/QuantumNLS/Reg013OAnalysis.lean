import Mathlib

/-! REG-013 (`lem:regularity-induction`, `fractional_moments.tex:610`), opus_tensor stage O1:
measure-theoretic analysis used by the induction step. Mathlib only; no project input.

* The positive fractional kernel `x^{2k} r_α(t,x²)` (`t = Y²`, `r_α = Real.rpowIntegrand₀₁`),
  its scalar integral `C_α |x|^{2(k+α)}`, Tonelli, and the positive-integral criterion
  (`criterion`): for two s-finite measures with finite `2k` moments whose kernel difference
  `P_μ - P_ν` is integrable on `(0,∞)`, the order-`2(k+α)` moments are simultaneously finite,
  and then differ by `∫ (P_μ - P_ν) / C_α`. No total Bochner value is assigned to a
  non-integrable moment.
* The two-regime majorant `A t^{α-1}` / `B t^{α-2}` (small-`Y` / large-`Y` bounds).
* Tail calculus for nonnegative sequences (Scheffé form) and for weakly convergent finite
  measures on `ℝ` (bounded continuous test functions). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace QuantumNLS.Reg013OAnalysis

/-! ### The fractional kernel -/

/-- The positive fractional kernel `x^{2k} r_α(t, x²)`; the printed parameter is `Y = √t`. -/
def kern (k : ℕ) (α t x : ℝ) : ℝ := x^(2*k) * Real.rpowIntegrand₀₁ α t (x^2)

/-- The normalizing constant `C_α = ∫_0^∞ r_α(t,1) dt > 0`. -/
def Cα (α : ℝ) : ℝ := ∫ t in Ioi 0, Real.rpowIntegrand₀₁ α t 1

/-- The printed regularized kernel `Y² x^{2k+2}/(Y²+x²)` of `D_{k+1,u}(Y)`. -/
def K (k : ℕ) (Y x : ℝ) : ℝ := Y ^ 2 * x ^ (2 * (k+1)) / (Y ^ 2 + x ^ 2)

theorem Cα_pos {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) : 0 < Cα α :=
  Real.integral_rpowIntegrand₀₁_one_pos hα

theorem kern_nonneg (k : ℕ) {α t : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) (ht : 0 ≤ t) (x : ℝ) :
    0 ≤ kern k α t x :=
  mul_nonneg ((even_two_mul k).pow_nonneg x) (Real.rpowIntegrand₀₁_nonneg hα.1 ht (sq_nonneg x))

theorem kern_le (k : ℕ) {α t : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) (ht : 0 ≤ t) (x : ℝ) :
    kern k α t x ≤ t^(α-1) * x^(2*k) := by
  unfold kern
  rw [mul_comm (t^(α-1))]
  exact mul_le_mul_of_nonneg_left (Real.rpowIntegrand₀₁_le_rpow_sub_one hα ht (sq_nonneg x))
    ((even_two_mul k).pow_nonneg x)

theorem measurable_kern (k : ℕ) (α : ℝ) : Measurable (Function.uncurry (kern k α)) := by
  unfold Function.uncurry kern Real.rpowIntegrand₀₁
  fun_prop

theorem measurable_kern_right (k : ℕ) (α t : ℝ) : Measurable (fun x => kern k α t x) := by
  unfold kern Real.rpowIntegrand₀₁
  fun_prop

theorem K_nonneg (k : ℕ) (Y x : ℝ) : 0 ≤ K k Y x := by
  unfold K
  exact div_nonneg (mul_nonneg (sq_nonneg Y) ((even_two_mul (k+1)).pow_nonneg x))
    (add_nonneg (sq_nonneg Y) (sq_nonneg x))

/-- The small-`Y` bound: `Y² x^{2k+2}/(Y²+x²) ≤ Y² x^{2k}`. -/
theorem K_le (k : ℕ) (Y x : ℝ) : K k Y x ≤ Y^2 * x^(2*k) := by
  unfold K
  rcases (add_nonneg (sq_nonneg Y) (sq_nonneg x)).eq_or_lt with h | h
  · rw [← h, div_zero]; exact mul_nonneg (sq_nonneg Y) ((even_two_mul k).pow_nonneg x)
  · rw [div_le_iff₀ h, show 2*(k+1) = 2*k+2 by ring, pow_add]
    have := mul_nonneg (sq_nonneg Y) ((even_two_mul k).pow_nonneg x)
    nlinarith [mul_nonneg this (sq_nonneg Y)]

theorem K_measurable (k : ℕ) (Y : ℝ) : Measurable (K k Y) := by
  unfold K; fun_prop

/-- Relation to the printed kernel, `t = Y²`. -/
theorem kern_eq_K (k : ℕ) {α t : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) (ht : 0 < t) (x : ℝ) :
    kern k α t x = t^(α-2) * K k (Real.sqrt t) x := by
  unfold kern K
  rw [Real.rpowIntegrand₀₁_eq_pow_div hα ht.le (sq_nonneg x), Real.sq_sqrt ht.le]
  have h := Real.rpow_add ht (α-2) 1
  rw [Real.rpow_one, show α-2+1 = α-1 by ring] at h
  rw [h, show 2*(k+1) = 2*k+2 by omega, pow_add]
  ring

theorem power_identity (k : ℕ) {α : ℝ} (hα : 0 < α) (x : ℝ) :
    x^(2*k) * (x^2)^α = |x|^(2*((k:ℝ)+α)) := by
  by_cases hx : x = 0
  · subst x
    rw [abs_zero, Real.zero_rpow (by positivity : 2*((k:ℝ)+α) ≠ 0)]
    simp [Real.zero_rpow hα.ne']
  · have he : x^(2*k) = |x|^((2*k:ℕ):ℝ) := by
      rw [Real.rpow_natCast, ← abs_pow, abs_of_nonneg ((even_two_mul k).pow_nonneg x)]
    have he2 : x^2 = |x|^(2:ℝ) := by rw [Real.rpow_two, sq_abs]
    rw [he, he2, ← Real.rpow_mul (abs_nonneg x), ← Real.rpow_add (abs_pos.mpr hx)]
    congr 1
    push_cast
    ring

theorem scalar_integral (k : ℕ) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) (x : ℝ) :
    (∫ t in Ioi 0, kern k α t x) = Cα α * |x|^(2*((k:ℝ)+α)) := by
  unfold kern Cα
  rw [integral_const_mul, Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const hα (sq_nonneg x),
    ← mul_assoc, power_identity k hα.1 x]
  ring

theorem scalar_lintegral (k : ℕ) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) (x : ℝ) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (kern k α t x)) =
      ENNReal.ofReal (Cα α * |x|^(2*((k:ℝ)+α))) := by
  rw [← scalar_integral k hα x]
  refine (ofReal_integral_eq_lintegral_ofReal ?_ ?_).symm
  · exact (Real.integrableOn_rpowIntegrand₀₁_Ioi hα (sq_nonneg x)).const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact kern_nonneg k hα (le_of_lt ht) x

/-- Tonelli for the positive kernel (no integrability needed). -/
theorem tonelli (k : ℕ) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) (ρ : Measure ℝ) [SFinite ρ] :
    (∫⁻ t in Ioi 0, ∫⁻ x, ENNReal.ofReal (kern k α t x) ∂ρ) =
      ENNReal.ofReal (Cα α) * ∫⁻ x, ENNReal.ofReal (|x|^(2*((k:ℝ)+α))) ∂ρ := by
  rw [lintegral_lintegral_swap]
  · simp_rw [scalar_lintegral k hα, ENNReal.ofReal_mul (Cα_pos hα).le]
    rw [lintegral_const_mul]
    exact (by fun_prop : Measurable fun x : ℝ => |x|^(2*((k:ℝ)+α))).ennreal_ofReal
  · exact ((measurable_kern k α).ennreal_ofReal).aemeasurable

/-- `P_ρ(t) = ∫ x^{2k} r_α(t,x²) dρ(x)`. -/
def P (k : ℕ) (α : ℝ) (ρ : Measure ℝ) (t : ℝ) : ℝ := ∫ x, kern k α t x ∂ρ

theorem kern_integrable (k : ℕ) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) {ρ : Measure ℝ}
    (hm : Integrable (fun x : ℝ => x^(2*k)) ρ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => kern k α t x) ρ :=
  Integrable.mono' (hm.const_mul (t^(α-1))) (measurable_kern_right k α t).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (kern_nonneg k hα ht x)]
      exact kern_le k hα ht x)

theorem P_nonneg (k : ℕ) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) (ρ : Measure ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ P k α ρ t := integral_nonneg (fun x => kern_nonneg k hα ht x)

theorem P_le (k : ℕ) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) {ρ : Measure ℝ}
    (hm : Integrable (fun x : ℝ => x^(2*k)) ρ) {t : ℝ} (ht : 0 ≤ t) :
    P k α ρ t ≤ t^(α-1) * ∫ x, x^(2*k) ∂ρ := by
  rw [← integral_const_mul]
  exact integral_mono (kern_integrable k hα hm ht) (hm.const_mul _) (fun x => kern_le k hα ht x)

theorem P_eq_K (k : ℕ) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) (ρ : Measure ℝ) {t : ℝ} (ht : 0 < t) :
    P k α ρ t = t^(α-2) * ∫ x, K k (Real.sqrt t) x ∂ρ := by
  unfold P
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun x => kern_eq_K k hα ht x)

theorem lintegral_kern (k : ℕ) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) {ρ : Measure ℝ}
    (hm : Integrable (fun x : ℝ => x^(2*k)) ρ) {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ x, ENNReal.ofReal (kern k α t x) ∂ρ) = ENNReal.ofReal (P k α ρ t) :=
  (ofReal_integral_eq_lintegral_ofReal (kern_integrable k hα hm ht)
    (Eventually.of_forall fun x => kern_nonneg k hα ht x)).symm

theorem P_measurable (k : ℕ) (α : ℝ) (ρ : Measure ℝ) [SFinite ρ] :
    StronglyMeasurable (P k α ρ) :=
  StronglyMeasurable.integral_prod_right (f := kern k α) (measurable_kern k α).stronglyMeasurable

theorem key (k : ℕ) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) (ρ : Measure ℝ) [SFinite ρ]
    (hm : Integrable (fun x : ℝ => x^(2*k)) ρ) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (P k α ρ t)) =
      ENNReal.ofReal (Cα α) * ∫⁻ x, ENNReal.ofReal (|x|^(2*((k:ℝ)+α))) ∂ρ := by
  rw [← tonelli k hα ρ]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  exact (lintegral_kern k hα hm (le_of_lt ht)).symm

theorem finite_iff (k : ℕ) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) (ρ : Measure ℝ) [SFinite ρ]
    (hm : Integrable (fun x : ℝ => x^(2*k)) ρ) :
    (∫⁻ x, ENNReal.ofReal (|x|^(2*((k:ℝ)+α))) ∂ρ) ≠ ⊤ ↔ IntegrableOn (P k α ρ) (Ioi 0) := by
  have hC : ENNReal.ofReal (Cα α) ≠ 0 := by simpa using Cα_pos hα
  rw [IntegrableOn, ← lintegral_ofReal_ne_top_iff_integrable
    (P_measurable k α ρ).aestronglyMeasurable
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact P_nonneg k hα ρ (le_of_lt ht)),
    key k hα ρ hm]
  constructor
  · intro h; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h
  · intro h hb; rw [hb, ENNReal.mul_top hC] at h; exact h rfl

theorem integral_P (k : ℕ) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) (ρ : Measure ℝ) [SFinite ρ]
    (hm : Integrable (fun x : ℝ => x^(2*k)) ρ) (hP : IntegrableOn (P k α ρ) (Ioi 0)) :
    (∫ t in Ioi 0, P k α ρ t) = Cα α * ∫ x, |x|^(2*((k:ℝ)+α)) ∂ρ := by
  have hfin := (finite_iff k hα ρ hm).mpr hP
  have hmeas : AEStronglyMeasurable (fun x : ℝ => |x|^(2*((k:ℝ)+α))) ρ :=
    (by fun_prop : Measurable fun x : ℝ => |x|^(2*((k:ℝ)+α))).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[ρ] (fun x : ℝ => |x|^(2*((k:ℝ)+α))) :=
    Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg x) _
  have hint : Integrable (fun x : ℝ => |x|^(2*((k:ℝ)+α))) ρ :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas hnn).mp hfin
  have h1 := key k hα ρ hm
  rw [← ofReal_integral_eq_lintegral_ofReal hP
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact P_nonneg k hα ρ (le_of_lt ht)),
    ← ofReal_integral_eq_lintegral_ofReal hint hnn, ← ENNReal.ofReal_mul (Cα_pos hα).le] at h1
  exact (ENNReal.ofReal_eq_ofReal_iff (setIntegral_nonneg measurableSet_Ioi
    (fun t ht => P_nonneg k hα ρ (le_of_lt ht)))
    (mul_nonneg (Cα_pos hα).le (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg x) _))).mp h1

/-- **The fractional criterion.** For two s-finite measures with finite `2k` moments whose
kernel difference is integrable on `(0,∞)`, the `2(k+α)` moments are finite simultaneously, and
then their difference is the absolutely convergent correction `∫ (P_μ - P_ν) / C_α`. -/
theorem criterion (k : ℕ) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (hμ : Integrable (fun x : ℝ => x^(2*k)) μ) (hν : Integrable (fun x : ℝ => x^(2*k)) ν)
    (hE : IntegrableOn (fun t => P k α μ t - P k α ν t) (Ioi 0)) :
    ((∫⁻ x, ENNReal.ofReal (|x|^(2*((k:ℝ)+α))) ∂μ) ≠ ⊤ ↔
        (∫⁻ x, ENNReal.ofReal (|x|^(2*((k:ℝ)+α))) ∂ν) ≠ ⊤) ∧
    ((∫⁻ x, ENNReal.ofReal (|x|^(2*((k:ℝ)+α))) ∂ν) ≠ ⊤ →
      (∫ x, |x|^(2*((k:ℝ)+α)) ∂μ) =
        (∫ x, |x|^(2*((k:ℝ)+α)) ∂ν) + (∫ t in Ioi 0, (P k α μ t - P k α ν t)) / Cα α) := by
  have hiff : IntegrableOn (P k α μ) (Ioi 0) ↔ IntegrableOn (P k α ν) (Ioi 0) := by
    constructor
    · intro h
      exact (h.sub hE).congr_fun (fun t _ => by simp) measurableSet_Ioi
    · intro h
      exact (h.add hE).congr_fun (fun t _ => by simp) measurableSet_Ioi
  refine ⟨by rw [finite_iff k hα μ hμ, finite_iff k hα ν hν]; exact hiff, fun hfin => ?_⟩
  have hPν := (finite_iff k hα ν hν).mp hfin
  have hPμ := hiff.mpr hPν
  have h1 := integral_P k hα μ hμ hPμ
  have h2 := integral_P k hα ν hν hPν
  have h3 : (∫ t in Ioi 0, P k α μ t) = (∫ t in Ioi 0, P k α ν t) +
      ∫ t in Ioi 0, (P k α μ t - P k α ν t) := by
    rw [← integral_add hPν hE]; simp only [add_sub_cancel]
  have hC := (Cα_pos hα).ne'
  rw [h1, h2] at h3
  field_simp
  linarith

/-! ### The two-regime majorant -/

/-- `A t^{α-1}` for `t ≤ T`, `B t^{α-2}` for `t > T`. -/
def majorant (α A B T : ℝ) (t : ℝ) : ℝ := if t ≤ T then A * t^(α-1) else B * t^(α-2)

theorem majorant_integrable {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) (A B : ℝ) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (majorant α A B T) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi hT.le]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun t : ℝ => A * t^(α-1)) (Ioc 0 T) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith [hα.1]))).const_mul A
    exact IntegrableOn.congr_fun h1 (fun t ht => by simp [majorant, ht.2]) measurableSet_Ioc
  · have h2 : IntegrableOn (fun t : ℝ => B * t^(α-2)) (Ioi T) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith [hα.2]) hT).const_mul B
    exact IntegrableOn.congr_fun h2
      (fun t ht => by simp [majorant, not_le.mpr (show T < t from ht)]) measurableSet_Ioi

theorem le_majorant {α A B T : ℝ} {f : ℝ → ℝ} {t : ℝ}
    (h1 : |f t| ≤ A * t^(α-1)) (h2 : T < t → |f t| ≤ B * t^(α-2)) :
    ‖f t‖ ≤ majorant α A B T t := by
  rw [Real.norm_eq_abs]; unfold majorant
  split_ifs with h
  · exact h1
  · exact h2 (lt_of_not_ge h)

/-- `|P_μ - P_ν| ≤ t^{α-1}(m_μ + m_ν)`. -/
theorem abs_P_sub_le (k : ℕ) {α : ℝ} (hα : α ∈ Ioo (0:ℝ) 1) {μ ν : Measure ℝ}
    (hμ : Integrable (fun x : ℝ => x^(2*k)) μ) (hν : Integrable (fun x : ℝ => x^(2*k)) ν)
    {t : ℝ} (ht : 0 ≤ t) :
    |P k α μ t - P k α ν t| ≤ ((∫ x, x^(2*k) ∂μ) + ∫ x, x^(2*k) ∂ν) * t^(α-1) := by
  have a1 := P_nonneg k hα μ ht
  have a2 := P_nonneg k hα ν ht
  have b1 := P_le k hα hμ ht
  have b2 := P_le k hα hν ht
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Elementary weights -/

theorem one_add_rpow_le (a q : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q) :
    (1 + a)^q ≤ 2^q * (1 + a^q) := by
  rcases le_total a 1 with h | h
  · have h1 : (1 + a)^q ≤ 2^q := Real.rpow_le_rpow (by linarith) (by linarith) hq
    have h2 : 0 ≤ 2^q * a^q := by positivity
    nlinarith
  · have h1 : (1 + a)^q ≤ (2 * a)^q := Real.rpow_le_rpow (by linarith) (by linarith) hq
    rw [Real.mul_rpow (by norm_num) ha] at h1
    have h2 : (0:ℝ) ≤ 2^q := by positivity
    nlinarith

theorem tsum_ofReal_ne_top_iff {ι : Type*} (f : ι → ℝ) (h : ∀ n, 0 ≤ f n) :
    (∑' n, ENNReal.ofReal (f n)) ≠ ⊤ ↔ Summable f := by
  constructor
  · intro hf
    have : Summable (fun n => (ENNReal.ofReal (f n)).toReal) := ENNReal.summable_toReal hf
    simpa [ENNReal.toReal_ofReal (h _)] using this
  · intro hf
    rw [← ENNReal.ofReal_tsum_of_nonneg h hf]; exact ENNReal.ofReal_ne_top

/-! ### Tails of nonnegative sequences -/

theorem tendsto_tsum_zero_of_tails {ι : Type*} (c : ℕ → ι → ℝ) (hc0 : ∀ j n, 0 ≤ c j n)
    (hcs : ∀ j, Summable (c j)) (hpt : ∀ n, Tendsto (fun j => c j n) atTop (𝓝 0))
    (htail : ∀ ε > 0, ∃ F : Finset ι, ∀ᶠ j in atTop, ∑' n : {n // n ∉ F}, c j n ≤ ε) :
    Tendsto (fun j => ∑' n, c j n) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨F, hF⟩ := htail (ε/2) (by positivity)
  have hfin : Tendsto (fun j => ∑ n ∈ F, c j n) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum F (fun n _ => hpt n)
  have hfe := (hfin.eventually (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity)))
  obtain ⟨N, hN⟩ := (hF.and hfe).exists_forall_of_atTop
  refine ⟨N, fun j hj => ?_⟩
  obtain ⟨h1, h2⟩ := hN j hj
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg (hc0 j)),
    ← (hcs j).sum_add_tsum_subtype_compl F]
  linarith

/-- Scheffé form: coordinatewise convergence and convergence of the sums give uniformly small
tails. -/
theorem tails_of_tsum_tendsto {ι : Type*} (a : ℕ → ι → ℝ) (b : ι → ℝ)
    (has : ∀ j, Summable (a j)) (hbs : Summable b)
    (hpt : ∀ n, Tendsto (fun j => a j n) atTop (𝓝 (b n)))
    (hsum : Tendsto (fun j => ∑' n, a j n) atTop (𝓝 (∑' n, b n))) :
    ∀ ε > 0, ∃ F : Finset ι, ∀ᶠ j in atTop, ∑' n : {n // n ∉ F}, a j n ≤ ε := by
  intro ε hε
  have hb := (tendsto_tsum_compl_atTop_zero b).eventually
    (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity))
  obtain ⟨F, hF⟩ := hb.exists
  refine ⟨F, ?_⟩
  have hfin : Tendsto (fun j => ∑ n ∈ F, a j n) atTop (𝓝 (∑ n ∈ F, b n)) :=
    tendsto_finsetSum F (fun n _ => hpt n)
  have htl : Tendsto (fun j => ∑' n : {n // n ∉ F}, a j n) atTop
      (𝓝 (∑' n : {n // n ∉ F}, b n)) := by
    have e1 : (fun j => ∑' n : {n // n ∉ F}, a j n) =
        fun j => (∑' n, a j n) - ∑ n ∈ F, a j n := by
      funext j; rw [← (has j).sum_add_tsum_subtype_compl F]; ring
    have e2 : (∑' n : {n // n ∉ F}, b n) = (∑' n, b n) - ∑ n ∈ F, b n := by
      rw [← hbs.sum_add_tsum_subtype_compl F]; ring
    rw [e1, e2]; exact hsum.sub hfin
  filter_upwards [htl.eventually (gt_mem_nhds (show ∑' n : {n // n ∉ F}, b n < ε by linarith))]
    with j hj using hj.le

/-! ### Tails of weakly convergent finite measures on `ℝ` -/

/-- Continuous cutoff: `1` on `|x| ≤ T`, `0` on `|x| ≥ T+1`. -/
def cut (T x : ℝ) : ℝ := max 0 (min 1 (T + 1 - |x|))

theorem continuous_cut (T : ℝ) : Continuous (cut T) := by unfold cut; fun_prop
theorem cut_nonneg (T x : ℝ) : 0 ≤ cut T x := le_max_left _ _
theorem cut_le_one (T x : ℝ) : cut T x ≤ 1 := max_le zero_le_one (min_le_left _ _)
theorem cut_eq_one {T x : ℝ} (h : |x| ≤ T) : cut T x = 1 := by
  unfold cut; rw [min_eq_left (by linarith)]; simp
theorem cut_eq_zero {T x : ℝ} (h : T + 1 ≤ |x|) : cut T x = 0 := by
  unfold cut; apply le_antisymm _ (le_max_left _ _)
  exact max_le le_rfl (le_trans (min_le_right _ _) (by linarith))

theorem cut_support (f : ℝ → ℝ) (T : ℝ) : HasCompactSupport (fun x => f x * cut T x) :=
  HasCompactSupport.intro (isCompact_closedBall (0:ℝ) (T+1)) (fun x hx => by
    have : T + 1 < |x| := by simpa [Metric.mem_closedBall, Real.dist_eq] using hx
    simp [cut_eq_zero this.le])

/-- The truncation `f · cut_T` as a bounded continuous test function. -/
def truncBCF (f : ℝ → ℝ) (hf : Continuous f) (T : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => f x * cut T x)
    (hf.mul (continuous_cut T))
    (Classical.choose ((hf.mul (continuous_cut T)).bounded_above_of_compact_support
      (cut_support f T)))
    (Classical.choose_spec ((hf.mul (continuous_cut T)).bounded_above_of_compact_support
      (cut_support f T)))

theorem truncBCF_apply (f : ℝ → ℝ) (hf : Continuous f) (T x : ℝ) :
    truncBCF f hf T x = f x * cut T x := rfl

theorem far_tendsto (μ : Measure ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (hfμ : Integrable f μ) :
    Tendsto (fun T : ℕ => ∫ x, f x * (1 - cut T x) ∂μ) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun T : ℕ => fun x => f x * (1 - cut T x)) (f := fun _ => 0) (fun x => ‖f x‖)
    (fun T => (hf.mul (continuous_const.sub (continuous_cut T))).aestronglyMeasurable)
    hfμ.norm
    (fun T => Eventually.of_forall fun x => by
      rw [norm_mul]
      have h0 := cut_nonneg (T:ℝ) x; have h1 := cut_le_one (T:ℝ) x
      have : ‖1 - cut T x‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
      nlinarith [norm_nonneg (f x)])
    (Eventually.of_forall fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ⌈|x|⌉₊] with T hT
      have : |x| ≤ (T:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hT)
      simp [cut_eq_one this])
  simpa using h

theorem measurableSet_tail (T : ℝ) : MeasurableSet {x : ℝ | T < |x|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

theorem integrable_mul_cut {ν : Measure ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hν : Integrable f ν)
    (T : ℝ) : Integrable (fun x => f x * cut T x) ν :=
  hν.norm.mono' (hf.mul (continuous_cut T)).aestronglyMeasurable (Eventually.of_forall fun x => by
    rw [norm_mul, Real.norm_eq_abs (cut T x), abs_of_nonneg (cut_nonneg T x)]
    exact mul_le_of_le_one_right (norm_nonneg _) (cut_le_one T x))

theorem far_eq {ν : Measure ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hν : Integrable f ν) (T : ℝ) :
    (∫ x, f x * (1 - cut T x) ∂ν) = (∫ x, f x ∂ν) - ∫ x, f x * cut T x ∂ν := by
  rw [← integral_sub hν (integrable_mul_cut hf hν T)]; congr 1; funext x; ring

theorem tail_le_far {ν : Measure ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hν : Integrable f ν) (T : ℝ) :
    (∫ x in {x | T + 1 < |x|}, f x ∂ν) ≤ ∫ x, f x * (1 - cut T x) ∂ν := by
  rw [← integral_indicator (measurableSet_tail (T+1))]
  refine integral_mono (hν.indicator (measurableSet_tail (T+1)))
    (hν.sub (integrable_mul_cut hf hν T) |>.congr
      (Eventually.of_forall fun x => by simp; ring)) (fun x => ?_)
  by_cases hx : x ∈ {x : ℝ | T + 1 < |x|}
  · rw [indicator_of_mem hx, cut_eq_zero (le_of_lt hx)]; simp
  · rw [indicator_of_notMem hx]
    exact mul_nonneg (hf0 x) (by linarith [cut_le_one T x])

theorem far_le_tail {ν : Measure ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hν : Integrable f ν) (T : ℝ) :
    (∫ x, f x * (1 - cut T x) ∂ν) ≤ ∫ x in {x | T < |x|}, f x ∂ν := by
  rw [← integral_indicator (measurableSet_tail T)]
  refine integral_mono
    (hν.sub (integrable_mul_cut hf hν T) |>.congr
      (Eventually.of_forall fun x => by simp; ring))
    (hν.indicator (measurableSet_tail T)) (fun x => ?_)
  by_cases hx : x ∈ {x : ℝ | T < |x|}
  · rw [indicator_of_mem hx]
    exact mul_le_of_le_one_right (hf0 x) (by linarith [cut_nonneg T x])
  · rw [indicator_of_notMem hx, cut_eq_one (not_lt.mp hx)]; simp

/-- Weak convergence plus convergence of `∫ f` give uniformly small `f`-tails. -/
theorem uniform_tail (μs : ℕ → Measure ℝ) (μ : Measure ℝ)
    (hw : ∀ g : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, g x ∂(μs j)) atTop (𝓝 (∫ x, g x ∂μ)))
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : ∀ j, Integrable f (μs j)) (hfμ : Integrable f μ)
    (hlim : Tendsto (fun j => ∫ x, f x ∂(μs j)) atTop (𝓝 (∫ x, f x ∂μ))) :
    ∀ ε > 0, ∃ T : ℝ, ∀ᶠ j in atTop, ∫ x in {x | T < |x|}, f x ∂(μs j) ≤ ε := by
  intro ε hε
  obtain ⟨T, hT⟩ := ((far_tendsto μ f hf hfμ).eventually
    (gt_mem_nhds (show (0:ℝ) < ε by positivity))).exists
  refine ⟨(T:ℝ) + 1, ?_⟩
  have hg := hw (truncBCF f hf T)
  simp only [truncBCF_apply] at hg
  have hfar : Tendsto (fun j => ∫ x, f x * (1 - cut T x) ∂(μs j)) atTop
      (𝓝 (∫ x, f x * (1 - cut T x) ∂μ)) := by
    rw [far_eq hf hfμ]
    simp_rw [far_eq hf (hfi _)]
    exact hlim.sub hg
  filter_upwards [hfar.eventually (gt_mem_nhds hT)] with j hj
  exact (tail_le_far hf hf0 (hfi j) T).trans hj.le

/-- Weak convergence plus uniformly small `f`-tails give convergence of `∫ f`. -/
theorem integral_tendsto_of_tail (μs : ℕ → Measure ℝ) (μ : Measure ℝ)
    (hw : ∀ g : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, g x ∂(μs j)) atTop (𝓝 (∫ x, g x ∂μ)))
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : ∀ j, Integrable f (μs j)) (hfμ : Integrable f μ)
    (htail : ∀ ε > 0, ∃ T : ℝ, ∀ᶠ j in atTop, ∫ x in {x | T < |x|}, f x ∂(μs j) ≤ ε) :
    Tendsto (fun j => ∫ x, f x ∂(μs j)) atTop (𝓝 (∫ x, f x ∂μ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := htail (ε/4) (by positivity)
  obtain ⟨T, hT⟩ := ((far_tendsto μ f hf hfμ).eventually
    (gt_mem_nhds (show (0:ℝ) < ε/4 by positivity)) |>.and (eventually_ge_atTop ⌈T₁⌉₊)).exists
  have hTT : T₁ ≤ (T:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hT.2)
  have hg := (hw (truncBCF f hf T))
  simp only [truncBCF_apply] at hg
  obtain ⟨N, hN⟩ := ((hg.eventually (Metric.ball_mem_nhds _ (show (0:ℝ) < ε/4 by positivity))).and
    hT₁).exists_forall_of_atTop
  refine ⟨N, fun j hj => ?_⟩
  obtain ⟨h1, h2⟩ := hN j hj
  rw [Real.dist_eq] at h1
  have hfj : 0 ≤ ∫ x, f x * (1 - cut T x) ∂(μs j) := integral_nonneg fun x =>
    mul_nonneg (hf0 x) (by linarith [cut_le_one (T:ℝ) x])
  have hfm : 0 ≤ ∫ x, f x * (1 - cut T x) ∂μ := integral_nonneg fun x =>
    mul_nonneg (hf0 x) (by linarith [cut_le_one (T:ℝ) x])
  have hmono : (∫ x in {x | (T:ℝ) < |x|}, f x ∂(μs j)) ≤ ∫ x in {x | T₁ < |x|}, f x ∂(μs j) :=
    setIntegral_mono_set (hfi j).integrableOn
      (Eventually.of_forall fun x => hf0 x)
      (Eventually.of_forall fun x (hx : (T:ℝ) < |x|) =>
        (show T₁ < |x| from lt_of_le_of_lt hTT hx))
  have hj1 := (far_le_tail hf hf0 (hfi j) T).trans (hmono.trans h2)
  have e1 := far_eq hf (hfi j) T
  have e2 := far_eq hf hfμ T
  rw [Real.dist_eq, abs_lt]
  have := hT.1
  constructor <;> linarith [abs_lt.mp h1]

end QuantumNLS.Reg013OAnalysis

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg013OAnalysis." ||
        n.toString.startsWith "_private.QuantumNLS.Reg013OAnalysis." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Reg013OAnalysis aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
