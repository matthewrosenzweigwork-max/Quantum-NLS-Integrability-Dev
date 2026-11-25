import QuantumNLS.Ext025B9Bridges
import QuantumNLS.Ext025B7SpectralCompression

/-!
# EXT-025 layer A (completion), GP-07 support: spectral-integral inner products

Support module for `Ext025LGP07Full` (frozen sources untouched).  Built ON the frozen
spectral-calculus modules `Ext025B8BorelCalculus`, `Ext025B8BorelLaws`, `Ext025B9Bridges`
(arbitrary projection-valued measure `P`, bounded Borel integral `bounded P f ..`, maximal
unbounded integral `operator P g ..` with exact domain `domain P g`).  New facts, all for an
ARBITRARY `P : ProjectionMeasure E` (no atomicity, no countable-multiplicity hypothesis):

* `simple_inner`, `bounded_inner`: `⟪x, (∫ f dP) x⟫ = ∫ f d(μ_x)` for simple / bounded Borel `f`,
  where `μ_x = scalarMeasure P x`.
* `operator_inner`: the same for the maximal operator on its exact domain,
  `⟪x, (operator P g) x⟫ = ∫ g dμ_x` for `x ∈ domain P g`.
* `support_ge`: if the identity-symbol operator `T = operator P (t ↦ t)` satisfies
  `b ‖x‖² ≤ Re ⟪x, T x⟫` on its domain, then every scalar spectral measure `μ_x` vanishes on
  `(-∞, b)`.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
open MeasureTheory Filter Topology Function
open scoped InnerProductSpace ENNReal LinearPMap

namespace QuantumNLS.Ext025L.Spec
open BetheChargeResolution QuantumNLS.Ext025B6PVM QuantumNLS.Ext025B8SimpleCalculus
  QuantumNLS.Ext025B8BorelCalculus QuantumNLS.Ext025B8BorelLaws
  QuantumNLS.Ext025B9MaximalIntegral QuantumNLS.Ext025B9IntegralDomain
  QuantumNLS.Ext025B9IntegralCutoff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (P : ProjectionMeasure E)

/-- The identity symbol, as a complex valued Borel function. -/
def idSym : ℝ → ℂ := fun t => (t : ℂ)

theorem idSym_meas : Measurable idSym := Complex.measurable_ofReal

theorem simple_inner (f : SimpleFunc ℝ ℂ) (x : E) :
    ⟪x, simple P f x⟫_ℂ = ∫ t, f t ∂scalarMeasure P x := by
  classical
  have hfi : Integrable f (scalarMeasure P x) := SimpleFunc.integrable_of_isFiniteMeasure f
  rw [SimpleFunc.integral_eq_sum f hfi]
  simp only [simple, sum_apply, smul_apply, inner_sum, inner_smul_right]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [inner_self_project P _ (f.measurableSet_fiber z), measureReal_def,
    scalarMeasure_apply P x _ (f.measurableSet_fiber z), ENNReal.toReal_ofReal (sq_nonneg _),
    Complex.real_smul, mul_comm]

theorem bounded_inner (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t, ‖f t‖ ≤ C) (x : E) :
    ⟪x, bounded P f hf C hC hb x⟫_ℂ = ∫ t, f t ∂scalarMeasure P x := by
  have hl := Filter.Tendsto.inner (𝕜 := ℂ) (tendsto_const_nhds (x := x)) (approx_bounded P f hf C hC hb x)
  have hr : Tendsto (fun n => ∫ t, approx f hf n t ∂scalarMeasure P x) atTop
      (𝓝 (∫ t, f t ∂scalarMeasure P x)) :=
    tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (approx f hf n).measurable.aestronglyMeasurable) (integrable_const C)
      (fun n => Eventually.of_forall fun t => approx_bound f hf C hC hb n t)
      (Eventually.of_forall fun t => approx_pointwise f hf t)
  exact tendsto_nhds_unique hl (hr.congr fun n => (simple_inner P (approx f hf n) x).symm)

theorem operator_inner (g : ℝ → ℂ) (hg : Measurable g) (x : E) (hx : x ∈ domain P g) :
    ⟪x, operator P g hg ⟨x, hx⟩⟫_ℂ = ∫ t, g t ∂scalarMeasure P x := by
  let s : ℕ → Set ℝ := fun n => {t | ‖g t‖ ≤ (n : ℝ)}
  have hs : ∀ n, MeasurableSet (s n) := fun n => measurableSet_le hg.norm measurable_const
  have hmono : Monotone s := fun m n hmn t ht =>
    (show ‖g t‖ ≤ (m : ℝ) from ht).trans (Nat.cast_le.mpr hmn)
  have hu : ⋃ n, s n = Set.univ := windows_exhaust g
  set z := operator P g hg ⟨x, hx⟩ with hz
  have hmem : MemLp g 2 (scalarMeasure P x) := (mem_domain P g hg x).mp hx
  have hint : Integrable g (scalarMeasure P x) := hmem.integrable (by norm_num)
  have h1 : ∀ n, ⟪x, P.toFun (s n) z⟫_ℂ = ∫ t, (s n).indicator g t ∂scalarMeasure P x := by
    intro n
    have hb' : ∀ t, ‖(s n).indicator g t‖ ≤ (n : ℝ) := by
      intro t
      by_cases ht : t ∈ s n
      · rw [Set.indicator_of_mem ht]; exact ht
      · rw [Set.indicator_of_notMem ht, norm_zero]; exact Nat.cast_nonneg n
    have hw := window_action P g hg (s n) (hs n) n (Nat.cast_nonneg n) (fun t ht => ht) x
    have hc := projection_commutes P g hg (s n) (hs n) x hx
    have : P.toFun (s n) z = bounded P ((s n).indicator g) (hg.indicator (hs n)) n
        (Nat.cast_nonneg n) hb' x := by
      rw [hz, ← hc]
      exact hw
    rw [this, bounded_inner]
  have hl := Filter.Tendsto.inner (𝕜 := ℂ) (tendsto_const_nhds (x := x))
    (Ext025B7SpectralCompression.exhaustion_strong P s hs hmono hu z)
  have hr : Tendsto (fun n => ∫ t, (s n).indicator g t ∂scalarMeasure P x) atTop
      (𝓝 (∫ t, g t ∂scalarMeasure P x)) := by
    refine tendsto_integral_of_dominated_convergence (fun t => ‖g t‖)
      (fun n => (hg.indicator (hs n)).aestronglyMeasurable) hint.norm
      (fun n => Eventually.of_forall fun t => norm_indicator_le_norm_self g t) ?_
    refine Eventually.of_forall fun t => ?_
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈‖g t‖⌉₊) fun n hn => ?_
    have : t ∈ s n := (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
    exact Set.indicator_of_mem this g
  exact tendsto_nhds_unique hl (hr.congr fun n => (h1 n).symm)

/-- Lower bound of the identity operator on its domain forces the support to lie in `[b, ∞)`. -/
theorem support_ge (b : ℝ)
    (hlb : ∀ (x : E) (hx : x ∈ domain P idSym),
      b * ‖x‖ ^ 2 ≤ (⟪x, operator P idSym idSym_meas ⟨x, hx⟩⟫_ℂ).re) (x : E) :
    scalarMeasure P x (Set.Iio b) = 0 := by
  have hcover : Set.Iio b = ⋃ (n : ℕ) (m : ℕ), Set.Icc (-(n : ℝ)) (b - 1 / ((m : ℝ) + 1)) := by
    ext t
    simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Icc]
    constructor
    · intro ht
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr ht)
      obtain ⟨n, hn⟩ := exists_nat_ge (-t)
      exact ⟨n, m, by linarith, by linarith⟩
    · rintro ⟨n, m, -, h2⟩
      have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      linarith
  rw [hcover]
  refine measure_iUnion_null fun n => measure_iUnion_null fun m => ?_
  set δ : ℝ := 1 / ((m : ℝ) + 1) with hδ
  have hδpos : 0 < δ := by positivity
  set s : Set ℝ := Set.Icc (-(n : ℝ)) (b - δ) with hsdef
  have hs : MeasurableSet s := measurableSet_Icc
  set y : E := P.toFun s x with hy
  have hbd : ∀ t ∈ s, ‖idSym t‖ ≤ (n : ℝ) + |b| + 1 := by
    intro t ht
    have h1 : -(n : ℝ) ≤ t := ht.1
    have h2 : t ≤ b - δ := ht.2
    have h3 : |b| ≥ b := le_abs_self b
    have h4 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h5 : |b| ≥ 0 := abs_nonneg b
    change ‖(t : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith
  have hyd : y ∈ domain P idSym :=
    bounded_window_mem P idSym idSym_meas s hs ((n : ℝ) + |b| + 1) hbd x
  have hlbn := hlb y hyd
  rw [operator_inner P idSym idSym_meas y hyd] at hlbn
  have hν : scalarMeasure P y = (scalarMeasure P x).restrict s := scalarMeasure_project P s hs x
  have hmemy : MemLp idSym 2 (scalarMeasure P y) := (mem_domain P idSym idSym_meas y).mp hyd
  have hinty : Integrable idSym (scalarMeasure P y) := hmemy.integrable (by norm_num)
  have hre : (∫ t, idSym t ∂scalarMeasure P y).re = ∫ t, t ∂scalarMeasure P y := by
    have : (∫ t, idSym t ∂scalarMeasure P y) = ((∫ t, t ∂scalarMeasure P y : ℝ) : ℂ) :=
      integral_ofReal
    rw [this, Complex.ofReal_re]
  rw [hre] at hlbn
  have hreal : Integrable (fun t : ℝ => t) (scalarMeasure P y) := by
    have := hinty.re
    simpa [idSym] using this
  have hmono : ∫ t, t ∂scalarMeasure P y ≤ ∫ _t, (b - δ) ∂scalarMeasure P y := by
    refine integral_mono_ae hreal (integrable_const _) ?_
    rw [hν]
    filter_upwards [ae_restrict_mem hs] with t ht using ht.2
  have hconst : ∫ _t, (b - δ) ∂scalarMeasure P y = (b - δ) * ‖y‖ ^ 2 := by
    rw [integral_const, measureReal_def, scalarMeasure_univ, ENNReal.toReal_ofReal (sq_nonneg _),
      smul_eq_mul, mul_comm]
  have hfin : b * ‖y‖ ^ 2 ≤ (b - δ) * ‖y‖ ^ 2 := hlbn.trans (hmono.trans hconst.le)
  have hy0 : ‖y‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖y‖]
  rw [scalarMeasure_apply P x s hs]
  rw [← hy, hy0, ENNReal.ofReal_zero]

end QuantumNLS.Ext025L.Spec

#print axioms QuantumNLS.Ext025L.Spec.simple_inner
#print axioms QuantumNLS.Ext025L.Spec.bounded_inner
#print axioms QuantumNLS.Ext025L.Spec.operator_inner
#print axioms QuantumNLS.Ext025L.Spec.support_ge
