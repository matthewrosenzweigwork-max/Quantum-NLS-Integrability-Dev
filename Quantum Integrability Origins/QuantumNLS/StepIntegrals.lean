import Mathlib
import QuantumNLS.GLowerBound
import QuantumNLS.FiniteResponse

/-!
# R-8F7E0394 (`CC:F03:deterministic`), stage (G), part 4: step functions and the finite sums

Source (F03.tex, proof of `CC:F03:deterministic`): for `v ∈ V_N` (constant on the `N` equal cells of `(0,1)`),
"The same-cell numerator vanishes. Summing over pairs of distinct cells gives `𝒥_N(v) = (1/2N) vᵀ B_N v − (1/N) (q^{(N)})ᵀ v`."

Here the step function `stepF N a` (value `a_i` on the `i`-th cell, `idx N t = ⌊N t⌋`) is related to the finite sums of `FiniteResponse`:
* `norm_sq_step`: `‖stepL2 a‖² = L2N N a`;
* `inner_step`: `⟨stepL2 q, stepL2 v⟩ = ipN N q v`;
* `ENint_step`: `ENint c (stepF N q) (stepF N v) = ofReal (EN N c q v)` (the double integral equals the finite double sum);
* `JN_step`: `JN L κ N q v = (L/2)‖stepL2 v‖² + (κ/2)(ENint ..).toReal − ⟨stepL2 q, stepL2 v⟩`.
The proof pushes `uI` forward by `idx N` to the uniform measure `muN N` on `{0..N-1}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace QuantumNLS.StepIntegrals

open QuantumNLS.BulkResponseRiesz (mu2 inner_eq_integral ofReal_norm_sq')
open QuantumNLS.QuantileForm (uI)
open QuantumNLS.BulkResponseForm (L2Unit)
open QuantumNLS.GLowerBound (ENint)
open QuantumNLS.FiniteResponse (L2N EN ipN dot JN)

/-- The cell index `⌊N t⌋`. -/
def idx (N : ℕ) (t : ℝ) : ℕ := ⌊(N : ℝ) * t⌋₊

theorem measurable_idx (N : ℕ) : Measurable (idx N) :=
  Nat.measurable_floor.comp (measurable_const.mul measurable_id)

/-- The uniform measure on `{0, …, N-1}`. -/
def muN (N : ℕ) : Measure ℕ := ∑ i ∈ Finset.range N, ((N : ℝ≥0∞)⁻¹) • Measure.dirac i

theorem lintegral_muN (N : ℕ) (h : ℕ → ℝ≥0∞) :
    ∫⁻ k, h k ∂muN N = ∑ j ∈ Finset.range N, (N : ℝ≥0∞)⁻¹ * h j := by
  unfold muN
  rw [lintegral_finset_sum_measure]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac]
  rfl

theorem map_idx {N : ℕ} (hN : 0 < N) : uI.map (idx N) = muN N := by
  refine Measure.ext_of_singleton fun k => ?_
  rw [Measure.map_apply (measurable_idx N) (measurableSet_singleton k)]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hd : ∀ i : ℕ, Measure.dirac i {k} = if i = k then 1 else 0 := fun i => by
    rw [Measure.dirac_apply' _ (measurableSet_singleton k)]
    simp [Set.indicator_apply, eq_comm]
  have hR : muN N {k} = if k < N then (N : ℝ≥0∞)⁻¹ else 0 := by
    simp only [muN, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul, hd]
    simp [mul_ite, Finset.sum_ite_eq', Finset.mem_range]
  rw [hR]
  show uI (idx N ⁻¹' {k}) = _
  unfold QuantumNLS.QuantileForm.uI QuantumNLS.BulkResponseForm.unitInterval
  rw [Measure.restrict_apply ((measurable_idx N) (measurableSet_singleton k))]
  by_cases hk : k < N
  · rw [if_pos hk]
    have hsub : idx N ⁻¹' {k} ∩ Ioo (0 : ℝ) 1 ⊆ Ico ((k : ℝ) / N) (((k : ℝ) + 1) / N) := by
      rintro t ⟨ht1, ht2⟩
      have h0 : 0 ≤ (N : ℝ) * t := mul_nonneg hN'.le ht2.1.le
      have := (Nat.floor_eq_iff h0).1 (show ⌊(N : ℝ) * t⌋₊ = k from ht1)
      exact ⟨by rw [div_le_iff₀ hN']; linarith, by rw [lt_div_iff₀ hN']; linarith⟩
    have hsup : Ioo ((k : ℝ) / N) (((k : ℝ) + 1) / N) ⊆ idx N ⁻¹' {k} ∩ Ioo (0 : ℝ) 1 := by
      rintro t ⟨h1, h2⟩
      rw [div_lt_iff₀ hN'] at h1
      rw [lt_div_iff₀ hN'] at h2
      have hk1 : ((k : ℝ) + 1) ≤ N := by exact_mod_cast hk
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      refine ⟨?_, ?_, ?_⟩
      · show ⌊(N : ℝ) * t⌋₊ = k
        rw [Nat.floor_eq_iff (by nlinarith)]
        constructor <;> linarith
      · by_contra hneg
        push_neg at hneg
        nlinarith
      · by_contra hneg
        push_neg at hneg
        nlinarith
    have hv : (N : ℝ≥0∞)⁻¹ = ENNReal.ofReal (((k : ℝ) + 1) / N - (k : ℝ) / N) := by
      rw [show ((k : ℝ) + 1) / N - (k : ℝ) / N = (N : ℝ)⁻¹ by field_simp; ring,
        ENNReal.ofReal_inv_of_pos hN', ENNReal.ofReal_natCast]
    refine le_antisymm ?_ ?_
    · calc volume (idx N ⁻¹' {k} ∩ Ioo (0 : ℝ) 1) ≤ volume (Ico ((k : ℝ) / N) (((k : ℝ) + 1) / N)) :=
          measure_mono hsub
        _ = _ := by rw [Real.volume_Ico, hv]
    · calc (N : ℝ≥0∞)⁻¹ = volume (Ioo ((k : ℝ) / N) (((k : ℝ) + 1) / N)) := by
            rw [Real.volume_Ioo, hv]
        _ ≤ _ := measure_mono hsup
  · rw [if_neg hk]
    have : idx N ⁻¹' {k} ∩ Ioo (0 : ℝ) 1 = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, h3⟩
      have h0 : 0 ≤ (N : ℝ) * t := mul_nonneg hN'.le h2.le
      have : ⌊(N : ℝ) * t⌋₊ < N := (Nat.floor_lt h0).2 (by nlinarith)
      exact hk (h1 ▸ this)
    rw [this, measure_empty]

theorem lintegral_idx {N : ℕ} (hN : 0 < N) (h : ℕ → ℝ≥0∞) :
    ∫⁻ t, h (idx N t) ∂uI = ∑ j ∈ Finset.range N, (N : ℝ≥0∞)⁻¹ * h j := by
  rw [← lintegral_map (measurable_of_countable h) (measurable_idx N), map_idx hN, lintegral_muN]

theorem lintegral_idx2 {N : ℕ} (hN : 0 < N) (g : ℕ → ℕ → ℝ≥0∞) :
    ∫⁻ p : ℝ × ℝ, g (idx N p.1) (idx N p.2) ∂mu2 =
      ∑ i ∈ Finset.range N, (N : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range N, (N : ℝ≥0∞)⁻¹ * g i j := by
  have hmap : (uI.prod uI).map (Prod.map (idx N) (idx N)) = (muN N).prod (muN N) := by
    rw [← Measure.map_prod_map uI uI (measurable_idx N) (measurable_idx N), map_idx hN]
  have hG : Measurable (fun z : ℕ × ℕ => g z.1 z.2) := measurable_of_countable _
  have hmeas : Measurable (Prod.map (idx N) (idx N)) := (measurable_idx N).prodMap (measurable_idx N)
  calc ∫⁻ p : ℝ × ℝ, g (idx N p.1) (idx N p.2) ∂mu2
      = ∫⁻ z : ℕ × ℕ, g z.1 z.2 ∂((uI.prod uI).map (Prod.map (idx N) (idx N))) :=
        (lintegral_map hG hmeas).symm
    _ = ∫⁻ z : ℕ × ℕ, g z.1 z.2 ∂((muN N).prod (muN N)) := by rw [hmap]
    _ = ∫⁻ i, ∫⁻ j, g i j ∂muN N ∂muN N := lintegral_prod _ hG.aemeasurable
    _ = _ := by
      simp_rw [lintegral_muN]

/-- `(1/N)`-weighted sums of `ofReal`. -/
theorem sum_ofReal {N : ℕ} (hN : 0 < N) (x : ℕ → ℝ) (hx : ∀ j, 0 ≤ x j) :
    ∑ j ∈ Finset.range N, (N : ℝ≥0∞)⁻¹ * ENNReal.ofReal (x j) =
      ENNReal.ofReal ((1 / (N : ℝ)) * ∑ j ∈ Finset.range N, x j) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hinv : (N : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / (N : ℝ)) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hN', ENNReal.ofReal_natCast]
  rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (by positivity) (hx j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hinv, ENNReal.ofReal_mul (by positivity)]

theorem sum_ofReal2 {N : ℕ} (hN : 0 < N) (y : ℕ → ℕ → ℝ) (hy : ∀ i j, 0 ≤ y i j) :
    ∑ i ∈ Finset.range N, (N : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range N, (N : ℝ≥0∞)⁻¹ * ENNReal.ofReal (y i j) =
      ENNReal.ofReal ((1 / (N : ℝ) ^ 2) * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, y i j) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ∀ i, ∑ j ∈ Finset.range N, (N : ℝ≥0∞)⁻¹ * ENNReal.ofReal (y i j) =
      ENNReal.ofReal ((1 / (N : ℝ)) * ∑ j ∈ Finset.range N, y i j) := fun i => sum_ofReal hN _ (hy i)
  simp_rw [h1]
  refine (sum_ofReal hN (fun i => (1 / (N : ℝ)) * ∑ j ∈ Finset.range N, y i j)
    (fun i => mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => hy i j))).trans ?_
  congr 1
  rw [← Finset.mul_sum, ← mul_assoc]
  congr 1
  ring

/-! ### Step functions -/

variable {N : ℕ}

/-- Extension by zero of a vector. -/
def ext (a : Fin N → ℝ) (k : ℕ) : ℝ := if h : k < N then a ⟨k, h⟩ else 0

/-- The step function with value `a_i` on the `i`-th cell. -/
def stepF (N : ℕ) (a : Fin N → ℝ) (t : ℝ) : ℝ := ext a (idx N t)

theorem measurable_stepF (a : Fin N → ℝ) : Measurable (stepF N a) :=
  (measurable_of_countable (ext a)).comp (measurable_idx N)

theorem ext_fin (a : Fin N → ℝ) (i : Fin N) : ext a (i : ℕ) = a i := by
  simp [ext]

theorem sum_ext (a : Fin N → ℝ) (f : ℝ → ℝ) :
    ∑ i ∈ Finset.range N, f (ext a i) = ∑ i : Fin N, f (a i) := by
  rw [Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => by rw [ext_fin]

theorem sum_ext4 (a b : Fin N → ℝ) (f : ℝ → ℝ → ℝ → ℝ → ℝ) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, f (ext a i) (ext a j) (ext b i) (ext b j) =
      ∑ i : Fin N, ∑ j : Fin N, f (a i) (a j) (b i) (b j) := by
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range]
  exact Finset.sum_congr rfl fun j _ => by rw [ext_fin, ext_fin, ext_fin, ext_fin]

theorem memLp_step (a : Fin N → ℝ) : MemLp (stepF N a) 2 uI := by
  refine MemLp.of_bound (measurable_stepF a).aestronglyMeasurable (∑ i, |a i|)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs]
  unfold stepF ext
  split_ifs with h
  · exact Finset.single_le_sum (f := fun i => |a i|) (fun i _ => abs_nonneg _) (Finset.mem_univ _)
  · simp only [abs_zero]; exact Finset.sum_nonneg fun i _ => abs_nonneg _

/-- The `L²(0,1)` element of a step function. -/
def stepL2 (a : Fin N → ℝ) : L2Unit := (memLp_step a).toLp _

theorem stepL2_ae (a : Fin N → ℝ) : (stepL2 a : ℝ → ℝ) =ᵐ[uI] stepF N a :=
  (memLp_step a).coeFn_toLp

theorem norm_sq_step (hN : 0 < N) (a : Fin N → ℝ) : ‖stepL2 a‖ ^ 2 = L2N N a := by
  have e : ∫⁻ t, ENNReal.ofReal (((stepL2 a : L2Unit) : ℝ → ℝ) t ^ 2) ∂uI =
      ∫⁻ t, ENNReal.ofReal (stepF N a t ^ 2) ∂uI :=
    lintegral_congr_ae (by filter_upwards [stepL2_ae a] with t h; rw [h])
  have h1 : ENNReal.ofReal (‖stepL2 a‖ ^ 2) = ENNReal.ofReal (L2N N a) := by
    rw [ofReal_norm_sq', e]
    refine (lintegral_idx hN (fun k => ENNReal.ofReal (ext a k ^ 2))).trans ?_
    refine (sum_ofReal hN (fun k => ext a k ^ 2) (fun k => sq_nonneg _)).trans ?_
    rw [show ∑ j ∈ Finset.range N, ext a j ^ 2 = ∑ i : Fin N, a i ^ 2 from sum_ext a (fun x => x ^ 2)]
    rfl
  have h2 : 0 ≤ L2N N a := by
    unfold L2N; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) h2).1 h1

theorem stepL2_add (a b : Fin N → ℝ) : stepL2 (a + b) = stepL2 a + stepL2 b := by
  apply Lp.ext
  filter_upwards [stepL2_ae (a + b), stepL2_ae a, stepL2_ae b, Lp.coeFn_add (stepL2 a) (stepL2 b)]
    with t h1 h2 h3 h4
  rw [h4, Pi.add_apply, h1, h2, h3]
  unfold stepF ext
  split_ifs <;> simp

theorem stepL2_sub (a b : Fin N → ℝ) : stepL2 (a - b) = stepL2 a - stepL2 b := by
  apply Lp.ext
  filter_upwards [stepL2_ae (a - b), stepL2_ae a, stepL2_ae b, Lp.coeFn_sub (stepL2 a) (stepL2 b)]
    with t h1 h2 h3 h4
  rw [h4, Pi.sub_apply, h1, h2, h3]
  unfold stepF ext
  split_ifs <;> simp

theorem inner_step (hN : 0 < N) (q v : Fin N → ℝ) :
    inner ℝ (stepL2 q) (stepL2 v) = ipN N q v := by
  have h1 := norm_add_sq_real (stepL2 q) (stepL2 v)
  have h2 := norm_sub_sq_real (stepL2 q) (stepL2 v)
  have h3 := norm_sq_step hN (q + v)
  have h4 := norm_sq_step hN (q - v)
  have h5 := norm_sq_step hN q
  have h6 := norm_sq_step hN v
  rw [← stepL2_add] at h1
  rw [← stepL2_sub] at h2
  unfold ipN dot
  unfold L2N at h3 h4 h5 h6
  have e : ∑ i, (q + v) i ^ 2 - ∑ i, (q - v) i ^ 2 = 4 * ∑ i, q i * v i := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply, Pi.sub_apply]; ring
  have : 4 * inner ℝ (stepL2 q) (stepL2 v) = (1 / (N : ℝ)) * (4 * ∑ i, q i * v i) := by
    rw [← e]
    nlinarith [h1, h2, h3, h4, h5, h6]
  linarith

theorem ENint_step (hN : 0 < N) (c : ℝ) (q v : Fin N → ℝ) :
    ENint c (stepF N q) (stepF N v) = ENNReal.ofReal (EN N c q v) := by
  unfold ENint
  refine (lintegral_idx2 hN (fun i j => ENNReal.ofReal
    ((ext v i - ext v j) ^ 2 / (c ^ 2 + (ext q i - ext q j) ^ 2)))).trans ?_
  refine (sum_ofReal2 hN (fun i j => (ext v i - ext v j) ^ 2 / (c ^ 2 + (ext q i - ext q j) ^ 2))
    (fun i j => by positivity)).trans ?_
  unfold EN
  rw [show ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (ext v i - ext v j) ^ 2 / (c ^ 2 + (ext q i - ext q j) ^ 2) =
      ∑ i : Fin N, ∑ j : Fin N, (v i - v j) ^ 2 / (c ^ 2 + (q i - q j) ^ 2) from
    sum_ext4 v q (fun x y z w => (x - y) ^ 2 / (c ^ 2 + (z - w) ^ 2))]

/-- `𝒥_N(v) = (L/2)‖v‖² + (κ/2)ℰ_N(v) − ⟨Q_N,v⟩` for the step functions, with `ℰ_N` the double integral. -/
theorem JN_step (hN : 0 < N) (L κ : ℝ) (q v : Fin N → ℝ) :
    JN L κ N q v = (L / 2) * ‖stepL2 v‖ ^ 2 +
      (κ / 2) * (ENint (κ / N) (stepF N q) (stepF N v)).toReal - inner ℝ (stepL2 q) (stepL2 v) := by
  have hE : 0 ≤ EN N (κ / N) q v := by
    unfold EN
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)
  unfold JN
  rw [ENint_step hN, ENNReal.toReal_ofReal hE, norm_sq_step hN, inner_step hN]

end QuantumNLS.StepIntegrals

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.StepIntegrals.norm_sq_step
#print axioms QuantumNLS.StepIntegrals.inner_step
#print axioms QuantumNLS.StepIntegrals.ENint_step
#print axioms QuantumNLS.StepIntegrals.JN_step
