import Mathlib
import QuantumNLS.QuantileTransport
import QuantumNLS.BetheLabels
import QuantumNLS.F07StepsR6
import QuantumNLS.F07ContinuityR6
import QuantumNLS.IndividualRootBound
import QuantumNLS.REF88QuantumBridge

/-!
# REF88QuantumLabels: free labels of occupation arrays (R-EF8C2837, item (iii), step S1, part 1)

Source: `source-text/chapters/global/physical_cubic.tex` (sha256 `64ec3e02...`), printed lines 232-262
("The root-label confinement `|p_i-q_i| <= 2 sqrt(K/L)` controls the free-label second-moment tails ... The finite-root
label contraction in Lemma CC:F07:root-stability compares these samples with every deterministic rounding ... The coupling
estimate in Lemma CC:F07:root-stability bounds the normalized root change by `|sqrt K_j - sqrt K|/sqrt L`").

* `ncorr`, `plab`: the sorted corrected integers of `a in M_N` and the free labels `p_i = 2 pi n_i / L`;
  `arrRoots_eq_freeForce`: `arrRoots L c a = root L (freeForce L (plab L a)) c` (so the accepted F07 label contraction
  applies); `ncorr_count`: the multiplicity of the label `k` is `a_k`.
* `sum_label`: `sum_j g(n_j) = sum_k a_k g(k)`; `integral_emp_clip`: integrals against the clipped free-label empirical
  measure are `sum_k (a_k/N) f(clip(2 pi k/L))`.
* `W2_roots_le`: `W2(emp roots(a), emp roots(b)) <= W2(emp plab a, emp plab b)` (accepted `label_contraction_sq` +
  `W2_empirical_sq`).
* `W2_coupling_le`: `W2(emp roots_{c'}(a), emp roots_c(a)) <= |sqrt c' N^{1/2} - ...|` form of accepted
  `coupling_continuity`.
* `clip_weak`: if `sum_k |a_k/N - x_k| -> 0` then the clipped free-label empirical measures converge in `W2` to the clipped
  limit measure (weak convergence of the clipped labels + second moments, accepted
  `QuantileTransport.tendsto_W2_of_weak_of_moment`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators

namespace QuantumNLS.REF88QuantumLabels

open QuantumNLS.BetheLabels QuantumNLS.QuantileTransport

variable {L : ℝ}

/-- The sorted corrected integers of an occupation array. -/
def ncorr {N : ℕ} (a : MArr N) : Fin N → ℤ := correctedInt (labelsEquivArr.symm a)

theorem ncorr_mono {N : ℕ} (a : MArr N) : Monotone (ncorr a) := correctedInt_monotone _

theorem ncorr_count {N : ℕ} (a : MArr N) (k : ℤ) :
    (Finset.univ.filter fun j => ncorr a j = k).card = a.1 k := by
  have h := labelsEquivArr_apply (labelsEquivArr.symm a) k
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The free labels `p_i = 2 pi n_i / L`. -/
def plab (L : ℝ) {N : ℕ} (a : MArr N) : Fin N → ℝ := fun j => 2 * Real.pi * (ncorr a j : ℝ) / L

theorem plab_mono (hL : 0 < L) {N : ℕ} (a : MArr N) : Monotone (plab L a) := by
  intro i j hij
  have : (ncorr a i : ℝ) ≤ ncorr a j := by exact_mod_cast ncorr_mono a hij
  unfold plab
  gcongr

theorem arrRoots_eq_freeForce {N : ℕ} (hL : 0 < L) {c : ℝ} (hc : 0 < c) (a : MArr N) :
    arrRoots L c a = BetheSmooth.root L (F07Round6.freeForce L (plab L a)) c := by
  rw [REF88QuantumBridge.arrRoots_eq_root hL hc a]
  congr 1
  funext j
  have h := correctedInt_spec (labelsEquivArr.symm a) j
  unfold F07Round6.freeForce plab ncorr
  have hL' : L ≠ 0 := hL.ne'
  have e : L * (2 * Real.pi * ((correctedInt (labelsEquivArr.symm a) j : ℤ) : ℝ) / L) =
      2 * Real.pi * ((correctedInt (labelsEquivArr.symm a) j : ℤ) : ℝ) := by field_simp
  rw [e, h]
  ring

theorem arrRoots_mono {N : ℕ} (hL : 0 < L) {c : ℝ} (hc : 0 < c) (a : MArr N) :
    Monotone (arrRoots L c a) := by
  unfold arrRoots
  exact (BetheLabels.roots_strictMono_labels hL hc _).monotone

/-- `∑_j g(n_j) = ∑_k a_k g(k)`. -/
theorem sum_label {N : ℕ} (a : MArr N) (g : ℤ → ℝ) :
    ∑ j, g (ncorr a j) = ∑' k, (a.1 k : ℝ) * g k := by
  classical
  have h1 : ∑ j, g (ncorr a j) =
      ∑ k ∈ Finset.univ.image (ncorr a), ∑ j ∈ Finset.univ.filter (fun j => ncorr a j = k), g (ncorr a j) :=
    (Finset.sum_fiberwise_of_maps_to (fun j hj => Finset.mem_image_of_mem _ hj) _).symm
  have h2 : ∀ k ∈ Finset.univ.image (ncorr a),
      ∑ j ∈ Finset.univ.filter (fun j => ncorr a j = k), g (ncorr a j) = (a.1 k : ℝ) * g k := by
    intro k _
    rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.1 hj).2] : ∀ j ∈ Finset.univ.filter
      (fun j => ncorr a j = k), g (ncorr a j) = g k)]
    rw [Finset.sum_const, ncorr_count a k]
    simp
  rw [h1, Finset.sum_congr rfl h2]
  symm
  refine (tsum_eq_sum (s := Finset.univ.image (ncorr a)) ?_)
  intro k hk
  have : a.1 k = 0 := by
    rw [← ncorr_count a k]
    simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
    intro j hj
    exact hk (Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj⟩)
  simp [this]


/-! ### Finite-sum, label-regrouping and weak-limit lemmas -/

theorem integrable_empirical {N : ℕ} (x : Fin N → ℝ) (f : ℝ → ℝ) :
    Integrable f (empirical N x) := by
  unfold empirical
  refine (integrable_finsetSum_measure).2 fun j _ => ?_
  exact (integrable_dirac (by simp)).smul_measure (ENNReal.inv_ne_top.2 (by exact_mod_cast (Fin.pos j).ne'))

theorem integral_empirical {N : ℕ} (x : Fin N → ℝ) (f : ℝ → ℝ) :
    ∫ t, f t ∂(empirical N x) = (N : ℝ)⁻¹ * ∑ j, f (x j) := by
  unfold empirical
  rw [integral_finsetSum_measure]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  · intro j _
    exact (integrable_dirac (by simp)).smul_measure (ENNReal.inv_ne_top.2 (by exact_mod_cast (Fin.pos j).ne'))

theorem map_clip_empirical (R : ℝ) {N : ℕ} (x : Fin N → ℝ) :
    (empirical N x).map (clip R) = empirical N (fun j => clip R (x j)) := by
  ext S hS
  rw [Measure.map_apply (continuous_clip R).measurable hS,
    empirical_apply _ _ ((continuous_clip R).measurable hS), empirical_apply _ _ hS]
  rfl

theorem hasFiniteSecondMoment_empirical {N : ℕ} (x : Fin N → ℝ) :
    HasFiniteSecondMoment (empirical N x) := integrable_empirical x _

theorem tsum_diff_le {o q g : ℤ → ℝ} {C : ℝ} (ho : Summable o) (hq : Summable q)
    (hg : ∀ k, |g k| ≤ C) :
    |∑' k, o k * g k - ∑' k, q k * g k| ≤ C * ∑' k, |o k - q k| := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hg 0)
  have h1 : Summable fun k => o k * g k :=
    Summable.of_norm_bounded (ho.abs.mul_left C) fun k => by
      rw [Real.norm_eq_abs, abs_mul]; nlinarith [abs_nonneg (o k), hg k]
  have h2 : Summable fun k => q k * g k :=
    Summable.of_norm_bounded (hq.abs.mul_left C) fun k => by
      rw [Real.norm_eq_abs, abs_mul]; nlinarith [abs_nonneg (q k), hg k]
  have hs : Summable fun k => |o k - q k| := (ho.sub hq).abs
  have h3 : Summable fun k => |(o k - q k) * g k| :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => by
      rw [abs_mul]; nlinarith [abs_nonneg (o k - q k), hg k]) (hs.mul_left C)
  have e : ∑' k, o k * g k - ∑' k, q k * g k = ∑' k, (o k - q k) * g k := by
    rw [← h1.tsum_sub h2]; congr 1; ext k; ring
  rw [e]
  calc |∑' k, (o k - q k) * g k| ≤ ∑' k, |(o k - q k) * g k| := by
        have := norm_tsum_le_tsum_norm (f := fun k => (o k - q k) * g k)
          (by simpa only [Real.norm_eq_abs] using h3)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' k, C * |o k - q k| := Summable.tsum_le_tsum (fun k => by
        rw [abs_mul]; nlinarith [abs_nonneg (o k - q k), hg k]) h3 (hs.mul_left C)
    _ = C * ∑' k, |o k - q k| := tsum_mul_left

/-- The clipped label of the integer `k`. -/
def clipPt (L R : ℝ) (k : ℤ) : ℝ := clip R (2 * Real.pi * (k : ℝ) / L)

theorem measurable_clipPt (L R : ℝ) : Measurable (clipPt L R) := Measurable.of_discrete

/-- The clipped free-label measure with indexed probabilities `p`. -/
def limMeas (L R : ℝ) (p : PMF ℤ) : Measure ℝ := p.toMeasure.map (clipPt L R)

instance (L R : ℝ) (p : PMF ℤ) : IsProbabilityMeasure (limMeas L R p) :=
  by unfold limMeas; infer_instance

theorem abs_clipPt_le {R : ℝ} (hR : 0 ≤ R) (L : ℝ) (k : ℤ) : |clipPt L R k| ≤ R :=
  abs_clip_le hR _

theorem integral_limMeas (L R : ℝ) (p : PMF ℤ) (f : ℝ → ℝ) (hf : Continuous f) (C : ℝ)
    (hC : ∀ k, |f (clipPt L R k)| ≤ C) :
    ∫ t, f t ∂(limMeas L R p) = ∑' k, (p k).toReal * f (clipPt L R k) := by
  unfold limMeas
  rw [integral_map (measurable_clipPt L R).aemeasurable hf.aestronglyMeasurable,
    PMF.integral_eq_tsum _ _ (Integrable.of_bound (C := C) Measurable.of_discrete.aestronglyMeasurable
      (Eventually.of_forall fun k => by simpa only [Function.comp, Real.norm_eq_abs] using hC k))]
  simp only [smul_eq_mul]

theorem hasFiniteSecondMoment_limMeas (L : ℝ) {R : ℝ} (hR : 0 ≤ R) (p : PMF ℤ) :
    HasFiniteSecondMoment (limMeas L R p) := by
  unfold HasFiniteSecondMoment limMeas
  rw [integrable_map_measure (by fun_prop) (measurable_clipPt L R).aemeasurable]
  refine Integrable.of_bound (C := R ^ 2) Measurable.of_discrete.aestronglyMeasurable
    (Eventually.of_forall fun k => ?_)
  simp only [Function.comp, Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_clipPt_le hR L k) 2

theorem integral_emp_clip {N : ℕ} (a : MArr N) (L R : ℝ) (f : ℝ → ℝ) :
    ∫ t, f t ∂(empirical N (fun j => clip R (plab L a j))) =
      ∑' k, ((a.1 k : ℝ) / N) * f (clipPt L R k) := by
  rw [integral_empirical]
  have := sum_label a (fun k => f (clipPt L R k))
  have e : ∑ j, f (clip R (plab L a j)) = ∑ j, f (clipPt L R (ncorr a j)) := rfl
  rw [e, this, ← tsum_mul_left]
  congr 1; ext k; ring

theorem clip_weak (_hL : 0 < L) {R : ℝ} (hR : 0 ≤ R) (p : PMF ℤ) (a : ∀ n : ℕ, MArr (n + 1))
    (h : Tendsto (fun n : ℕ => ∑' k, |(((a n).1 k : ℕ) : ℝ) / ((n : ℝ) + 1) - (p k).toReal|)
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => W2 (empirical (n + 1) (fun j => clip R (plab L (a n) j)))
      (limMeas L R p)) atTop (𝓝 0) := by
  set σs : ℕ → Measure ℝ := fun n => empirical (n + 1) (fun j => clip R (plab L (a n) j)) with hσs
  have : ∀ n, IsProbabilityMeasure (σs n) := fun n => isProbabilityMeasure_empirical (Nat.succ_pos n) _
  have hps : Summable fun k => (p k).toReal := ENNReal.summable_toReal (PMF.tsum_coe_ne_top p)
  have hos : ∀ n : ℕ, Summable fun k => (((a n).1 k : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ)) := fun n =>
    summable_of_ne_finset_zero (s := (a n).1.support) fun k hk => by
      simp [Finsupp.notMem_support_iff.1 hk]
  have key : ∀ (f : ℝ → ℝ), Continuous f → ∀ C : ℝ, (∀ k, |f (clipPt L R k)| ≤ C) →
      Tendsto (fun n => ∫ t, f t ∂(σs n)) atTop (𝓝 (∫ t, f t ∂(limMeas L R p))) := by
    intro f hf C hC
    rw [integral_limMeas L R p f hf C hC]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using h.const_mul C)
    rw [Real.norm_eq_abs, hσs]
    show |∫ t, f t ∂(empirical (n + 1) _) - _| ≤ _
    rw [integral_emp_clip]
    have := tsum_diff_le (hos n) hps hC
    simpa only [Nat.cast_add, Nat.cast_one] using this
  have hw : WeakConv σs (limMeas L R p) := fun f =>
    key f f.continuous ‖f‖ fun k => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm _
  have hmom := key (fun t => t ^ 2) (by fun_prop) (R ^ 2) fun k => by
    simp only [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_clipPt_le hR L k) 2
  exact tendsto_W2_of_weak_of_moment (fun n => hasFiniteSecondMoment_empirical _)
    (hasFiniteSecondMoment_limMeas L hR p) hw hmom

/-! ### Label contraction and coupling continuity in `W2` -/

theorem W2_roots_le {N : ℕ} (hN : 0 < N) (hL : 0 < L) {c : ℝ} (hc : 0 < c) (a b : MArr N) :
    W2 (empirical N (arrRoots L c a)) (empirical N (arrRoots L c b)) ≤
      W2 (empirical N (plab L a)) (empirical N (plab L b)) := by
  have h1 := W2_empirical_sq hN (arrRoots_mono hL hc a) (arrRoots_mono hL hc b)
  have h2 := W2_empirical_sq hN (plab_mono hL a) (plab_mono hL b)
  have hle : (1 / N : ℝ) * ∑ j, (arrRoots L c a j - arrRoots L c b j) ^ 2 ≤
      (1 / N : ℝ) * ∑ j, (plab L a j - plab L b j) ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [arrRoots_eq_freeForce hL hc a, arrRoots_eq_freeForce hL hc b]
    exact F07Round6.label_contraction_sq hL hc (plab L b) (plab L a)
  have : W2 (empirical N (arrRoots L c a)) (empirical N (arrRoots L c b)) ^ (2 : ℝ) ≤
      W2 (empirical N (plab L a)) (empirical N (plab L b)) ^ (2 : ℝ) := by
    rw [ENNReal.rpow_two, ENNReal.rpow_two, h1, h2]
    exact ENNReal.ofReal_le_ofReal hle
  exact (ENNReal.rpow_le_rpow_iff (by norm_num)).1 this

theorem W2_coupling_le {N : ℕ} (hN : 0 < N) (hL : 0 < L) {K₀ K₁ : ℝ} (h0 : 0 < K₀) (h1 : 0 < K₁)
    (a : MArr N) :
    W2 (empirical N (arrRoots L (K₁ / N) a)) (empirical N (arrRoots L (K₀ / N) a)) ≤
      ENNReal.ofReal (|Real.sqrt K₁ - Real.sqrt K₀| / Real.sqrt L) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 < K₀ / N := div_pos h0 hNr
  have hc1 : 0 < K₁ / N := div_pos h1 hNr
  have e := W2_empirical_sq hN (arrRoots_mono hL hc1 a) (arrRoots_mono hL hc0 a)
  have hcc := F07ContinuityR6.coupling_continuity hN hL h0 h1 (F07Round6.freeForce L (plab L a))
  rw [← arrRoots_eq_freeForce hL hc1, ← arrRoots_eq_freeForce hL hc0] at hcc
  set T : ℝ := |Real.sqrt K₁ - Real.sqrt K₀| / Real.sqrt L with hT
  have hn : ‖(EuclideanSpace.equiv (Fin N) ℝ).symm (arrRoots L (K₁ / N) a - arrRoots L (K₀ / N) a)‖ ^ 2 =
      ∑ j, (arrRoots L (K₁ / N) a j - arrRoots L (K₀ / N) a j) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]; rfl
  have hsq : (1 / N : ℝ) * ∑ j, (arrRoots L (K₁ / N) a j - arrRoots L (K₀ / N) a j) ^ 2 ≤ T ^ 2 := by
    have h3 := (div_le_iff₀ (Real.sqrt_pos.2 hNr)).1 hcc
    have h4 : ‖(EuclideanSpace.equiv (Fin N) ℝ).symm (arrRoots L (K₁ / N) a - arrRoots L (K₀ / N) a)‖ ^ 2 ≤
        (T * Real.sqrt N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    rw [hn, mul_pow, Real.sq_sqrt hNr.le] at h4
    rw [one_div, inv_mul_le_iff₀ hNr]
    linarith
  have : W2 (empirical N (arrRoots L (K₁ / N) a)) (empirical N (arrRoots L (K₀ / N) a)) ^ (2 : ℝ) ≤
      (ENNReal.ofReal T) ^ (2 : ℝ) := by
    rw [ENNReal.rpow_two, ENNReal.rpow_two, e, ← ENNReal.ofReal_pow (by positivity)]
    exact ENNReal.ofReal_le_ofReal hsq
  exact (ENNReal.rpow_le_rpow_iff (by norm_num)).1 this

end QuantumNLS.REF88QuantumLabels

#print axioms QuantumNLS.REF88QuantumLabels.arrRoots_eq_freeForce
#print axioms QuantumNLS.REF88QuantumLabels.sum_label
#print axioms QuantumNLS.REF88QuantumLabels.integral_emp_clip
#print axioms QuantumNLS.REF88QuantumLabels.clip_weak
#print axioms QuantumNLS.REF88QuantumLabels.W2_roots_le
#print axioms QuantumNLS.REF88QuantumLabels.W2_coupling_le
