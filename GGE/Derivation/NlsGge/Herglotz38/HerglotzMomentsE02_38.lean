import Mathlib

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

open MeasureTheory Filter Topology

/-- kernel `y²/(t²+y²)` -/
lemma hm38_K_le (y t : ℝ) (hy : 1 ≤ y) : y ^ 2 / (t ^ 2 + y ^ 2) ≤ (1 + y) / (1 + |t|) := by
  have h1 : 0 < t ^ 2 + y ^ 2 := by positivity
  rw [div_le_div_iff₀ h1 (by positivity)]
  have : |t| * y ≤ (t ^ 2 + y ^ 2) / 2 := by
    nlinarith [sq_abs t, sq_nonneg (|t| - y)]
  nlinarith [abs_nonneg t, mul_nonneg (abs_nonneg t) (by linarith : (0:ℝ) ≤ y)]

lemma hm38_K_nonneg (y t : ℝ) : 0 ≤ y ^ 2 / (t ^ 2 + y ^ 2) := by positivity

lemma hm38_K_le_one (y t : ℝ) : y ^ 2 / (t ^ 2 + y ^ 2) ≤ 1 := by
  rcases eq_or_lt_of_le (by positivity : (0:ℝ) ≤ t ^ 2 + y ^ 2) with h | h
  · rw [← h]; simp
  · rw [div_le_one h]; nlinarith [sq_nonneg t]

lemma hm38_K_meas (y : ℝ) : Measurable (fun t : ℝ => y ^ 2 / (t ^ 2 + y ^ 2)) := by fun_prop

lemma hm38_intK (v : ℝ → ℝ) (hv0 : ∀ t, 0 ≤ v t) (hvm : Measurable v)
    (hvi : Integrable (fun t => v t / (1 + |t|))) (y : ℝ) (hy : 1 ≤ y) :
    Integrable (fun t => v t * (y ^ 2 / (t ^ 2 + y ^ 2))) := by
  refine Integrable.mono' (hvi.const_mul (1 + y)) ((hvm.mul (hm38_K_meas y)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hv0 t) (hm38_K_nonneg y t))]
  calc v t * (y ^ 2 / (t ^ 2 + y ^ 2)) ≤ v t * ((1 + y) / (1 + |t|)) :=
        mul_le_mul_of_nonneg_left (hm38_K_le y t hy) (hv0 t)
    _ = (1 + y) * (v t / (1 + |t|)) := by ring

lemma hm38_intG (v : ℝ → ℝ) (hv0 : ∀ t, 0 ≤ v t) (hvm : Measurable v)
    (hvi : Integrable (fun t => v t / (1 + |t|))) (y : ℝ) (hy : 1 ≤ y) :
    Integrable (fun t => v t * (t / (t ^ 2 + y ^ 2))) := by
  refine Integrable.mono' (hvi.const_mul 2) ((hvm.mul (by fun_prop)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun t => ?_)
  have h1 : 0 < t ^ 2 + y ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hv0 t), abs_div, abs_of_pos h1]
  have : |t| / (t ^ 2 + y ^ 2) ≤ 2 / (1 + |t|) := by
    rw [div_le_div_iff₀ h1 (by positivity)]
    nlinarith [sq_abs t, sq_nonneg (|t| - 1), abs_nonneg t]
  calc v t * (|t| / (t ^ 2 + y ^ 2)) ≤ v t * (2 / (1 + |t|)) :=
        mul_le_mul_of_nonneg_left this (hv0 t)
    _ = 2 * (v t / (1 + |t|)) := by ring

lemma hm38_geom (y t : ℝ) (hy : y ≠ 0) (j : ℕ) :
    y ^ 2 / (t ^ 2 + y ^ 2) = (∑ i ∈ Finset.range j, (-1 : ℝ) ^ i * (t ^ (2 * i) / y ^ (2 * i)))
      + (-1 : ℝ) ^ j * (t ^ (2 * j) / y ^ (2 * j)) * (y ^ 2 / (t ^ 2 + y ^ 2)) := by
  have h1 : t ^ 2 + y ^ 2 ≠ 0 := by positivity
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have e : (-1 : ℝ) ^ j * (t ^ (2 * j) / y ^ (2 * j)) * (y ^ 2 / (t ^ 2 + y ^ 2))
        = (-1 : ℝ) ^ j * (t ^ (2 * j) / y ^ (2 * j))
          + (-1 : ℝ) ^ (j + 1) * (t ^ (2 * (j + 1)) / y ^ (2 * (j + 1))) * (y ^ 2 / (t ^ 2 + y ^ 2)) := by
      field_simp
      ring
    linarith

lemma hm38_expand (w : ℝ → ℝ) (j : ℕ) (y : ℝ) (hy : 1 ≤ y)
    (hint : ∀ i < j, Integrable (fun t => t ^ (2 * i) * w t))
    (hS : Integrable (fun t => w t * (y ^ 2 / (t ^ 2 + y ^ 2)))) :
    Integrable (fun t => t ^ (2 * j) * w t * (y ^ 2 / (t ^ 2 + y ^ 2))) ∧
    ∫ t, t ^ (2 * j) * w t * (y ^ 2 / (t ^ 2 + y ^ 2)) =
      (-1 : ℝ) ^ j * y ^ (2 * j) * ((∫ t, w t * (y ^ 2 / (t ^ 2 + y ^ 2)))
        - ∑ i ∈ Finset.range j, (-1 : ℝ) ^ i * ((∫ t, t ^ (2 * i) * w t) / y ^ (2 * i))) := by
  have hy0 : y ≠ 0 := by positivity
  have hpt : ∀ t : ℝ, t ^ (2 * j) * w t * (y ^ 2 / (t ^ 2 + y ^ 2)) =
      (-1 : ℝ) ^ j * y ^ (2 * j) * (w t * (y ^ 2 / (t ^ 2 + y ^ 2))
        - ∑ i ∈ Finset.range j, (-1 : ℝ) ^ i * ((t ^ (2 * i) * w t) / y ^ (2 * i))) := by
    intro t
    have g := hm38_geom y t hy0 j
    set k := y ^ 2 / (t ^ 2 + y ^ 2) with hk
    have hS' : ∑ i ∈ Finset.range j, (-1 : ℝ) ^ i * ((t ^ (2 * i) * w t) / y ^ (2 * i))
        = w t * ∑ i ∈ Finset.range j, (-1 : ℝ) ^ i * (t ^ (2 * i) / y ^ (2 * i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    have h2 : w t * k - ∑ i ∈ Finset.range j, (-1 : ℝ) ^ i * ((t ^ (2 * i) * w t) / y ^ (2 * i))
        = w t * ((-1 : ℝ) ^ j * (t ^ (2 * j) / y ^ (2 * j)) * k) := by
      rw [hS']
      nth_rewrite 1 [g]
      ring
    rw [h2]
    have : (y ^ (2 * j)) ≠ 0 := by positivity
    have h3 : ((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ j) = 1 := by rw [← mul_pow]; simp
    have h4 : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [sq]; exact h3
    field_simp
    rw [h4]; ring
  have hI : Integrable (fun t => (-1 : ℝ) ^ j * y ^ (2 * j) * (w t * (y ^ 2 / (t ^ 2 + y ^ 2))
        - ∑ i ∈ Finset.range j, (-1 : ℝ) ^ i * ((t ^ (2 * i) * w t) / y ^ (2 * i)))) := by
    refine Integrable.const_mul (hS.sub (integrable_finsetSum _ (fun i hi => ?_))) _
    exact ((hint i (Finset.mem_range.mp hi)).div_const _).const_mul _
  refine ⟨by simpa only [hpt] using hI, ?_⟩
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub hS (integrable_finsetSum _ (fun i hi =>
    ((hint i (Finset.mem_range.mp hi)).div_const _).const_mul _)), integral_finsetSum _ (fun i hi =>
    ((hint i (Finset.mem_range.mp hi)).div_const _).const_mul _)]
  congr 3
  funext i
  rw [integral_const_mul, integral_div]

lemma hm38_dct (g : ℝ → ℝ) (hg : Integrable g) :
    Tendsto (fun y : ℝ => ∫ t, g t * (y ^ 2 / (t ^ 2 + y ^ 2))) atTop (𝓝 (∫ t, g t)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖g t‖) ?_ ?_ hg.norm ?_
  · exact Filter.Eventually.of_forall (fun y => (hg.aestronglyMeasurable.mul
      (hm38_K_meas y).aestronglyMeasurable))
  · refine Filter.Eventually.of_forall (fun y => Filter.Eventually.of_forall (fun t => ?_))
    rw [norm_mul, Real.norm_eq_abs (y ^ 2 / (t ^ 2 + y ^ 2)),
      abs_of_nonneg (hm38_K_nonneg y t)]
    calc ‖g t‖ * (y ^ 2 / (t ^ 2 + y ^ 2)) ≤ ‖g t‖ * 1 :=
          mul_le_mul_of_nonneg_left (hm38_K_le_one y t) (norm_nonneg _)
      _ = ‖g t‖ := mul_one _
  · refine Filter.Eventually.of_forall (fun t => ?_)
    have : Tendsto (fun y : ℝ => y ^ 2 / (t ^ 2 + y ^ 2)) atTop (𝓝 1) := by
      have h1 : Tendsto (fun y : ℝ => t ^ 2 / y ^ 2) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
      have h2 : Tendsto (fun y : ℝ => (1 + t ^ 2 / y ^ 2)⁻¹) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds.add h1).inv₀ (by norm_num : (1:ℝ) + 0 ≠ 0)
      refine h2.congr' ?_
      filter_upwards [eventually_ne_atTop (0:ℝ)] with y hy
      field_simp
      ring
    simpa using this.const_mul (g t)

lemma hm38_K_tendsto (t : ℝ) : Tendsto (fun y : ℝ => y ^ 2 / (t ^ 2 + y ^ 2)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun y : ℝ => t ^ 2 / y ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  have h2 : Tendsto (fun y : ℝ => (1 + t ^ 2 / y ^ 2)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add h1).inv₀ (by norm_num : (1:ℝ) + 0 ≠ 0)
  refine h2.congr' ?_
  filter_upwards [eventually_ne_atTop (0:ℝ)] with y hy
  field_simp
  ring

lemma hm38_fatou (g : ℝ → ℝ) (hgm : Measurable g) (hg0 : ∀ t, 0 ≤ g t)
    (hint : ∀ y : ℝ, 1 ≤ y → Integrable (fun t => g t * (y ^ 2 / (t ^ 2 + y ^ 2))))
    (L : ℝ) (hlim : Tendsto (fun y : ℝ => ∫ t, g t * (y ^ 2 / (t ^ 2 + y ^ 2))) atTop (𝓝 L)) :
    Integrable g := by
  have hn : Tendsto (fun n : ℕ => ∫ t, g t * ((n:ℝ) ^ 2 / (t ^ 2 + (n:ℝ) ^ 2))) atTop (𝓝 L) :=
    hlim.comp tendsto_natCast_atTop_atTop
  set f : ℕ → ℝ → ENNReal := fun n t => ENNReal.ofReal (g t * ((n:ℝ) ^ 2 / (t ^ 2 + (n:ℝ) ^ 2))) with hf
  have hfm : ∀ n, Measurable (f n) := fun n =>
    ENNReal.measurable_ofReal.comp (hgm.mul (hm38_K_meas _))
  have hpt : ∀ t, Tendsto (fun n => f n t) atTop (𝓝 (ENNReal.ofReal (g t))) := by
    intro t
    have : Tendsto (fun n : ℕ => g t * ((n:ℝ) ^ 2 / (t ^ 2 + (n:ℝ) ^ 2))) atTop (𝓝 (g t)) := by
      simpa using ((hm38_K_tendsto t).comp tendsto_natCast_atTop_atTop).const_mul (g t)
    exact (ENNReal.tendsto_ofReal this)
  have h1 := lintegral_liminf_le (μ := volume) (u := (atTop : Filter ℕ)) hfm
  have e1 : ∀ t, liminf (fun n => f n t) atTop = ENNReal.ofReal (g t) := fun t => (hpt t).liminf_eq
  have e2 : ∀ n : ℕ, ∫⁻ t, f n t = ENNReal.ofReal (∫ t, g t * ((n:ℝ) ^ 2 / (t ^ 2 + (n:ℝ) ^ 2))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp only [hf]
      have : ∀ t : ℝ, g t * (((0:ℕ):ℝ) ^ 2 / (t ^ 2 + ((0:ℕ):ℝ) ^ 2)) = 0 := by intro t; simp
      simp [this]
    · symm
      refine ofReal_integral_eq_lintegral_ofReal (hint _ ?_) (Filter.Eventually.of_forall (fun t => ?_))
      · exact_mod_cast h
      · exact mul_nonneg (hg0 t) (hm38_K_nonneg _ _)
  have e3 : Tendsto (fun n : ℕ => ∫⁻ t, f n t) atTop (𝓝 (ENNReal.ofReal L)) := by
    simp_rw [e2]; exact ENNReal.tendsto_ofReal hn
  simp_rw [e1, e3.liminf_eq] at h1
  have hlt : ∫⁻ t, ENNReal.ofReal (g t) < ⊤ := lt_of_le_of_lt h1 ENNReal.ofReal_lt_top
  exact ⟨hgm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hg0)).2 hlt⟩

lemma hm38_step (w : ℝ → ℝ) (N R : ℕ) (b : ℕ → ℝ) (j : ℕ) (hj : j < N) (hjR : 2 * j ≤ R)
    (h0 : Tendsto (fun y : ℝ => y ^ R * ((∫ t, w t * (y ^ 2 / (t ^ 2 + y ^ 2))) / Real.pi
        - ∑ i ∈ Finset.range N, b i / y ^ (2 * i))) atTop (𝓝 0))
    (hint : ∀ i < j, Integrable (fun t => t ^ (2 * i) * w t))
    (hb : ∀ i < j, b i = (-1 : ℝ) ^ i * (∫ t, t ^ (2 * i) * w t) / Real.pi)
    (hS : ∀ y : ℝ, 1 ≤ y → Integrable (fun t => w t * (y ^ 2 / (t ^ 2 + y ^ 2)))) :
    Tendsto (fun y : ℝ => ∫ t, t ^ (2 * j) * w t * (y ^ 2 / (t ^ 2 + y ^ 2))) atTop
      (𝓝 ((-1 : ℝ) ^ j * Real.pi * b j)) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  set Sj : ℝ → ℝ := fun y => ∫ t, t ^ (2 * j) * w t * (y ^ 2 / (t ^ 2 + y ^ 2)) with hSj
  set X : ℝ → ℝ := fun y => y ^ (2 * j) * ((∫ t, w t * (y ^ 2 / (t ^ 2 + y ^ 2))) / Real.pi
        - ∑ i ∈ Finset.range N, b i / y ^ (2 * i)) with hX
  set Tail : ℝ → ℝ := fun y => ∑ i ∈ Finset.Ico (j + 1) N, b i / y ^ (2 * (i - j)) with hTail
  have hXt : Tendsto X atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) ?_
      (tendsto_zero_iff_norm_tendsto_zero.mp h0)
    filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    simp only [hX, norm_mul, norm_pow, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    exact pow_le_pow_right₀ (by rw [abs_of_nonneg (by linarith)]; exact hy) hjR
  have hTt : Tendsto Tail atTop (𝓝 0) := by
    have : Tendsto Tail atTop (𝓝 (∑ i ∈ Finset.Ico (j + 1) N, (0:ℝ))) := by
      refine tendsto_finsetSum _ (fun i hi => ?_)
      have hi' : 1 ≤ i - j := by
        have := (Finset.mem_Ico.mp hi).1
        omega
      exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by omega))
    simpa using this
  have hE : ∀ y : ℝ, 1 ≤ y → (-1 : ℝ) ^ j * Sj y / Real.pi = X y + b j + Tail y := by
    intro y hy
    have hy0 : y ≠ 0 := by positivity
    obtain ⟨_, hEq⟩ := hm38_expand w j y hy hint (hS y hy)
    simp only [hSj, hX]
    rw [hEq]
    have h1 := Finset.sum_range_add_sum_Ico (fun i => b i / y ^ (2 * i)) hj.le
    have h2 := Finset.sum_eq_sum_Ico_succ_bot hj (fun i => b i / y ^ (2 * i))
    have h3 : ∑ i ∈ Finset.range j, b i / y ^ (2 * i)
        = (∑ i ∈ Finset.range j, (-1 : ℝ) ^ i * ((∫ t, t ^ (2 * i) * w t) / y ^ (2 * i))) / Real.pi := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [hb i (Finset.mem_range.mp hi)]
      field_simp
    have h4 : y ^ (2 * j) * ∑ i ∈ Finset.Ico (j + 1) N, b i / y ^ (2 * i) = Tail y := by
      simp only [hTail]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      obtain ⟨k, hk⟩ : ∃ k, i = j + k := ⟨i - j, by have := (Finset.mem_Ico.mp hi).1; omega⟩
      subst hk
      have : j + k - j = k := by omega
      rw [this, show 2 * (j + k) = 2 * j + 2 * k by ring, pow_add]
      have : y ^ (2 * j) ≠ 0 := by positivity
      have : y ^ (2 * k) ≠ 0 := by positivity
      field_simp
    rw [← h1, h2, h3]
    have h5 : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    have hyj : y ^ (2 * j) ≠ 0 := by positivity
    have h6 : y ^ (2 * j) * (b j / y ^ (2 * j)) = b j := by field_simp
    generalize (∫ t, w t * (y ^ 2 / (t ^ 2 + y ^ 2))) = S at *
    generalize (∑ i ∈ Finset.range j, (-1 : ℝ) ^ i * ((∫ t, t ^ (2 * i) * w t) / y ^ (2 * i))) = D at *
    generalize (∑ i ∈ Finset.Ico (j + 1) N, b i / y ^ (2 * i)) = U at *
    linear_combination (y ^ (2 * j) * (S - D) / Real.pi) * h5 + h6 + h4
  have hlim : Tendsto (fun y : ℝ => (-1 : ℝ) ^ j * Sj y / Real.pi) atTop (𝓝 (b j)) := by
    have : Tendsto (fun y : ℝ => X y + b j + Tail y) atTop (𝓝 (0 + b j + 0)) :=
      (hXt.add_const _).add hTt
    rw [zero_add, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    exact (hE y hy).symm
  have h5 : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have := hlim.const_mul ((-1 : ℝ) ^ j * Real.pi)
  refine this.congr (fun y => ?_)
  field_simp
  simp only [hSj]
  rw [h5, one_mul]

lemma hm38_ident (j : ℕ) (b S : ℝ) (hS : S = (-1 : ℝ) ^ j * Real.pi * b) :
    b = (-1 : ℝ) ^ j * S / Real.pi := by
  have h5 : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hS]
  field_simp
  rw [h5]; ring

lemma hm38_even_ind (v : ℝ → ℝ) (hv0 : ∀ t, 0 ≤ v t) (hvm : Measurable v)
    (hvi : Integrable (fun t => v t / (1 + |t|))) (M : ℕ) (b : ℕ → ℝ)
    (h0 : Tendsto (fun y : ℝ => y ^ (2 * M) * ((∫ t, v t * (y ^ 2 / (t ^ 2 + y ^ 2))) / Real.pi
        - ∑ i ∈ Finset.range (M + 1), b i / y ^ (2 * i))) atTop (𝓝 0)) :
    ∀ j ≤ M, Integrable (fun t => t ^ (2 * j) * v t) ∧
      b j = (-1 : ℝ) ^ j * (∫ t, t ^ (2 * j) * v t) / Real.pi := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjM
    have hint : ∀ i < j, Integrable (fun t => t ^ (2 * i) * v t) :=
      fun i hi => (ih i hi (by omega)).1
    have hb : ∀ i < j, b i = (-1 : ℝ) ^ i * (∫ t, t ^ (2 * i) * v t) / Real.pi :=
      fun i hi => (ih i hi (by omega)).2
    have hS := fun y (hy : 1 ≤ y) => hm38_intK v hv0 hvm hvi y hy
    have hstep := hm38_step v (M + 1) (2 * M) b j (by omega) (by omega) h0 hint hb hS
    have hgm : Measurable (fun t : ℝ => t ^ (2 * j) * v t) := by fun_prop
    have hg0 : ∀ t : ℝ, 0 ≤ t ^ (2 * j) * v t := fun t => by
      rw [pow_mul]; exact mul_nonneg (by positivity) (hv0 t)
    have hInt : Integrable (fun t : ℝ => t ^ (2 * j) * v t) :=
      hm38_fatou _ hgm hg0 (fun y hy => (hm38_expand v j y hy hint (hS y hy)).1) _ hstep
    refine ⟨hInt, ?_⟩
    exact hm38_ident j _ _ (tendsto_nhds_unique (hm38_dct _ hInt) hstep)

lemma hm38_odd_ind (v : ℝ → ℝ) (hv0 : ∀ t, 0 ≤ v t) (hvm : Measurable v) (M : ℕ)
    (hev : ∀ j ≤ M, Integrable (fun t => t ^ (2 * j) * v t))
    (N R : ℕ) (hN : N ≤ M) (hR : 2 * N ≤ R + 2) (b : ℕ → ℝ)
    (h0 : Tendsto (fun y : ℝ => y ^ R * ((∫ t, (t * v t) * (y ^ 2 / (t ^ 2 + y ^ 2))) / Real.pi
        - ∑ i ∈ Finset.range N, b i / y ^ (2 * i))) atTop (𝓝 0)) :
    ∀ j < N, Integrable (fun t => t ^ (2 * j) * (t * v t)) ∧
      b j = (-1 : ℝ) ^ j * (∫ t, t ^ (2 * j) * (t * v t)) / Real.pi := by
  have hodd : ∀ j < N, Integrable (fun t => t ^ (2 * j) * (t * v t)) := by
    intro j hj
    refine Integrable.mono' ((hev j (by omega)).add (hev (j + 1) (by omega)))
      (by fun_prop : Measurable (fun t : ℝ => t ^ (2 * j) * (t * v t))).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun t => ?_)
    have h1 : 0 ≤ t ^ (2 * j) := by rw [pow_mul]; positivity
    have h2 : |t| ≤ 1 + t ^ 2 := by nlinarith [sq_abs t, sq_nonneg (|t| - 1), abs_nonneg t]
    have h3 : t ^ (2 * (j + 1)) = t ^ (2 * j) * t ^ 2 := by rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add]
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg (hv0 t), h3]
    have := mul_le_mul_of_nonneg_left h2 (mul_nonneg h1 (hv0 t))
    nlinarith [this]
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjN
    have hint : ∀ i < j, Integrable (fun t => t ^ (2 * i) * (t * v t)) :=
      fun i hi => hodd i (by omega)
    have hb : ∀ i < j, b i = (-1 : ℝ) ^ i * (∫ t, t ^ (2 * i) * (t * v t)) / Real.pi :=
      fun i hi => (ih i hi (by omega)).2
    have hw : Integrable (fun t => t * v t) := by
      have := hodd 0 (by omega)
      simpa using this
    have hS : ∀ y : ℝ, 1 ≤ y → Integrable (fun t => (t * v t) * (y ^ 2 / (t ^ 2 + y ^ 2))) := by
      intro y hy
      refine Integrable.mono' hw.norm
        (hw.aestronglyMeasurable.mul (hm38_K_meas y).aestronglyMeasurable) ?_
      refine Filter.Eventually.of_forall (fun t => ?_)
      rw [norm_mul, Real.norm_eq_abs (y ^ 2 / (t ^ 2 + y ^ 2)), abs_of_nonneg (hm38_K_nonneg y t)]
      calc ‖t * v t‖ * (y ^ 2 / (t ^ 2 + y ^ 2)) ≤ ‖t * v t‖ * 1 :=
            mul_le_mul_of_nonneg_left (hm38_K_le_one y t) (norm_nonneg _)
        _ = ‖t * v t‖ := mul_one _
    have hstep := hm38_step (fun t => t * v t) N R b j hjN (by omega) h0 hint hb hS
    have hInt := hodd j hjN
    exact ⟨hInt, hm38_ident j _ _ (tendsto_nhds_unique (hm38_dct _ hInt) hstep)⟩

lemma hm38_I_pow (n : ℕ) (y : ℝ) :
    (Complex.I * (y : ℂ)) ^ (2 * n) = (((-1 : ℝ) ^ n * y ^ (2 * n) : ℝ) : ℂ) := by
  rw [mul_pow, pow_mul, pow_mul, Complex.I_sq]
  push_cast
  ring

lemma hm38_term_odd (a y : ℝ) (hy : y ≠ 0) (i : ℕ) :
    (a : ℂ) / (Complex.I * (y : ℂ)) ^ (2 * i + 2) = (((-1 : ℝ) ^ (i + 1) * a / y ^ (2 * i + 2) : ℝ) : ℂ) := by
  have h : 2 * i + 2 = 2 * (i + 1) := by ring
  rw [h, hm38_I_pow]
  have : (-1 : ℝ) ^ (i + 1) * y ^ (2 * (i + 1)) ≠ 0 := by positivity
  push_cast
  have h2 : ((-1 : ℂ)) ^ (i + 1) ≠ 0 := by simp
  have h3 : (y : ℂ) ^ (2 * (i + 1)) ≠ 0 := by simp [hy]
  field_simp
  have h4 : ((-1 : ℂ) ^ (i + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [h4]; ring

lemma hm38_term_even (a y : ℝ) (hy : y ≠ 0) (j : ℕ) :
    (a : ℂ) / (Complex.I * (y : ℂ)) ^ (2 * j + 1) =
      Complex.I * (((-1 : ℝ) ^ (j + 1) * a / y ^ (2 * j + 1) : ℝ) : ℂ) := by
  rw [pow_succ, hm38_I_pow]
  have h3 : (y : ℂ) ^ (2 * j) ≠ 0 := by simp [hy]
  have h2 : ((-1 : ℂ)) ^ j ≠ 0 := by simp
  push_cast
  have hy' : (y : ℂ) ≠ 0 := by simp [hy]
  field_simp
  have h4 : ((-1 : ℂ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  rw [Complex.I_sq]
  linear_combination (-(a : ℂ) * (y : ℂ) ^ (2 * j + 1)) * h4

lemma hm38_sum_split (a : ℕ → ℝ) (y : ℝ) (hy : y ≠ 0) (M : ℕ) :
    ∑ m ∈ Finset.range (2 * M + 1), (a m : ℂ) / (Complex.I * (y : ℂ)) ^ (m + 1) =
      ((∑ i ∈ Finset.range M, (-1 : ℝ) ^ (i + 1) * a (2 * i + 1) / y ^ (2 * i + 2) : ℝ) : ℂ)
      + Complex.I * ((∑ j ∈ Finset.range (M + 1), (-1 : ℝ) ^ (j + 1) * a (2 * j) / y ^ (2 * j + 1) : ℝ) : ℂ) := by
  induction M with
  | zero =>
    simp only [zero_add, mul_zero, Finset.range_one, Finset.sum_singleton, Finset.range_zero,
      Finset.sum_empty, Complex.ofReal_zero, zero_add]
    exact hm38_term_even (a 0) y hy 0
  | succ M ih =>
    have e : 2 * (M + 1) + 1 = (2 * M + 1) + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ (fun i => (-1 : ℝ) ^ (i + 1) * a (2 * i + 1) / y ^ (2 * i + 2)) M,
      Finset.sum_range_succ (fun j => (-1 : ℝ) ^ (j + 1) * a (2 * j) / y ^ (2 * j + 1)) (M + 1)]
    have h1 := hm38_term_odd (a (2 * M + 1)) y hy M
    have h2 := hm38_term_even (a (2 * M + 2)) y hy (M + 1)
    have e1 : 2 * M + 1 + 1 = 2 * M + 2 := by ring
    rw [show 2 * (M + 1) + 1 = 2 * M + 2 + 1 by ring] at h2
    rw [e1, h1, h2]
    simp only [Complex.ofReal_add, mul_add]
    abel

lemma hm38_pt (x t y : ℝ) (hy : 1 ≤ y) :
    (x : ℂ) / ((t : ℂ) - Complex.I * (y : ℂ)) =
      ((x * (t / (t ^ 2 + y ^ 2)) : ℝ) : ℂ) + Complex.I * ((x * (y / (t ^ 2 + y ^ 2)) : ℝ) : ℂ) := by
  have h1 : t ^ 2 + y ^ 2 ≠ 0 := by positivity
  have h2 : (t : ℂ) - Complex.I * (y : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have h1' : (t : ℂ) ^ 2 + (y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast h1
  push_cast
  rw [div_eq_iff h2]
  field_simp
  linear_combination ((x:ℂ) * (y:ℂ)^2) * Complex.I_sq


lemma hm38_cdecomp (v : ℝ → ℝ) (hv0 : ∀ t, 0 ≤ v t) (hvm : Measurable v)
    (hvi : Integrable (fun t => v t / (1 + |t|))) (y : ℝ) (hy : 1 ≤ y) :
    (∫ t, (v t : ℂ) / ((t : ℂ) - Complex.I * (y : ℂ))) =
      ((∫ t, v t * (t / (t ^ 2 + y ^ 2)) : ℝ) : ℂ)
        + Complex.I * ((∫ t, v t * (y / (t ^ 2 + y ^ 2)) : ℝ) : ℂ) := by
  have hG := hm38_intG v hv0 hvm hvi y hy
  have hH : Integrable (fun t => v t * (y / (t ^ 2 + y ^ 2))) := by
    have := (hm38_intK v hv0 hvm hvi y hy).const_mul y⁻¹
    refine this.congr (Filter.Eventually.of_forall (fun t => ?_))
    have : t ^ 2 + y ^ 2 ≠ 0 := by positivity
    have : y ≠ 0 := by positivity
    simp only
    field_simp
  simp_rw [hm38_pt (v _) _ y hy]
  rw [integral_add hG.ofReal (hH.ofReal.const_mul _), integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]

lemma hm38_Sv (v : ℝ → ℝ) (y : ℝ) :
    (∫ t, v t * (y ^ 2 / (t ^ 2 + y ^ 2))) = y * ∫ t, v t * (y / (t ^ 2 + y ^ 2)) := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  simp only
  ring

lemma hm38_Sw (v : ℝ → ℝ) (y : ℝ) :
    (∫ t, (t * v t) * (y ^ 2 / (t ^ 2 + y ^ 2))) = y ^ 2 * ∫ t, v t * (t / (t ^ 2 + y ^ 2)) := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  simp only
  ring

lemma hm38_sign (j : ℕ) (ar ν : ℝ) (h : (-1 : ℝ) ^ (j + 1) * ar = (-1 : ℝ) ^ j * ν / Real.pi) :
    ar = -(ν / Real.pi) := by
  have h5 : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have h' : (-1 : ℝ) ^ (j + 1) * ar = (-1 : ℝ) ^ j * (ν / Real.pi) := by rw [h]; ring
  linear_combination (-(-1 : ℝ) ^ j) * h' + (-(ar + ν / Real.pi)) * h5

/-- real part sum of the expansion (odd orders) -/
noncomputable def hm38_O (ar : ℕ → ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range M, (-1 : ℝ) ^ (i + 1) * ar (2 * i + 1) / y ^ (2 * i + 2)

/-- imaginary part sum of the expansion (even orders) -/
noncomputable def hm38_E (ar : ℕ → ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (M + 1), (-1 : ℝ) ^ (j + 1) * ar (2 * j) / y ^ (2 * j + 1)

theorem herglotz_moments_of_expansion_E02_38 (v : ℝ → ℝ) (hv0 : ∀ t, 0 ≤ v t) (hvm : Measurable v)
    (hvi : Integrable (fun t => v t / (1 + |t|))) (M : ℕ) (a : ℕ → ℂ)
    (ha : ∀ m ≤ 2 * M, (a m).im = 0)
    (hexp : Tendsto (fun y : ℝ => (y : ℂ) ^ (2 * M + 1) * ((1 / Real.pi : ℂ) *
        (∫ t, (v t : ℂ) / ((t : ℂ) - Complex.I * y)) -
        ∑ m ∈ Finset.range (2 * M + 1), a m / (Complex.I * y) ^ (m + 1))) atTop (𝓝 0)) :
    ∀ m ≤ 2 * M, Integrable (fun t => t ^ m * v t) ∧
      a m = -(1 / Real.pi : ℂ) * ∫ t, (t ^ m * v t : ℝ) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have haC : ∀ m ≤ 2 * M, a m = ((a m).re : ℂ) := fun m hm =>
    Complex.ext (by simp) (by simp [ha m hm])
  set ar : ℕ → ℝ := fun m => (a m).re with har
  have hform : ∀ y : ℝ, 1 ≤ y → (y : ℂ) ^ (2 * M + 1) * ((1 / Real.pi : ℂ) *
        (∫ t, (v t : ℂ) / ((t : ℂ) - Complex.I * y)) -
        ∑ m ∈ Finset.range (2 * M + 1), a m / (Complex.I * y) ^ (m + 1)) =
      ((y ^ (2 * M + 1) * ((∫ t, v t * (t / (t ^ 2 + y ^ 2))) / Real.pi - hm38_O ar M y) : ℝ) : ℂ)
      + Complex.I * ((y ^ (2 * M + 1) * ((∫ t, v t * (y / (t ^ 2 + y ^ 2))) / Real.pi
          - hm38_E ar M y) : ℝ) : ℂ) := by
    intro y hy
    have hy0 : y ≠ 0 := by positivity
    rw [hm38_cdecomp v hv0 hvm hvi y hy]
    have hs : ∑ m ∈ Finset.range (2 * M + 1), a m / (Complex.I * (y : ℂ)) ^ (m + 1)
        = ∑ m ∈ Finset.range (2 * M + 1), (ar m : ℂ) / (Complex.I * (y : ℂ)) ^ (m + 1) :=
      Finset.sum_congr rfl (fun m hm => by
        rw [← haC m (by have := Finset.mem_range.mp hm; omega)])
    have hsp : ∑ m ∈ Finset.range (2 * M + 1), (ar m : ℂ) / (Complex.I * (y : ℂ)) ^ (m + 1)
        = ((hm38_O ar M y : ℝ) : ℂ) + Complex.I * ((hm38_E ar M y : ℝ) : ℂ) :=
      hm38_sum_split ar y hy0 M
    rw [hs, hsp]
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_one]
    ring
  have hRe : Tendsto (fun y : ℝ => y ^ (2 * M + 1) *
        ((∫ t, v t * (t / (t ^ 2 + y ^ 2))) / Real.pi - hm38_O ar M y)) atTop (𝓝 0) := by
    have h := (Complex.continuous_re.tendsto 0).comp hexp
    rw [Complex.zero_re] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    simp only [Function.comp]
    rw [hform y hy]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hIm : Tendsto (fun y : ℝ => y ^ (2 * M + 1) *
        ((∫ t, v t * (y / (t ^ 2 + y ^ 2))) / Real.pi - hm38_E ar M y)) atTop (𝓝 0) := by
    have h := (Complex.continuous_im.tendsto 0).comp hexp
    rw [Complex.zero_im] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    simp only [Function.comp]
    rw [hform y hy]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, zero_add, one_mul]
  -- even moments
  set b : ℕ → ℝ := fun j => (-1 : ℝ) ^ (j + 1) * ar (2 * j) with hbdef
  have h0e : Tendsto (fun y : ℝ => y ^ (2 * M) * ((∫ t, v t * (y ^ 2 / (t ^ 2 + y ^ 2))) / Real.pi
        - ∑ i ∈ Finset.range (M + 1), b i / y ^ (2 * i))) atTop (𝓝 0) := by
    refine hIm.congr' ?_
    filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
    have hy0 : y ≠ 0 := by positivity
    rw [hm38_Sv]
    have : y * hm38_E ar M y = ∑ i ∈ Finset.range (M + 1), b i / y ^ (2 * i) := by
      unfold hm38_E
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hbdef]
      have : y ^ (2 * i) ≠ 0 := by positivity
      field_simp
      ring
    rw [← this]
    field_simp
    ring
  have hev := hm38_even_ind v hv0 hvm hvi M b h0e
  -- odd moments
  set b' : ℕ → ℝ := fun j => (-1 : ℝ) ^ (j + 1) * ar (2 * j + 1) with hbdef'
  have hod : ∀ j < M, Integrable (fun t => t ^ (2 * j) * (t * v t)) ∧
      b' j = (-1 : ℝ) ^ j * (∫ t, t ^ (2 * j) * (t * v t)) / Real.pi := by
    cases M with
    | zero => intro j hj; omega
    | succ M' =>
      refine hm38_odd_ind v hv0 hvm (M' + 1) (fun j hj => (hev j hj).1) (M' + 1) (2 * M' + 1)
        le_rfl (by omega) b' ?_
      refine hRe.congr' ?_
      filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
      have hy0 : y ≠ 0 := by positivity
      rw [hm38_Sw]
      have : y ^ 2 * hm38_O ar (M' + 1) y = ∑ i ∈ Finset.range (M' + 1), b' i / y ^ (2 * i) := by
        unfold hm38_O
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp only [hbdef']
        have : y ^ (2 * i) ≠ 0 := by positivity
        field_simp
        ring
      rw [← this]
      have : y ^ (2 * (M' + 1) + 1) = y ^ (2 * M' + 1) * y ^ 2 := by ring
      rw [this]
      ring
  intro m hm
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' m
  · subst hj
    obtain ⟨hI, hb⟩ := hev j (by omega)
    refine ⟨hI, ?_⟩
    have h1 : ar (2 * j) = -((∫ t, t ^ (2 * j) * v t) / Real.pi) := hm38_sign j _ _ hb
    rw [haC _ hm]
    show ((ar (2 * j) : ℝ) : ℂ) = _
    rw [h1]
    push_cast
    ring
  · subst hj
    obtain ⟨hI, hb⟩ := hod j (by omega)
    have e : ∀ t : ℝ, t ^ (2 * j + 1) * v t = t ^ (2 * j) * (t * v t) := fun t => by ring
    simp only [e]
    refine ⟨hI, ?_⟩
    have h1 : ar (2 * j + 1) = -((∫ t, t ^ (2 * j) * (t * v t)) / Real.pi) := hm38_sign j _ _ hb
    rw [haC _ hm]
    show ((ar (2 * j + 1) : ℝ) : ℂ) = _
    rw [h1]
    push_cast
    ring
