import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB6Fejer

/-! # Track B, package 3: Fejér pairing against the cubic nonlinearity

For `f, h ∈ L⁴(𝕋)` and every `λ > 0`:
`|fejP N f̂ (N(h))^| ≤ 2 (‖f‖⁴₄ / (4λ¹²) + ¾ λ⁴ ‖h‖⁴₄)` (Young's inequality `ab³ ≤ a⁴/4 + 3b⁴/4`
and the two unit marginals of the nonnegative Fejér kernel), the same bound for `∫ conj(f) N(h)`,
and `fejP N ĥ (N(h))^ → ∫ conj(h) N(h)` (`fejP_cubic_tendsto`; density of trigonometric
polynomials in `L⁴`, Mathlib `span_fourierLp_closure_eq_top`). Here `N(z) = cubicNL z = 2|z|²z`.
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory Filter Topology NlsGge.Pilot
open scoped ComplexConjugate ENNReal
set_option autoImplicit false
noncomputable section

attribute [local instance] isProbabilityMeasure_spatial

theorem amgm4 {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) : A * B ^ 3 ≤ A ^ 4 / 4 + 3 / 4 * B ^ 4 := by
  nlinarith [mul_nonneg (sq_nonneg (A - B)) (by positivity : (0 : ℝ) ≤ A ^ 2 + 2 * A * B + 3 * B ^ 2)]

theorem young4 {a b l : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 < l) :
    a * b ^ 3 ≤ a ^ 4 / (4 * l ^ 12) + 3 / 4 * l ^ 4 * b ^ 4 := by
  have h := amgm4 (div_nonneg ha (pow_nonneg hl.le 3)) (mul_nonneg hl.le hb)
  have e1 : a / l ^ 3 * (l * b) ^ 3 = a * b ^ 3 := by
    rw [div_mul_eq_mul_div, div_eq_iff (by positivity)]
    ring
  have e2 : (a / l ^ 3) ^ 4 / 4 = a ^ 4 / (4 * l ^ 12) := by ring
  have e3 : 3 / 4 * (l * b) ^ 4 = 3 / 4 * l ^ 4 * b ^ 4 := by ring
  rw [e1, e2, e3] at h
  exact h

theorem norm_cubicNL (z : ℂ) : ‖cubicNL z‖ = 2 * ‖z‖ ^ 3 := by
  unfold cubicNL
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_two_complex]
  ring

theorem young_cubic (u v : ℂ) {l : ℝ} (hl : 0 < l) :
    ‖u‖ * ‖cubicNL v‖ ≤ 2 * (‖u‖ ^ 4 / (4 * l ^ 12) + 3 / 4 * l ^ 4 * ‖v‖ ^ 4) := by
  rw [norm_cubicNL]
  have := young4 (norm_nonneg u) (norm_nonneg v) hl
  nlinarith

theorem integrable_norm_pow4 {f : PhysicalCircle → ℂ} (hf : MemLp f 4 spatialMeasure) :
    Integrable (fun x => ‖f x‖ ^ 4) spatialMeasure := by
  have h := hf.integrable_norm_rpow (by norm_num) (by norm_num)
  simpa using h

theorem integrable_fejK_mul_fst (N : ℕ) {F : PhysicalCircle → ℝ} (hF : Integrable F spatialMeasure) :
    Integrable (fun p : PhysicalCircle × PhysicalCircle => fejK N p * F p.1)
      (spatialMeasure.prod spatialMeasure) := by
  have h : Integrable (fun p : PhysicalCircle × PhysicalCircle => F p.1 * (1 : ℝ))
      (spatialMeasure.prod spatialMeasure) := hF.mul_prod (integrable_const 1)
  simp only [mul_one] at h
  exact h.bdd_mul (c := N) (continuous_fejK N).aestronglyMeasurable
    (ae_of_all _ fun p => by rw [Real.norm_of_nonneg (fejK_nonneg N p)]; exact fejK_le N p)

theorem integrable_fejK_mul_snd (N : ℕ) {F : PhysicalCircle → ℝ} (hF : Integrable F spatialMeasure) :
    Integrable (fun p : PhysicalCircle × PhysicalCircle => fejK N p * F p.2)
      (spatialMeasure.prod spatialMeasure) := by
  have h : Integrable (fun p : PhysicalCircle × PhysicalCircle => (1 : ℝ) * F p.2)
      (spatialMeasure.prod spatialMeasure) := (integrable_const 1).mul_prod hF
  simp only [one_mul] at h
  exact h.bdd_mul (c := N) (continuous_fejK N).aestronglyMeasurable
    (ae_of_all _ fun p => by rw [Real.norm_of_nonneg (fejK_nonneg N p)]; exact fejK_le N p)

theorem integral_fejK_mul_fst (N : ℕ) (hN : 0 < N) {F : PhysicalCircle → ℝ}
    (hF : Integrable F spatialMeasure) :
    ∫ p, fejK N p * F p.1 ∂(spatialMeasure.prod spatialMeasure) = ∫ x, F x ∂spatialMeasure := by
  rw [integral_prod _ (integrable_fejK_mul_fst N hF)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [integral_mul_const, integral_fejK_right N hN, one_mul]

theorem integral_fejK_mul_snd (N : ℕ) (hN : 0 < N) {F : PhysicalCircle → ℝ}
    (hF : Integrable F spatialMeasure) :
    ∫ p, fejK N p * F p.2 ∂(spatialMeasure.prod spatialMeasure) = ∫ x, F x ∂spatialMeasure := by
  rw [integral_prod_symm _ (integrable_fejK_mul_snd N hF)]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only
  rw [integral_mul_const, integral_fejK_left N hN, one_mul]

/-- **Uniform bound** for the Fejér pairing against the cubic nonlinearity. -/
theorem fejP_cubic_bound (N : ℕ) (hN : 0 < N) {f h : PhysicalCircle → ℂ}
    (hf : MemLp f 4 spatialMeasure) (hh : MemLp h 4 spatialMeasure) {l : ℝ} (hl : 0 < l) :
    ‖fejP N (physicalFourier f) (physicalFourier (fun x => cubicNL (h x)))‖ ≤
      2 * ((∫ x, ‖f x‖ ^ 4 ∂spatialMeasure) / (4 * l ^ 12) +
        3 / 4 * l ^ 4 * ∫ x, ‖h x‖ ^ 4 ∂spatialMeasure) := by
  have hfi : Integrable f spatialMeasure := hf.integrable (by norm_num)
  have hG : Integrable (fun x => cubicNL (h x)) spatialMeasure :=
    (memLp_cubic hh).integrable one_le_four_thirds
  set F1 : PhysicalCircle → ℝ := fun x => 2 * (‖f x‖ ^ 4 / (4 * l ^ 12)) with hF1
  set F2 : PhysicalCircle → ℝ := fun x => 2 * (3 / 4 * l ^ 4 * ‖h x‖ ^ 4) with hF2
  have hF1i : Integrable F1 spatialMeasure :=
    ((integrable_norm_pow4 hf).div_const _).const_mul 2
  have hF2i : Integrable F2 spatialMeasure :=
    ((integrable_norm_pow4 hh).const_mul _).const_mul 2
  rw [fejer_kernel_identity N hfi hG]
  refine (norm_integral_le_of_norm_le ((integrable_fejK_mul_fst N hF1i).add
    (integrable_fejK_mul_snd N hF2i)) (ae_of_all _ fun p => ?_)).trans (le_of_eq ?_)
  · simp only [Pi.add_apply]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (fejK_nonneg N p),
      Complex.norm_conj, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (fejK_nonneg N p)
    have := young_cubic (f p.1) (h p.2) hl
    simp only [hF1, hF2]
    linarith
  · simp only [Pi.add_apply]
    rw [integral_add (integrable_fejK_mul_fst N hF1i) (integrable_fejK_mul_snd N hF2i),
      integral_fejK_mul_fst N hN hF1i, integral_fejK_mul_snd N hN hF2i, hF1, hF2,
      integral_const_mul, integral_const_mul, integral_div, integral_const_mul]
    ring

theorem integrable_conj_mul_cubic {f h : PhysicalCircle → ℂ}
    (hf : MemLp f 4 spatialMeasure) (hh : MemLp h 4 spatialMeasure) :
    Integrable (fun x => conj (f x) * cubicNL (h x)) spatialMeasure := by
  refine Integrable.mono' (((integrable_norm_pow4 hf).div_const (4 * (1 : ℝ) ^ 12)).add
    ((integrable_norm_pow4 hh).const_mul (3 / 4 * (1 : ℝ) ^ 4)) |>.const_mul 2) ?_
    (ae_of_all _ fun x => ?_)
  · exact (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable).mul
      (continuous_cubicNL.comp_aestronglyMeasurable hh.aestronglyMeasurable)
  · rw [norm_mul, Complex.norm_conj]
    exact young_cubic (f x) (h x) one_pos

/-- Same bound for the diagonal pairing `∫ conj(f) N(h)`. -/
theorem diag_cubic_bound {f h : PhysicalCircle → ℂ}
    (hf : MemLp f 4 spatialMeasure) (hh : MemLp h 4 spatialMeasure) {l : ℝ} (hl : 0 < l) :
    ‖∫ x, conj (f x) * cubicNL (h x) ∂spatialMeasure‖ ≤
      2 * ((∫ x, ‖f x‖ ^ 4 ∂spatialMeasure) / (4 * l ^ 12) +
        3 / 4 * l ^ 4 * ∫ x, ‖h x‖ ^ 4 ∂spatialMeasure) := by
  have hi : Integrable (fun x => 2 * (‖f x‖ ^ 4 / (4 * l ^ 12) + 3 / 4 * l ^ 4 * ‖h x‖ ^ 4))
      spatialMeasure :=
    (((integrable_norm_pow4 hf).div_const _).add ((integrable_norm_pow4 hh).const_mul _)).const_mul 2
  refine (norm_integral_le_of_norm_le hi (ae_of_all _ fun x => ?_)).trans (le_of_eq ?_)
  · rw [norm_mul, Complex.norm_conj]
    exact young_cubic (f x) (h x) hl
  · rw [integral_const_mul, integral_add ((integrable_norm_pow4 hf).div_const _)
      ((integrable_norm_pow4 hh).const_mul _), integral_div, integral_const_mul]

/-! ### Linearity of the Fejér pairing and trigonometric polynomials -/

theorem fejP_add (N : ℕ) (a a' b : ℤ → ℂ) :
    fejP N (fun n => a n + a' n) b = fejP N a b + fejP N a' b := by
  unfold fejP
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_add, add_mul]

theorem fejP_smul (N : ℕ) (c : ℂ) (a b : ℤ → ℂ) :
    fejP N (fun n => c * a n) b = conj c * fejP N a b := by
  unfold fejP
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul]
  ring

theorem fejP_zero (N : ℕ) (b : ℤ → ℂ) : fejP N (fun _ => 0) b = 0 := by
  unfold fejP
  simp

theorem fejP_sum (N : ℕ) (S : Finset ℤ) (c : ℤ → ℂ) (b : ℤ → ℂ) :
    fejP N (fun n => ∑ i ∈ S, c i * (if n = i then 1 else 0)) b =
      ∑ i ∈ S, conj (c i) * fejP N (fun n => if n = i then 1 else 0) b := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact fejP_zero N b
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [fejP_add, fejP_smul, ih]

/-- Trigonometric polynomial `Σ_{i∈S} c_i e_i`. -/
def trigP (S : Finset ℤ) (c : ℤ → ℂ) (x : PhysicalCircle) : ℂ := ∑ i ∈ S, c i * fourier i x

theorem continuous_trigP (S : Finset ℤ) (c : ℤ → ℂ) : Continuous (trigP S c) := by
  unfold trigP
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (map_continuous (fourier i))

theorem norm_trigP_le (S : Finset ℤ) (c : ℤ → ℂ) (x : PhysicalCircle) :
    ‖trigP S c x‖ ≤ ∑ i ∈ S, ‖c i‖ := by
  unfold trigP
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [norm_mul, norm_fourier_apply, mul_one]

theorem memLp_trigP (S : Finset ℤ) (c : ℤ → ℂ) : MemLp (trigP S c) 4 spatialMeasure :=
  MemLp.of_bound (continuous_trigP S c).aestronglyMeasurable _
    (ae_of_all _ fun x => norm_trigP_le S c x)

theorem physicalFourier_eq_conj (f : PhysicalCircle → ℂ) (n : ℤ) :
    physicalFourier f n = ∫ x, conj (fourier n x) * f x ∂spatialMeasure := by
  unfold physicalFourier fourierCoeff spatialMeasure
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [smul_eq_mul]
  rw [fourier_neg]

theorem integrable_char {i j : ℤ} :
    Integrable (fun x : PhysicalCircle => conj (fourier i x) * fourier j x) spatialMeasure :=
  integrable_cont_bdd (f := fun x => conj (fourier i x) * fourier j x)
    ((Complex.continuous_conj.comp (map_continuous (fourier i))).mul (map_continuous (fourier j)))
    (fun x => by simp only [norm_mul, Complex.norm_conj, norm_fourier_apply, one_mul, le_refl])

theorem physicalFourier_trigP (S : Finset ℤ) (c : ℤ → ℂ) (n : ℤ) :
    physicalFourier (trigP S c) n = ∑ i ∈ S, c i * (if n = i then 1 else 0) := by
  rw [physicalFourier_eq_conj]
  unfold trigP
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => (integrable_char (i := n) (j := i)).const_mul (c i) |>.congr
    (ae_of_all _ fun x => by simp only; ring))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_conj_fourier_mul, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun x => by simp only; ring)

theorem integral_conj_trigP_mul (S : Finset ℤ) (c : ℤ → ℂ) {G : PhysicalCircle → ℂ}
    (hG : Integrable G spatialMeasure) :
    ∫ x, conj (trigP S c x) * G x ∂spatialMeasure =
      ∑ i ∈ S, conj (c i) * physicalFourier G i := by
  unfold trigP
  simp_rw [map_sum, Finset.sum_mul]
  have hi : ∀ i : ℤ, Integrable (fun x => conj (c i * fourier i x) * G x) spatialMeasure :=
    fun i => (hG.bdd_mul (c := ‖c i‖) ((Complex.continuous_conj.comp
      (continuous_const.mul (map_continuous (fourier i)))).aestronglyMeasurable)
      (ae_of_all _ fun x => by
        simp only [map_mul, norm_mul, Complex.norm_conj, norm_fourier_apply,
          mul_one, le_refl]))
  rw [integral_finsetSum _ (fun i _ => hi i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [physicalFourier_eq_conj, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun x => by simp only [map_mul]; ring)

/-! ### Density of trigonometric polynomials in `L⁴` -/

theorem integral_norm_pow4_eq {f : PhysicalCircle → ℂ} (hf : MemLp f 4 spatialMeasure) :
    ∫ x, ‖f x‖ ^ 4 ∂spatialMeasure = ((eLpNorm f 4 spatialMeasure).toReal) ^ 4 := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  have e : (4 : ℝ≥0∞).toReal = ((4 : ℕ) : ℝ) := by norm_num
  rw [e, Real.rpow_inv_natCast_pow (integral_nonneg fun x => by positivity) (by norm_num)]
  simp_rw [Real.rpow_natCast]

theorem exists_trig_L4 {h : PhysicalCircle → ℂ} (hh : MemLp h 4 spatialMeasure) {η : ℝ}
    (hη : 0 < η) : ∃ (S : Finset ℤ) (c : ℤ → ℂ),
      ∫ x, ‖h x - trigP S c x‖ ^ 4 ∂spatialMeasure < η := by
  have : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hh' : MemLp h 4 (AddCircle.haarAddCircle (T := 1)) := hh
  set h' : Lp ℂ 4 (AddCircle.haarAddCircle (T := 1)) := hh'.toLp h
  have hcl := span_fourierLp_closure_eq_top (T := 1) (p := 4) (by norm_num)
  have hmem : h' ∈ ((Submodule.span ℂ (Set.range (fourierLp (T := 1) 4))).topologicalClosure :
      Set (Lp ℂ 4 (AddCircle.haarAddCircle (T := 1)))) := by
    rw [hcl]; trivial
  rw [Submodule.topologicalClosure_coe] at hmem
  set ε : ℝ := min 1 (η / 2) with hεdef
  have hε : 0 < ε := lt_min one_pos (by linarith)
  obtain ⟨q, hq, hdist⟩ := Metric.mem_closure_iff.1 hmem ε hε
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hq
  refine ⟨c.support, c, ?_⟩
  have hqe : (q : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] trigP c.support c := by
    have hq2 : q = ContinuousMap.toLp (E := ℂ) 4 (AddCircle.haarAddCircle (T := 1)) ℂ
        (∑ i ∈ c.support, c i • fourier i) := by
      rw [← hc, Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
    rw [hq2]
    refine (ContinuousMap.coeFn_toLp _ _).trans (ae_of_all _ fun x => ?_)
    simp [trigP, ContinuousMap.coe_sum, Finset.sum_apply, smul_eq_mul]
  have hfe : (⇑(h' - q) : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
      fun x => h x - trigP c.support c x := by
    filter_upwards [Lp.coeFn_sub h' q, hh'.coeFn_toLp, hqe] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have hmemf : MemLp (fun x => h x - trigP c.support c x) 4 spatialMeasure :=
    hh.sub (memLp_trigP _ _)
  rw [integral_norm_pow4_eq hmemf, ← eLpNorm_congr_ae hfe]
  have hn : (eLpNorm (⇑(h' - q)) 4 spatialMeasure).toReal = dist h' q := by
    rw [dist_eq_norm, Lp.norm_def]
    rfl
  rw [hn]
  have hd0 : 0 ≤ dist h' q := dist_nonneg
  have hε1 : ε ≤ 1 := min_le_left _ _
  calc dist h' q ^ 4 ≤ ε ^ 4 := pow_le_pow_left₀ hd0 hdist.le 4
    _ ≤ ε := pow_le_of_le_one hε.le hε1 (by norm_num)
    _ ≤ η / 2 := min_le_right _ _
    _ < η := by linarith

/-! ### Convergence -/

/-- **Fejér convergence** against the cubic nonlinearity, for `h ∈ L⁴(𝕋)`. -/
theorem fejP_cubic_tendsto {h : PhysicalCircle → ℂ} (hh : MemLp h 4 spatialMeasure) :
    Tendsto (fun N => fejP N (physicalFourier h) (physicalFourier (fun x => cubicNL (h x))))
      atTop (𝓝 (∫ x, conj (h x) * cubicNL (h x) ∂spatialMeasure)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M : ℝ := ∫ x, ‖h x‖ ^ 4 ∂spatialMeasure with hMdef
  have hM : 0 ≤ M := integral_nonneg fun x => by positivity
  set l : ℝ := min 1 (ε / (8 * (M + 1))) with hldef
  have hl : 0 < l := lt_min one_pos (by positivity)
  have hl1 : l ≤ 1 := min_le_left _ _
  have hlM : 3 / 2 * l ^ 4 * M ≤ 3 * ε / 16 := by
    have h4 : l ^ 4 ≤ l := pow_le_of_le_one hl.le hl1 (by norm_num)
    have h2 : l ≤ ε / (8 * (M + 1)) := min_le_right _ _
    have h3 : l * M ≤ ε / 8 := by
      calc l * M ≤ ε / (8 * (M + 1)) * M := mul_le_mul_of_nonneg_right h2 hM
        _ ≤ ε / 8 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h4 hM]
  set η : ℝ := l ^ 12 * ε / 4 with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨S, c, hP⟩ := exists_trig_L4 hh hη
  set P := trigP S c with hPdef
  set f : PhysicalCircle → ℂ := fun x => h x - P x with hfdef
  have hf : MemLp f 4 spatialMeasure := hh.sub (memLp_trigP S c)
  have hfP : f + P = h := funext fun x => by simp [hfdef]
  have hG : Integrable (fun x => cubicNL (h x)) spatialMeasure :=
    (memLp_cubic hh).integrable one_le_four_thirds
  have hsplit : ∀ N, fejP N (physicalFourier h) (physicalFourier (fun x => cubicNL (h x))) =
      fejP N (physicalFourier f) (physicalFourier (fun x => cubicNL (h x))) +
        fejP N (physicalFourier P) (physicalFourier (fun x => cubicNL (h x))) := by
    intro N
    rw [← fejP_add]
    congr 1
    funext n
    rw [← hfP, physicalFourier_add_of_integrable (hf.integrable (by norm_num))
      ((memLp_trigP S c).integrable (by norm_num))]
    rfl
  have hdsplit : ∫ x, conj (h x) * cubicNL (h x) ∂spatialMeasure =
      ∫ x, conj (f x) * cubicNL (h x) ∂spatialMeasure +
        ∫ x, conj (P x) * cubicNL (h x) ∂spatialMeasure := by
    rw [← integral_add (integrable_conj_mul_cubic hf hh)
      (integrable_conj_mul_cubic (memLp_trigP S c) hh)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hfdef, map_sub]
    ring
  have hmid : Tendsto (fun N => fejP N (physicalFourier P)
      (physicalFourier (fun x => cubicNL (h x)))) atTop
      (𝓝 (∫ x, conj (P x) * cubicNL (h x) ∂spatialMeasure)) := by
    have e : ∀ N, fejP N (physicalFourier P) (physicalFourier (fun x => cubicNL (h x))) =
        ∑ i ∈ S, conj (c i) * fejP N (fun n => if n = i then 1 else 0)
          (physicalFourier (fun x => cubicNL (h x))) := fun N => by
      rw [← fejP_sum]
      congr 1
      funext n
      exact physicalFourier_trigP S c n
    simp_rw [e]
    rw [hPdef, integral_conj_trigP_mul S c hG]
    exact tendsto_finsetSum _ fun i _ => (fejP_single_tendsto i _).const_mul _
  have hbd : 2 * ((∫ x, ‖f x‖ ^ 4 ∂spatialMeasure) / (4 * l ^ 12) + 3 / 4 * l ^ 4 * M) ≤
      5 * ε / 16 := by
    have h1 : (∫ x, ‖f x‖ ^ 4 ∂spatialMeasure) / (4 * l ^ 12) ≤ ε / 16 := by
      rw [div_le_iff₀ (by positivity)]
      have : (∫ x, ‖f x‖ ^ 4 ∂spatialMeasure) < η := hP
      rw [hηdef] at this
      nlinarith [pow_pos hl 12]
    nlinarith
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 hmid (ε / 4) (by positivity)
  refine ⟨max N1 1, fun N hN => ?_⟩
  have hN0 : 0 < N := lt_of_lt_of_le one_pos (le_of_max_le_right hN)
  rw [hsplit, hdsplit, dist_eq_norm]
  have e1 := fejP_cubic_bound N hN0 hf hh hl
  have e2 := diag_cubic_bound hf hh hl
  have e3 := hN1 N (le_of_max_le_left hN)
  rw [dist_eq_norm] at e3
  calc ‖fejP N (physicalFourier f) (physicalFourier (fun x => cubicNL (h x))) +
        fejP N (physicalFourier P) (physicalFourier (fun x => cubicNL (h x))) -
        ((∫ x, conj (f x) * cubicNL (h x) ∂spatialMeasure) +
          ∫ x, conj (P x) * cubicNL (h x) ∂spatialMeasure)‖
      = ‖fejP N (physicalFourier f) (physicalFourier (fun x => cubicNL (h x))) +
          (fejP N (physicalFourier P) (physicalFourier (fun x => cubicNL (h x))) -
            ∫ x, conj (P x) * cubicNL (h x) ∂spatialMeasure) -
          ∫ x, conj (f x) * cubicNL (h x) ∂spatialMeasure‖ := by ring_nf
    _ ≤ ‖fejP N (physicalFourier f) (physicalFourier (fun x => cubicNL (h x)))‖ +
          ‖fejP N (physicalFourier P) (physicalFourier (fun x => cubicNL (h x))) -
            ∫ x, conj (P x) * cubicNL (h x) ∂spatialMeasure‖ +
          ‖∫ x, conj (f x) * cubicNL (h x) ∂spatialMeasure‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ < ε := by linarith

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
