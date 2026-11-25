import QuantumNLS.L4Strichartz

/-!
# EXT-003, stage A (continued): the periodic `L⁴` estimate for every `L²` datum

Source: `ROOT_L2_extension.tex`, proof of `lem:root-L4-duality` (R-02871DC6), lines 47-50:
"Approximation by finite sums proves the bound for arbitrary `f`. The approximating solutions
converge ... in `L⁴` by the bound, so the `L⁴` limit is the Fourier solution."

Imports the frozen stage-A1 module `L4Strichartz` (`546d7e5b…`) read-only.

For `f ∈ L²(𝕋_L)` with coefficients `a = fourierL2 L f` and the Fourier truncations
`u_N(t,x) = Σ_{|n|≤N} a_n e^{−itp_n²} e_n(x)`, on `J = (α, β]` with `β − α ≤ T_L`:
* `‖u_N‖⁴_{L⁴(J×𝕋_L)} = ∫_α^β ∫ |u_N|⁴` and `≤ (2T_L/L)(Σ_{|n|≤N}|a_n|²)²` (stage A1);
* `(u_N)` is Cauchy in `L⁴(J × 𝕋_L)`; its limit `u` satisfies `‖u‖⁴_{L⁴} ≤ (2T_L/L)‖f‖₂⁴`,
  i.e. `‖u‖_{L⁴(J×𝕋_L)} ≤ C_L ‖f‖₂` with `C_L = (2T_L/L)^{1/4}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate BigOperators Topology ENNReal
open MeasureTheory Filter QuantumNLS.Fourier QuantumNLS.LocalWellPosedness QuantumNLS.L4Strichartz

namespace QuantumNLS.L4StrichartzL2

variable {L : ℝ} [Fact (0 < L)]

instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The space-time measure `dt|_{(α,β]} ⊗ dx` on `ℝ × 𝕋_L`. -/
def μJ (α β : ℝ) : Measure (ℝ × AddCircle L) := (volume.restrict (Set.Ioc α β)).prod volume

instance (α β : ℝ) : IsFiniteMeasure (volume.restrict (Set.Ioc α β) : Measure ℝ) :=
  isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne

instance (α β : ℝ) : IsFiniteMeasure (μJ (L := L) α β) := by
  unfold μJ; infer_instance

/-- The window `{|n| ≤ N}`. -/
def win (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) N

lemma win_mono : Monotone win := fun a b hab =>
  Finset.Icc_subset_Icc (neg_le_neg (by exact_mod_cast hab)) (by exact_mod_cast hab)

lemma win_exh (m : ℤ) : ∃ N, m ∈ win N := ⟨m.natAbs, by simp only [win, Finset.mem_Icc]; omega⟩

/-- The free solution as a function on space-time. -/
def solP (S : Finset ℤ) (a : ℤ → ℂ) (p : ℝ × AddCircle L) : ℂ := freeSol S a p.1 p.2

lemma continuous_solP (S : Finset ℤ) (a : ℤ → ℂ) : Continuous (solP (L := L) S a) := by
  unfold solP freeSol
  exact continuous_finsetSum _ fun n _ => (continuous_const.mul
    ((continuous_phase L n).comp continuous_fst)).mul ((continuous_mode' n).comp continuous_snd)

lemma norm_freeSol_le (S : Finset ℤ) (a : ℤ → ℂ) (t : ℝ) (x : AddCircle L) :
    ‖freeSol S a t x‖ ≤ ∑ n ∈ S, ‖a n‖ * (Real.sqrt L)⁻¹ := by
  unfold freeSol
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, norm_mul, norm_phase, norm_mode, mul_one]

lemma memLp_solP (S : Finset ℤ) (a : ℤ → ℂ) (α β : ℝ) :
    MemLp (solP (L := L) S a) 4 (μJ α β) :=
  MemLp.of_bound (continuous_solP S a).aestronglyMeasurable _
    (Eventually.of_forall fun p => norm_freeSol_le S a p.1 p.2)

/-- `‖u‖⁴_{L⁴(J×𝕋_L)} = ∫_α^β ∫_{𝕋_L} |u|⁴` for a finite Fourier sum. -/
lemma norm_toLp_pow (S : Finset ℤ) (a : ℤ → ℂ) {α β : ℝ} (hαβ : α ≤ β) :
    ‖(memLp_solP S a α β).toLp (solP (L := L) S a)‖ ^ 4 =
      ∫ t in α..β, ∫ x, ‖freeSol (L := L) S a t x‖ ^ 4 := by
  have hm := memLp_solP (L := L) S a α β
  rw [Lp.norm_toLp, hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofNat]
  have hI : 0 ≤ ∫ p, ‖solP (L := L) S a p‖ ^ (4 : ℝ) ∂(μJ α β) :=
    integral_nonneg fun p => by positivity
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _),
    show ((4 : ℝ))⁻¹ = ((4 : ℕ) : ℝ)⁻¹ by norm_num, Real.rpow_inv_natCast_pow hI (by norm_num)]
  have hfun : (fun p => ‖solP (L := L) S a p‖ ^ (4 : ℝ)) = fun p => ‖solP (L := L) S a p‖ ^ 4 := by
    funext p; exact_mod_cast Real.rpow_natCast _ 4
  rw [hfun]
  have hint : Integrable (fun p => ‖solP (L := L) S a p‖ ^ 4) (μJ α β) :=
    Integrable.of_bound ((continuous_solP S a).norm.pow 4).aestronglyMeasurable
      ((∑ n ∈ S, ‖a n‖ * (Real.sqrt L)⁻¹) ^ 4) (Eventually.of_forall fun p => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_freeSol_le S a p.1 p.2) 4)
  rw [μJ, integral_prod _ hint, intervalIntegral.integral_of_le hαβ]
  rfl

/-- Stage A1 in `L⁴` norm: `‖u_S‖⁴_{L⁴(J×𝕋_L)} ≤ (2T_L/L)(Σ_{n∈S}|a_n|²)²`. -/
lemma norm_toLp_pow_le (S : Finset ℤ) (a : ℤ → ℂ) {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) :
    ‖(memLp_solP S a α β).toLp (solP (L := L) S a)‖ ^ 4 ≤
      2 * TL L / L * (∑ n ∈ S, ‖a n‖ ^ 2) ^ 2 := by
  rw [norm_toLp_pow S a hαβ]
  exact L4_free_bound S a hαβ hlen

lemma solP_sdiff {S S' : Finset ℤ} (h : S' ⊆ S) (a : ℤ → ℂ) :
    solP (L := L) S a - solP S' a = solP (S \ S') a := by
  funext p
  simp only [Pi.sub_apply, solP, freeSol]
  rw [← Finset.sum_sdiff h]; ring

#print axioms norm_toLp_pow
#print axioms norm_toLp_pow_le

/-! ## The `L⁴` limit for an `L²` datum -/

/-- The `n`-th Fourier coefficient sequence of `f`. -/
abbrev coef (f : Lp ℂ 2 (volume : Measure (AddCircle L))) (n : ℤ) : ℂ := fourierL2 L f n

/-- Partial sums `P(N) = Σ_{|n|≤N} |a_n|²`. -/
def Psum (f : Lp ℂ 2 (volume : Measure (AddCircle L))) (N : ℕ) : ℝ :=
  ∑ n ∈ win N, ‖coef f n‖ ^ 2

lemma tendsto_Psum (f : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    Tendsto (Psum f) atTop (𝓝 (‖f‖ ^ 2)) := by
  have hs : HasSum (fun n => ‖coef f n‖ ^ 2) (‖fourierL2 L f‖ ^ 2) := by
    have h := lp.hasSum_norm (p := 2) (by norm_num) (fourierL2 L f)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    exact h
  rw [LinearIsometryEquiv.norm_map] at hs
  exact hs.comp (tendsto_atTop_finset_of_monotone win_mono win_exh)

lemma Psum_mono (f : Lp ℂ 2 (volume : Measure (AddCircle L))) : Monotone (Psum f) :=
  fun _ _ h => Finset.sum_le_sum_of_subset_of_nonneg (win_mono h) fun _ _ _ => sq_nonneg _

lemma Psum_le (f : Lp ℂ 2 (volume : Measure (AddCircle L))) (N : ℕ) : Psum f N ≤ ‖f‖ ^ 2 :=
  (Psum_mono f).ge_of_tendsto (tendsto_Psum f) N

/-- The truncated free solutions `u_N` as elements of `L⁴(J × 𝕋_L)`. -/
def wN (f : Lp ℂ 2 (volume : Measure (AddCircle L))) (α β : ℝ) (N : ℕ) : Lp ℂ 4 (μJ (L := L) α β) :=
  (memLp_solP (win N) (coef f) α β).toLp (solP (win N) (coef f))

lemma norm_wN_sub_pow (f : Lp ℂ 2 (volume : Measure (AddCircle L))) {α β : ℝ} (hαβ : α ≤ β)
    (hlen : β ≤ α + TL L) {M N : ℕ} (h : M ≤ N) :
    ‖wN f α β N - wN f α β M‖ ^ 4 ≤ 2 * TL L / L * (Psum f N - Psum f M) ^ 2 := by
  have e : wN f α β N - wN f α β M =
      (memLp_solP (win N \ win M) (coef f) α β).toLp (solP (L := L) (win N \ win M) (coef f)) := by
    rw [wN, wN, ← MemLp.toLp_sub]
    exact (MemLp.toLp_eq_toLp_iff _ _).mpr
      (Eventually.of_forall fun p => congrFun (solP_sdiff (win_mono h) _) p)
  rw [e]
  refine (norm_toLp_pow_le _ _ hαβ hlen).trans_eq ?_
  rw [Psum, Psum, Finset.sum_sdiff_eq_sub (win_mono h)]

lemma norm_wN_pow (f : Lp ℂ 2 (volume : Measure (AddCircle L))) {α β : ℝ} (hαβ : α ≤ β)
    (hlen : β ≤ α + TL L) (N : ℕ) :
    ‖wN f α β N‖ ^ 4 ≤ 2 * TL L / L * ‖f‖ ^ 4 := by
  have hL : 0 < L := Fact.out
  have hK : 0 ≤ 2 * TL L / L := by have := TL_pos (L := L); positivity
  refine (norm_toLp_pow_le _ _ hαβ hlen).trans ?_
  have h0 : 0 ≤ Psum f N := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 := Psum_le f N
  have h2 : (∑ n ∈ win N, ‖coef f n‖ ^ 2) ^ 2 ≤ ‖f‖ ^ 4 := by
    have := pow_le_pow_left₀ h0 h1 2
    rw [← pow_mul] at this
    exact this
  exact mul_le_mul_of_nonneg_left h2 hK

lemma cauchy_wN (f : Lp ℂ 2 (volume : Measure (AddCircle L))) {α β : ℝ} (hαβ : α ≤ β)
    (hlen : β ≤ α + TL L) : CauchySeq (wN f α β) := by
  have hL : 0 < L := Fact.out
  set K := 2 * TL L / L
  have hK : 0 ≤ K := by have := TL_pos (L := L); positivity
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hP := Metric.cauchySeq_iff'.mp (tendsto_Psum f).cauchySeq
  set δ := ε ^ 2 / (Real.sqrt K + 1)
  have hsK := Real.sqrt_nonneg K
  have hδ : 0 < δ := by positivity
  obtain ⟨M, hM⟩ := hP δ hδ
  refine ⟨M, fun N hN => ?_⟩
  rw [dist_eq_norm]
  have h1 := norm_wN_sub_pow f hαβ hlen hN
  have h2 : |Psum f N - Psum f M| < δ := by have := hM N hN; rwa [Real.dist_eq] at this
  have h3 : (Psum f N - Psum f M) ^ 2 < δ ^ 2 := by
    rw [← sq_abs]; exact pow_lt_pow_left₀ h2 (abs_nonneg _) two_ne_zero
  have h4 : K * δ ^ 2 < ε ^ 4 := by
    have hKs : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK
    have e : K * δ ^ 2 = ε ^ 4 * (K / (Real.sqrt K + 1) ^ 2) := by
      simp only [δ]; field_simp
    rw [e]
    have : K / (Real.sqrt K + 1) ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith
    have hε4 : 0 < ε ^ 4 := by positivity
    nlinarith
  have h5 : ‖wN f α β N - wN f α β M‖ ^ 4 < ε ^ 4 :=
    lt_of_le_of_lt h1 (lt_of_le_of_lt (mul_le_mul_of_nonneg_left h3.le hK) h4)
  exact lt_of_pow_lt_pow_left₀ 4 hε.le h5

/-- **`eq:root-L4-free` for every `L²` datum.** The Fourier truncations of the free solution
converge in `L⁴(J × 𝕋_L)`, `J = (α, β]`, `β − α ≤ T_L`, and the limit `u` (the Fourier solution)
satisfies `‖u‖⁴_{L⁴} ≤ (2T_L/L)‖f‖₂⁴`, i.e. `‖u‖_{L⁴(J×𝕋_L)} ≤ C_L‖f‖₂`, `C_L = (2T_L/L)^{1/4}`. -/
theorem L4_free_L2 (f : Lp ℂ 2 (volume : Measure (AddCircle L))) {α β : ℝ} (hαβ : α ≤ β)
    (hlen : β ≤ α + TL L) :
    ∃ u : Lp ℂ 4 (μJ (L := L) α β), Tendsto (wN f α β) atTop (𝓝 u) ∧
      ‖u‖ ^ 4 ≤ 2 * TL L / L * ‖f‖ ^ 4 ∧
      ‖u‖ ≤ (2 * TL L / L) ^ (4⁻¹ : ℝ) * ‖f‖ := by
  have hL : 0 < L := Fact.out
  have hK : 0 ≤ 2 * TL L / L := by have := TL_pos (L := L); positivity
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete (cauchy_wN f hαβ hlen)
  have h4 : ‖u‖ ^ 4 ≤ 2 * TL L / L * ‖f‖ ^ 4 :=
    le_of_tendsto (((continuous_pow 4).tendsto _).comp ((continuous_norm.tendsto u).comp hu))
      (Eventually.of_forall fun N => show ‖wN f α β N‖ ^ 4 ≤ _ from norm_wN_pow f hαβ hlen N)
  refine ⟨u, hu, h4, ?_⟩
  have hr : ‖u‖ = (‖u‖ ^ 4) ^ (4⁻¹ : ℝ) := by
    rw [show (4⁻¹ : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast (norm_nonneg _)
      (by norm_num)]
  rw [hr]
  calc (‖u‖ ^ 4) ^ (4⁻¹ : ℝ) ≤ (2 * TL L / L * ‖f‖ ^ 4) ^ (4⁻¹ : ℝ) :=
        Real.rpow_le_rpow (by positivity) h4 (by norm_num)
    _ = (2 * TL L / L) ^ (4⁻¹ : ℝ) * ‖f‖ := by
        rw [Real.mul_rpow hK (by positivity), show (4⁻¹ : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
          Real.pow_rpow_inv_natCast (norm_nonneg _) (by norm_num)]

#print axioms cauchy_wN
#print axioms L4_free_L2

/-! ## The `L⁴` limit is the Fourier solution: slice identification -/

/-- The coefficients `(e^{−itp_n²} a_n)_n` of `U(t)f`, an element of `ℓ²`. -/
def evolCoef (f : Lp ℂ 2 (volume : Measure (AddCircle L))) (t : ℝ) : lp (fun _ : ℤ => ℂ) 2 :=
  ⟨fun n => phase L t n * coef f n, by
    refine memℓp_gen ?_
    refine ((lp.memℓp (fourierL2 L f)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).congr
      fun n => ?_
    rw [norm_mul, norm_phase, one_mul]⟩

/-- `U(t)f = e^{it∂²}f ∈ L²(𝕋_L)`. -/
def evol (f : Lp ℂ 2 (volume : Measure (AddCircle L))) (t : ℝ) :
    Lp ℂ 2 (volume : Measure (AddCircle L)) :=
  (fourierL2 L).symm (evolCoef f t)

lemma fourierL2_evol (f : Lp ℂ 2 (volume : Measure (AddCircle L))) (t : ℝ) (n : ℤ) :
    fourierL2 L (evol f t) n = phase L t n * coef f n := by
  rw [evol, LinearIsometryEquiv.apply_symm_apply]; rfl

lemma memLp2_slice (S : Finset ℤ) (a : ℤ → ℂ) (t : ℝ) :
    MemLp (fun x => freeSol (L := L) S a t x) 2 (volume : Measure (AddCircle L)) :=
  MemLp.of_bound ((continuous_solP (L := L) S a).comp
    (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable _
    (Eventually.of_forall fun x => norm_freeSol_le S a t x)

lemma coeff_freeSol (S : Finset ℤ) (a : ℤ → ℂ) (t : ℝ) (n : ℤ) :
    coeff L (fun x => freeSol (L := L) S a t x) n = if n ∈ S then phase L t n * a n else 0 := by
  have hc : ∀ m : ℤ, Continuous fun x : AddCircle L =>
      conj (mode L n x) * (a m * phase L t m * mode L m x) := fun m =>
    (Complex.continuous_conj.comp (continuous_mode' n)).mul (continuous_const.mul (continuous_mode' m))
  have e : coeff L (fun x => freeSol (L := L) S a t x) n =
      ∑ m ∈ S, a m * phase L t m * coeff L (mode L m) n := by
    unfold coeff freeSol
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun m _ => integrable_cont (hc m)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [e]
  simp_rw [coeff_mode, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs <;> ring

lemma norm_sq_lp (z : lp (fun _ : ℤ => ℂ) 2) : ‖z‖ ^ 2 = ∑' n, ‖z n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num : 0 < (2 : ℝ≥0∞).toReal) z
  rw [ENNReal.toReal_ofNat] at h
  simpa only [Real.rpow_two] using h

/-- `‖u_N(t) − U(t)f‖_{L²}² = Σ_{|n|>N} |a_n|²`. -/
lemma dist_slice_sq (f : Lp ℂ 2 (volume : Measure (AddCircle L))) (t : ℝ) (N : ℕ) :
    ‖(memLp2_slice (win N) (coef f) t).toLp (fun x => freeSol (L := L) (win N) (coef f) t x) -
        evol f t‖ ^ 2 = ∑' n, (if n ∈ win N then 0 else ‖coef f n‖ ^ 2) := by
  rw [← (fourierL2 L).norm_map, map_sub, norm_sq_lp]
  refine tsum_congr fun n => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, QuantumNLS.Sobolev.fourierL2_toLp, coeff_freeSol, fourierL2_evol]
  split_ifs
  · rw [sub_self, norm_zero]; norm_num
  · rw [zero_sub, norm_neg, norm_mul, norm_phase, one_mul]

lemma tendsto_slice (f : Lp ℂ 2 (volume : Measure (AddCircle L))) (t : ℝ) :
    Tendsto (fun N => (memLp2_slice (win N) (coef f) t).toLp
      (fun x => freeSol (L := L) (win N) (coef f) t x)) atTop (𝓝 (evol f t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsum : Summable fun n => ‖coef f n‖ ^ 2 := by
    have h := (lp.memℓp (fourierL2 L f)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (G := ℝ)
    (f := fun (N : ℕ) n => if n ∈ win N then 0 else ‖coef f n‖ ^ 2) (g := fun _ => 0)
    (bound := fun n => ‖coef f n‖ ^ 2) hsum (fun n => ?_) (Eventually.of_forall fun N n => ?_)
  · rw [tsum_zero] at h
    have hsq := h.congr fun N => (dist_slice_sq f t N).symm
    have h2 := hsq.sqrt
    rw [Real.sqrt_zero] at h2
    exact h2.congr fun N => Real.sqrt_sq (norm_nonneg _)
  · obtain ⟨N0, hN0⟩ := win_exh n
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N0] with N hN
    simp [win_mono hN hN0]
  · split_ifs
    · rw [norm_zero]; positivity
    · rw [Real.norm_of_nonneg (sq_nonneg _)]

/-- **The `L⁴` limit is the Fourier solution**: for almost every `t ∈ (α, β]`, the slice
`x ↦ u(t,x)` equals `U(t)f` almost everywhere on `𝕋_L`. -/
theorem slice_eq (f : Lp ℂ 2 (volume : Measure (AddCircle L))) {α β : ℝ}
    (u : Lp ℂ 4 (μJ (L := L) α β)) (hu : Tendsto (wN f α β) atTop (𝓝 u)) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)),
      (fun x => u (t, x)) =ᵐ[volume] (evol f t : AddCircle L → ℂ) := by
  have hm : TendstoInMeasure (μJ α β) (fun N => (wN f α β N : ℝ × AddCircle L → ℂ)) atTop u :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hu)
  obtain ⟨ns, hns_mono, hns⟩ := hm.exists_seq_tendsto_ae
  have hcoe : ∀ᵐ p ∂(μJ (L := L) α β), ∀ i, (wN f α β (ns i) : ℝ × AddCircle L → ℂ) p =
      solP (win (ns i)) (coef f) p :=
    ae_all_iff.mpr fun i => MemLp.coeFn_toLp _
  have hpt : ∀ᵐ p ∂(μJ (L := L) α β),
      Tendsto (fun i => solP (L := L) (win (ns i)) (coef f) p) atTop (𝓝 (u p)) := by
    filter_upwards [hns, hcoe] with p h1 h2
    simpa only [h2] using h1
  have hslice := Measure.ae_ae_of_ae_prod hpt
  filter_upwards [hslice] with t ht
  -- `L²` convergence of the slices along `ns`, then an a.e. subsequence
  have hL2 := (tendsto_slice f t).comp hns_mono.tendsto_atTop
  have hm2 : TendstoInMeasure (volume : Measure (AddCircle L))
      (fun i => (((memLp2_slice (win (ns i)) (coef f) t).toLp
        (fun x => freeSol (L := L) (win (ns i)) (coef f) t x)) : AddCircle L → ℂ)) atTop
      (evol f t) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hL2)
  obtain ⟨ms, hms_mono, hms⟩ := hm2.exists_seq_tendsto_ae
  have hcoe2 : ∀ᵐ x ∂(volume : Measure (AddCircle L)), ∀ j,
      (((memLp2_slice (win (ns (ms j))) (coef f) t).toLp
        (fun x => freeSol (L := L) (win (ns (ms j))) (coef f) t x)) : AddCircle L → ℂ) x =
        freeSol (L := L) (win (ns (ms j))) (coef f) t x :=
    ae_all_iff.mpr fun j => MemLp.coeFn_toLp _
  filter_upwards [ht, hms, hcoe2] with x hx1 hx2 hx3
  have hA : Tendsto (fun j => freeSol (L := L) (win (ns (ms j))) (coef f) t x) atTop
      (𝓝 (u (t, x))) := hx1.comp hms_mono.tendsto_atTop
  have hB : Tendsto (fun j => freeSol (L := L) (win (ns (ms j))) (coef f) t x) atTop
      (𝓝 ((evol f t : AddCircle L → ℂ) x)) := by
    simpa only [hx3] using hx2
  exact tendsto_nhds_unique hA hB

#print axioms slice_eq

/-- **Stage A, full statement.** For `f ∈ L²(𝕋_L)` and `J = (α, β]` with `β − α ≤ T_L`, the Fourier
truncations of `U(·)f` converge in `L⁴(J × 𝕋_L)` to a limit `u` with
`‖u‖_{L⁴(J×𝕋_L)} ≤ (2T_L/L)^{1/4} ‖f‖₂`, whose slices are `U(t)f` for a.e. `t ∈ J`. -/
theorem L4_free (f : Lp ℂ 2 (volume : Measure (AddCircle L))) {α β : ℝ} (hαβ : α ≤ β)
    (hlen : β ≤ α + TL L) :
    ∃ u : Lp ℂ 4 (μJ (L := L) α β), Tendsto (wN f α β) atTop (𝓝 u) ∧
      ‖u‖ ^ 4 ≤ 2 * TL L / L * ‖f‖ ^ 4 ∧ ‖u‖ ≤ (2 * TL L / L) ^ (4⁻¹ : ℝ) * ‖f‖ ∧
      ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)),
        (fun x => u (t, x)) =ᵐ[volume] (evol f t : AddCircle L → ℂ) := by
  obtain ⟨u, hu, h4, h1⟩ := L4_free_L2 f hαβ hlen
  exact ⟨u, hu, h4, h1, slice_eq f u hu⟩

#print axioms L4_free

end QuantumNLS.L4StrichartzL2
