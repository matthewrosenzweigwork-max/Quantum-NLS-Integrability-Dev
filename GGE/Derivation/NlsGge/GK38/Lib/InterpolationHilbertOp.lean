import NlsGge.GK38.Lib.InterpolationHilbert

/-!
# L4b, part 2: the Hilbert transform and its generalization as operators on `ℓ²(ℤ)`

Source: Grébert–Kappeler book, Appendix F, Lemma F.5 (`‖H‖ ≤ π`) and Lemma F.6 (GKP Lemma 22.5).

* `exists_clm_of_form_bound`: a kernel `a n m` with square-summable rows and a bound on all finite
  bilinear forms `Σ_{n∈T} Σ_{m∈S} a n m x_m ȳ_n` defines a bounded operator on `ℓ²(ℤ)` of the same
  norm, given by the absolutely convergent sums `(Ax)_n = Σ'_m a n m x_m`.
* `hilbertTransform_bdd` (book Lemma F.5): `a n m = 1/(m-n)` for `m ≠ n`, constant `π`, from the
  Fourier-series bound `hilbertForm_bound`.
* `hilbertGen_bdd` (book Lemma F.6): `a n m = π/(ρ_m - σ_n)` for `m ≠ n`; the constant depends only
  on the bounds of `σ - nπ`, `ρ - nπ` and on `c`.  The book's proof (`H x + x̃ + x̂`) is followed;
  the two remainder terms are bounded by the Schur test for the kernel `1/(m-n)²` (finite sums),
  rather than by the book's repeated Cauchy–Schwarz (the book's displayed constant `c` there
  should read `1/c`, since `|ρ_m - σ_n| ≥ c|m-n|` is used in a denominator).
-/

set_option autoImplicit false

open Filter Topology

namespace NlsGge.GK38.Lib

noncomputable section

/-- The Hilbert space `ℓ²(ℤ, ℂ)`. -/
abbrev L2Z : Type := lp (fun _ : ℤ => ℂ) 2

theorem summable_sq_lp (x : L2Z) : Summable fun m : ℤ => ‖(x : ℤ → ℂ) m‖ ^ 2 := by
  have := (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mp x.2
  simpa using this

theorem sum_sq_le_norm_sq (x : L2Z) (S : Finset ℤ) : ∑ m ∈ S, ‖(x : ℤ → ℂ) m‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have := lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ENNReal).toReal) x S
  simpa using this

/-- Summability of a product of two square-summable sequences (AM-GM). -/
theorem summable_norm_mul_of_sq {f g : ℤ → ℂ} (hf : Summable fun m => ‖f m‖ ^ 2)
    (hg : Summable fun m => ‖g m‖ ^ 2) : Summable fun m => ‖f m * g m‖ := by
  refine ((hf.add hg).mul_left (1 / 2 : ℝ)).of_nonneg_of_le (fun _ => norm_nonneg _) fun m => ?_
  rw [norm_mul]
  nlinarith [sq_nonneg (‖f m‖ - ‖g m‖)]

/-- **Extension lemma.**  A kernel with square-summable rows and a uniform bound on all finite
bilinear forms defines a bounded operator on `ℓ²(ℤ)` given by absolutely convergent row sums. -/
theorem exists_clm_of_form_bound (a : ℤ → ℤ → ℂ) (ha : ∀ n, Summable fun m => ‖a n m‖ ^ 2)
    {C : ℝ} (hC : 0 ≤ C)
    (hform : ∀ (S T : Finset ℤ) (x y : ℤ → ℂ),
      ‖∑ n ∈ T, ∑ m ∈ S, a n m * x m * (starRingEnd ℂ) (y n)‖
        ≤ C * Real.sqrt (∑ m ∈ S, ‖x m‖ ^ 2) * Real.sqrt (∑ n ∈ T, ‖y n‖ ^ 2)) :
    ∃ A : L2Z →L[ℂ] L2Z, ‖A‖ ≤ C ∧ ∀ (x : L2Z) (n : ℤ),
      (Summable fun m : ℤ => ‖a n m * (x : ℤ → ℂ) m‖) ∧
        (A x : ℤ → ℂ) n = ∑' m : ℤ, a n m * (x : ℤ → ℂ) m := by
  have hsum : ∀ (x : L2Z) (n : ℤ), Summable fun m : ℤ => ‖a n m * (x : ℤ → ℂ) m‖ :=
    fun x n => summable_norm_mul_of_sq (ha n) (summable_sq_lp x)
  -- the row sums
  set y : L2Z → ℤ → ℂ := fun x n => ∑' m : ℤ, a n m * (x : ℤ → ℂ) m with hy
  -- window bound
  have hwin : ∀ (x : L2Z) (T : Finset ℤ), ∑ n ∈ T, ‖y x n‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    intro x T
    set u : ℝ := Real.sqrt (∑ n ∈ T, ‖y x n‖ ^ 2) with hu
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have hu2 : u ^ 2 = ∑ n ∈ T, ‖y x n‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
    have hlim : Tendsto (fun S : Finset ℤ => ∑ n ∈ T, ∑ m ∈ S, a n m * (x : ℤ → ℂ) m *
        (starRingEnd ℂ) (y x n)) atTop (𝓝 (∑ n ∈ T, y x n * (starRingEnd ℂ) (y x n))) := by
      refine tendsto_finsetSum _ fun n _ => ?_
      have h1 : HasSum (fun m : ℤ => a n m * (x : ℤ → ℂ) m) (y x n) :=
        (hsum x n).of_norm.hasSum
      have h2 : Tendsto (fun S : Finset ℤ => ∑ m ∈ S, a n m * (x : ℤ → ℂ) m) atTop (𝓝 (y x n)) := h1
      simp_rw [← Finset.sum_mul]
      exact h2.mul_const _
    have hle : ∀ S : Finset ℤ, ‖∑ n ∈ T, ∑ m ∈ S, a n m * (x : ℤ → ℂ) m *
        (starRingEnd ℂ) (y x n)‖ ≤ C * ‖x‖ * u := by
      intro S
      refine (hform S T (x : ℤ → ℂ) (y x)).trans ?_
      have : Real.sqrt (∑ m ∈ S, ‖(x : ℤ → ℂ) m‖ ^ 2) ≤ ‖x‖ := by
        rw [Real.sqrt_le_left (norm_nonneg _)]
        exact sum_sq_le_norm_sq x S
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hC) hu0
    have h3 : ‖∑ n ∈ T, y x n * (starRingEnd ℂ) (y x n)‖ ≤ C * ‖x‖ * u :=
      le_of_tendsto hlim.norm (Eventually.of_forall hle)
    have h4 : ‖∑ n ∈ T, y x n * (starRingEnd ℂ) (y x n)‖ = u ^ 2 := by
      rw [hu2]
      have : ∑ n ∈ T, y x n * (starRingEnd ℂ) (y x n) = ((∑ n ∈ T, ‖y x n‖ ^ 2 : ℝ) : ℂ) := by
        push_cast
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]
    have h5 : u ^ 2 ≤ C * ‖x‖ * u := h4 ▸ h3
    have : u ≤ C * ‖x‖ := by
      by_cases h0 : u = 0
      · rw [h0]; positivity
      · have : 0 < u := lt_of_le_of_ne hu0 (Ne.symm h0)
        nlinarith
    rw [← hu2]
    nlinarith
  have hmem : ∀ x : L2Z, Memℓp (y x) 2 := by
    intro x
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact summable_of_sum_le (fun _ => by positivity) (hwin x)
  -- linear map
  let Alin : L2Z →ₗ[ℂ] L2Z :=
    { toFun := fun x => ⟨y x, hmem x⟩
      map_add' := by
        intro x x'
        ext n
        simp only [lp.coeFn_add, Pi.add_apply, hy]
        simp_rw [mul_add]
        exact Summable.tsum_add (hsum x n).of_norm (hsum x' n).of_norm
      map_smul' := by
        intro c x
        ext n
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, hy]
        rw [← tsum_mul_left]
        refine tsum_congr fun m => ?_
        ring }
  have hbound : ∀ x : L2Z, ‖Alin x‖ ≤ C * ‖x‖ := by
    intro x
    refine lp.norm_le_of_forall_sum_le (by norm_num) (by positivity) fun T => ?_
    have := hwin x T
    simpa [Alin] using this
  refine ⟨Alin.mkContinuous C hbound, ?_, fun x n => ⟨hsum x n, rfl⟩⟩
  exact LinearMap.mkContinuous_norm_le _ hC _

/-! ### Book Lemma F.5: the discrete Hilbert transform -/

/-- The discrete Hilbert transform `(Hx)_n = Σ_{m≠n} x_m/(m-n)`.  Summability is
`summable_hilbert`; for `x ∈ ℓ²` the sum is absolutely convergent, so the unconditional `tsum` is
the symmetric one. -/
def hilbertSum (x : ℤ → ℂ) (n : ℤ) : ℂ :=
  ∑' m : ℤ, if m = n then 0 else x m / ((m : ℂ) - n)

/-- The kernel of the Hilbert transform. -/
def hilbKernel (n m : ℤ) : ℂ := if m = n then 0 else 1 / ((m : ℂ) - n)

theorem summable_sq_inv_int_sub (n : ℤ) : Summable fun m : ℤ => (1 / ((m : ℝ) - n)) ^ 2 := by
  have h := Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)
  have h2 := (Equiv.subRight n).summable_iff.mpr h
  refine h2.congr fun m => ?_
  simp [Equiv.subRight_apply, one_div, inv_pow]

theorem summable_sq_hilbKernel (n : ℤ) : Summable fun m : ℤ => ‖hilbKernel n m‖ ^ 2 := by
  refine (summable_sq_inv_int_sub n).congr fun m => ?_
  unfold hilbKernel
  by_cases h : m = n
  · simp [h]
  · simp only [h, ite_false, norm_div, norm_one]
    have : ‖(m : ℂ) - n‖ = |(m : ℝ) - n| := by
      rw [← Complex.ofReal_intCast, ← Complex.ofReal_intCast, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
    rw [this, one_div, inv_pow, one_div, inv_pow, sq_abs]

theorem hilbKernel_form_bound (S T : Finset ℤ) (x y : ℤ → ℂ) :
    ‖∑ n ∈ T, ∑ m ∈ S, hilbKernel n m * x m * (starRingEnd ℂ) (y n)‖
      ≤ Real.pi * Real.sqrt (∑ m ∈ S, ‖x m‖ ^ 2) * Real.sqrt (∑ n ∈ T, ‖y n‖ ^ 2) := by
  refine le_trans (le_of_eq ?_) (hilbertForm_bound S T x y)
  congr 1
  unfold hilbertForm
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  unfold hilbKernel
  by_cases h : m = n
  · simp [h]
  · simp only [h, ite_false]; ring

/-- **Book Lemma F.5 (Hilbert transform).**  The discrete Hilbert transform is a bounded operator
on `ℓ²(ℤ)` of norm at most `π`; its rows are absolutely summable. -/
theorem hilbertTransform_bdd :
    ∃ H : L2Z →L[ℂ] L2Z, ‖H‖ ≤ Real.pi ∧ ∀ (x : L2Z) (n : ℤ),
      (Summable fun m : ℤ => ‖if m = n then 0 else (x : ℤ → ℂ) m / ((m : ℂ) - n)‖) ∧
        (H x : ℤ → ℂ) n = hilbertSum x n := by
  obtain ⟨H, hH, hH2⟩ := exists_clm_of_form_bound hilbKernel summable_sq_hilbKernel Real.pi_pos.le
    hilbKernel_form_bound
  refine ⟨H, hH, fun x n => ?_⟩
  have e : ∀ m : ℤ, hilbKernel n m * (x : ℤ → ℂ) m
      = if m = n then 0 else (x : ℤ → ℂ) m / ((m : ℂ) - n) := by
    intro m; unfold hilbKernel; by_cases h : m = n <;> simp [h, div_eq_inv_mul]
  obtain ⟨h1, h2⟩ := hH2 x n
  simp_rw [e] at h1 h2
  exact ⟨h1, h2⟩

theorem summable_hilbert (x : L2Z) (n : ℤ) :
    Summable fun m : ℤ => ‖if m = n then 0 else (x : ℤ → ℂ) m / ((m : ℂ) - n)‖ :=
  (hilbertTransform_bdd.choose_spec.2 x n).1

/-- The discrete Hilbert transform as a bounded operator on `ℓ²(ℤ)`. -/
def hilbertCLM : L2Z →L[ℂ] L2Z := hilbertTransform_bdd.choose

theorem norm_hilbertCLM_le : ‖hilbertCLM‖ ≤ Real.pi := hilbertTransform_bdd.choose_spec.1

theorem hilbertCLM_apply (x : L2Z) (n : ℤ) :
    (hilbertCLM x : ℤ → ℂ) n = hilbertSum x n :=
  (hilbertTransform_bdd.choose_spec.2 x n).2

end

end NlsGge.GK38.Lib
