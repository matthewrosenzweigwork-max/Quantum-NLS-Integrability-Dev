import QuantumNLS.CollisionTrace

/-!
# DEF-005 / R-98129FE7 (first part): the contact quadratic form `q_{N,c}` on `H¹(T_L^N)`

Source (pinned PR11 `3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f`):
* DEF-005 (`chapters/definitions.tex:31`): for `c ≥ 0` the contact form on `H¹_sym(T_L^N)` is
  `Σ_j ‖∂_jψ‖² + 2c Σ_{j<k} ∫_{x_j=x_k} |ψ|² dy_{jk}`; the operator is defined through the closed form.
* `chapters/foundations/A01.tex:33` (`contact:eq:form`): `q_{N,c}(φ,ψ) = Σ_j ∫ conj ∂_jφ ∂_jψ +
  2c Σ_{i<j} ∫ conj T_ijφ T_ijψ dy_ij`, `D(q_{N,c}) = H¹_sym(T_L^N)`.
* `A01.tex:44` (R-98129FE7, `contact:thm:form`), first assertion: the form is closed and nonnegative.
  Source argument: "`q[ψ] + ‖ψ‖² ≥ ‖ψ‖²_{H¹}`; the trace estimate gives the reverse bound; hence the form
  norm is equivalent to the complete `H¹` norm, and the form is closed."

Built on the frozen physical `H¹` (`PhysicalEnergy`) and the constructed collision trace
(`CollisionTrace`, `T_ij : H¹ →L ℓ²` with the source's estimate); nothing about the trace or the
contact bound is assumed.  `‖∂_jψ‖²` is the Fourier-multiplier norm `Σ_w (2πw_j/L)²|ψ̂(w)|²`; the
identification with distributional derivatives is the (separate) weak-derivative chain.

No `sorry`, no custom axioms.
-/

set_option autoImplicit false

noncomputable section

open scoped ComplexConjugate Real InnerProductSpace
open MeasureTheory QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.CollisionTrace
  QuantumNLS.Fourier

namespace QuantumNLS.ContactForm

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-! ## §1 The kinetic part: bounded derivative maps `D_j : H¹ → ℓ²` -/

omit [Fact (0 < L)] in
theorem abs_freq_div_le (j : Fin N) (w : Fin N → ℤ) :
    |freq L (w j) / kinSqrt L N w| ≤ 1 := by
  have hs : 0 < kinSqrt L N w := by linarith [one_le_kinSqrt L N w]
  have hle : freq L (w j) ^ 2 ≤ kinSqrt L N w ^ 2 := by
    rw [kinSqrt_sq]
    unfold kinWeight
    have := Finset.single_le_sum (f := fun l => freq L (w l) ^ 2) (fun l _ => sq_nonneg _)
      (Finset.mem_univ j)
    linarith
  rw [abs_div, abs_of_pos hs, div_le_one hs]
  exact abs_le_of_sq_le_sq hle hs.le

/-- `D_j = -i∂_{x_j}` on `H¹(T_L^N)`: `(D_j ψ)^(w) = (2πw_j/L) ψ̂(w)`, a bounded map into `ℓ²(ℤ^N)`
(norm `≤ 1`, since `|2πw_j/L| ≤ √a_N(w)`). -/
def Dj (j : Fin N) : PhysH1 L N →L[ℂ] L2 (Fin N → ℤ) :=
  (mulCLM (fun w => freq L (w j) / kinSqrt L N w) 1 zero_le_one (abs_freq_div_le j)).comp
    ((Psi (L := L) (N := N)).toContinuousLinearEquiv.toContinuousLinearMap)

theorem Dj_apply (j : Fin N) (x : PhysH1 L N) (w : Fin N → ℤ) :
    ((Dj j x : L2 (Fin N → ℤ)) : (Fin N → ℤ) → ℂ) w = (freq L (w j) : ℂ) * coeffFun x w := by
  have hs : (kinSqrt L N w : ℂ) ≠ 0 := by
    exact_mod_cast (by linarith [one_le_kinSqrt L N w] : kinSqrt L N w ≠ 0)
  show ((mulCLM (fun w => freq L (w j) / kinSqrt L N w) 1 zero_le_one (abs_freq_div_le j)
      (Psi x) : L2 (Fin N → ℤ)) : (Fin N → ℤ) → ℂ) w = _
  rw [mulCLM_apply, Psi_apply]
  push_cast
  field_simp

/-- `‖D_jψ‖² = Σ_w (2πw_j/L)²|ψ̂(w)|²`. -/
theorem norm_sq_Dj (j : Fin N) (x : PhysH1 L N) :
    ‖Dj j x‖ ^ 2 = ∑' w, freq L (w j) ^ 2 * ‖coeffFun x w‖ ^ 2 := by
  rw [QuantumNLS.Energy.norm_sq_eq_tsum]
  refine tsum_congr fun w => ?_
  rw [Dj_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Kinetic part of the form norm**: `Σ_j ‖D_jψ‖² = ‖ψ‖²_{H¹} − ‖ψ‖²_{L²}`. -/
theorem sum_norm_sq_Dj (x : PhysH1 L N) : ∑ j, ‖Dj j x‖ ^ 2 = ‖x‖ ^ 2 - ‖x.val‖ ^ 2 := by
  have h := PhysH1.kinetic_split x
  have e : ∀ j, ‖Dj j x‖ ^ 2 = ∑' w, freq L (w j) ^ 2 *
      ‖(momUnitary L N x.val : Mom N → ℂ) w‖ ^ 2 := fun j => norm_sq_Dj j x
  simp_rw [e]
  linarith

/-! ## §2 The contact part and the form `q_{N,c}` -/

/-- The collision pairs `i < j`. -/
abbrev Pair (N : ℕ) : Type := {p : Fin N × Fin N // p.1 < p.2}

/-- The collision trace `T_ij : H¹ →L ℓ²(TIdx)` for the pair `p = (i,j)`, `i < j`
(constructed in `CollisionTrace`). -/
def Tpair (p : Pair N) : PhysH1 L N →L[ℂ] L2 (TIdx N p.1.1 p.1.2) :=
  traceCLM p.1.1 p.1.2 (ne_of_lt p.2)

/-- `Σ_j ⟨∂_jφ, ∂_jψ⟩`. -/
def kinSum (φ ψ : PhysH1 L N) : ℂ := ∑ j, ⟪Dj j φ, Dj j ψ⟫_ℂ

/-- `Σ_{i<j} ⟨T_ijφ, T_ijψ⟩`. -/
def contactSum (φ ψ : PhysH1 L N) : ℂ := ∑ p : Pair N, ⟪Tpair p φ, Tpair p ψ⟫_ℂ

/-- **The contact form** `q_{N,c}(φ,ψ) = Σ_j ⟨∂_jφ,∂_jψ⟩ + 2c Σ_{i<j} ⟨T_ijφ, T_ijψ⟩`
(`contact:eq:form`; conjugate-linear in `φ`, linear in `ψ`), on the physical `H¹(T_L^N)`. -/
def q (c : ℝ) (φ ψ : PhysH1 L N) : ℂ := kinSum φ ψ + ((2 * c : ℝ) : ℂ) * contactSum φ ψ

theorem q_add_right (c : ℝ) (φ ψ ψ' : PhysH1 L N) :
    q c φ (ψ + ψ') = q c φ ψ + q c φ ψ' := by
  simp only [q, kinSum, contactSum, map_add, inner_add_right, Finset.sum_add_distrib]
  ring

theorem q_smul_right (c : ℝ) (r : ℂ) (φ ψ : PhysH1 L N) : q c φ (r • ψ) = r * q c φ ψ := by
  simp only [q, kinSum, contactSum, map_smul, inner_smul_right, ← Finset.mul_sum]
  ring

theorem q_add_left (c : ℝ) (φ φ' ψ : PhysH1 L N) :
    q c (φ + φ') ψ = q c φ ψ + q c φ' ψ := by
  simp only [q, kinSum, contactSum, map_add, inner_add_left, Finset.sum_add_distrib]
  ring

theorem q_smul_left (c : ℝ) (r : ℂ) (φ ψ : PhysH1 L N) : q c (r • φ) ψ = conj r * q c φ ψ := by
  simp only [q, kinSum, contactSum, map_smul, inner_smul_left, ← Finset.mul_sum]
  ring

/-- `q[ψ] = Σ_j ‖∂_jψ‖² + 2c Σ_{i<j} ‖T_ijψ‖²` (real). -/
theorem q_self (c : ℝ) (ψ : PhysH1 L N) :
    q c ψ ψ = ((∑ j, ‖Dj j ψ‖ ^ 2 + 2 * c * ∑ p : Pair N, ‖Tpair p ψ‖ ^ 2 : ℝ) : ℂ) := by
  simp only [q, kinSum, contactSum, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/-- **Nonnegativity**: `q_{N,c}[ψ] ≥ 0` for `c ≥ 0` (R-98129FE7, "nonnegative"). -/
theorem q_nonneg {c : ℝ} (hc : 0 ≤ c) (ψ : PhysH1 L N) : 0 ≤ (q c ψ ψ).re := by
  rw [q_self, Complex.ofReal_re]
  have h1 : 0 ≤ ∑ j, ‖Dj j ψ‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h2 : 0 ≤ ∑ p : Pair N, ‖Tpair p ψ‖ ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  positivity

/-- The form norm squared `q[ψ] + ‖ψ‖²_{L²}`. -/
def formNormSq (c : ℝ) (ψ : PhysH1 L N) : ℝ := (q c ψ ψ).re + ‖ψ.val‖ ^ 2

/-- **Exact form-norm identity**: `q[ψ] + ‖ψ‖² = ‖ψ‖²_{H¹} + 2c Σ_{i<j} ‖T_ijψ‖²`. -/
theorem formNormSq_eq (c : ℝ) (ψ : PhysH1 L N) :
    formNormSq c ψ = ‖ψ‖ ^ 2 + 2 * c * ∑ p : Pair N, ‖Tpair p ψ‖ ^ 2 := by
  unfold formNormSq
  rw [q_self, Complex.ofReal_re, sum_norm_sq_Dj]
  ring

/-- **Lower bound** (source: `q[ψ] + ‖ψ‖² ≥ ‖ψ‖²_{H¹}`). -/
theorem H1_le_formNormSq {c : ℝ} (hc : 0 ≤ c) (ψ : PhysH1 L N) : ‖ψ‖ ^ 2 ≤ formNormSq c ψ := by
  rw [formNormSq_eq]
  have h2 : 0 ≤ ∑ p : Pair N, ‖Tpair p ψ‖ ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  nlinarith [mul_nonneg hc h2]

/-- **Upper bound from the trace estimate** (source: "the trace estimate gives the reverse bound"):
`q[ψ] + ‖ψ‖² ≤ (1 + 2c·#pairs·(1+L⁻¹)) ‖ψ‖²_{H¹}`. -/
theorem formNormSq_le {c : ℝ} (hc : 0 ≤ c) (ψ : PhysH1 L N) :
    formNormSq c ψ ≤ (1 + 2 * c * (Fintype.card (Pair N) * (1 + L⁻¹))) * ‖ψ‖ ^ 2 := by
  rw [formNormSq_eq]
  have hp : ∀ p : Pair N, ‖Tpair p ψ‖ ^ 2 ≤ (1 + L⁻¹) * ‖ψ‖ ^ 2 := fun p =>
    norm_sq_traceMap_le p.1.1 p.1.2 (ne_of_lt p.2) ψ
  have hsum : ∑ p : Pair N, ‖Tpair p ψ‖ ^ 2 ≤ Fintype.card (Pair N) * ((1 + L⁻¹) * ‖ψ‖ ^ 2) := by
    calc ∑ p : Pair N, ‖Tpair p ψ‖ ^ 2 ≤ ∑ _p : Pair N, (1 + L⁻¹) * ‖ψ‖ ^ 2 :=
          Finset.sum_le_sum fun p _ => hp p
      _ = Fintype.card (Pair N) * ((1 + L⁻¹) * ‖ψ‖ ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hc)]

/-- **Closedness of the contact form** (R-98129FE7, first assertion): the form norm
`q[ψ]+‖ψ‖²` is equivalent to the complete `H¹` norm, so every Cauchy sequence for the form norm
converges for the form norm.  (For `c ≥ 0`.) -/
theorem form_complete {c : ℝ} (hc : 0 ≤ c) (u : ℕ → PhysH1 L N)
    (hu : ∀ ε > 0, ∃ n₀ : ℕ, ∀ m n, n₀ ≤ m → n₀ ≤ n → formNormSq c (u m - u n) < ε) :
    ∃ x : PhysH1 L N, Filter.Tendsto (fun n => formNormSq c (u n - x)) Filter.atTop (nhds 0) := by
  have hcs : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨n₀, hn⟩ := hu (ε ^ 2) (by positivity)
    refine ⟨n₀, fun m hm n hn' => ?_⟩
    rw [dist_eq_norm]
    have h1 := H1_le_formNormSq hc (u m - u n)
    have h2 := hn m n hm hn'
    exact lt_of_pow_lt_pow_left₀ 2 hε.le (lt_of_le_of_lt h1 h2)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨x, ?_⟩
  set C : ℝ := 1 + 2 * c * (Fintype.card (Pair N) * (1 + L⁻¹)) with hC
  have hnorm : Filter.Tendsto (fun n => ‖u n - x‖) Filter.atTop (nhds 0) := by
    simpa using (hx.sub_const x).norm
  have hlim : Filter.Tendsto (fun n => C * ‖u n - x‖ ^ 2) Filter.atTop (nhds 0) := by
    simpa using (hnorm.pow 2).const_mul C
  refine squeeze_zero (fun n => ?_) (fun n => formNormSq_le hc (u n - x)) hlim
  exact le_trans (sq_nonneg _) (H1_le_formNormSq hc (u n - x))

/-- **Closedness on `H¹_sym`** (the form domain of DEF-005): the same statement for sequences in the
symmetric subspace, whose limit is again symmetric (`isClosed_sym`). -/
theorem form_complete_sym {c : ℝ} (hc : 0 ≤ c) (u : ℕ → PhysH1 L N)
    (hsym : ∀ n, u n ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)))
    (hu : ∀ ε > 0, ∃ n₀ : ℕ, ∀ m n, n₀ ≤ m → n₀ ≤ n → formNormSq c (u m - u n) < ε) :
    ∃ x : PhysH1 L N, x ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)) ∧
      Filter.Tendsto (fun n => formNormSq c (u n - x)) Filter.atTop (nhds 0) := by
  obtain ⟨x, hx⟩ := form_complete hc u hu
  have hcs : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨n₀, hn⟩ := hu (ε ^ 2) (by positivity)
    refine ⟨n₀, fun m hm n hn' => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le
      (lt_of_le_of_lt (H1_le_formNormSq hc (u m - u n)) (hn m n hm hn'))
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcs
  have hxy : x = y := by
    have hC : Filter.Tendsto (fun n => ‖u n - x‖) Filter.atTop (nhds 0) := by
      have hl : Filter.Tendsto (fun n => formNormSq c (u n - x)) Filter.atTop (nhds 0) := hx
      have h0 : Filter.Tendsto (fun n => ‖u n - x‖ ^ 2) Filter.atTop (nhds 0) :=
        squeeze_zero (fun n => sq_nonneg _) (fun n => H1_le_formNormSq hc (u n - x)) hl
      have := h0.sqrt
      simpa [Real.sqrt_sq (norm_nonneg _)] using this
    have : Filter.Tendsto u Filter.atTop (nhds x) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact hC
    exact tendsto_nhds_unique this hy
  subst hxy
  exact ⟨x, PhysH1.isClosed_sym.mem_of_tendsto hy (Filter.Eventually.of_forall hsym), hx⟩

end QuantumNLS.ContactForm
