/-
QuantumNLS.EnergyRealization — EXISTENCE of the positive trace-class form realization
`A_k^{1/2} ρ A_k^{1/2}` for positive `ρ` with `Tr(A_k ρ) < ∞` (owner: opus_tensor).

Source (energy_trace.tex:18–26): "For k ≥ 1, put A_k = 1 + Σ_{j≤k} D_j², D_j = −i∂_{x_j}.  If ρ is
positive and Tr(A_k ρ) < ∞, the notation A_k^{1/2} ρ A_k^{1/2} denotes its positive trace-class
realization. … This definition does not require that the range of ρ lie in the operator domain
of A_k."  DEF-031 (definitions.tex:187).

Frozen imports, read-only:
* EnergyMultiplier (the formalization), sha256 7394da58…fff3e5: the multiplier `invCLM m` and `AhalfInv L k`
  (`A_k^{-1/2}` on `ℓ²(ℤ^k)`), `kinWeight` / `kinSqrt` (symbols of `A_k` and `A_k^{1/2}`).
* EnergyForm EF1, sha256 7f15cc6d…94ba7: uniqueness of the realization, `energyTraceNorm`.

Exact hypotheses (Fourier representation, where `A_k` is diagonal):
* `ρ : ℓ²(ℤ^k) →L ℓ²(ℤ^k)` positive;
* `Tr(A_k ρ) := Σₙ a_k(n) ⟨eₙ, ρ eₙ⟩ < ∞` (`kinTrace`), with `a_k(n) = 1 + Σⱼ (2πnⱼ/L)²`.  Since
  `A_k` is diagonal in the Fourier basis, this is the trace of `A_k ρ` in its eigenbasis.  No
  domain condition on the range of `ρ` is imposed.

Construction (generic multiplier `m ≥ 1`; the kinetic case is `m = √a_k`):
`S = √ρ`; `K = A^{1/2} S`, `(K x)ₙ = mₙ (S x)ₙ`, is bounded because
`|(Sx)ₙ| ≤ ‖S eₙ‖ ‖x‖` and `Σ mₙ² ‖S eₙ‖² = Tr(Aρ) < ∞`.  `T := K K†` is positive,
`W T W = (W K)(W K)† = S S = ρ` for `W = A^{-1/2}`, and `K† eₙ = mₙ S eₙ` gives
`Tr T = Σ mₙ² ‖S eₙ‖² = Tr(Aρ)`.  Hence `energyTraceNorm (A^{-1/2}) ρ = Tr(Aρ)`.

Physical carrier bridge (`L²(𝕋_L^k)` to `ℓ²(ℤ^k)`) is the formalization's PhysicalEnergy and is not done
here.  The R-828C5F7E S2 policy hold is unchanged.
-/
import QuantumNLS.EnergyMultiplier
import QuantumNLS.EnergyForm

open scoped InnerProductSpace ENNReal
open QuantumNLS.TraceClass QuantumNLS.Fidelity QuantumNLS.EnergyForm QuantumNLS.Energy

noncomputable section

namespace QuantumNLS.EnergyRealization

/-- Existence of a self-adjoint square root, stated without the functional calculus so that it can
be applied on `ℓ²` (the proof uses `CFC.sqrt` on a generic Hilbert space). -/
theorem exists_sqrt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {ρ : E →L[ℂ] E} (hρ : ρ.IsPositive) : ∃ S : E →L[ℂ] E, IsSelfAdjoint S ∧ S * S = ρ :=
  ⟨CFC.sqrt ρ, (CFC.sqrt_nonneg ρ).isSelfAdjoint, sqrt_mul_sqrt hρ⟩

section Generic

variable {ι : Type*}

/-- The canonical Hilbert basis `(eₙ)` of `ℓ²(ι)`. -/
def stdBasis : HilbertBasis ι ℂ (L2 ι) := default

/-- `eₙ`. -/
def ev (n : ι) : L2 ι := stdBasis n

theorem inner_ev_left (n : ι) (f : L2 ι) : ⟪ev n, f⟫_ℂ = (f : ι → ℂ) n := by
  rw [ev, ← HilbertBasis.repr_apply_apply]; rfl

/-- `Tr(A ρ) = Σₙ mₙ² ⟨eₙ, ρ eₙ⟩` for the multiplier `A` with symbol `m²` (diagonal in `(eₙ)`). -/
def formTrace (m : ι → ℝ) (ρ : L2 ι →L[ℂ] L2 ι) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (m n ^ 2 * RCLike.re ⟪ev n, ρ (ev n)⟫_ℂ)

variable (m : ι → ℝ) (hm : ∀ n, 1 ≤ m n) {ρ : L2 ι →L[ℂ] L2 ι}
variable (S : L2 ι →L[ℂ] L2 ι) (hSsa : IsSelfAdjoint S) (hSS : S * S = ρ)

include hSsa in
theorem inner_S (x y : L2 ι) : ⟪S x, y⟫_ℂ = ⟪x, S y⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, hSsa.adjoint_eq]

include hSsa hSS in
theorem re_inner_ev_eq (n : ι) : RCLike.re ⟪ev n, ρ (ev n)⟫_ℂ = ‖S (ev n)‖ ^ 2 := by
  rw [← hSS, ContinuousLinearMap.mul_apply, ← inner_S S hSsa, inner_self_eq_norm_sq]

include hSsa hSS in
theorem formTrace_eq : formTrace m ρ = ∑' n, ENNReal.ofReal ((m n * ‖S (ev n)‖) ^ 2) := by
  unfold formTrace
  congr 1; funext n
  rw [re_inner_ev_eq S hSsa hSS, mul_pow]

variable (hE : formTrace m ρ ≠ ⊤)

include hSsa hSS hE in
theorem hasSum_energy : HasSum (fun n => (m n * ‖S (ev n)‖) ^ 2) (formTrace m ρ).toReal :=
  hasSum_of_tsum_ofReal (fun n => by positivity) ENNReal.toReal_nonneg
    (by rw [← formTrace_eq m S hSsa hSS, ENNReal.ofReal_toReal hE])

include hSsa in
theorem norm_coord_le (x : L2 ι) (n : ι) : ‖(S x : ι → ℂ) n‖ ≤ ‖S (ev n)‖ * ‖x‖ := by
  rw [← inner_ev_left, ← inner_S S hSsa]
  exact norm_inner_le_norm _ _

/-- The coordinates of `K x = A^{1/2} S x`. -/
def Kfun (x : L2 ι) : ι → ℂ := fun n => (m n : ℂ) * (S x : ι → ℂ) n

include hm hSsa hSS hE in
theorem Kfun_sq_le (x : L2 ι) (n : ι) :
    ‖Kfun m S x n‖ ^ 2 ≤ (m n * ‖S (ev n)‖) ^ 2 * ‖x‖ ^ 2 := by
  simp only [Kfun, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := norm_coord_le S hSsa x n
  have h0 : 0 ≤ m n := by linarith [hm n]
  rw [abs_of_nonneg h0]
  calc (m n * ‖(S x : ι → ℂ) n‖) ^ 2 ≤ (m n * (‖S (ev n)‖ * ‖x‖)) ^ 2 := by gcongr
    _ = (m n * ‖S (ev n)‖) ^ 2 * ‖x‖ ^ 2 := by ring

include hm hSsa hSS hE in
theorem memℓp_Kfun (x : L2 ι) : Memℓp (Kfun m S x) 2 := by
  rw [memL2_iff]
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => Kfun_sq_le m hm S hSsa hSS hE x n)
    ((hasSum_energy m S hSsa hSS hE).summable.mul_right (‖x‖ ^ 2))

/-- `K = A^{1/2} S` as a bounded operator (finite energy makes it bounded). -/
def Kop : L2 ι →L[ℂ] L2 ι :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨Kfun m S x, memℓp_Kfun m hm S hSsa hSS hE x⟩
      map_add' := fun x y => by
        apply lp.ext; funext n
        show Kfun m S (x + y) n = Kfun m S x n + Kfun m S y n
        simp only [Kfun, map_add, lp.coeFn_add, Pi.add_apply]
        ring
      map_smul' := fun c x => by
        apply lp.ext; funext n
        show Kfun m S (c • x) n = c * Kfun m S x n
        simp only [Kfun, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        ring }
    √((formTrace m ρ).toReal)
    (fun x => by
      have hsum := hasSum_energy m S hSsa hSS hE
      have hK : Memℓp (Kfun m S x) 2 := memℓp_Kfun m hm S hSsa hSS hE x
      show ‖(⟨Kfun m S x, hK⟩ : L2 ι)‖ ≤ _
      have hsq : ‖(⟨Kfun m S x, hK⟩ : L2 ι)‖ ^ 2 ≤ (√((formTrace m ρ).toReal) * ‖x‖) ^ 2 := by
        rw [norm_sq_eq_tsum, mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg, ← hsum.tsum_eq,
          ← tsum_mul_right]
        exact Summable.tsum_le_tsum (fun n => Kfun_sq_le m hm S hSsa hSS hE x n)
          (summable_sq _) (hsum.summable.mul_right _)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq)

theorem Kop_apply (x : L2 ι) (n : ι) :
    (Kop m hm S hSsa hSS hE x : ι → ℂ) n = (m n : ℂ) * (S x : ι → ℂ) n := rfl

/-- `A^{-1/2} K = S`. -/
theorem invCLM_Kop : invCLM m hm * Kop m hm S hSsa hSS hE = S := by
  ext x n
  rw [ContinuousLinearMap.mul_apply, invCLM_apply, Kop_apply]
  have := m_ne_zero hm n
  push_cast
  field_simp

/-- `K† eₙ = mₙ S eₙ`. -/
theorem adjoint_Kop_ev (n : ι) :
    ContinuousLinearMap.adjoint (Kop m hm S hSsa hSS hE) (ev n) = (m n : ℂ) • S (ev n) := by
  refine ext_inner_left ℂ fun y => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, inner_ev_left, Kop_apply,
    inner_smul_right, ← inner_conj_symm y, inner_S S hSsa, inner_ev_left, map_mul,
    Complex.conj_ofReal]

/-- The realization `T = A^{1/2} ρ A^{1/2} := K K†`. -/
def realization : L2 ι →L[ℂ] L2 ι :=
  Kop m hm S hSsa hSS hE * ContinuousLinearMap.adjoint (Kop m hm S hSsa hSS hE)

theorem realization_isPositive : (realization m hm S hSsa hSS hE).IsPositive :=
  ContinuousLinearMap.isPositive_self_comp_adjoint _

/-- **`ρ = A^{-1/2} T A^{-1/2}`.** -/
theorem realization_spec : ρ = invCLM m hm * realization m hm S hSsa hSS hE * invCLM m hm := by
  have hsa := invCLM_isSelfAdjoint (m := m) hm
  have hW : ContinuousLinearMap.adjoint (Kop m hm S hSsa hSS hE) * invCLM m hm =
      ContinuousLinearMap.adjoint (invCLM m hm * Kop m hm S hSsa hSS hE) := by
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
      hsa.adjoint_eq]
  rw [realization, ← mul_assoc, mul_assoc (invCLM m hm * Kop m hm S hSsa hSS hE), hW, invCLM_Kop,
    hSsa.adjoint_eq, hSS]

/-- **`Tr T = Tr(A ρ)`.** -/
theorem posTrace_realization : posTrace (realization m hm S hSsa hSS hE) = formTrace m ρ := by
  have hT : realization m hm S hSsa hSS hE = ContinuousLinearMap.adjoint
      (ContinuousLinearMap.adjoint (Kop m hm S hSsa hSS hE)) ∘L
        ContinuousLinearMap.adjoint (Kop m hm S hSsa hSS hE) := by
    rw [ContinuousLinearMap.adjoint_adjoint]; rfl
  rw [posTrace_eq stdBasis (realization_isPositive m hm S hSsa hSS hE), hT,
    traceIn_adjoint_comp_self, formTrace_eq m S hSsa hSS, hsSq]
  congr 1; funext n
  rw [show stdBasis n = ev n from rfl, adjoint_Kop_ev, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith [hm n] : (0 : ℝ) ≤ m n)]

omit hE in
theorem invCLM_injective : Function.Injective (invCLM m hm) := by
  intro x y h
  have hx := mulOp_invCLM hm x
  have hy := mulOp_invCLM hm y
  rw [← hx, ← hy]
  congr 1
  exact Subtype.ext h

omit hE in
theorem invCLM_denseRange : DenseRange (invCLM m hm) := by
  rw [DenseRange, invCLM_range]
  exact dense_mulDomain hm

end Generic

section Main

variable {ι : Type*} (m : ι → ℝ) (hm : ∀ n, 1 ≤ m n) {ρ : L2 ι →L[ℂ] L2 ι}

/-- **Existence (source hypotheses).** A positive `ρ` with `Tr(Aρ) < ∞` has a positive
trace-class realization `T` with `ρ = A^{-1/2} T A^{-1/2}` and `Tr T = Tr(Aρ)`. -/
theorem exists_realization (hρ : ρ.IsPositive) (hE : formTrace m ρ ≠ ⊤) :
    ∃ T : L2 ι →L[ℂ] L2 ι, T.IsPositive ∧ IsTraceClass T ∧
      ρ = invCLM m hm * T * invCLM m hm ∧ posTrace T = formTrace m ρ := by
  obtain ⟨S, hSsa, hSS⟩ := exists_sqrt hρ
  refine ⟨realization m hm S hSsa hSS hE, realization_isPositive m hm S hSsa hSS hE, ?_,
    realization_spec m hm S hSsa hSS hE, posTrace_realization m hm S hSsa hSS hE⟩
  rw [IsTraceClass, traceNorm_of_isPositive (realization_isPositive m hm S hSsa hSS hE),
    posTrace_realization]
  exact lt_top_iff_ne_top.mpr hE

/-- With uniqueness (EnergyForm): `energyTraceNorm (A^{-1/2}) ρ = Tr(Aρ)`. -/
theorem energyTraceNorm_eq_formTrace (hρ : ρ.IsPositive) (hE : formTrace m ρ ≠ ⊤) :
    energyTraceNorm (invCLM m hm) ρ = formTrace m ρ := by
  obtain ⟨S, hSsa, hSS⟩ := exists_sqrt hρ
  rw [energyTraceNorm_eq (invCLM_injective m hm) (invCLM_denseRange m hm)
    (realization_spec m hm S hSsa hSS hE),
    traceNorm_of_isPositive (realization_isPositive m hm S hSsa hSS hE), posTrace_realization]

include hm in
/-- Finite energy forces trace class (`mₙ ≥ 1`): `Tr ρ ≤ Tr(Aρ)`. -/
theorem posTrace_le_formTrace (hρ : ρ.IsPositive) : posTrace ρ ≤ formTrace m ρ := by
  rw [posTrace_eq stdBasis hρ, traceIn, formTrace]
  refine ENNReal.tsum_le_tsum fun n => ENNReal.ofReal_le_ofReal ?_
  have h0 := hρ.re_inner_nonneg_right (ev n)
  have h1 : 1 ≤ m n ^ 2 := by nlinarith [hm n]
  show RCLike.re ⟪ev n, ρ (ev n)⟫_ℂ ≤ _
  nlinarith

/-- Non-vacuity: `ρ = |eₙ⟩⟨eₙ|` is positive with `Tr(Aρ) = mₙ² < ∞`. -/
theorem formTrace_rankOne_ev (n : ι) :
    formTrace m (InnerProductSpace.rankOne ℂ (ev n) (ev n)) = ENNReal.ofReal (m n ^ 2) := by
  classical
  have hon := orthonormal_iff_ite.mp (stdBasis (ι := ι)).orthonormal
  unfold formTrace
  rw [tsum_eq_single n]
  · simp only [InnerProductSpace.rankOne_apply, inner_smul_right, ev, hon]
    simp
  · intro j hj
    simp only [InnerProductSpace.rankOne_apply, inner_smul_right, ev, hon]
    simp [hj, Ne.symm hj]

end Main

/-! ## The kinetic instance `A_k = 1 + Σ D_j²` on `ℓ²(ℤ^k)` -/

section Kinetic

variable (L : ℝ) (k : ℕ)

/-- `Tr(A_k ρ) = Σₙ a_k(n) ⟨eₙ, ρ eₙ⟩` with `a_k(n) = 1 + Σⱼ (2πnⱼ/L)²` (energy_trace.tex:18–20). -/
def kinTrace (ρ : L2 (Mom k) →L[ℂ] L2 (Mom k)) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (kinWeight L k n * RCLike.re ⟪ev n, ρ (ev n)⟫_ℂ)

theorem kinTrace_eq_formTrace (ρ : L2 (Mom k) →L[ℂ] L2 (Mom k)) :
    kinTrace L k ρ = formTrace (kinSqrt L k) ρ := by
  unfold kinTrace formTrace
  simp_rw [kinSqrt_sq]

/-- **Source statement (energy_trace.tex:20–26), Fourier representation.**  If `ρ ≥ 0` and
`Tr(A_k ρ) < ∞`, then `A_k^{1/2} ρ A_k^{1/2}` exists as a positive trace-class operator `T`,
characterized by `ρ = A_k^{-1/2} T A_k^{-1/2}`, with `Tr T = Tr(A_k ρ)`.  It is unique, and the
DEF-031 energy trace norm of `ρ` equals `Tr(A_k ρ)`. -/
theorem kinetic_realization {ρ : L2 (Mom k) →L[ℂ] L2 (Mom k)} (hρ : ρ.IsPositive)
    (hE : kinTrace L k ρ ≠ ⊤) :
    (∃ T : L2 (Mom k) →L[ℂ] L2 (Mom k), T.IsPositive ∧ IsTraceClass T ∧
      ρ = AhalfInv L k * T * AhalfInv L k ∧ posTrace T = kinTrace L k ρ) ∧
    energyTraceNorm (AhalfInv L k) ρ = kinTrace L k ρ := by
  rw [kinTrace_eq_formTrace] at hE ⊢
  exact ⟨exists_realization (kinSqrt L k) (one_le_kinSqrt L k) hρ hE,
    energyTraceNorm_eq_formTrace (kinSqrt L k) (one_le_kinSqrt L k) hρ hE⟩

/-- Uniqueness of the kinetic realization (EnergyForm). -/
theorem kinetic_realization_unique {T₁ T₂ : L2 (Mom k) →L[ℂ] L2 (Mom k)}
    (h : AhalfInv L k * T₁ * AhalfInv L k = AhalfInv L k * T₂ * AhalfInv L k) : T₁ = T₂ :=
  eq_of_mul_mul_eq (invCLM_injective (kinSqrt L k) (one_le_kinSqrt L k))
    (invCLM_denseRange (kinSqrt L k) (one_le_kinSqrt L k)) h

end Kinetic

end QuantumNLS.EnergyRealization

#print axioms QuantumNLS.EnergyRealization.realization_spec
#print axioms QuantumNLS.EnergyRealization.posTrace_realization
#print axioms QuantumNLS.EnergyRealization.exists_realization
#print axioms QuantumNLS.EnergyRealization.energyTraceNorm_eq_formTrace
#print axioms QuantumNLS.EnergyRealization.posTrace_le_formTrace
#print axioms QuantumNLS.EnergyRealization.kinetic_realization
#print axioms QuantumNLS.EnergyRealization.kinetic_realization_unique
#print axioms QuantumNLS.EnergyRealization.formTrace_rankOne_ev
