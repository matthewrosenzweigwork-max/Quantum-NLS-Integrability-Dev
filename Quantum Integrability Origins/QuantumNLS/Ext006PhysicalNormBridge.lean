import QuantumNLS.Ext006PairTensor
import QuantumNLS.Ext006PhysicalExponentialTerms
import QuantumNLS.Ext006TraceExponentialMajorant

/-! Transport the operator pair tensor into the actual physical sector HN L 2.
This constructs the missing carrier bridge without assuming a Fock norm law. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace ENNReal TensorProduct
namespace QuantumNLS.Ext006PhysicalNormBridge.PairTensor
open TensorCarrier TensorFourier PhysicalTensor BetheCoefficientTransform TraceClass

section TwoPower
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def twoAlgIso : AlgTensorPower ℂ E 2 ≃ₗᵢ[ℂ] (E ⊗[ℂ] E) :=
  (mulIsometry 1 1).symm.trans
    (TensorProduct.congrIsometry firstAlgIsometry firstAlgIsometry)

def twoIso : HilbertTensorPower ℂ E 2 ≃ₗᵢ[ℂ] HilbertTensor ℂ E E :=
  lieCompletion twoAlgIso

lemma twoIso_ptprod (f : Fin 2 → E) :
    twoIso ((ptprod f : AlgTensorPower ℂ E 2) : HilbertTensorPower ℂ E 2) =
      htmul (f 0) (f 1) := by
  have hf : f = Fin.append (fun _ : Fin 1 => f 0) (fun _ : Fin 1 => f 1) := by
    funext i
    fin_cases i <;> rfl
  have hm : (mulIsometry (𝕜 := ℂ) (E := E) 1 1).symm (ptprod f) =
      (ptprod (fun _ : Fin 1 => f 0) : AlgTensorPower ℂ E 1) ⊗ₜ[ℂ]
        (ptprod (fun _ : Fin 1 => f 1) : AlgTensorPower ℂ E 1) := by
    apply (mulIsometry (𝕜 := ℂ) (E := E) 1 1).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (congrArg ptprod hf).trans (mulLinearEquiv_tmul _ _).symm
  rw [twoIso, lieCompletion_coe]
  change ((TensorProduct.congrIsometry firstAlgIsometry firstAlgIsometry
    ((mulIsometry 1 1).symm (ptprod f)) : E ⊗[ℂ] E) : HilbertTensor ℂ E E) = _
  rw [hm]
  simp only [TensorProduct.congrIsometry_apply, TensorProduct.congr_tmul]
  change (((firstAlgEquiv (ptprod (fun _ : Fin 1 => f 0)) : E) ⊗ₜ[ℂ]
    (firstAlgEquiv (ptprod (fun _ : Fin 1 => f 1)) : E) : E ⊗[ℂ] E) :
      HilbertTensor ℂ E E) = _
  rw [firstAlgEquiv_ptprod, firstAlgEquiv_ptprod]
  rfl

lemma twoIso_swap (x : HilbertTensorPower ℂ E 2) :
    twoIso (permHilbertIsometry (Equiv.swap (0 : Fin 2) 1) x) =
      htcommIsometry ℂ E E (twoIso x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((twoIso (E := E)).continuous.comp (permHilbertIsometry _).continuous)
      ((htcommIsometry ℂ E E).continuous.comp (twoIso (E := E)).continuous)
  | ih a =>
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod c f =>
      simp only [UniformSpace.Completion.coe_smul, map_smul,
        permHilbertIsometry_coe, permLinearEquiv_ptprod, twoIso_ptprod,
        Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right,
        htcommIsometry_htmul]
    | add a b ha hb => simp only [UniformSpace.Completion.coe_add, map_add, ha, hb]

lemma twoIso_mem_sym (x : HilbertTensorPower ℂ E 2)
    (hx : htcommIsometry ℂ E E (twoIso x) = twoIso x) :
    x ∈ SymSector ℂ E 2 := by
  intro σ
  have hσ : σ = 1 ∨ σ = Equiv.swap (0 : Fin 2) 1 := by
    fin_cases σ <;> decide
  rcases hσ with rfl | rfl
  · change (permHom ℂ E 2 1) x = x
    rw [map_one]
    rfl
  · apply (twoIso (E := E)).injective
    exact (twoIso_swap x).trans hx
end TwoPower

variable {L : ℝ} [Fact (0 < L)] {ι : Type*}

/-- The actual physical bosonic pair vector associated with K. -/
def physicalPair (b : HilbertBasis ι ℂ (L2T L)) (K : L2T L →L[ℂ] L2T L)
    (hHS : hsSq b K ≠ ⊤)
    (hSym : ∀ i j, inner ℂ (b i) (K (b j)) = inner ℂ (b j) (K (b i))) : HN L 2 :=
  ⟨twoIso.symm (Ext006PairTensor.pairTensor b K hHS), by
    apply twoIso_mem_sym
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact Ext006PairTensor.pairTensor_flip b K hHS hSym⟩

lemma physicalPair_twoIso (b : HilbertBasis ι ℂ (L2T L)) (K : L2T L →L[ℂ] L2T L)
    (hHS : hsSq b K ≠ ⊤)
    (hSym : ∀ i j, inner ℂ (b i) (K (b j)) = inner ℂ (b j) (K (b i))) :
    twoIso (physicalPair b K hHS hSym : HilbertTensorPower ℂ (L2T L) 2) =
      Ext006PairTensor.pairTensor b K hHS :=
  twoIso.apply_symm_apply _

/-- Exact matrix coefficients in physical tensor coordinates. -/
theorem physicalPair_coefficient (b : HilbertBasis ι ℂ (L2T L))
    (K : L2T L →L[ℂ] L2T L) (hHS : hsSq b K ≠ ⊤)
    (hSym : ∀ i j, inner ℂ (b i) (K (b j)) = inner ℂ (b j) (K (b i))) (i j : ι) :
    inner ℂ ((ptprod ![b i, b j] : AlgTensorPower ℂ (L2T L) 2) :
      HilbertTensorPower ℂ (L2T L) 2) (physicalPair b K hHS hSym) =
        inner ℂ (b i) (K (b j)) := by
  have h := (twoIso (E := L2T L)).inner_map_map
    (((ptprod ![b i, b j] : AlgTensorPower ℂ (L2T L) 2) :
      HilbertTensorPower ℂ (L2T L) 2))
    (physicalPair b K hHS hSym : HilbertTensorPower ℂ (L2T L) 2)
  rw [twoIso_ptprod, physicalPair_twoIso] at h
  change inner ℂ (htmul (b i) (b j)) (Ext006PairTensor.pairTensor b K hHS) = _ at h
  exact h.symm.trans (Ext006PairTensor.pairTensor_coefficient b K hHS i j)

/-- The physical pair norm is exactly the operator Hilbert-Schmidt norm. -/
theorem physicalPair_norm_sq (b : HilbertBasis ι ℂ (L2T L))
    (K : L2T L →L[ℂ] L2T L) (hHS : hsSq b K ≠ ⊤)
    (hSym : ∀ i j, inner ℂ (b i) (K (b j)) = inner ℂ (b j) (K (b i))) :
    ‖physicalPair b K hHS hSym‖^2 = (hsSq b K).toReal := by
  change ‖twoIso.symm (Ext006PairTensor.pairTensor b K hHS)‖^2 = _
  rw [LinearIsometryEquiv.norm_map]
  exact Ext006PairTensor.pairTensor_norm_sq b K hHS

end QuantumNLS.Ext006PhysicalNormBridge.PairTensor
end

/-! Exact constant and linear coefficients of the trace exponential.
These are algebraic coefficient computations, without any physical norm premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped ENNReal
namespace QuantumNLS.Ext006PhysicalNormBridge.TraceCoefficients
open Ext006TraceExponentialMajorant Ext006FredholmTracePower TraceClass

lemma length_le_degree (n : ℕ) (w : Word n) : n ≤ wordDegree n w := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    change n+1 ≤ w.1+1 + wordDegree n w.2
    have := ih w.2
    omega

/-- The empty word is the only word of total degree zero. -/
theorem coefficient_zero (a : ℕ → ℝ≥0∞) : coefficient a 0 = 1 := by
  classical
  let p0 : {p : AllWords // degree p = 0} := ⟨⟨0, PUnit.unit⟩, rfl⟩
  rw [coefficient, tsum_eq_single p0]
  · simp [family, wordWeight, p0]
  · intro p hp
    obtain ⟨⟨n,w⟩,h⟩ := p
    cases n with
    | zero => cases w; exact (hp rfl).elim
    | succ n =>
      change w.1+1 + wordDegree n w.2 = 0 at h
      omega

/-- The unique word of total degree one has one letter, of degree one. -/
theorem coefficient_one (a : ℕ → ℝ≥0∞) : coefficient a 1 = a 0 := by
  classical
  let p1 : {p : AllWords // degree p = 1} := ⟨⟨1, (0, PUnit.unit)⟩, rfl⟩
  rw [coefficient, tsum_eq_single p1]
  · simp [family, wordWeight, p1]
  · intro p hp
    obtain ⟨⟨n,w⟩,h⟩ := p
    cases n with
    | zero => change 0 = 1 at h; omega
    | succ n =>
      obtain ⟨i,w⟩ := w
      change i+1 + wordDegree n w = 1 at h
      have hd := length_le_degree n w
      have hn : n = 0 := by omega
      have hi : i = 0 := by omega
      subst n
      subst i
      cases w
      exact (hp rfl).elim

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma traceCoefficient_zero (T : H →L[ℂ] H) : traceCoefficient T 0 = 1 :=
  coefficient_zero _

lemma traceCoefficient_one (T : H →L[ℂ] H) :
    traceCoefficient T 1 = ENNReal.ofReal ((traceNorm T).toReal / 2) := by
  rw [traceCoefficient, coefficient_one]
  simp [traceLetter, tracePowerTerm]

/-- Exact linear coefficient for K* K, with no small Hilbert-Schmidt norm. -/
theorem kernel_coefficient_one (b : HilbertBasis ι ℂ H) (K : H →L[ℂ] H)
    (hHS : hsSq b K ≠ ⊤) :
    traceCoefficient (K.adjoint ∘L K) 1 = ENNReal.ofReal ((hsSq b K).toReal / 2) := by
  rw [traceCoefficient_one, traceNorm_of_isPositive
    (ContinuousLinearMap.isPositive_adjoint_comp_self K),
    (Ext006Blocks.beta_adjoint_beta_traceClass b K hHS).2]

end QuantumNLS.Ext006PhysicalNormBridge.TraceCoefficients
end

/-! Identify the adjoint-defined physical pair creator with symmetrized tensor
multiplication. This is a physical operator identity on every completed sector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006PhysicalNormBridge.CreationFormula
open TensorCarrier PhysicalTensor BetheCoefficientTransform IntrinsicContact Ext005PairSector
variable {L : ℝ} [Fact (0 < L)]

/-- Exact physical creation formula, including the bosonic factor. -/
theorem creation_eq_projection (b : HN L 2) (n : ℕ) (x : HN L n) :
    creation b n x = (Real.sqrt (((n : ℝ)+1)*((n : ℝ)+2)) : ℂ) •
      (physSector L (2+n)).orthogonalProjectionOnto
        ((splitIsometry 2 n).symm (htmul
          (b : HilbertTensorPower ℂ (L2T L) 2)
          (x : HilbertTensorPower ℂ (L2T L) n))) := by
  apply ext_inner_right ℂ
  intro y
  rw [creation, ContinuousLinearMap.adjoint_inner_left]
  simp only [annihilation, smul_apply, inner_smul_right, inner_smul_left,
    Complex.conj_ofReal]
  congr 1
  change inner ℂ x ((physSector L n).orthogonalProjectionOnto
    (contractL (b : HilbertTensorPower ℂ (L2T L) 2) (splitIsometry 2 n y))) = _
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, inner_contractL,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    (splitIsometry (𝕜 := ℂ) (E := L2T L) 2 n).inner_map_map
      ((splitIsometry 2 n).symm (htmul
        (b : HilbertTensorPower ℂ (L2T L) 2)
        (x : HilbertTensorPower ℂ (L2T L) n)))
      (y : HilbertTensorPower ℂ (L2T L) (2+n))

/-- The zero-particle split has the actual physical vacuum in its last factor. -/
lemma split_zero_right (x : HilbertTensorPower ℂ (L2T L) 2) :
    splitIsometry 2 0 x = htmul x
      (Ext006ZeroVacuum.sectorVacuum L : HilbertTensorPower ℂ (L2T L) 0) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    apply isClosed_eq (splitIsometry 2 0).continuous
    exact (UniformSpace.Completion.continuous_coe _).comp
      ((TensorProduct.mkL ℂ (HilbertTensorPower ℂ (L2T L) 2)
        (HilbertTensorPower ℂ (L2T L) 0)).continuous₂.comp
          (continuous_id.prodMk continuous_const))
  | ih a =>
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod c f =>
      simp only [UniformSpace.Completion.coe_smul, map_smul, htmul_smul_left]
      have hf : Fin.append f (fun _ : Fin 0 => (0 : L2T L)) = f := by
        funext i
        exact Fin.append_left f (fun _ : Fin 0 => (0 : L2T L)) i
      simpa only [hf, Ext006ZeroVacuum.sectorVacuum, htpow] using
        congrArg (fun z => c • z)
          (splitIsometry_ptprod_append f (fun _ : Fin 0 => (0 : L2T L)))
    | add a b ha hb =>
      simp only [UniformSpace.Completion.coe_add, map_add, ha, hb, htmul_add_left]

/-- The first pair creator acts on the physical vacuum as sqrt(2) times b. -/
theorem creation_vacuum (b : HN L 2) :
    creation b 0 (Ext006ZeroVacuum.sectorVacuum L) = (Real.sqrt 2 : ℂ) • b := by
  rw [creation_eq_projection]
  have hz := split_zero_right (b : HilbertTensorPower ℂ (L2T L) 2)
  rw [← hz, LinearIsometryEquiv.symm_apply_apply,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  norm_num

/-- Exact first physical exponential term. -/
theorem term_one (b : HN L 2) :
    Ext006PhysicalExponentialTerms.term b 1 = (-(Real.sqrt 2)/2 : ℂ) • b := by
  rw [Ext006PhysicalExponentialTerms.term_step,
    Ext006PhysicalExponentialTerms.term_zero, creation_vacuum]
  change Ext006PhysicalExponentialTerms.stepScalar 0 • ((Real.sqrt 2 : ℂ) • b) = _
  rw [smul_smul]
  congr 1
  norm_num [Ext006PhysicalExponentialTerms.stepScalar]
  ring

/-- The exact first squared norm, without a smallness restriction on b. -/
theorem term_one_norm_sq (b : HN L 2) :
    ‖Ext006PhysicalExponentialTerms.term b 1‖^2 = ‖b‖^2 / 2 := by
  rw [term_one, norm_smul, mul_pow]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : ‖(-(Real.sqrt 2)/2 : ℂ)‖ = Real.sqrt 2 / 2 := by
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    norm_num
  rw [hn, div_pow, hs]
  ring

/-- Exact squared norm of creation as a symmetrized tensor product. -/
theorem creation_norm_sq (b : HN L 2) (n : ℕ) (x : HN L n) :
    ‖creation b n x‖^2 = (((n : ℝ)+1)*((n : ℝ)+2)) *
      ‖(physSector L (2+n)).orthogonalProjectionOnto
        ((splitIsometry 2 n).symm (htmul
          (b : HilbertTensorPower ℂ (L2T L) 2)
          (x : HilbertTensorPower ℂ (L2T L) n)))‖^2 := by
  rw [creation_eq_projection, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity)]

/-- The physical norm recursion reduces to the norm of a symmetrized tensor
insertion. Evaluating that norm in all degrees is the remaining Wick calculation. -/
theorem term_norm_sq_step (b : HN L 2) (n : ℕ) :
    ‖Ext006PhysicalExponentialTerms.term b (n+1)‖^2 =
      ((2*((n : ℝ)+1))⁻¹)^2 *
        ((((2*n : ℕ) : ℝ)+1)*(((2*n : ℕ) : ℝ)+2)) *
      ‖(physSector L (2+2*n)).orthogonalProjectionOnto
        ((splitIsometry 2 (2*n)).symm (htmul
          (b : HilbertTensorPower ℂ (L2T L) 2)
          (Ext006PhysicalExponentialTerms.term b n :
            HilbertTensorPower ℂ (L2T L) (2*n))))‖^2 := by
  rw [Ext006PhysicalExponentialTerms.term_step, LinearIsometryEquiv.norm_map,
    norm_smul, Ext006PhysicalExponentialTerms.norm_stepScalar, mul_pow,
    creation_norm_sq]
  ring

end QuantumNLS.Ext006PhysicalNormBridge.CreationFormula
end

/-! Physical norm/trace coefficient identity in degrees zero and one.
The all-degree identity remains a separate obligation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped ENNReal InnerProductSpace
namespace QuantumNLS.Ext006PhysicalNormBridge.InitialNormIdentity
open PhysicalTensor BetheCoefficientTransform TraceClass
open Ext006PhysicalExponentialTerms Ext006PhysicalNormBridge.PairTensor
open Ext006PhysicalNormBridge.CreationFormula Ext006TraceExponentialMajorant Ext006PhysicalNormBridge.TraceCoefficients
variable {L : ℝ} [Fact (0 < L)] {ι : Type*}

/-- Constant physical coefficient and constant trace coefficient agree. -/
theorem norm_trace_zero (b : HilbertBasis ι ℂ (L2T L)) (K : L2T L →L[ℂ] L2T L)
    (hHS : hsSq b K ≠ ⊤)
    (hSym : ∀ i j, inner ℂ (b i) (K (b j)) = inner ℂ (b j) (K (b i))) :
    ENNReal.ofReal (‖term (physicalPair b K hHS hSym) 0‖^2) =
      traceCoefficient (K.adjoint ∘L K) 0 := by
  rw [term_zero_norm, traceCoefficient_zero]
  norm_num

/-- The first nonconstant coefficient is the squared norm of the actual
adjoint-defined physical pair-creation term, with its exact factor one half. -/
theorem norm_trace_one (b : HilbertBasis ι ℂ (L2T L)) (K : L2T L →L[ℂ] L2T L)
    (hHS : hsSq b K ≠ ⊤)
    (hSym : ∀ i j, inner ℂ (b i) (K (b j)) = inner ℂ (b j) (K (b i))) :
    ENNReal.ofReal (‖term (physicalPair b K hHS hSym) 1‖^2) =
      traceCoefficient (K.adjoint ∘L K) 1 := by
  rw [term_one_norm_sq, physicalPair_norm_sq, kernel_coefficient_one b K hHS]

/-- Initial degrees of the physical norm identity, without any operator-norm
or small-Hilbert-Schmidt-norm hypothesis. This is not an all-degree theorem. -/
theorem norm_trace_initial (b : HilbertBasis ι ℂ (L2T L)) (K : L2T L →L[ℂ] L2T L)
    (hHS : hsSq b K ≠ ⊤)
    (hSym : ∀ i j, inner ℂ (b i) (K (b j)) = inner ℂ (b j) (K (b i)))
    (n : ℕ) (hn : n ≤ 1) :
    ENNReal.ofReal (‖term (physicalPair b K hHS hSym) n‖^2) =
      traceCoefficient (K.adjoint ∘L K) n := by
  interval_cases n
  · exact norm_trace_zero b K hHS hSym
  · exact norm_trace_one b K hHS hSym

end QuantumNLS.Ext006PhysicalNormBridge.InitialNormIdentity
end

#print axioms QuantumNLS.Ext006PhysicalNormBridge.PairTensor.twoAlgIso
#print axioms QuantumNLS.Ext006PhysicalNormBridge.PairTensor.twoIso
#print axioms QuantumNLS.Ext006PhysicalNormBridge.PairTensor.twoIso_ptprod
#print axioms QuantumNLS.Ext006PhysicalNormBridge.PairTensor.twoIso_swap
#print axioms QuantumNLS.Ext006PhysicalNormBridge.PairTensor.twoIso_mem_sym
#print axioms QuantumNLS.Ext006PhysicalNormBridge.PairTensor.physicalPair
#print axioms QuantumNLS.Ext006PhysicalNormBridge.PairTensor.physicalPair_twoIso
#print axioms QuantumNLS.Ext006PhysicalNormBridge.PairTensor.physicalPair_coefficient
#print axioms QuantumNLS.Ext006PhysicalNormBridge.PairTensor.physicalPair_norm_sq
#print axioms QuantumNLS.Ext006PhysicalNormBridge.TraceCoefficients.length_le_degree
#print axioms QuantumNLS.Ext006PhysicalNormBridge.TraceCoefficients.coefficient_zero
#print axioms QuantumNLS.Ext006PhysicalNormBridge.TraceCoefficients.coefficient_one
#print axioms QuantumNLS.Ext006PhysicalNormBridge.TraceCoefficients.traceCoefficient_zero
#print axioms QuantumNLS.Ext006PhysicalNormBridge.TraceCoefficients.traceCoefficient_one
#print axioms QuantumNLS.Ext006PhysicalNormBridge.TraceCoefficients.kernel_coefficient_one
#print axioms QuantumNLS.Ext006PhysicalNormBridge.CreationFormula.creation_eq_projection
#print axioms QuantumNLS.Ext006PhysicalNormBridge.CreationFormula.split_zero_right
#print axioms QuantumNLS.Ext006PhysicalNormBridge.CreationFormula.creation_vacuum
#print axioms QuantumNLS.Ext006PhysicalNormBridge.CreationFormula.term_one
#print axioms QuantumNLS.Ext006PhysicalNormBridge.CreationFormula.term_one_norm_sq
#print axioms QuantumNLS.Ext006PhysicalNormBridge.CreationFormula.creation_norm_sq
#print axioms QuantumNLS.Ext006PhysicalNormBridge.CreationFormula.term_norm_sq_step
#print axioms QuantumNLS.Ext006PhysicalNormBridge.InitialNormIdentity.norm_trace_zero
#print axioms QuantumNLS.Ext006PhysicalNormBridge.InitialNormIdentity.norm_trace_one
#print axioms QuantumNLS.Ext006PhysicalNormBridge.InitialNormIdentity.norm_trace_initial

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006PhysicalNormBridge." then
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
