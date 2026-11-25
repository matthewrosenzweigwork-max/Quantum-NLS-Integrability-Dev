import QuantumNLS.RootSymbolFrechet
import QuantumNLS.KernelFactorialBound

/-! Actual real multilinear coefficients of the transfer polynomials. The
complex inner product is real bilinear on the underlying real spaces, so
these coefficients include radial and mixed physical directions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace
open QuantumNLS.TensorCarrier QuantumNLS.RootOverlapLimit QuantumNLS.RootOverlapCommutator
namespace QuantumNLS.Q07TensorCoefficientsR15
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Fixing the first tensor in the actual kernel pairing. -/
def rightCoefficient (n : ℕ)
    (A : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n)
    (x : HilbertTensorPower ℂ H n) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => H) ℂ :=
  (((innerSL ℂ x).comp A).restrictScalars ℝ).compContinuousMultilinearMap (htpowML n)

theorem rightCoefficient_apply (n : ℕ)
    (A : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n)
    (x : HilbertTensorPower ℂ H n) (v : Fin n → H) :
    rightCoefficient n A x v = ⟪x, A (ptC v)⟫_ℂ := by
  simp [rightCoefficient, ContinuousLinearMap.compContinuousMultilinearMap_coe,
    htpowML_apply, ContinuousLinearMap.comp_apply]

def coefficientMap (n : ℕ)
    (A : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) :
    HilbertTensorPower ℂ H n →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => H) ℂ :=
  LinearMap.mkContinuous
    { toFun := rightCoefficient n A
      map_add' := by intros; ext v; simp [rightCoefficient_apply, inner_add_left]
      map_smul' := by
        intro r x
        ext v
        simp only [rightCoefficient_apply, RingHom.id_apply]
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r x, inner_smul_left]
        simp [Complex.real_smul, rightCoefficient_apply] }
    ‖A‖ (fun x => by
      apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
      intro v
      change ‖rightCoefficient n A x v‖ ≤ (‖A‖ * ‖x‖) * ∏ i, ‖v i‖
      rw [rightCoefficient_apply]
      calc
        _ ≤ ‖x‖ * ‖A (ptC v)‖ := norm_inner_le_norm _ _
        _ ≤ ‖x‖ * (‖A‖ * ‖(ptC v : HilbertTensorPower ℂ H n)‖) :=
          mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
        _ = (‖A‖ * ‖x‖) * ∏ i, ‖v i‖ := by rw [RootSymbolFrechet.norm_ptC']; ring)

/-- The degree 2n real coefficient of the diagonal kernel polynomial. -/
def tensorCoefficient (n : ℕ)
    (A : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (n+n) => H) ℂ :=
  (((coefficientMap n A).compContinuousMultilinearMap (htpowML n)).uncurrySum).domDomCongr
    finSumFinEquiv

theorem tensorCoefficient_diagonal (n : ℕ)
    (A : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) (u : H) :
    tensorCoefficient n A (fun _ => u) = RootSymbolFrechet.symFun n A u := by
  change rightCoefficient n A (htpowML n (fun _ => u)) (fun _ => u) = _
  rw [rightCoefficient_apply, htpowML_apply]
  rfl

theorem norm_htpowML_le (n : ℕ) : ‖htpowML (H := H) n‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro v
  rw [htpowML_apply, RootSymbolFrechet.norm_ptC', one_mul]

theorem norm_tensorCoefficient_le (n : ℕ)
    (A : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) :
    ‖tensorCoefficient n A‖ ≤ ‖A‖ := by
  rw [tensorCoefficient, ContinuousMultilinearMap.norm_domDomCongr]
  have h1 : ‖coefficientMap n A‖ ≤ ‖A‖ :=
    LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  have h2 := ContinuousLinearMap.norm_compContinuousMultilinearMap_le
    (coefficientMap n A) (htpowML (H := H) n)
  have h3 := (ContinuousMultilinearMap.currySumEquiv ℝ (Fin n) (Fin n) H ℂ).symm.norm_map
    ((coefficientMap n A).compContinuousMultilinearMap (htpowML n))
  change ‖((coefficientMap n A).compContinuousMultilinearMap (htpowML n)).uncurrySum‖ ≤ _
  rw [show ‖((coefficientMap n A).compContinuousMultilinearMap (htpowML n)).uncurrySum‖ =
      ‖(coefficientMap n A).compContinuousMultilinearMap (htpowML n)‖ from h3]
  exact h2.trans ((mul_le_mul h1 (norm_htpowML_le n) (ContinuousMultilinearMap.opNorm_nonneg (htpowML (H := H) n))
    (norm_nonneg _)).trans_eq (mul_one _))


theorem contDiff_symFun_all (n : ℕ)
    (A : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) (N : WithTop ℕ∞) :
    ContDiff ℝ N (RootSymbolFrechet.symFun n A) := by
  have he : RootSymbolFrechet.symFun n A =
      tensorCoefficient n A ∘ diagL (H := H) (n+n) := by
    funext v
    exact (tensorCoefficient_diagonal n A v).symm
  rw [he]
  exact (tensorCoefficient n A).contDiff.comp (diagL (H := H) (n+n)).contDiff

/-- Full real multilinear derivative bound for the actual degree-2n kernel
polynomial. This includes arbitrary independent physical directions. -/
theorem norm_iterated_symFun_le (n k : ℕ)
    (A : HilbertTensorPower ℂ H n →L[ℂ] HilbertTensorPower ℂ H n) (u : H) :
    ‖iteratedFDeriv ℝ k (RootSymbolFrechet.symFun n A) u‖ ≤
      ((n+n).descFactorial k : ℝ) * ‖A‖ * ‖u‖ ^ (n+n-k) := by
  let P := tensorCoefficient n A
  let d := diagL (H := H) (n+n)
  have hd : ‖d‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simp only [one_mul]
    exact pi_norm_le_iff_of_nonneg (norm_nonneg v) |>.mpr (fun _ => le_rfl)
  have hdu : ‖d u‖ ≤ ‖u‖ := by
    simpa only [one_mul] using (d.le_of_opNorm_le hd u)
  have he : RootSymbolFrechet.symFun n A = P ∘ d := by
    funext v
    exact (tensorCoefficient_diagonal n A v).symm
  rw [he, d.iteratedFDeriv_comp_right P.contDiff u le_rfl]
  have hp := P.norm_iteratedFDeriv_le k (d u)
  have hc := (iteratedFDeriv ℝ k P (d u)).norm_compContinuousLinearMap_le
    (fun _ : Fin k => d)
  have hprod : (∏ _ : Fin k, ‖d‖) ≤ 1 := by
    simpa using (pow_le_one₀ (norm_nonneg d) hd : ‖d‖^k ≤ 1)
  calc
    _ ≤ ‖iteratedFDeriv ℝ k P (d u)‖ * ∏ _ : Fin k, ‖d‖ := hc
    _ ≤ ‖iteratedFDeriv ℝ k P (d u)‖ := by nlinarith [norm_nonneg (iteratedFDeriv ℝ k P (d u))]
    _ ≤ ((n+n).descFactorial k : ℝ) * ‖P‖ * ‖d u‖ ^ (n+n-k) := by
      simpa only [Fintype.card_fin] using hp
    _ ≤ ((n+n).descFactorial k : ℝ) * ‖A‖ * ‖u‖ ^ (n+n-k) := by
      gcongr
      exact norm_tensorCoefficient_le n A

open QuantumNLS.TensorPlacements QuantumNLS.NormalizedTransfer
  QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition

/-- The actual weighted transfer term inherits the printed factorial bound
for every full real derivative. No derivative estimate is a premise. -/
theorem physical_term_derivative_bound {L : ℝ} [Fact (0 < L)]
    (κ : ℝ) (z : ℂ) (n k : ℕ) (u : L2T L) :
    ‖iteratedFDeriv ℝ k (fun v => symbolTerm L κ v z n) u‖ ≤
      ((n+n).descFactorial k : ℝ) *
        (2 * Real.exp (L * |z.im|) * (|κ| * L)^n / Real.sqrt ((2*n).factorial : ℝ)) *
        ‖u‖ ^ (n+n-k) := by
  let A := extendSymKernel (orderedKernel L n z)
  have he : (fun v => symbolTerm L κ v z n) =
      fun v => ((κ^n : ℝ) : ℂ) • RootSymbolFrechet.symFun n A v := by
    funext v
    simp only [symbolTerm, RootSymbolFrechet.symFun, kernelProductSymbol,
      smul_eq_mul, A, extend_htpow]
  have hc : ContDiff ℝ k (RootSymbolFrechet.symFun n A) := by
    simpa +instances only [NormedSpace.complexToReal, NormedSpace.restrictScalars_eq] using contDiff_symFun_all n A k
  rw [he, iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (i := k) (x := u)
    (f := RootSymbolFrechet.symFun n A) (a := ((κ^n : ℝ) : ℂ)) hc.contDiffAt]
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_pow]
  have hA : |κ|^n * ‖A‖ ≤
      2 * Real.exp (L * |z.im|) * (|κ| * L)^n / Real.sqrt ((2*n).factorial : ℝ) := by
    exact (mul_le_mul_of_nonneg_left (norm_extendSymKernel_le _) (pow_nonneg (abs_nonneg _) n)).trans
      (KernelFactorialBound.kernel_bound κ n z)
  have hp : ‖iteratedFDeriv ℝ k (RootSymbolFrechet.symFun n A) u‖ ≤
      ((n+n).descFactorial k : ℝ) * ‖A‖ * ‖u‖^(n+n-k) := by
    let nsR : NormedSpace ℝ (L2T L) := by
      letI : NormedSpace ℂ (L2T L) := (inferInstance : InnerProductSpace ℂ (L2T L)).toNormedSpace
      exact NormedSpace.complexToReal
    let P (s : NormedSpace ℝ (L2T L)) : Prop := by
      letI : NormedSpace ℝ (L2T L) := s
      letI : Module ℝ (L2T L) := s.toModule
      exact ‖iteratedFDeriv ℝ k (RootSymbolFrechet.symFun n A) u‖ ≤
        ((n+n).descFactorial k : ℝ) * ‖A‖ * ‖u‖^(n+n-k)
    have hs : P nsR := norm_iterated_symFun_le n k A u
    have hn : nsR = (inferInstance : NormedSpace ℝ (L2T L)) := by
      let : NormedSpace ℂ (L2T L) := (inferInstance : InnerProductSpace ℂ (L2T L)).toNormedSpace
      exact NormedSpace.restrictScalars_eq ℝ ℂ
    exact Eq.mp (congrArg P hn) hs
  calc
    _ ≤ |κ|^n * (((n+n).descFactorial k : ℝ) * ‖A‖ * ‖u‖ ^ (n+n-k)) :=
      mul_le_mul_of_nonneg_left hp (pow_nonneg (abs_nonneg _) n)
    _ = ((n+n).descFactorial k : ℝ) * (|κ|^n * ‖A‖) * ‖u‖ ^ (n+n-k) := by ring
    _ ≤ _ := by gcongr

end QuantumNLS.Q07TensorCoefficientsR15
