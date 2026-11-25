import QuantumNLS.IndexedPrincipalBindingR30b
import QuantumNLS.Local014Main

/-! The actual contour Hamiltonian's time-2pi propagator tends to identity.
The two operators commute in the accepted physical Bethe basis; subtracting
before exponentiation gives a small operator and avoids an exponential-in-N
estimate. The exact occupation return is the frozen R27b theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 30000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology Complex
namespace QuantumNLS.IndexedQuantumEndpointR30b
open LOCAL009R22LiteralScalar
open PhysicalTensor TensorCarrier NormalityBridge IndexedHermitianR30b IndexedPrincipalBindingR30b
  IndexedCFCBindingR29b IndexedContourBoundsR29b IndexedQuantumR27b Local014Main Local014Heisenberg
  LOCAL009R23PhysicalInverse LOCAL009R23OperatorContour LOCAL009R23DiagonalAnalytic
  LOCAL009R22OperatorSupport LOCAL009R22Assembly LOCAL009R23Final
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isDiag_hermitian (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] H) (hA : IsDiag b A) :
    IsDiag b (hermitianPart A) := by
  intro m
  obtain ⟨a,ha⟩ := hA m
  obtain ⟨d,hd⟩ := hA.adjoint m
  refine ⟨(1/2 : ℂ)*(a+d),?_⟩
  simp only [hermitianPart,smul_apply,add_apply,ha,hd,
    ← add_smul,smul_smul]

theorem exp_small_diagonal (b : HilbertBasis ι ℂ H) (D : H →L[ℂ] H)
    (hD : IsDiag b D) (hb : ‖D‖ ≤ 1) : ‖opExp D-1‖ ≤ 2*‖D‖ := by
  classical
  let a : ι → ℂ := fun m => (hD m).choose
  have ha (m : ι) : D (b m) = a m • b m := (hD m).choose_spec
  apply norm_le_of_eigen b (opExp D-1) (fun m => Complex.exp (a m)-1)
  · intro m
    simp only [sub_apply,opExp,IndexedQuantumR27b.exp_eigen D (b m) (a m) (ha m),
      ContinuousLinearMap.one_def,ContinuousLinearMap.id_apply,sub_smul,one_smul]
  · positivity
  · intro m
    have hm := norm_eigen_le b D _ m (ha m)
    exact (Complex.norm_exp_sub_one_le (hm.trans hb)).trans (by linarith)

theorem opExp_add_commute {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    {x y : 𝔸} (hxy : Commute x y) : opExp (x+y) = opExp x*opExp y :=
  NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hxy
    ((NormedSpace.expSeries_radius_eq_top ℂ 𝔸).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℂ 𝔸).symm ▸ edist_lt_top _ _)

variable {L κ : ℝ} [Fact (0 < L)]

def endpointScalar (N : ℕ) : ℂ := I*(2*Real.pi)*(N : ℂ)
def endpointError (hκ : 0 < κ) (n : ℤ) (N : ℕ) : Sector L N →L[ℂ] Sector L N :=
  endpointScalar N • (hamiltonian (L := L) κ n N-normalizedOccupation (L := L) hκ n N)
def endpointBound (κ L : ℝ) : ℝ := 2*Real.pi*scalarConstant κ L 1

theorem actual_diagonal (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) :
    IsDiag (basis (L := L) hκ (eps_pos hN) hN) (hamiltonian (L := L) κ n N) ∧
    IsDiag (basis (L := L) hκ (eps_pos hN) hN) (normalizedOccupation (L := L) hκ n N) := by
  constructor
  · rw [hamiltonian_literal hκ hs hN]
    apply isDiag_hermitian
    intro m
    exact ⟨_,approximation_eigen hκ (by norm_num : (0 : ℝ) < 1)
      (show κ*L*1 ≤ 1/1000000 by nlinarith) hN (eps_pos hN) (eps_le_one hN)
      (by rw [eps_budget hN]) n m⟩
  · intro m
    refine ⟨(eps N : ℂ)*(m.1 n : ℂ),?_⟩
    rw [normalizedOccupation,dite_eq_left hN,smul_apply,
      occupationCount_eigen hκ (eps_pos hN) hN,smul_smul]

theorem endpointError_diagonal (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) :
    IsDiag (basis (L := L) hκ (eps_pos hN) hN) (endpointError (L := L) hκ n N) := by
  obtain ⟨hH,hQ⟩ := actual_diagonal hκ hs hN n
  intro m
  obtain ⟨a,ha⟩ := hH m
  obtain ⟨q,hq⟩ := hQ m
  refine ⟨endpointScalar N*(a-q),?_⟩
  simp only [endpointError,smul_apply,sub_apply,ha,hq,
    ← sub_smul,smul_smul]

theorem endpointError_bound (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) : ‖endpointError (L := L) hκ n N‖ ≤ endpointBound κ L*eps N := by
  have hC := scalarConstant_nonneg hκ (Fact.out : 0 < L) (by norm_num : (0 : ℝ) < 1)
  have hc : ‖endpointScalar N‖ = (2*Real.pi)*(N : ℝ) := by
    simp only [endpointScalar,norm_mul,norm_I,one_mul,Complex.norm_natCast]
    norm_num [norm_mul,Real.pi_pos.le,abs_of_nonneg]
  rw [endpointError,RadiusBound.norm_smul_kernel,hc]
  calc
    _ ≤ ((2*Real.pi)*(N : ℝ))*(scalarConstant κ L 1*(eps N)^2) :=
      mul_le_mul_of_nonneg_left (contour_occupation_bound hκ hs hN n) (by positivity)
    _ = (2*Real.pi*scalarConstant κ L 1)*(eps N*(N : ℝ))*eps N := by ring
    _ = endpointBound κ L*eps N := by rw [eps_budget hN]; unfold endpointBound; ring

theorem occupation_endpoint (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (n : ℤ) :
    (opExp (endpointScalar N • normalizedOccupation (L := L) hκ n N) : Sector L N →L[ℂ] Sector L N) = 1 := by
  have hm : (opExp ((-endpointScalar N) • normalizedOccupation (L := L) hκ n N) : Sector L N →L[ℂ] Sector L N) = 1 := by
    rw [normalizedOccupation,dite_eq_left hN,smul_smul]
    have hc : (-endpointScalar N)*(eps N : ℂ) = -(((2*Real.pi : ℝ) : ℂ)*I) := by
      have he := eps_budget hN
      have hec : (eps N : ℂ)*(N : ℂ) = 1 := by exact_mod_cast he
      unfold endpointScalar
      calc
        _ = -(((2*Real.pi : ℝ) : ℂ)*I)*((eps N : ℂ)*(N : ℂ)) := by push_cast; ring
        _ = _ := by rw [hec,mul_one]
    rw [hc]
    exact propagator_period hκ (eps_pos hN) n N
  have hi := opExp_smul_mul (endpointScalar N) (-endpointScalar N) (normalizedOccupation (L := L) hκ n N)
  rw [hm,mul_one,add_neg_cancel] at hi
  simpa only [zero_smulL,opExp_zeroL] using hi

theorem endpoint_as_small_exp (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    {N : ℕ} (hN : 0 < N) (n : ℤ) :
    opExp (endpointScalar N • hamiltonian (L := L) κ n N) = opExp (endpointError (L := L) hκ n N) := by
  obtain ⟨hH,hQ⟩ := actual_diagonal hκ hs hN n
  have hc := hH.commute hQ
  have hd : Commute (endpointError (L := L) hκ n N) (endpointScalar N • normalizedOccupation (L := L) hκ n N) :=
    ((hc.sub_left (Commute.refl _)).smul_left _).smul_right _
  have he : endpointError (L := L) hκ n N+endpointScalar N • normalizedOccupation (L := L) hκ n N =
      endpointScalar N • hamiltonian (L := L) κ n N := by rw [endpointError,smul_sub,sub_add_cancel]
  have hexp : opExp (endpointError (L := L) hκ n N+endpointScalar N • normalizedOccupation (L := L) hκ n N) =
      opExp (endpointError (L := L) hκ n N)*opExp (endpointScalar N • normalizedOccupation (L := L) hκ n N) :=
    opExp_add_commute hd
  calc
    _ = opExp (endpointError (L := L) hκ n N+endpointScalar N • normalizedOccupation (L := L) hκ n N) :=
      congrArg opExp he.symm
    _ = opExp (endpointError (L := L) hκ n N)*opExp (endpointScalar N • normalizedOccupation (L := L) hκ n N) := hexp
    _ = _ := by rw [occupation_endpoint hκ hN n,mul_one]

theorem endpoint_norm_tendsto_zero (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000) (n : ℤ) :
    Tendsto (fun N => ‖opExp (endpointScalar N • hamiltonian (L := L) κ n N)-1‖)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun N => endpointBound κ L*eps N) atTop (𝓝 0) := by
    simpa using eps_tendsto_zero.const_mul (endpointBound κ L)
  have hsmall : ∀ᶠ N in atTop, endpointBound κ L*eps N < 1 := ht.eventually (gt_mem_nhds (by norm_num))
  apply squeeze_zero' (g := fun N => 2*(endpointBound κ L*eps N)) (Eventually.of_forall fun N => ContinuousLinearMap.opNorm_nonneg
    ((opExp (endpointScalar N • hamiltonian (L := L) κ n N)-1) : Sector L N →L[ℂ] Sector L N))
  · filter_upwards [eventually_gt_atTop 0,hsmall] with N hN hsm
    rw [endpoint_as_small_exp hκ hs hN n]
    exact (exp_small_diagonal (basis hκ (eps_pos hN) hN) _
      (endpointError_diagonal hκ hs hN n) ((endpointError_bound hκ hs hN n).trans hsm.le)).trans
      (mul_le_mul_of_nonneg_left (endpointError_bound hκ hs hN n) (by norm_num))
  · simpa using ht.const_mul 2

end QuantumNLS.IndexedQuantumEndpointR30b
#print axioms QuantumNLS.IndexedQuantumEndpointR30b.endpoint_norm_tendsto_zero
