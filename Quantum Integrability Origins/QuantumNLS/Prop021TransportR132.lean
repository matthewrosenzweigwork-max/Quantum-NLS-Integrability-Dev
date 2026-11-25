import QuantumNLS.Prop021MarginalTransportR132
import QuantumNLS.Prop021ManyBodyR129
import QuantumNLS.Prop022GClassical
import QuantumNLS.HighAngleLinearEvolution
import QuantumNLS.Prop021AssemblyR131
import QuantumNLS.Prop022AExact
import QuantumNLS.Prop021RemainderInputR131
import QuantumNLS.Prop022AIsoTensor

/-! The source many-body Hamiltonian on any Hilbert space, with exact
sectorwise equivariance and restriction to the second-quantized image. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Prop021ManyBodyTransportR132
open TensorCarrier TensorPlacements IntrinsicContact KernelDefinition
open Prop022GTensor Prop022AIsoTensor Prop022GClassical Prop021MarginalTransportR132
open LinearTailPhysicalEvolution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The positive-rank series of the paper, with both particle numbers kept distinct. -/
def sector (K : Kernels E) (N n : ℕ) : SymSector ℂ E n →L[ℂ] SymSector ℂ E n :=
  (N : ℂ) • ∑ i : Fin n,
    (((N : ℝ)⁻¹ ^ (i.val+1) * (n.descFactorial (i.val+1) : ℝ) : ℝ) : ℂ) •
      genericU_N_r n (i.val+1) (Nat.succ_le_of_lt i.isLt) (K i.val)

theorem sector_adjoint (K : Kernels E) (hK : KSelfAdj K) (N n : ℕ) :
    (sector K N n).adjoint = sector K N n := by
  change ∀ r, (K r).adjoint = K r at hK
  simp only [sector, map_smulₛₗ, map_sum, Complex.conj_natCast, Complex.conj_ofReal,
    GenericUAdjoint.adjoint_genericU_N_r, hK]

/-- The maximal direct-sum domain in the source Hamiltonian. -/
def HamiltonianDomain (K : Kernels E) (N : ℕ) (x : FockSpace E) : Prop :=
  Memℓp (fun n => sector K N n (x n)) 2

/-- On its maximal domain, the Hamiltonian acts by the bounded sector operators. -/
def hamiltonian (K : Kernels E) (N : ℕ) (x : FockSpace E) (hx : HamiltonianDomain K N x) :
    FockSpace E := ⟨fun n => sector K N n (x n), hx⟩

/-- The spectral exponential on each homogeneous sector. -/
def sectorEvolution (K : Kernels E) (N n : ℕ) (t : ℝ) :=
  evolution (sector K N n) t

/-- The unitary direct-sum orbit expressed in particle coordinates. -/
def manyBodyEvolution (K : Kernels E) (hK : KSelfAdj K) (N : ℕ) (t : ℝ)
    (x : FockSpace E) : FockSpace E :=
  ⟨fun n => sectorEvolution K N n t (x n), by
    apply Memℓp.of_norm
    have h (n : ℕ) : ‖sectorEvolution K N n t (x n)‖ = ‖x n‖ :=
      evolution_norm (show IsSelfAdjoint (sector K N n) from sector_adjoint K hK N n) t (x n)
    simpa only [h] using (lp.memℓp x).norm⟩

/-- Extend each interaction kernel by zero, preserving the self-adjointness hypothesis. -/
def extendKernels (J : E →ₗᵢ[ℂ] F) (K : Kernels E) : Kernels F :=
  fun r => extend (symMapI J (r+1)) (K r)

theorem extendKernels_selfAdj (J : E →ₗᵢ[ℂ] F) (K : Kernels E) (hK : KSelfAdj K) :
    KSelfAdj (extendKernels J K) :=
  fun n => by rw [extendKernels, extend_adjoint, hK n]

omit [CompleteSpace E] [CompleteSpace F] in
private theorem symProj_tensorMapI (J : E →ₗᵢ[ℂ] F) (n : ℕ)
    (x : HilbertTensorPower ℂ E n) :
    tensorMapI J n (symProj ℂ E n x) = symProj ℂ F n (tensorMapI J n x) := by
  rw [symProj_eq_factorial_average, symProj_eq_factorial_average]
  simp only [smul_apply, sum_apply, map_smul, map_sum, permRep_apply]
  congr 1
  exact Finset.sum_congr rfl fun σ _ => (tensorMapI_perm J σ x).symm

private theorem extendSymKernel_tensorMapI (J : E →ₗᵢ[ℂ] F) (r : ℕ)
    (A : SymSector ℂ E r →L[ℂ] SymSector ℂ E r) (x : HilbertTensorPower ℂ E r) :
    tensorMapI J r (extendSymKernel A x) =
      extendSymKernel (extend (symMapI J r) A) (tensorMapI J r x) := by
  have h : symMapI J r (symProjToSector r x) = symProjToSector r (tensorMapI J r x) :=
    Subtype.ext (symProj_tensorMapI J r x)
  change ((symMapI J r (A (symProjToSector r x)) : SymSector ℂ F r) : HilbertTensorPower ℂ F r) =
    ((extend (symMapI J r) A (symProjToSector r (tensorMapI J r x)) : SymSector ℂ F r) :
      HilbertTensorPower ℂ F r)
  rw [← h, extend_apply_image]

private theorem firstPlacement_tensorMapI (J : E →ₗᵢ[ℂ] F) (r q : ℕ)
    (A : SymSector ℂ E r →L[ℂ] SymSector ℂ E r) (x : HilbertTensorPower ℂ E (r+q)) :
    tensorMapI J (r+q) (firstPlacement (q := q) A x) =
      firstPlacement (q := q) (extend (symMapI J r) A) (tensorMapI J (r+q) x) := by
  apply (splitIsometry r q).injective
  change splitIsometry r q (tensorMapI J (r+q)
      ((splitIsometry r q).symm (htmap (extendSymKernel A) (ContinuousLinearMap.id ℂ _)
        (splitIsometry r q x)))) =
    splitIsometry r q ((splitIsometry r q).symm
      (htmap (extendSymKernel (extend (symMapI J r) A)) (ContinuousLinearMap.id ℂ _)
        (splitIsometry r q (tensorMapI J (r+q) x))))
  rw [split_tensorMapI, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply,
    split_tensorMapI]
  have h : tensorCLM J r ∘L extendSymKernel A =
      extendSymKernel (extend (symMapI J r) A) ∘L tensorCLM J r := by
    ext y
    exact extendSymKernel_tensorMapI J r A y
  have h₁ := htmap_comp (tensorCLM J r) (extendSymKernel A) (tensorCLM J q)
    (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E q))
  have h₂ := htmap_comp (extendSymKernel (extend (symMapI J r) A)) (tensorCLM J r)
    (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ F q)) (tensorCLM J q)
  rw [ContinuousLinearMap.comp_id, h] at h₁
  rw [ContinuousLinearMap.id_comp] at h₂
  exact DFunLike.congr_fun (h₁.symm.trans h₂) (splitIsometry r q x)

private theorem placement_tensorMapI (J : E →ₗᵢ[ℂ] F) (r q : ℕ)
    (A : SymSector ℂ E r →L[ℂ] SymSector ℂ E r) (x : SymSector ℂ E (r+q)) :
    symMapI J (r+q) (U_N_r (q := q) A x) =
      U_N_r (q := q) (extend (symMapI J r) A) (symMapI J (r+q) x) := by
  rw [U_N_r_eq_Q_N_p, U_N_r_eq_Q_N_p]
  apply Subtype.ext
  change tensorMapI J (r+q) (symmetrizedPlacement A x.val) =
    symmetrizedPlacement (extend (symMapI J r) A) (tensorMapI J (r+q) x.val)
  unfold symmetrizedPlacement
  simp only [smul_apply, sum_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  unfold permutedPlacement
  simp only [ContinuousLinearMap.comp_apply, permRep_apply]
  rw [← tensorMapI_perm, firstPlacement_tensorMapI, ← tensorMapI_perm]

private theorem cast_placement_tensorMapI (J : E →ₗᵢ[ℂ] F) (r q : ℕ) {n : ℕ}
    (h : r+q = n) (A : SymSector ℂ E r →L[ℂ] SymSector ℂ E r) (x : SymSector ℂ E n) :
    symMapI J n (castSymSectorOperator h (U_N_r (q := q) A) x) =
      castSymSectorOperator h (U_N_r (q := q) (extend (symMapI J r) A)) (symMapI J n x) := by
  subst n
  exact placement_tensorMapI J r q A x

theorem sector_transport (J : E →ₗᵢ[ℂ] F) (K : Kernels E) (N n : ℕ)
    (x : SymSector ℂ E n) :
    symMapI J n (sector K N n x) = sector (extendKernels J K) N n (symMapI J n x) := by
  unfold sector
  simp only [smul_apply, sum_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  unfold genericU_N_r
  exact cast_placement_tensorMapI J (i.val+1) (n-(i.val+1)) _ (K i.val) x

/-- Transport of the full graph domain, with both directions coming from the same sector norms. -/
theorem hamiltonian_domain_transport (J : E →ₗᵢ[ℂ] F) (K : Kernels E) (N : ℕ)
    (x : FockSpace E) :
    HamiltonianDomain (extendKernels J K) N (fockMapI J x) ↔ HamiltonianDomain K N x := by
  unfold HamiltonianDomain
  rw [← memℓp_norm_iff (f := fun n => sector (extendKernels J K) N n (fockMapI J x n)),
    ← memℓp_norm_iff (f := fun n => sector K N n (x n))]
  simp only [fockMapI_apply, ← sector_transport, LinearIsometry.norm_map]

theorem hamiltonian_transport (J : E →ₗᵢ[ℂ] F) (K : Kernels E) (N : ℕ)
    (x : FockSpace E) (hx : HamiltonianDomain K N x) :
    hamiltonian (extendKernels J K) N (fockMapI J x) ((hamiltonian_domain_transport J K N x).mpr hx) =
      fockMapI J (hamiltonian K N x hx) := by
  apply lp.ext
  funext n
  exact (sector_transport J K N n (x n)).symm

theorem sectorEvolution_transport (J : E →ₗᵢ[ℂ] F) (K : Kernels E) (N n : ℕ) (t : ℝ)
    (x : SymSector ℂ E n) :
    sectorEvolution (extendKernels J K) N n t (symMapI J n x) =
      symMapI J n (sectorEvolution K N n t x) := by
  symm
  unfold sectorEvolution evolution
  apply HighAngleLinearEvolution.intertwine_exp (symMapI J n).toContinuousLinearMap
  intro v
  simp only [smul_apply, LinearIsometry.coe_toContinuousLinearMap,
    map_smul, sector_transport]

theorem manyBodyEvolution_transport (J : E →ₗᵢ[ℂ] F) (K : Kernels E) (hK : KSelfAdj K)
    (N : ℕ) (t : ℝ) (x : FockSpace E) :
    manyBodyEvolution (extendKernels J K) (extendKernels_selfAdj J K hK) N t (fockMapI J x) =
      fockMapI J (manyBodyEvolution K hK N t x) := by
  apply lp.ext
  funext n
  exact sectorEvolution_transport J K N n t (x n)

/-- The embedded Fock space is invariant for every signed time, with exact compression. -/
theorem manyBodyEvolution_compression (J : E →ₗᵢ[ℂ] F) (K : Kernels E) (hK : KSelfAdj K)
    (N : ℕ) (t : ℝ) (x : FockSpace E) :
    (fockMapI J).toContinuousLinearMap.adjoint
      (manyBodyEvolution (extendKernels J K) (extendKernels_selfAdj J K hK) N t (fockMapI J x)) =
      manyBodyEvolution K hK N t x := by
  rw [manyBodyEvolution_transport J K hK]
  exact DFunLike.congr_fun (fockMapI J).adjoint_comp_self _

open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors Prop022PositiveDataR126

theorem sector_torus {L : ℝ} [Fact (0 < L)] (K : Kernels (L2T L)) (N n : ℕ) :
    sector K N n = Prop021ManyBodyR129.sector (positiveExtension K) N n := rfl

theorem manyBodyEvolution_torus {L : ℝ} [Fact (0 < L)] (K : Kernels (L2T L)) (hK : KSelfAdj K)
    (N : ℕ) (t : ℝ) (x : Fock L) :
    manyBodyEvolution K hK N t x =
      Prop021ManyBodyR129.manyBodyEvolution (positiveExtension K)
        (positiveExtension_selfAdjoint K hK) N t x := rfl

end QuantumNLS.Prop021ManyBodyTransportR132

#print axioms QuantumNLS.Prop021ManyBodyTransportR132.manyBodyEvolution_compression
#print axioms QuantumNLS.Prop021ManyBodyTransportR132.manyBodyEvolution_torus

end

/-! Printed PROP-021 estimates on a general symmetric Fock space. The data
are the classical trajectory and its variational derivative, the Weyl
operators, the vacuum and the pure-quasifree predicate of that carrier. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 150000
open scoped InnerProductSpace ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop021StatementR132
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors TraceClass
open Prop022GTensor Prop022GClassical Prop022AIsoTensor Prop022AFock Prop022OVacuum
open Prop021ManyBodyTransportR132 Prop021MarginalTransportR132
open Prop022ActualProfileR117 Prop022ClassicalFlowR126 Prop022PositiveDataR126
open Prop025OInputs Ext006NumberPhase Ext006PhysQuasifree Ext006PhysFockCoord

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

/-- The coherent approximation and the depletion bound for the same witnesses. -/
def CoherentWitness (K : Kernels H) (hs : KSelfAdj K) (u₀ : H) (u : ℝ → H)
    (W : H → FockSpace H → FockSpace H) (Ω : FockSpace H) (QF : FockSpace H → Prop)
    (A T M P CAT : ℝ) (N : ℕ) (θ : ℝ → ℝ) (ξ : ℝ → FockSpace H) : Prop :=
  ξ 0 = Ω ∧
  (∀ t, |t| ≤ T → ‖ξ t‖ = 1 ∧ QF (ξ t)) ∧
  (∀ t, |t| ≤ T →
    ‖manyBodyEvolution K hs N t (W ((Real.sqrt N : ℂ) • u₀) Ω) -
      Complex.exp (-(Complex.I * (θ t : ℂ))) • W ((Real.sqrt N : ℂ) • u t) (ξ t)‖ ≤
      CAT * M * (N : ℝ)^(-(1/2 : ℝ)) * Qpar A T M P ^ ((3 : ℝ)/2)) ∧
  (∀ t, |t| ≤ T → numExpH (ξ t) ≤ ENNReal.ofReal (Qpar A T M P - 1))

/-- All three printed estimates, including the error for a normalized preparation. -/
def Bounds (K : Kernels H) (hs : KSelfAdj K) (u₀ : H) (u : ℝ → H)
    (W : H → FockSpace H → FockSpace H) (Ω : FockSpace H) (QF : FockSpace H → Prop)
    (A T M P CAT : ℝ) (N : ℕ) : Prop :=
  (∃ (θ : ℝ → ℝ) (ξ : ℝ → FockSpace H),
    CoherentWitness K hs u₀ u W Ω QF A T M P CAT N θ ξ) ∧
  (∀ k : ℕ, 1 ≤ k → ∀ hk : k ≤ N, ∀ t, |t| ≤ T →
    traceNorm (reducedDensityN N k hk (sectorEvolution K N N t (powerH N u₀)).val -
      InnerProductSpace.rankOne ℂ (htpow k (u t)) (htpow k (u t))) ≤
    ENNReal.ofReal (CAT * Real.sqrt k * (N : ℝ)^(-(1/4 : ℝ)) *
      (M * Qpar A T M P ^ ((3 : ℝ)/2) + Real.sqrt (Qpar A T M P)))) ∧
  (∀ k : ℕ, 1 ≤ k → ∀ hk : k ≤ N, ∀ ψ : SymSector ℂ H N, ‖ψ‖ = 1 → ∀ t, |t| ≤ T →
    traceNorm (reducedDensityN N k hk (sectorEvolution K N N t ψ).val -
      InnerProductSpace.rankOne ℂ (htpow k (u t)) (htpow k (u t))) ≤
    ENNReal.ofReal (CAT * Real.sqrt k * (N : ℝ)^(-(1/4 : ℝ)) *
      (M * Qpar A T M P ^ ((3 : ℝ)/2) + Real.sqrt (Qpar A T M P)) +
      2 * ‖ψ - powerH N u₀‖))

/-- The frozen physical statement with its two constants fixed. -/
def TorusAtConstants (A : ℝ) (hA : 0 < A) (cA T CAT : ℝ) : Prop :=
  ∀ (K : Kernels (L2T L)) (M : ℝ), 1 ≤ M →
  ∀ (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : Prop001.Sphere (L2T L)) (P : ℝ), 1 ≤ P →
  (∀ s t : ℝ, |s| ≤ T → |t| ≤ T →
    ‖fderiv ℝ (classicalFlow (positiveExtension K) M A hA.le (positiveExtension_bound K M A hK)
      (positiveExtension_selfAdjoint K hs) (t - s))
      (profile (positiveExtension K) M A hA.le (positiveExtension_bound K M A hK)
        (positiveExtension_selfAdjoint K hs) u₀ s)‖ ≤ P) →
  ∀ N : ℕ, 1 ≤ N → cA * Qpar A T M P ≤ N →
  Bounds K hs (u₀ : L2T L)
    (profile (positiveExtension K) M A hA.le (positiveExtension_bound K M A hK)
      (positiveExtension_selfAdjoint K hs) u₀)
    (fun v x => printedWeyl v x) vac PhysicalQuasifreeSource A T M P CAT N

/-- Specialization to the physical carrier gives the exact frozen PROP-025 input. -/
theorem torus_statement :
    (∀ A : ℝ, ∀ hA : 0 < A, ∃ cA : ℝ, ∀ T : ℝ, 0 < T → ∃ CAT : ℝ,
      TorusAtConstants (L := L) A hA cA T CAT) ↔ Prop025OInputs.Prop021Input (L := L) := Iff.rfl

omit [CompleteSpace H] in
theorem numExp_transport (J : H →ₗᵢ[ℂ] L2T L) (x : FockSpace H) :
    numberExpectation (fun n => (n : ℝ≥0∞)) (fockMapI J x) = numExpH x := by
  unfold numberExpectation numExpH
  simp only [fockMapI_apply, LinearIsometry.norm_map]

omit [CompleteSpace H] in
theorem power_transport (J : H →ₗᵢ[ℂ] L2T L) (n : ℕ) (x : H) :
    symMapI J n (powerH n x) = powerH n (J x) :=
  Subtype.ext (tensorMapI_htpow J n x)

/-- The pure-state marginal and the prepared-state marginal compress along the
same isometry. In particular the preparation error keeps its exact norm. -/
theorem marginal_transport (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H)
    (N k : ℕ) (hk : k ≤ N) (t : ℝ) (ψ : SymSector ℂ H N) (u : H) :
    traceNorm (reducedDensityN N k hk
        (sectorEvolution (extendKernels J K) N N t (symMapI J N ψ)).val -
      InnerProductSpace.rankOne ℂ (htpow k (J u)) (htpow k (J u))) =
    traceNorm (reducedDensityN N k hk (sectorEvolution K N N t ψ).val -
      InnerProductSpace.rankOne ℂ (htpow k u) (htpow k u)) := by
  rw [sectorEvolution_transport]
  exact marginal_distance_tensorMapI J N k hk _ u

/-- The optional minimum with two is valid for every unit product and
every normalized state in the printed reduced-density estimate. -/
theorem marginal_cap (N k : ℕ) (hk : k ≤ N) (u : H) (hu : ‖u‖ = 1)
    (x : HilbertTensorPower ℂ H N) (hx : ‖x‖ = 1) :
    traceNorm (reducedDensityN N k hk x -
      InnerProductSpace.rankOne ℂ (htpow k u) (htpow k u)) ≤ 2 := by
  have hprod : reducedDensityN N k hk (htpow N u : HilbertTensorPower ℂ H N) =
      InnerProductSpace.rankOne ℂ (htpow k u) (htpow k u) := by
    rw [reducedDensityN, castHTP_htpow, reducedDensityPower_htpow, hu]
    simp
  rw [← hprod, sub_eq_add_neg]
  refine (traceNorm_add_le _ _).trans ?_
  rw [← neg_one_smul ℂ, traceNorm_smul]
  norm_num [traceNorm_reducedDensityN, hx, norm_htpow, hu]

end QuantumNLS.Prop021StatementR132

#print axioms QuantumNLS.Prop021StatementR132.torus_statement
#print axioms QuantumNLS.Prop021StatementR132.marginal_transport
#print axioms QuantumNLS.Prop021StatementR132.marginal_cap

end

/-! The infinite-dimensional reduction uses the already frozen realization
of the classical and Fock objects on an arbitrary complex Hilbert space. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 160000
open scoped InnerProductSpace ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop021UnitaryR132
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022AIsoTensor Prop022GClassical Prop022GLinear Prop022GHilbert Prop022AFock
open Prop022ActualProfileR117 Prop022ClassicalFlowR126 Prop022PositiveDataR126 Prop022FlowDifferentialR126
open Prop022OVacuum Ext006PhysQuasifree Ext006PhysFockCoord Prop025OInputs
open Prop021ManyBodyTransportR132 Prop021MarginalTransportR132 Prop021StatementR132

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

/-- The identity chart on the physical carrier. -/
abbrev torusId (L : ℝ) [Fact (0 < L)] := LinearIsometryEquiv.refl ℂ (L2T L)

theorem symMap_refl (n : ℕ) (x : HN L n) : symMap (torusId L) n x = x := by
  apply Subtype.ext
  change tensorMap (torusId L) n x.val = x.val
  have hid : (torusId L).trans (torusId L) = torusId L := by ext y; rfl
  have h := tensorMap_trans (torusId L) (torusId L) n x.val
  rw [hid] at h
  exact (tensorMap (torusId L) n).injective h.symm

theorem kernelsL_refl (K : Kernels (L2T L)) : kernelsL (torusId L) K = K := by
  funext n
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨x,rfl⟩ := (symMap (torusId L) (n+1)).surjective y
  change conjSym (torusId L) (n+1) (K n) (symMap (torusId L) (n+1) x) =
    K n (symMap (torusId L) (n+1) x)
  rw [conjSym_apply, LinearIsometryEquiv.symm_apply_apply, symMap_refl, symMap_refl]

theorem gam_refl (x : Fock L) : gam (torusId L) x = x := by
  apply lp.ext
  funext n
  exact symMap_refl n (x n)

/-- This expression exhibits the dimension-independent order of quantifiers. -/
def AtConstants (U : H ≃ₗᵢ[ℂ] L2T L) (A : ℝ) (hA : 0 < A) (cA T CAT : ℝ) : Prop :=
  ∀ (K : Kernels H) (M : ℝ), 1 ≤ M →
  ∀ (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) (P : ℝ), 1 ≤ P →
    (∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ‖SH U K M A hA.le hK hs u₀ hu₀ t s‖ ≤ P) →
  ∀ N : ℕ, 1 ≤ N → cA * Qpar A T M P ≤ N →
    Bounds K hs u₀ (profH U K M A hA.le hK hs u₀ hu₀)
      (fun v x => WH U v x) (vacH U) (QFH U) A T M P CAT N

omit [CompleteSpace H] in
lemma symMapI_unitary (U : H ≃ₗᵢ[ℂ] L2T L) (n : ℕ) (x : SymSector ℂ H n) :
    symMapI U.toLinearIsometry n x = symMap U n x :=
  Subtype.ext (tensorMapI_equiv U n x.val)

theorem extendKernels_unitary (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) :
    extendKernels U.toLinearIsometry K = kernelsL U K := by
  funext n
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (symMap U (n+1)).surjective y
  change extend (symMapI U.toLinearIsometry (n+1)) (K n) (symMap U (n+1) x) =
    conjSym U (n+1) (K n) (symMap U (n+1) x)
  calc
    _ = symMapI U.toLinearIsometry (n+1) (K n x) := by
      rw [← symMapI_unitary U (n+1) x, extend_apply_image]
    _ = symMap U (n+1) (K n x) := symMapI_unitary U (n+1) _
    _ = _ := by rw [conjSym_apply, LinearIsometryEquiv.symm_apply_apply]

private theorem variational_norm (U : H ≃ₗᵢ[ℂ] L2T L)
    (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A) (hK : KBound K M A) (hs : KSelfAdj K)
    (u₀ : H) (hu₀ : ‖u₀‖ = 1) (s t P : ℝ) (hP : 0 ≤ P)
    (hS : ‖SH U K M A hA hK hs u₀ hu₀ t s‖ ≤ P) :
    ‖fderiv ℝ (classicalFlow (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs)
        (t-s)) (profile (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs)
          (sphL U u₀ hu₀) s)‖ ≤ P := by
  rw [← flow_eq_fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ hP fun y => ?_
  obtain ⟨x, rfl⟩ := U.surjective y
  rw [U.norm_map]
  have h := ContinuousLinearMap.le_opNorm (SH U K M A hA hK hs u₀ hu₀ t s) x
  rw [SH_apply, U.symm.norm_map] at h
  exact h.trans (mul_le_mul_of_nonneg_right hS (norm_nonneg x))

/-- A single torus proof supplies the same constants on every separable infinite-dimensional
carrier. The unitary only transports the proof and all three physical estimates. -/
theorem transfer_at_constants (U : H ≃ₗᵢ[ℂ] L2T L)
    (A : ℝ) (hA : 0 < A) (cA T CAT : ℝ)
    (hTorus : TorusAtConstants (L := L) A hA cA T CAT) :
    AtConstants U A hA cA T CAT := by
  intro K M hM hK hs u₀ hu₀ P hP hS N hN hNQ
  let B := kernelsL U K
  have hB : KBound B M A := fun i =>
    (norm_conjSym_le U (i+1) (K i)).trans (hK i)
  have hsB : KSelfAdj B := fun i => conjSym_adjoint U (i+1) (K i) (hs i)
  have hSL s t hst htt :=
    variational_norm U K M A hA.le hK hs u₀ hu₀ s t P (zero_le_one.trans hP) (hS s t hst htt)
  let u := profH U K M A hA.le hK hs u₀ hu₀
  let uL := profile (positiveExtension B) M A hA.le (positiveExtension_bound B M A hB)
    (positiveExtension_selfAdjoint B hsB) (sphL U u₀ hu₀)
  have hu (t : ℝ) : U (u t) = uL t :=
    U_profH U K M A hA.le hK hs u₀ hu₀ t
  obtain ⟨⟨θ,z,hz0,hzn,herr,hdep⟩,hmarg,hprep⟩ :=
    hTorus B M hM hB hsB (sphL U u₀ hu₀) P hP hSL N hN hNQ
  let Γ := gam U
  let ξ := fun t => Γ.symm (z t)
  have hΓ (x : FockSpace H) : fockMapI U.toLinearIsometry x = Γ x :=
    fockMapI_equiv U x
  have hz (t : ℝ) : Γ (ξ t) = z t := Γ.apply_symm_apply _
  have hE (t : ℝ) (x : FockSpace H) :
      Γ (manyBodyEvolution K hs N t x) = manyBodyEvolution B hsB N t (Γ x) := by
    apply lp.ext
    funext n
    have h := (sectorEvolution_transport U.toLinearIsometry K N n t (x n)).symm
    rw [extendKernels_unitary] at h
    exact (by simpa only [symMapI_unitary] using h :
      symMap U n (sectorEvolution K N n t (x n)) = sectorEvolution B N n t (symMap U n (x n)))
  have hW (v : H) (x : FockSpace H) : Γ (WH U v x) = printedWeyl (U v) (Γ x) :=
    Γ.apply_symm_apply _
  have hΩ : Γ (vacH U) = (vac : Fock L) := Γ.apply_symm_apply _
  refine ⟨⟨θ,ξ,?_,?_,?_,?_⟩,?_,?_⟩
  · exact congrArg Γ.symm hz0
  · intro t ht
    have h := hzn t ht
    exact ⟨by rw [← Γ.norm_map (ξ t), hz]; exact h.1, by change PhysicalQuasifreeSource (Γ (ξ t)); rw [hz]; exact h.2⟩
  · intro t ht
    rw [← Γ.norm_map, map_sub, map_smul, hE, hW, hW, hΩ, hz, map_smul U, map_smul U, hu]
    exact herr t ht
  · intro t ht
    rw [← numExp_transport U.toLinearIsometry, hΓ, hz]
    exact hdep t ht
  · intro k hk0 hk t ht
    have h := marginal_transport U.toLinearIsometry K N k hk t (powerH N u₀) (u t)
    rw [extendKernels_unitary, power_transport, LinearIsometryEquiv.coe_toLinearIsometry, hu] at h
    rw [← h]
    exact hmarg k hk0 hk t ht
  · intro k hk0 hk ψ hψ t ht
    have h := marginal_transport U.toLinearIsometry K N k hk t ψ (u t)
    rw [extendKernels_unitary, LinearIsometryEquiv.coe_toLinearIsometry, hu] at h
    rw [← h]
    have hp := hprep k hk0 hk (symMapI U.toLinearIsometry N ψ)
      (by rw [LinearIsometry.norm_map, hψ]) t ht
    have hnorm : ‖symMapI U.toLinearIsometry N ψ - powerH N (U u₀)‖ =
        ‖ψ - powerH N u₀‖ := by
      have hpow := power_transport U.toLinearIsometry N u₀
      rw [LinearIsometryEquiv.coe_toLinearIsometry] at hpow
      rw [← hpow, ← map_sub, LinearIsometry.norm_map]
    have hsp : (sphL U u₀ hu₀ : L2T L) = U u₀ := rfl
    rw [hsp, hnorm] at hp
    exact hp

/-- The identity unitary gives the same fixed-constant statement as the torus proof. -/
theorem torus_refl (A : ℝ) (hA : 0 < A) (cA T CAT : ℝ) :
    AtConstants (torusId L) A hA cA T CAT ↔ TorusAtConstants (L := L) A hA cA T CAT := by
  refine ⟨?_, transfer_at_constants (torusId L) A hA cA T CAT⟩
  intro h K M hM hK hs u₀ P hP hS N hN hNQ
  let U := torusId L
  let B := kernelsL U K
  have hB : KBound B M A := fun i =>
    (norm_conjSym_le U (i+1) (K i)).trans (hK i)
  have hsB : KSelfAdj B := fun i => conjSym_adjoint U (i+1) (K i) (hs i)
  have hU : sphL U u₀.val u₀.property = u₀ := Subtype.ext rfl
  have hProfile (B' : Kernels (L2T L)) (hb : KBound B' M A) (hsb : KSelfAdj B')
      (eB : B' = K) (v : Prop001.Sphere (L2T L)) (ev : v = u₀) :
      profile (positiveExtension B') M A hA.le (positiveExtension_bound B' M A (fun i => hb i))
        (positiveExtension_selfAdjoint B' (fun i => hsb i)) v =
      profile (positiveExtension K) M A hA.le (positiveExtension_bound K M A (fun i => hK i))
        (positiveExtension_selfAdjoint K (fun i => hs i)) u₀ := by
    subst B'
    subst v
    rfl
  have hu : profH (torusId L) K M A hA.le hK hs u₀.val u₀.property =
      profile (positiveExtension K) M A hA.le (positiveExtension_bound K M A (fun i => hK i))
        (positiveExtension_selfAdjoint K (fun i => hs i)) u₀ :=
    hProfile B hB hsB (kernelsL_refl K) _ hU
  have hFlow (B' : Kernels (L2T L)) (hb : KBound B' M A) (hsb : KSelfAdj B')
      (eB : B' = K) (s : ℝ) :
      classicalFlow (positiveExtension B') M A hA.le (positiveExtension_bound B' M A (fun i => hb i))
        (positiveExtension_selfAdjoint B' (fun i => hsb i)) s =
      classicalFlow (positiveExtension K) M A hA.le (positiveExtension_bound K M A (fun i => hK i))
        (positiveExtension_selfAdjoint K (fun i => hs i)) s := by
    subst B'
    rfl
  have hΦ (s : ℝ) : flowH (torusId L) K M A hA.le hK hs s =
      classicalFlow (positiveExtension K) M A hA.le (positiveExtension_bound K M A (fun i => hK i))
        (positiveExtension_selfAdjoint K (fun i => hs i)) s :=
    hFlow B hB hsB (kernelsL_refl K) s
  have hSH (s t : ℝ) (hsT : |s| ≤ T) (htT : |t| ≤ T) :
      ‖SH (torusId L) K M A hA.le hK hs u₀.val u₀.property t s‖ ≤ P := by
    rw [SH, hΦ, hu]
    exact hS s t hsT htT
  have hw : (fun (v : L2T L) (x : Fock L) => WH (torusId L) v x) =
      (fun (v : L2T L) (x : Fock L) => printedWeyl v x) := by
    funext v x
    have hi (y : Fock L) : (gam (torusId L)).symm y = y := by
      apply (gam (torusId L)).injective
      rw [LinearIsometryEquiv.apply_symm_apply, gam_refl]
    change (gam (torusId L)).symm (printedWeyl v (gam (torusId L) x)) = _
    rw [gam_refl, hi]
  have hvac : vacH (torusId L) = (vac : Fock L) := by
    apply (gam (torusId L)).injective
    exact ((gam (torusId L)).apply_symm_apply vac).trans (gam_refl vac).symm
  have hQF : QFH (torusId L) = (PhysicalQuasifreeSource (L := L)) := by
    funext x
    unfold QFH
    rw [gam_refl]
  have h' := h K M hM hK hs u₀.val u₀.property P hP hSH N hN hNQ
  rw [hu, hw, hvac, hQF] at h'
  exact h'

/-- Infinite-dimensional separability supplies a unitary; every choice
gives the same constants. -/
theorem infinite_transport [TopologicalSpace.SeparableSpace H] (hH : ¬FiniteDimensional ℂ H)
    (hTorus : Prop025OInputs.Prop021Input (L := L)) :
    Nonempty (H ≃ₗᵢ[ℂ] L2T L) ∧
    ∀ A : ℝ, ∀ hA : 0 < A, ∃ cA : ℝ, ∀ T : ℝ, 0 < T → ∃ CAT : ℝ,
      ∀ U : H ≃ₗᵢ[ℂ] L2T L, AtConstants U A hA cA T CAT := by
  refine ⟨exists_unitary_L2T L hH, ?_⟩
  obtain h := (torus_statement (L := L)).mpr hTorus
  intro A hA
  obtain ⟨cA,hc⟩ := h A hA
  refine ⟨cA,fun T hT => ?_⟩
  obtain ⟨CAT,hCAT⟩ := hc T hT
  exact ⟨CAT,fun U => transfer_at_constants U A hA cA T CAT hCAT⟩

/-- The intrinsic trajectory, derivative, displacement and vacuum are
exactly the same for any two choices of unitary. -/
theorem unitary_data_indep (U U' : H ≃ₗᵢ[ℂ] L2T L)
    (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A) (hK : KBound K M A) (hs : KSelfAdj K)
    (u₀ : H) (hu₀ : ‖u₀‖ = 1) :
    profH U' K M A hA hK hs u₀ hu₀ = profH U K M A hA hK hs u₀ hu₀ ∧
    (∀ t s, SH U' K M A hA hK hs u₀ hu₀ t s = SH U K M A hA hK hs u₀ hu₀ t s) ∧
    (∀ v, WH U' v = WH U v) ∧ vacH U' = vacH U :=
  ⟨(profH_indep U U' K M A hA hK hs u₀ hu₀).symm,
    fun t s => (SH_indep U U' K M A hA hK hs u₀ hu₀ t s).symm,
    Prop022AIndep.WH_indep U U', Prop022AIndep.vacH_indep U U'⟩

/-- The distinguished evolved vacuum also agrees exactly between the two
unitaries, even though PROP-021 only requires existence of a witness. -/
theorem unitary_vacuum_indep (U U' : H ≃ₗᵢ[ℂ] L2T L)
    (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A)
    (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) (t : ℝ) :
    VH U' K M A hA.le hK hs u₀ hu₀ (zero_le_one.trans hM) t 0 (vacH U') =
      VH U K M A hA.le hK hs u₀ hu₀ (zero_le_one.trans hM) t 0 (vacH U) := by
  rw [Prop022AIndep.vacH_indep U U',
    Prop022ACovIndep.VH_indep K M A hM hA hK hs u₀ hu₀ U U' t 0]

end QuantumNLS.Prop021UnitaryR132

#print axioms QuantumNLS.Prop021UnitaryR132.infinite_transport
#print axioms QuantumNLS.Prop021UnitaryR132.unitary_data_indep
#print axioms QuantumNLS.Prop021UnitaryR132.unitary_vacuum_indep
#print axioms QuantumNLS.Prop021UnitaryR132.torus_refl

end

/-! Keep the actual quadratic vacuum as the coherent witness. This permits
restriction of the vector itself to an invariant Fock subspace. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 150000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Prop021CoherentTransportR132
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022AIsoTensor Prop022GClassical Prop022AFock Ext006NumberPhase
open Prop022PositiveDataR126 Prop022ActualProfileR117 Prop022ClassicalFlowR126
open Prop022FlowDifferentialR126 Prop022OVacuum Ext006PhysQuasifree Ext006PhysFockCoord
open Prop021StatementR132 Prop021RemainderInputR131 Prop024WeylConventionR55
open Prop021ManyBodyTransportR132 Prop021QuadraticBindingR129 Prop025OInputs
open Prop021CoherentComparisonR131 Prop021RatesR128 Prop022FactorialMajorantR115

variable {L : ℝ} [Fact (0 < L)]

section Canonical

variable (K : Kernels (L2T L)) (A M : ℝ) (hA : 0 < A) (hM : 1 ≤ M)
  (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : Prop001.Sphere (L2T L))
local notation "B" => positiveExtension K
local notation "hB" => positiveExtension_bound K M A hK
local notation "hsB" => positiveExtension_selfAdjoint K hs
local notation "hM₀" => (zero_le_one.trans hM)
local notation "u" => profile B M A hA.le hB hsB u₀
local notation "ξ" => fluctuation B M A hM₀ hA.le hB hsB u₀

/-- The frozen coherent estimate with the explicit phase and the actual evolved vacuum. -/
theorem canonical_torus (T P : ℝ) (hT : 0 ≤ T) (hP : 1 ≤ P)
    (hPair : Prop022PairInput K M A hM hA hK hs u₀ T P hP)
    (hS : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T →
      ‖fderiv ℝ (classicalFlow B M A hA.le hB hsB (t-s)) (u s)‖ ≤ P)
    (C : ℝ) (hC : 0 ≤ C) (hRem : RemainderEstimate (L := L) A C)
    (N : ℕ) (hNQ : 256 * Real.exp 1 * A * Qpar A T M P ≤ N) :
    CoherentWitness K hs (u₀ : L2T L) u (fun v x => printedWeyl v x)
      vac PhysicalQuasifreeSource A T M P (T*C) N
      (Prop021PhaseR130.theta B M A hA.le hB hsB u₀ N) ξ := by
  have hη := fluctuation_initial_norm_smooth B M A hM₀ hA.le hB hsB u₀
  refine ⟨hη.1, ?_, ?_, ?_⟩
  · intro t _
    have h := Prop021QuadraticR130.quadratic_vacuum B M A hM₀ hA.le hB hsB u₀ t
    exact ⟨h.2.1, h.1⟩
  · intro t ht
    rw [manyBodyEvolution_torus, ← neg_mul Complex.I]
    exact coherent_bound K M A hM hA hK hs u₀ T P hP N hT hPair
      (fun t s ht hs => hS s t hs ht) C hC hRem hNQ t ht
  · intro t ht
    have hv := Prop021QuadraticR130.quadratic_vacuum B M A hM₀ hA.le hB hsB u₀ t
    change numberExpectation (fun n => (n : ℝ≥0∞)) (ξ t) ≤ _
    rw [← ENNReal.ofReal_toReal hv.2.2.2]
    apply ENNReal.ofReal_le_ofReal
    apply Prop021QuadraticR130.quadratic_depletion B M A hM₀ hA.le hB hsB u₀ T P hT hP _ t ht
    intro t s ht hs
    rw [flow_eq_fderiv]
    exact hS s t hs ht

end Canonical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Restrict a supported coherent witness. Every norm and number expectation
is preserved, including the choice of scalar phase. -/
theorem restrict_coherent (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (hs : KSelfAdj K)
    (u₀ : H) (u : ℝ → H) (W : H → FockSpace H → FockSpace H) (Ω : FockSpace H)
    (hW : ∀ v x, fockMapI J (W v x) = printedWeyl (J v) (fockMapI J x))
    (hΩ : fockMapI J Ω = vac)
    (A T M P CAT : ℝ) (N : ℕ) (θ : ℝ → ℝ) (ξ : ℝ → FockSpace H)
    (h : CoherentWitness (extendKernels J K) (extendKernels_selfAdj J K hs)
      (J u₀) (fun t => J (u t)) (fun v x => printedWeyl v x) vac PhysicalQuasifreeSource
      A T M P CAT N θ (fun t => fockMapI J (ξ t))) :
    CoherentWitness K hs u₀ u W Ω (fun x => PhysicalQuasifreeSource (fockMapI J x))
      A T M P CAT N θ ξ := by
  obtain ⟨hz0,hzn,herr,hdep⟩ := h
  refine ⟨(fockMapI J).injective (hz0.trans hΩ.symm), ?_, ?_, ?_⟩
  · intro t ht
    simpa only [LinearIsometry.norm_map] using hzn t ht
  · intro t ht
    rw [← (fockMapI J).norm_map, map_sub, map_smul, ← manyBodyEvolution_transport J K hs, hW, hW, hΩ,
      map_smul J, map_smul J]
    exact herr t ht
  · intro t ht
    rw [← numExp_transport J]
    exact hdep t ht

end QuantumNLS.Prop021CoherentTransportR132

#print axioms QuantumNLS.Prop021CoherentTransportR132.canonical_torus
#print axioms QuantumNLS.Prop021CoherentTransportR132.restrict_coherent

end

/-! The exact spectral moment class used in the printed Wick remainder,
defined directly on the Fock space of an arbitrary Hilbert space. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Prop021MomentsR132
open TensorCarrier Prop022GTensor Prop022AIsoTensor PhysicalTensor Ext025B3PhysicalSectors

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {L : ℝ} [Fact (0 < L)]

def weightedNumber (w : ℕ → ℝ≥0∞) (x : FockSpace H) : ℝ≥0∞ :=
  ∑' n, w n * ENNReal.ofReal (‖x n‖ ^ 2)

def rootSectors (j : ℕ) (x : FockSpace H) (n : ℕ) : SymSector ℂ H n :=
  (Real.rpow ((n : ℝ) + j) ((j : ℝ) / 2) : ℂ) • x n

/-- The printed two estimates, with the polynomial multiplier on its maximal domain. -/
def NumberMoments (Q : ℝ) (x : FockSpace H) : Prop :=
  weightedNumber (fun n => ENNReal.ofReal (Real.exp ((n : ℝ) / (16 * Q)))) x ≤
    ENNReal.ofReal (Real.exp (1/4 : ℝ)) ∧
  ∀ j : ℕ, 1 ≤ j → ∃ hx : Memℓp (rootSectors j x) 2,
    ‖(⟨rootSectors j x,hx⟩ : FockSpace H)‖ ≤ Real.rpow (32 * Q * j) ((j : ℝ) / 2)

theorem rootSectors_transport (J : H →ₗᵢ[ℂ] F) (j : ℕ) (x : FockSpace H) (n : ℕ) :
    rootSectors j (fockMapI J x) n = symMapI J n (rootSectors j x n) :=
  (map_smul (symMapI J n) _ _).symm

theorem root_domain_transport (J : H →ₗᵢ[ℂ] F) (j : ℕ) (x : FockSpace H) :
    Memℓp (rootSectors j (fockMapI J x)) 2 ↔ Memℓp (rootSectors j x) 2 := by
  rw [← memℓp_norm_iff (f := rootSectors j (fockMapI J x)),
    ← memℓp_norm_iff (f := rootSectors j x)]
  simp only [rootSectors_transport, LinearIsometry.norm_map]

theorem root_transport (J : H →ₗᵢ[ℂ] F) (j : ℕ) (x : FockSpace H)
    (hx : Memℓp (rootSectors j x) 2) :
    fockMapI J (⟨rootSectors j x,hx⟩ : FockSpace H) =
      (⟨rootSectors j (fockMapI J x),(root_domain_transport J j x).mpr hx⟩ : FockSpace F) := by
  apply lp.ext
  funext n
  exact (rootSectors_transport J j x n).symm

theorem numberMoments_transport (J : H →ₗᵢ[ℂ] F) (Q : ℝ) (x : FockSpace H) :
    NumberMoments Q (fockMapI J x) ↔ NumberMoments Q x := by
  have hExp (w : ℕ → ℝ≥0∞) : weightedNumber w (fockMapI J x) = weightedNumber w x := by
    simp only [weightedNumber, fockMapI_apply, LinearIsometry.norm_map]
  unfold NumberMoments
  rw [hExp]
  refine and_congr_right fun _ => ⟨?_,?_⟩
  · intro h j hj
    obtain ⟨hx,hbound⟩ := h j hj
    let hx' := (root_domain_transport J j x).mp hx
    refine ⟨hx',?_⟩
    rw [← (fockMapI J).norm_map, root_transport]
    exact hbound
  · intro h j hj
    obtain ⟨hx,hbound⟩ := h j hj
    refine ⟨(root_domain_transport J j x).mpr hx,?_⟩
    rw [← root_transport J j x hx, LinearIsometry.norm_map]
    exact hbound

/-- The torus specialization is the same two moment inequalities used in R131. -/
theorem numberMoments_torus (Q : ℝ) (x : Fock L) :
    NumberMoments Q x ↔ Prop021RemainderInputR131.NumberMoments Q x := Iff.rfl

end QuantumNLS.Prop021MomentsR132

#print axioms QuantumNLS.Prop021MomentsR132.numberMoments_transport
#print axioms QuantumNLS.Prop021MomentsR132.numberMoments_torus

end

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let modules := ["Prop021TransportR132", "Prop021ManyBodyTransportR132", "Prop021StatementR132",
    "Prop021UnitaryR132", "Prop021CoherentTransportR132", "Prop021MomentsR132"]
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if modules.any (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
        n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
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
  Lean.logInfo m!"R132 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
