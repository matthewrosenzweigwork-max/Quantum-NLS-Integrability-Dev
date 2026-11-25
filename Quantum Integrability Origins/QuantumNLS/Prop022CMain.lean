import Mathlib
import QuantumNLS.Prop022CIntrinsic

/-! PROP-022 route A, round 4, stage C9: **`PROP022_general_intrinsic`**.

The printed lemma Q7B:lem:pair on an arbitrary complex separable Hilbert space `H` with the INTRINSIC
`H`-level operators:

* Weyl operators `W(v) = exp(a*(v) - a(v))` with `a*`, `a` the creation/annihilation operators of `Fock(H)`
  (`Prop022CCanon.creF`, `annF`), characterized through Stone's theorem (`Prop022CWeyl.IsWeylOp`); the frozen
  transported `WH U v` / compressed `WJ J v` are shown to be these (`WH_isWeylOp`, `WJ_isWeylOp`) and the
  characterization is unique (`weylOp_unique`);
* quadratic Hamiltonian `dΓ(a) + ½(a*(b)+a(b))` as the sectorwise relation `QRel` (`QH_QRel`, `QJ_QRel`), with
  second-moment-domain invariance of the propagator;
* evolved vacuum pure quasifree in the Bogoliubov-implementer sense (`PureQuasifreeH`) with the printed
  number identity.

The old `type_of%` headline `Prop022BMain.PROP022_general` is kept as the first conjunct. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace Topology NNReal ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022CMain
open QuantumNLS.TensorCarrier QuantumNLS.Prop022GTensor QuantumNLS.Prop022AIsoTensor
open QuantumNLS.Prop022BIso QuantumNLS.Prop022CCanon QuantumNLS.Prop022BFock1
open QuantumNLS.Prop022CWeyl QuantumNLS.Prop022CQuad QuantumNLS.Prop022CQuadTorus
open QuantumNLS.Prop022CIntrinsic QuantumNLS.Prop022AFock
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GAntiHS Prop022GClassical Prop022GLinear Prop022BClass1 Prop022BClass2 Prop022BFock2
open Prop022BFock3 Prop022FactorialCoefficientsR115 Prop022PositiveDataR126
open Occupation Ext006IdentityCyclicR35a Ext006PhysFockCoord Prop022ACoherent Prop022AWeyl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

/-! ### Vacuum -/

lemma vac_sector (n : ℕ) (hn : n ≠ 0) : (vac (L := L)) n = 0 := by
  have hv : Phi (vac (L := L)) = Phi (lp.single 2 0 (ketVec (L := L) 0) : Fock L) := by
    have h1 : (Phi (L := L)) (vac (L := L)) = (ketD (0 : Occ)).1 := by
      unfold vac
      rw [physCore_ket, LinearIsometryEquiv.apply_symm_apply]
      rfl
    rw [h1, ket_eq_emb (L := L) 0]
    rfl
  have h := (Phi (L := L)).injective hv
  rw [h]
  exact lp.single_apply_ne 2 0 (ketVec (L := L) 0) hn

lemma isVacuum_vacH (U : H ≃ₗᵢ[ℂ] L2T L) : IsVacuum (vacH U) := by
  refine ⟨?_, fun n hn => ?_⟩
  · unfold vacH
    rw [LinearIsometryEquiv.norm_map]
    exact Ext006VacuumNumberR30a.vac_norm
  · have h := norm_gam_symm_sector U (vac (L := L)) n
    rw [vac_sector n hn, norm_zero] at h
    exact norm_eq_zero.mp h

lemma isVacuum_vacJ (J : H →ₗᵢ[ℂ] L2T L) : IsVacuum (vacJ J) := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [← (fockMapI J).norm_map, gam_vacJ J]
    exact Ext006VacuumNumberR30a.vac_norm
  · have h := congrArg (fun z : Fock L => z n) (gam_vacJ J)
    change symMapI J n ((vacJ J) n) = (vac (L := L)) n at h
    rw [vac_sector n hn] at h
    have h0 : symMapI J n ((vacJ J) n) = symMapI J n 0 := by rw [h, map_zero]
    exact (symMapI J n).injective h0

/-! ### Symplecticity of `S` -/

theorem SH_symplectic (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A)
    (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) (t s : ℝ) (x y : H) :
    (⟪SH U K M A hA hK hs u₀ hu₀ t s x, SH U K M A hA hK hs u₀ hu₀ t s y⟫_ℂ).im =
      (⟪x, y⟫_ℂ).im := by
  rw [SH_apply, SH_apply, LinearIsometryEquiv.inner_map_map]
  have h := Prop022SymplecticR123.flow_symplectic (BL U K) M A hA (BL_bound U K M A hK)
    (BL_selfAdj U K hs) (sphL U u₀ hu₀) t s (U x) (U y)
  rw [LinearIsometryEquiv.inner_map_map] at h
  exact h

theorem SJ_symplectic (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A)
    (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) (t s : ℝ) (x y : H) :
    (⟪SJ J K M A hA hK hs u₀ hu₀ t s x, SJ J K M A hA hK hs u₀ hu₀ t s y⟫_ℂ).im =
      (⟪x, y⟫_ℂ).im := by
  have e1 := S_embed J K M A hA hK hs u₀ hu₀ t s x
  have e2 := S_embed J K M A hA hK hs u₀ hu₀ t s y
  have h := SH_symplectic (UI L) (kernelsI J K) M A hA (hKJ J K M A hK) (hsJ J K hs) (J u₀)
    (hJu J u₀ hu₀) t s (J x) (J y)
  rw [e1, e2, LinearIsometry.inner_map_map, LinearIsometry.inner_map_map] at h
  exact h

/-! ### Second-moment-domain invariance -/

lemma prop_moments (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (L2T L))
    (s t : ℝ) (x : Fock L) (hx : ∀ j : ℕ, x ∈ Ext005Moments.momentDomain (L := L) j) (j : ℕ) :
    Prop022FockPropagatorR122.propagator B M A hM hA hB hs u₀ s t x ∈
      Ext005Moments.momentDomain (L := L) j := by
  have h1 := (Prop022SmoothDomainR126.smooth_iff_moments x).2 hx
  have h2 := (Prop022SmoothDomainR126.evolution_smooth_iff B M A hM hA hB hs u₀ s t x).2 h1
  exact (Prop022SmoothDomainR126.smooth_iff_moments _).1 h2 j

lemma mem_moment_iff (J : H →ₗᵢ[ℂ] L2T L) (j : ℕ) (y : FockSpace H) :
    fockMapI J y ∈ Ext005Moments.momentDomain (L := L) j ↔ y ∈ momentDomainH j := by
  rw [Ext005Moments.momentDomain_iff]
  change Summable (fun n : ℕ => Ext005Moments.momentWeight j n * ‖fockMapI J y n‖ ^ 2) ↔ _
  simp only [fockMapI_apply, LinearIsometry.norm_map]
  exact Iff.rfl

theorem VH_domain (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A)
    (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) (hM0 : 0 ≤ M)
    (s t : ℝ) (x : FockSpace H) (hx : ∀ j : ℕ, x ∈ momentDomainH j) (j : ℕ) :
    VH U K M A hA hK hs u₀ hu₀ hM0 t s x ∈ momentDomainH j := by
  rw [← gam_mem_momentDomain U j]
  have e : gam U (VH U K M A hA hK hs u₀ hu₀ hM0 t s x) =
      propL U K M A hA hK hs u₀ hu₀ hM0 s t (gam U x) := (gam U).apply_symm_apply _
  rw [e]
  exact prop_moments _ _ _ _ _ _ _ _ s t (gam U x)
    (fun j => (gam_mem_momentDomain U j x).2 (hx j)) j

theorem VJ_domain (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
    (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)
    (s t : ℝ) (x : FockSpace H) (hx : ∀ j : ℕ, x ∈ momentDomainH j) (j : ℕ) :
    VJ J K M A hM hA hK hs u₀ hu₀ t s x ∈ momentDomainH j := by
  rw [← mem_moment_iff J j]
  have e : fockMapI J (VJ J K M A hM hA hK hs u₀ hu₀ t s x) =
      Pr J K M A hM hA hK hs u₀ hu₀ s t (fockMapI J x) := gam_compress J _ _ x
  rw [e]
  exact prop_moments _ _ _ _ _ _ _ _ s t (fockMapI J x)
    (fun j => (mem_moment_iff J j x).2 (hx j)) j

/-! ### The intrinsic conclusions -/

theorem intrinsic_of_U [TopologicalSpace.SeparableSpace H] (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H)
    (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H)
    (hu₀ : ‖u₀‖ = 1) (T P : ℝ) (hP : 1 ≤ P) {ι : Type*} (e : HilbertBasis ι ℂ H) :
    let hM0 : 0 ≤ M := by linarith
    IntrinsicFock (VH U K M A hA.le hK hs u₀ hu₀ hM0)
      (aSym U K M A hA.le hK hs u₀ hu₀) (bSym U K M A hA.le hK hs u₀ hu₀)
      (SH U K M A hA.le hK hs u₀ hu₀) (vacH U)
      (fun t => antiHS e (betaH U K M A hA.le hK hs u₀ hu₀ t 0)) := by
  intro hM0
  have h := PROP022_fock_transport U K M A hM hA hK hs u₀ hu₀ T P hP e
  obtain ⟨-, -, -, hSchr, himpl, hvac⟩ := h
  exact intrinsicFock_of_data _ _ _ _ _ _ (WH U) (QH U) (WH_isWeylOp U)
    (fun a b y hy => QH_QRel U a b y hy)
    (fun s t x hx j => VH_domain U K M A hA.le hK hs u₀ hu₀ hM0 s t x hx j)
    (fun s t x hx => hSchr s t x hx) (fun s t v x => himpl s t v x) (isVacuum_vacH U)
    (fun t s x y => SH_symplectic U K M A hA.le hK hs u₀ hu₀ t s x y)
    (fun t => ⟨(hvac t).2.1, (hvac t).2.2⟩)

theorem intrinsic_of_J [TopologicalSpace.SeparableSpace H] (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H)
    (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H)
    (hu₀ : ‖u₀‖ = 1) (T P : ℝ) (hP : 1 ≤ P) {ι : Type*} (e : HilbertBasis ι ℂ H) :
    IntrinsicFock (VJ J K M A hM hA hK hs u₀ hu₀)
      (aSymJ J K M A hA hK hs u₀ hu₀) (bSymJ J K M A hA hK hs u₀ hu₀)
      (SJ J K M A hA.le hK hs u₀ hu₀) (vacJ J)
      (fun t => antiHS e (betaJ J K M A hA.le hK hs u₀ hu₀ t 0)) := by
  have h := PROP022_fock_J J K M A hM hA hK hs u₀ hu₀ e T P hP
  obtain ⟨-, -, -, hSchr, himpl, hvac⟩ := h
  exact intrinsicFock_of_data _ _ _ _ _ _ (WJ J) (QJ J) (WJ_isWeylOp J)
    (fun a b y hy => QJ_QRel J a b y hy)
    (fun s t x hx j => VJ_domain J K M A hM hA hK hs u₀ hu₀ s t x hx j)
    (fun s t x hx => hSchr s t x hx) (fun s t v x => himpl s t v x) (isVacuum_vacJ J)
    (fun t s x y => SJ_symplectic J K M A hA.le hK hs u₀ hu₀ t s x y)
    (fun t => ⟨(hvac t).2.1, (hvac t).2.2⟩)

/-- **PROP-022 (Q7B:lem:pair, fluctuations.tex:93) on an arbitrary complex separable Hilbert space with the
INTRINSIC H-level operators.**  First conjunct: the frozen `Prop022BMain.PROP022_general` statement.  Then,
for infinite-dimensional `H` and every unitary `U`, resp. finite-dimensional `H` and every isometry `J`:
the intrinsic conclusions (`IntrinsicFock`), the identification of the frozen Weyl operators with
`exp(a*(v) - a(v))` (and its uniqueness), and the sectorwise identification of the quadratic generator. -/
theorem PROP022_general_intrinsic [TopologicalSpace.SeparableSpace H] (L : ℝ) [Fact (0 < L)]
    (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A) (hs : KSelfAdj K)
    (u₀ : H) (hu₀ : ‖u₀‖ = 1) (T P : ℝ) (hP : 1 ≤ P) {ι : Type*} (e : HilbertBasis ι ℂ H) :
    type_of% (Prop022BMain.PROP022_general L K M A hM hA hK hs u₀ hu₀ T P hP e) ∧
    (¬ FiniteDimensional ℂ H → ∀ U : H ≃ₗᵢ[ℂ] L2T L,
      (let hM0 : 0 ≤ M := by linarith
       IntrinsicFock (VH U K M A hA.le hK hs u₀ hu₀ hM0)
        (aSym U K M A hA.le hK hs u₀ hu₀) (bSym U K M A hA.le hK hs u₀ hu₀)
        (SH U K M A hA.le hK hs u₀ hu₀) (vacH U)
        (fun t => antiHS e (betaH U K M A hA.le hK hs u₀ hu₀ t 0))) ∧
      (∀ v, IsWeylOp v (WH U v) ∧ ∀ W, IsWeylOp v W → W = WH U v) ∧
      (∀ a b y, y ∈ momentDomainH 2 → QRel a b y (QH U a b y))) ∧
    (FiniteDimensional ℂ H → ∀ J : H →ₗᵢ[ℂ] L2T L,
      IntrinsicFock (VJ J K M A hM hA hK hs u₀ hu₀)
        (aSymJ J K M A hA hK hs u₀ hu₀) (bSymJ J K M A hA hK hs u₀ hu₀)
        (SJ J K M A hA.le hK hs u₀ hu₀) (vacJ J)
        (fun t => antiHS e (betaJ J K M A hA.le hK hs u₀ hu₀ t 0)) ∧
      (∀ v, IsWeylOp v (WJ J v) ∧ ∀ W, IsWeylOp v W → W = WJ J v) ∧
      (∀ a b y, y ∈ momentDomainH 2 → QRel a b y (QJ J a b y))) := by
  refine ⟨Prop022BMain.PROP022_general L K M A hM hA hK hs u₀ hu₀ T P hP e,
    fun _ U => ⟨intrinsic_of_U U K M A hM hA hK hs u₀ hu₀ T P hP e,
      fun v => ⟨WH_isWeylOp U v, fun W hW => weylOp_unique hW (WH_isWeylOp U v)⟩,
      fun a b y hy => QH_QRel U a b y hy⟩,
    fun _ J => ⟨intrinsic_of_J J K M A hM hA hK hs u₀ hu₀ T P hP e,
      fun v => ⟨WJ_isWeylOp J v, fun W hW => weylOp_unique hW (WJ_isWeylOp J v)⟩,
      fun a b y hy => QJ_QRel J a b y hy⟩⟩

end QuantumNLS.Prop022CMain

#print axioms QuantumNLS.Prop022CMain.PROP022_general_intrinsic
#print axioms QuantumNLS.Prop022CMain.SH_symplectic
#print axioms QuantumNLS.Prop022CMain.SJ_symplectic
