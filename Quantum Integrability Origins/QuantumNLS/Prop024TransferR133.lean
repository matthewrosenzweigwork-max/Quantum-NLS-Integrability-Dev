import QuantumNLS.Prop021GeneralR132
import QuantumNLS.Prop024FinalH1

/-! Transfer of the fixed-carrier remainder by second quantization.
The graph domain is carried by the sector Hamiltonians, and the Weyl
operator is compressed through its reducing Fock subspace. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option synthInstance.maxHeartbeats 150000
open scoped InnerProductSpace ENNReal

namespace QuantumNLS.Prop024TransferR133
open PhysicalTensor Prop022GTensor Prop022AIsoTensor Prop022GClassical
open Prop022BClass1 Prop022BFock1 Prop022BFock2 Prop022PositiveDataR126
open Prop021ManyBodyTransportR132 Prop021MomentsR132
open Prop021ContractsR132 Prop021UnitaryInputsR132
open Prop024FinalH1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

/-- The torus graph domain and action are the positive-rank Hamiltonian
used in the general-carrier transport. -/
theorem torus_domain (K : Kernels (L2T L)) (N : ℕ) (x : FockSpace (L2T L)) :
    x ∈ (Prop021ManyBodyR129.hamiltonian (positiveExtension K) N).domain ↔
      HamiltonianDomain K N x := Iff.rfl

theorem torus_action (K : Kernels (L2T L)) (N : ℕ) (x : FockSpace (L2T L))
    (hx : HamiltonianDomain K N x) :
    Prop021ManyBodyR129.hamiltonian (positiveExtension K) N
        ⟨x, (torus_domain K N x).mpr hx⟩ = hamiltonian K N x hx := by
  apply lp.ext
  funext n
  rfl

theorem weyl_unitary (U : H ≃ₗᵢ[ℂ] L2T L) (v : H) (x : FockSpace H) :
    WJ U.toLinearIsometry v x = Prop022AFock.WH U v x := by
  apply (Prop022AFock.gam U).injective
  simp only [Prop022AFock.WH, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  change fockMap U (WJ U.toLinearIsometry v x) = Prop022OVacuum.printedWeyl (U v) (fockMap U x)
  rw [← fockMapI_equiv U, ← fockMapI_equiv U]
  exact gam_compress _ _ _ x

/-- The printed estimate holds along every isometry, with no change to
the threshold or the explicit constant. -/
theorem transfer (J : H →ₗᵢ[ℂ] L2T L) (A : ℝ) (hA : 0 < A) :
    RemainderEstimateIsometry J A (printedConstant A) := by
  intro K M hM hK hs N Q hQ hN u hu x hx
  let K' := extendKernels J K
  let y := fockMapI J x
  let v := (Real.sqrt N : ℂ) • u
  let z := WJ J v x
  let W := Prop022OVacuum.printedWeyl ((Real.sqrt N : ℂ) • J u)
  have hK' : KBound K' M A := hKJ J K M A hK
  have hs' : KSelfAdj K' := extendKernels_selfAdj J K hs
  have hm := (numberMoments_torus Q y).mp ((numberMoments_transport J Q x).mpr hx)
  have hshift : J v = (Real.sqrt N : ℂ) • J u := map_smul J _ _
  have hW (a : FockSpace H) : fockMapI J (WJ J v a) = W (fockMapI J a) := by
    unfold W
    rw [← hshift]
    exact gam_compress J _ _ a
  obtain ⟨hy,h₂,hd,R,hR,hbound⟩ := printed_remainder (L := L) A hA
    (positiveExtension K') M hM (positiveExtension_bound K' M A hK')
    (positiveExtension_selfAdjoint K' hs') N Q hQ hN (J u)
    ((J.norm_map u).trans hu) y hm
  change W y ∈ (Prop021ManyBodyR129.hamiltonian (positiveExtension K') N).domain at hd
  have hdz : HamiltonianDomain K N z := by
    apply (hamiltonian_domain_transport J K N z).mp
    rw [hW x]
    exact (torus_domain K' N _).mp hd
  refine ⟨hdz, gamAdj J R, ?_, ?_⟩
  · have hH := hamiltonian_transport J K N z hdz
    have hY : fockMapI J z = W y := hW x
    have hphys : fockMapI J (hamiltonian K N z hdz) =
        Prop021ManyBodyR129.hamiltonian (positiveExtension K') N ⟨W y,hd⟩ := by
      rw [← hH]
      rw [← torus_action]
      exact Prop024WIdent.pmap_apply_congr _ _ rfl _ _ hY _ hd
    let a := Prop021RemainderInputR131.lowOrders (positiveExtension K') N (J u) y hy h₂
    have hp : fockMapI J (hamiltonian K N z hdz) = W (a + R) := hphys.trans hR
    have himage : a + R = fockMapI J ((WJ J v).symm (hamiltonian K N z hdz)) := by
      apply W.injective
      rw [← hW, LinearIsometryEquiv.apply_symm_apply]
      exact hp.symm
    have hsum : lowOrders J K N u Q x hx + gamAdj J R =
        (WJ J v).symm (hamiltonian K N z hdz) := by
      change gamAdj J a + gamAdj J R = _
      rw [← map_add, himage, gamAdj_gam]
    rw [hsum, LinearIsometryEquiv.apply_symm_apply]
  · have hg : ‖gamAdj J‖ ≤ 1 := by
      unfold gamAdj
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact LinearIsometry.norm_toContinuousLinearMap_le _
    exact ((ContinuousLinearMap.le_opNorm (gamAdj J) R).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hg (norm_nonneg R))).trans hbound

/-- Exact R132 consumer, with the same constant in the unitary and
finite-dimensional branches. -/
theorem remainderInput : Prop021ContractsR132.Prop024RemainderInput (L := L) := by
  intro A hA
  exact ⟨printedConstant A, printedConstant_nonneg A,
    (unitaryRemainder_iff_torus (L := L) A _).mpr (remainderEstimate_printed A hA),
    by intro E _ _ _ _ _ J; exact transfer J A hA⟩

end QuantumNLS.Prop024TransferR133
