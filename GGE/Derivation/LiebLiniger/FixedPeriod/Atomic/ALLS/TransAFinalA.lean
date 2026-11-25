import LiebLiniger.FixedPeriod.Atomic.ALLS.TransA6Approx
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G6.G6014
import NlsGge.Atomic.G6.G6028

/-! # Track A final theorems, part A (owner-approved statements, APPROVAL_PACKET_TRACK_A.md
sha256 0a7926e2…; statement approval only, proofs not yet accepted)

Author: Claude Opus 5.5 (track A).  Not self-reviewed, not accepted.
Statements copied verbatim from the approved packet: `allS_actualBirkhoff_seq` (A-SEQ),
`allS_mem_iff` (A-MEM), `allS_compat_nat`, `allS_compat_cross` (REVISED texts),
`allS_compat_cross_phys` (A-COMPAT-PHYS), `actual_provider_bridge` (A-BRIDGE),
`actual_birkhoff_bindings` (A-BIND).  A-TR / A-TRINV (`physicalBirkhoff_translate`,
`physicalInverseBirkhoff_translate`) are declared with the approved text in `TransA2Translate`. -/

set_option autoImplicit false
noncomputable section

open Filter Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.PDE

namespace NlsGge.ALLS.TransA

/-- Carrier-level right inverse law at level `s` (helper). -/
theorem carrierMap_T_Tinv (s : ℝ) (hs : 0 ≤ s)
    (hT : ∀ x ∈ seqSobolev38 s, actualBirkhoffTop38.T x ∈ seqSobolev38 s)
    (hTinv : ∀ z ∈ seqSobolev38 s, actualBirkhoffTop38.Tinv z ∈ seqSobolev38 s)
    (y : SobolevCarrier38 s) :
    carrierMap38 s s actualBirkhoffTop38.T hT (carrierMap38 s s actualBirkhoffTop38.Tinv hTinv y) = y := by
  apply carrierExt38
  have h := actualBirkhoffTop38.right_inv (carrierCoe38 s y) (seqSobolev38_mono hs (carrierCoe38_mem s y))
  rw [carrierMap38_coe, carrierMap38_coe]
  exact h

/-- **A-SEQ.** -/
theorem allS_actualBirkhoff_seq (s : ℝ) (hs : 0 ≤ s) :
    ∃ (hT : ∀ x ∈ seqSobolev38 s, actualBirkhoffTop38.T x ∈ seqSobolev38 s)
      (hTinv : ∀ z ∈ seqSobolev38 s, actualBirkhoffTop38.Tinv z ∈ seqSobolev38 s),
      AnalyticOnNhd ℝ (carrierMap38 s s actualBirkhoffTop38.T hT) Set.univ ∧
      AnalyticOnNhd ℝ (carrierMap38 s s actualBirkhoffTop38.Tinv hTinv) Set.univ ∧
      Function.LeftInverse (carrierMap38 s s actualBirkhoffTop38.Tinv hTinv)
        (carrierMap38 s s actualBirkhoffTop38.T hT) ∧
      Function.RightInverse (carrierMap38 s s actualBirkhoffTop38.Tinv hTinv)
        (carrierMap38 s s actualBirkhoffTop38.T hT) := by
  obtain ⟨hT, hanT⟩ := actualT_realExponent s hs
  obtain ⟨hTinv, hanTinv⟩ := actualTinv_realExponent s hs
  exact ⟨hT, hTinv, hanT, hanTinv, fun y => carrierMap_Tinv_T s hs hT hTinv y,
    fun y => carrierMap_T_Tinv s hs hT hTinv y⟩

/-- **A-MEM.** -/
theorem allS_mem_iff (s : ℝ) (hs : 0 ≤ s) (u : PhysicalL2) :
    fourierSeq38 u ∈ seqSobolev38 s ↔ (physicalBirkhoff u : ℤ → ℂ) ∈ seqSobolev38 s := by
  obtain ⟨hT, -⟩ := actualT_realExponent s hs
  obtain ⟨hTinv, -⟩ := actualTinv_realExponent s hs
  rw [physicalBirkhoff_coe_eq_T]
  constructor
  · exact hT _
  · intro h
    have e := actualBirkhoffTop38.left_inv (fourierSeq38 u) (fourierSeq38_mem_zero u)
    rw [← e]
    exact hTinv _ h

/-- **A-COMPAT-NAT** (revised text). -/
theorem allS_compat_nat (m : ℕ) :
    birkhoffSobolevRealExponent (m : ℝ) (Nat.cast_nonneg m) = birkhoffSobolev m ∧
    inverseBirkhoffSobolevRealExponent (m : ℝ) (Nat.cast_nonneg m) = inverseBirkhoffSobolev m ∧
    carrierMap38 (m : ℝ) (m : ℝ) actualBirkhoffTop38.T
      (actualBirkhoffTop38.mapsTo_T m) = actualBirkhoffTop38.TC m ∧
    carrierMap38 (m : ℝ) (m : ℝ) actualBirkhoffTop38.Tinv
      (actualBirkhoffTop38.mapsTo_Tinv m) = actualBirkhoffTop38.TinvC m :=
  ⟨birkhoffSobolevRealExponent_natCast m, inverseBirkhoffSobolevRealExponent_natCast m, rfl, rfl⟩

/-- **A-COMPAT-CROSS** (revised text). -/
theorem allS_compat_cross (s s' : ℝ) (hs : 0 ≤ s) (hss' : s ≤ s') :
    ∃ (hT : ∀ x ∈ seqSobolev38 s, actualBirkhoffTop38.T x ∈ seqSobolev38 s)
      (hT' : ∀ x ∈ seqSobolev38 s', actualBirkhoffTop38.T x ∈ seqSobolev38 s')
      (hTinv : ∀ z ∈ seqSobolev38 s, actualBirkhoffTop38.Tinv z ∈ seqSobolev38 s)
      (hTinv' : ∀ z ∈ seqSobolev38 s', actualBirkhoffTop38.Tinv z ∈ seqSobolev38 s'),
      ∀ x : SobolevCarrier38 s',
        carrierIncl38 hss' (carrierMap38 s' s' actualBirkhoffTop38.T hT' x) =
          carrierMap38 s s actualBirkhoffTop38.T hT (carrierIncl38 hss' x) ∧
        carrierIncl38 hss' (carrierMap38 s' s' actualBirkhoffTop38.Tinv hTinv' x) =
          carrierMap38 s s actualBirkhoffTop38.Tinv hTinv (carrierIncl38 hss' x) := by
  obtain ⟨hT, -⟩ := actualT_realExponent s hs
  obtain ⟨hT', -⟩ := actualT_realExponent s' (hs.trans hss')
  obtain ⟨hTinv, -⟩ := actualTinv_realExponent s hs
  obtain ⟨hTinv', -⟩ := actualTinv_realExponent s' (hs.trans hss')
  exact ⟨hT, hT', hTinv, hTinv', fun x =>
    ⟨carrierIncl38_carrierMap38 hss' _ hT hT' x, carrierIncl38_carrierMap38 hss' _ hTinv hTinv' x⟩⟩

/-- **A-COMPAT-PHYS.** -/
theorem allS_compat_cross_phys (s s' : ℝ) (hs : 0 ≤ s) (hss' : s ≤ s') :
    (∀ u : PhysicalSobolev38 s',
      birkhoffSobolevRealExponent s hs ((physicalSobolevFourierEquiv38 s).symm
          (carrierIncl38 hss' (physicalSobolevFourierEquiv38 s' u))) =
        carrierIncl38 hss' (birkhoffSobolevRealExponent s' (hs.trans hss') u)) ∧
    (∀ z : SobolevCarrier38 s',
      inverseBirkhoffSobolevRealExponent s hs (carrierIncl38 hss' z) =
        (physicalSobolevFourierEquiv38 s).symm (carrierIncl38 hss'
          (physicalSobolevFourierEquiv38 s' (inverseBirkhoffSobolevRealExponent s' (hs.trans hss') z)))) := by
  obtain ⟨hT, -⟩ := actualT_realExponent s hs
  obtain ⟨hT', -⟩ := actualT_realExponent s' (hs.trans hss')
  obtain ⟨hTinv, -⟩ := actualTinv_realExponent s hs
  obtain ⟨hTinv', -⟩ := actualTinv_realExponent s' (hs.trans hss')
  exact ⟨fun u => phys_cross_forward hs hss' hT hT' u, fun z => phys_cross_inverse hs hss' hTinv hTinv' z⟩

/-- **A-BRIDGE.** -/
theorem actual_provider_bridge :
    actualBirkhoffInput38.toBirkhoffTop38 = actualBirkhoffTop38 ∧
    NlsGge.ThirdConsultation.Common.actualPhi = physicalBirkhoff ∧
    NlsGge.ThirdConsultation.Common.actualPhiInv = physicalInverseBirkhoff ∧
    (∀ u : PhysicalL2, actualBirkhoffTop38.Φ u = (physicalBirkhoff u : ℤ → ℂ)) ∧
    (∀ z : NlsGge.GK38.Lib.L2Z,
      fourierSeq38 (physicalInverseBirkhoff z) = actualBirkhoffTop38.Tinv (z : ℤ → ℂ)) ∧
    (∀ (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0), actualBirkhoffTop38.T x =
      (physicalBirkhoff (physInv38 x hx) : ℤ → ℂ)) :=
  ⟨bridge_input_top, bridge_actualPhi, bridge_actualPhiInv, bridge_Phi,
    fourierSeq38_physicalInverseBirkhoff, bridge_T⟩

/-- **A-BIND.** -/
theorem actual_birkhoff_bindings :
    Function.LeftInverse physicalInverseBirkhoff physicalBirkhoff ∧
    Function.RightInverse physicalInverseBirkhoff physicalBirkhoff ∧
    AnalyticOnNhd ℝ physicalBirkhoff Set.univ ∧ AnalyticOnNhd ℝ physicalInverseBirkhoff Set.univ ∧
    (∀ u : PhysicalL2, ‖physicalBirkhoff u‖ = ‖u‖) ∧
    (∀ (u : PhysicalL2) (n : ℤ),
      NlsGge.SpectralFoundations.actualGapActionAllE02_38 u n = ‖(physicalBirkhoff u : ℤ → ℂ) n‖ ^ 2) ∧
    (∀ u : PhysicalL2,
      HasSum (fun n => NlsGge.SpectralFoundations.actualGapActionAllE02_38 u n) (‖u‖ ^ 2)) ∧
    (∀ u h k : PhysicalL2,
      inner ℝ (Complex.I • (fderiv ℝ physicalBirkhoff u) h) ((fderiv ℝ physicalBirkhoff u) k) =
        inner ℝ (Complex.I • h) k) ∧
    (∀ (u : PhysicalL2) (n : ℤ),
      ((fderiv ℝ physicalBirkhoff 0) u : ℤ → ℂ) n = -physicalFourier (u : PhysicalCircle → ℂ) (-n)) :=
  ⟨G6013.2.2.2.2.1, G6013.2.2.2.2.2, G6014.2.2.1, G6014.2.2.2.1,
    fun u => (G6014.2.2.2.2.2.2.1 u).2.2, fun u n => (G6028.1 u n).2.2, G6028.2.1, G6028.2.2.1,
    G6028.2.2.2.2⟩

end NlsGge.ALLS.TransA
