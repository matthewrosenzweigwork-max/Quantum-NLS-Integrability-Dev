import LiebLiniger.FixedPeriod.Atomic.ALLS.TransA6Phys
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization

/-! # Track A, step A6: helpers for the reviewer-listed missing interfaces (SOL-STMTA-20261111)

Author: Claude Opus 5.5 (track A).  Not self-reviewed, not accepted.  Helper lemmas only, with
membership/analyticity witnesses as explicit hypotheses (supplied later by
`actualT_realExponent`/`actualTinv_realExponent`); the final commands are NOT stated here.

* finite-support sequences lie in every `h^r`;
* Birkhoff truncations (`truncC38` applied to the Birkhoff coordinates, NOT Fourier truncations of
  `u`): finite support, inverse images in every integer Sobolev level, convergence of the
  truncations and of their inverse images `Ψ_s(P_N Φ_s u) → u` in `H^s`;
* physical cross-index diagrams through `physicalSobolevFourierEquiv38` and `carrierIncl38`;
* provider bridges binding `actualBirkhoffInput38`, `actualPhi`, `actualPhiInv` and the sequence
  maps of `actualBirkhoffTop38` to `physicalBirkhoff`/`physicalInverseBirkhoff`. -/

set_option autoImplicit false
noncomputable section

open Filter Topology Set
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.PDE

namespace NlsGge.ALLS.TransA

/-- Finitely supported sequences belong to every `h^r`. -/
theorem mem_seqSobolev38_of_finiteSupport (r : ℝ) (x : ℤ → ℂ) (hx : {n : ℤ | x n ≠ 0}.Finite) :
    x ∈ seqSobolev38 r := by
  rw [mem_seqSobolev38_iff]
  refine summable_of_ne_finset_zero (s := hx.toFinset) fun n hn => ?_
  have : x n = 0 := by simpa using hn
  simp [this]

/-! ### Provider bridges -/

theorem bridge_input_top : actualBirkhoffInput38.toBirkhoffTop38 = actualBirkhoffTop38 :=
  actualBirkhoffInput38_top

theorem bridge_actualPhi : NlsGge.ThirdConsultation.Common.actualPhi = physicalBirkhoff := rfl

theorem bridge_actualPhiInv :
    NlsGge.ThirdConsultation.Common.actualPhiInv = physicalInverseBirkhoff := rfl

theorem bridge_Phi (u : PhysicalL2) : actualBirkhoffTop38.Φ u = (physicalBirkhoff u : ℤ → ℂ) :=
  (physicalBirkhoff_coe_eq_T u).symm

theorem bridge_T (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0) :
    actualBirkhoffTop38.T x = (physicalBirkhoff (physInv38 x hx) : ℤ → ℂ) := by
  rw [physicalBirkhoff_coe_eq_T, fourierSeq38_physInv38]

/-! ### Birkhoff truncations -/

/-- Inverse images of finitely supported coordinates lie in every integer Sobolev level. -/
theorem fourierSeq38_inverse_finiteSupport_mem (s : ℝ) (hs : 0 ≤ s) (z : SobolevCarrier38 s)
    (hz : {n : ℤ | carrierCoe38 s z n ≠ 0}.Finite) (m : ℕ) :
    fourierSeq38 (physicalInverseBirkhoff (sequenceSobolevEmbedRealExponent s hs z)) ∈
      seqSobolev38 (m : ℝ) := by
  rw [fourierSeq38_physicalInverseBirkhoff, coe_sequenceSobolevEmbedRealExponent]
  exact actualTinv38_mapsTo m _ (mem_seqSobolev38_of_finiteSupport _ _ hz)

/-- Carrier-level left inverse law at level `s`. -/
theorem carrierMap_Tinv_T (s : ℝ) (hs : 0 ≤ s)
    (hT : ∀ x ∈ seqSobolev38 s, actualBirkhoffTop38.T x ∈ seqSobolev38 s)
    (hTinv : ∀ z ∈ seqSobolev38 s, actualBirkhoffTop38.Tinv z ∈ seqSobolev38 s)
    (y : SobolevCarrier38 s) :
    carrierMap38 s s actualBirkhoffTop38.Tinv hTinv (carrierMap38 s s actualBirkhoffTop38.T hT y) = y := by
  apply carrierExt38
  have h := actualBirkhoffTop38.left_inv (carrierCoe38 s y) (seqSobolev38_mono hs (carrierCoe38_mem s y))
  rw [carrierMap38_coe, carrierMap38_coe]
  exact h

/-- The level-`s` maps are mutually inverse on `H^s` (left law), given the witnesses. -/
theorem inverse_birkhoffSobolevRealExponent_apply (s : ℝ) (hs : 0 ≤ s)
    (hT : ∀ x ∈ seqSobolev38 s, actualBirkhoffTop38.T x ∈ seqSobolev38 s)
    (hTinv : ∀ z ∈ seqSobolev38 s, actualBirkhoffTop38.Tinv z ∈ seqSobolev38 s)
    (u : PhysicalSobolev38 s) :
    inverseBirkhoffSobolevRealExponent s hs (birkhoffSobolevRealExponent s hs u) = u := by
  rw [inverseBirkhoffSobolevRealExponent_eq s hs hTinv, birkhoffSobolevRealExponent_eq s hs hT,
    Function.comp_apply, Function.comp_apply, carrierMap_Tinv_T s hs hT hTinv,
    LinearIsometryEquiv.symm_apply_apply]

/-- **Birkhoff-truncation approximation helper** at every real level. -/
theorem birkhoff_truncation_helper (s : ℝ) (hs : 0 ≤ s)
    (hT : ∀ x ∈ seqSobolev38 s, actualBirkhoffTop38.T x ∈ seqSobolev38 s)
    (hTinv : ∀ z ∈ seqSobolev38 s, actualBirkhoffTop38.Tinv z ∈ seqSobolev38 s)
    (hcont : Continuous (carrierMap38 s s actualBirkhoffTop38.Tinv hTinv))
    (u : PhysicalSobolev38 s) :
    (∀ N : ℕ, {n : ℤ | carrierCoe38 s (truncC38 s N (birkhoffSobolevRealExponent s hs u)) n ≠ 0}.Finite) ∧
    (∀ (N m : ℕ), fourierSeq38 (physicalInverseBirkhoff (sequenceSobolevEmbedRealExponent s hs
        (truncC38 s N (birkhoffSobolevRealExponent s hs u)))) ∈ seqSobolev38 (m : ℝ)) ∧
    Tendsto (fun N : ℕ => truncC38 s N (birkhoffSobolevRealExponent s hs u)) atTop
      (𝓝 (birkhoffSobolevRealExponent s hs u)) ∧
    Tendsto (fun N : ℕ => inverseBirkhoffSobolevRealExponent s hs
      (truncC38 s N (birkhoffSobolevRealExponent s hs u))) atTop (𝓝 u) := by
  have htr := tendsto_truncC38 s (birkhoffSobolevRealExponent s hs u)
  refine ⟨fun N => finiteSupport_truncC38 s N _,
    fun N m => fourierSeq38_inverse_finiteSupport_mem s hs _ (finiteSupport_truncC38 s N _) m,
    htr, ?_⟩
  have hc : Continuous (inverseBirkhoffSobolevRealExponent s hs) := by
    rw [inverseBirkhoffSobolevRealExponent_eq s hs hTinv]
    exact (physicalSobolevFourierEquiv38 s).symm.continuous.comp hcont
  have := (hc.tendsto _).comp htr
  rwa [inverse_birkhoffSobolevRealExponent_apply s hs hT hTinv u] at this

/-! ### Physical cross-index diagrams -/

/-- Forward physical cross-index diagram. -/
theorem phys_cross_forward {s s' : ℝ} (hs : 0 ≤ s) (hss' : s ≤ s')
    (hT : ∀ x ∈ seqSobolev38 s, actualBirkhoffTop38.T x ∈ seqSobolev38 s)
    (hT' : ∀ x ∈ seqSobolev38 s', actualBirkhoffTop38.T x ∈ seqSobolev38 s')
    (u : PhysicalSobolev38 s') :
    birkhoffSobolevRealExponent s hs ((physicalSobolevFourierEquiv38 s).symm
        (carrierIncl38 hss' (physicalSobolevFourierEquiv38 s' u))) =
      carrierIncl38 hss' (birkhoffSobolevRealExponent s' (hs.trans hss') u) := by
  rw [birkhoffSobolevRealExponent_eq s hs hT, birkhoffSobolevRealExponent_eq s' (hs.trans hss') hT']
  simp only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  exact (carrierIncl38_carrierMap38 hss' _ hT hT' _).symm

/-- Inverse physical cross-index diagram. -/
theorem phys_cross_inverse {s s' : ℝ} (hs : 0 ≤ s) (hss' : s ≤ s')
    (hTinv : ∀ z ∈ seqSobolev38 s, actualBirkhoffTop38.Tinv z ∈ seqSobolev38 s)
    (hTinv' : ∀ z ∈ seqSobolev38 s', actualBirkhoffTop38.Tinv z ∈ seqSobolev38 s')
    (z : SobolevCarrier38 s') :
    inverseBirkhoffSobolevRealExponent s hs (carrierIncl38 hss' z) =
      (physicalSobolevFourierEquiv38 s).symm (carrierIncl38 hss'
        (physicalSobolevFourierEquiv38 s' (inverseBirkhoffSobolevRealExponent s' (hs.trans hss') z))) := by
  rw [inverseBirkhoffSobolevRealExponent_eq s hs hTinv,
    inverseBirkhoffSobolevRealExponent_eq s' (hs.trans hss') hTinv']
  simp only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [carrierIncl38_carrierMap38 hss' _ hTinv hTinv']

end NlsGge.ALLS.TransA
