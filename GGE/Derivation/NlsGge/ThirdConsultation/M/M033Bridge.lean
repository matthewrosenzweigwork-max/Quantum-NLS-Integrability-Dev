import Mathlib
import NlsGge.Atomic.M.M031
import NlsGge.Atomic.G2.G2038
import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.ThirdConsultation.G1.ProductBounds
import NlsGge.ThirdConsultation.M.M033Host

/-!
# M-033/M-034 bridge: M-031 localization on the real gaps of an H1 potential (proof development, AUTHOR; not self-reviewed)

For `u : SobolevR 1`:
* `physicalOfSobolev u` has H1 Fourier coefficients (its Fourier coefficients are the ordinary Sobolev coordinates);
* hence (as in landed G2-038) `realSlice (physicalOfSobolev u) = KSPS.toPotPair φ` for an actual `φ : KSPS.SobolevC 1`,
  and the M-031 constant `Q` for that `φ` is exactly `MTwoMode.H1Norm u`;
* landed `lamPlus_real` identifies the periodic eigenvalues with the real gap endpoints, so M-031 localizes
  `actualGapLowerAllE02_38`/`actualGapUpperAllE02_38` (the endpoints of `M.closedGap`).
No hypothesis beyond the M-031 thresholds; M-031 is consumed as landed.
-/

set_option autoImplicit false

noncomputable section

open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.HierarchyRiccati.Core NlsGge.Atomic.Common
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.M033Bridge

/-- The Fourier coefficients of `physicalOfSobolev u` are its ordinary Sobolev coordinates. -/
theorem physicalFourier_physicalOfSobolev (u : M.SobolevR 1) (n : ℤ) :
    physicalFourier (M.physicalOfSobolev u) n =
      (show WeightedHilbert (sobolevModeWeight ((1 : ℕ) : ℝ)) from
        M.ordinarySobolevCoordinates 1 u) n := by
  unfold M.physicalOfSobolev
  rw [riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier,
    riccatiSobolevJetCoefficientL2Recovery28Second, pow_zero, one_mul]

/-- `physicalOfSobolev u` is an H1 field. -/
theorem physicalSobolev_physicalOfSobolev (u : M.SobolevR 1) :
    NlsGge.GKDefinitionDesign.physicalSobolev ((1 : ℕ) : ℝ) (M.physicalOfSobolev u) := by
  rw [NlsGge.GKDefinitionDesign.physicalSobolev_iff_ordinary]
  unfold SobolevSquareSummable
  have hs := (weightedHilbert_hasSum (sobolevModeWeight ((1 : ℕ) : ℝ))
    (show WeightedHilbert (sobolevModeWeight ((1 : ℕ) : ℝ)) from
      M.ordinarySobolevCoordinates 1 u)).summable
  refine hs.congr (fun n => ?_)
  rw [physicalFourier_physicalOfSobolev]
  rfl

/-- The real slice of an H1 potential is an actual `KSPS.SobolevC 1` pair (route of landed G2-038). -/
theorem exists_sobolevC (u : M.SobolevR 1) :
    ∃ φ : KSPS.SobolevC 1, KSPS.toPotPair φ = realSlice (M.physicalOfSobolev u) := by
  have h1 := physicalSobolev_physicalOfSobolev u
  have h1' : NlsGge.GKDefinitionDesign.physicalSobolev ((1 : ℕ) : ℝ)
      (star (M.physicalOfSobolev u) : PhysicalL2) := by
    have h : NlsGge.GKDefinitionDesign.physicalSobolev 1 (M.physicalOfSobolev u) := by
      simpa using h1
    simpa using NlsGge.GKDefinitionDesign.G2038S.physicalSobolev_star' _ h
  obtain ⟨v1, hv1⟩ := NlsGge.ThirdConsultation.KST.KST065S.exists_recover 1 _
    ((NlsGge.GKDefinitionDesign.G1086S.physicalSobolev_iff _ _).1 h1)
  obtain ⟨v2, hv2⟩ := NlsGge.ThirdConsultation.KST.KST065S.exists_recover 1 _
    ((NlsGge.GKDefinitionDesign.G1086S.physicalSobolev_iff _ _).1 h1')
  exact ⟨(v1, v2), by rw [realSlice_apply]; exact Prod.ext hv1 hv2⟩

/-- The M-031 constant of that pair is the Molnar pair norm. -/
theorem H1Norm_eq (u : M.SobolevR 1) (φ : KSPS.SobolevC 1)
    (hφ : KSPS.toPotPair φ = realSlice (M.physicalOfSobolev u)) :
    MTwoMode.potentialCoefficientNorm M.sourceH1Weight (KSPS.toPotPair φ) = MTwoMode.H1Norm u := by
  rw [hφ]; rfl

theorem H1Norm_nonneg (u : M.SobolevR 1) : 0 ≤ MTwoMode.H1Norm u := Real.sqrt_nonneg _

theorem norm_ofReal_sub (n : ℤ) (x : ℝ) :
    ‖(x : ℂ) - (n : ℂ) * (Real.pi : ℂ)‖ = |x - (n : ℝ) * Real.pi| := by
  have e : (x : ℂ) - (n : ℂ) * (Real.pi : ℂ) = ((x - (n : ℝ) * Real.pi : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]

/-- M-031 high labels: both real gap endpoints lie in the source disc. -/
theorem high_endpoints (u : M.SobolevR 1) (n : ℤ)
    (h : 8 * MTwoMode.H1Norm u ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n) :
    |actualGapLowerAllE02_38 (M.physicalOfSobolev u) n - (n : ℝ) * Real.pi| ≤
        MTwoMode.H1Norm u ^ 2 / NlsGge.Atomic.M.M054.indexWeight n +
          Real.sqrt 2 * MTwoMode.H1Norm u / NlsGge.Atomic.M.M054.indexWeight (2 * n) ∧
      |actualGapUpperAllE02_38 (M.physicalOfSobolev u) n - (n : ℝ) * Real.pi| ≤
        MTwoMode.H1Norm u ^ 2 / NlsGge.Atomic.M.M054.indexWeight n +
          Real.sqrt 2 * MTwoMode.H1Norm u / NlsGge.Atomic.M.M054.indexWeight (2 * n) := by
  obtain ⟨φ, hφ⟩ := exists_sobolevC u
  have hW : KSPS.toPotPair φ ∈ gkW := by rw [hφ]; exact realSlice_mem_gkW _
  have L := M.periodic_spectral_localization φ hW
  rw [H1Norm_eq u φ hφ] at L
  dsimp only at L
  rw [hφ] at L
  obtain ⟨Lhi, -⟩ := L
  have ep := Lhi n h true
  have em := Lhi n h false
  rw [if_pos rfl] at ep
  rw [if_neg (by decide)] at em
  obtain ⟨hp, hm⟩ := lamPlus_real (M.physicalOfSobolev u) n
  rw [hp, norm_ofReal_sub] at ep
  rw [hm, norm_ofReal_sub] at em
  exact ⟨em, ep⟩

/-- M-031 low labels: both real gap endpoints lie in the central box. -/
theorem low_endpoints (u : M.SobolevR 1) (n : ℤ)
    (h : NlsGge.Atomic.M.M054.indexWeight n < 8 * MTwoMode.H1Norm u ^ 2) :
    |actualGapLowerAllE02_38 (M.physicalOfSobolev u) n| ≤
        (8 * MTwoMode.H1Norm u ^ 2 - 1 / 2) * Real.pi ∧
      |actualGapUpperAllE02_38 (M.physicalOfSobolev u) n| ≤
        (8 * MTwoMode.H1Norm u ^ 2 - 1 / 2) * Real.pi := by
  obtain ⟨φ, hφ⟩ := exists_sobolevC u
  have hW : KSPS.toPotPair φ ∈ gkW := by rw [hφ]; exact realSlice_mem_gkW _
  have L := M.periodic_spectral_localization φ hW
  rw [H1Norm_eq u φ hφ] at L
  dsimp only at L
  rw [hφ] at L
  obtain ⟨-, Llo⟩ := L
  have ep := (Llo n h true).1
  have em := (Llo n h false).1
  rw [if_pos rfl] at ep
  rw [if_neg (by decide)] at em
  obtain ⟨hp, hm⟩ := lamPlus_real (M.physicalOfSobolev u) n
  rw [hp, Complex.ofReal_re] at ep
  rw [hm, Complex.ofReal_re] at em
  exact ⟨em, ep⟩

end NlsGge.ThirdConsultation.M033Bridge

end
