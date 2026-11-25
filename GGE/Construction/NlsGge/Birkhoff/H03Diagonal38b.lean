import NlsGge.Birkhoff.F08Bare38h
import NlsGge.Birkhoff.H02Hierarchy38d

/-! # H03, file b: bridges between F08 (`H^{m-1}`-coordinates) and H02 (physical coordinates)

* `F08_weak_sobolev38`: v2 `C:eq:barelimits` on every fixed `H^r`, `r ≤ m-1` (not only `H^{m-1}`):
  `ν_{m,N} ⇀ μ_m` there, the limit being the image of `μ_m` under the inclusion `H^{m-1} → H^r`.
  (This is the general-`m` form of the `m = 2` argument of `L06_08a_38`.)
* `physFS38 r`: the physical field `u` as its Fourier coefficient sequence `(û(n))` in
  `SobolevHilbert r` (junk `0` off `H^r`), the same coordinates in which F08 states `ν_{m,N}`.
* `muHatM38_eq_hierMuHat38` and `integral_muM38_reSob_eq_hierMu38`: the F05/F08 objects
  `(Z_m, μ_m)` of `H^{m-1}`-coordinates equal the H02 objects `(hierZ38, hierMu38)` of physical
  coordinates (same Gaussian `γ_m`, same remainder `R_m(Φ⁻¹ z)`, same `Φ⁻¹`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory ProbabilityTheory Filter Topology NlsGge.Measure NlsGge.Pilot
  NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38 NlsGge.SpectralFoundations NlsGge.Weights
open scoped ENNReal BoundedContinuousFunction

namespace BirkhoffInput38

open BirkhoffTop38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {m : ℕ} {β : ℕ → ℝ}
  (hm : 2 ≤ m) (hβ : ∀ j ≤ m, 0 < β j)

include O hm hβ in
/-- **F08 on every `H^r`, `r ≤ m-1`** (`C:eq:barelimits`, first clause, in the fixed Sobolev space
`H^r`): for every bounded continuous `φ` on `H^r`,
`∫ φ dν_{m,N} → ∫ φ ∘ (H^{m-1} ↪ H^r) dμ_m`. -/
theorem F08_weak_sobolev38 (r : ℕ) (hr : r ≤ m - 1) (φ : SobolevHilbert (r : ℝ) →ᵇ ℝ) :
    Tendsto (fun N : ℕ => ∫ u, φ u ∂(nuBareS38 m β N (r : ℝ))) atTop
      (𝓝 (∫ u, φ (reSob38 ((m - 1 : ℕ) : ℝ) (r : ℝ) u) ∂(muM38 B m β))) := by
  have hφm : Measurable (fun u : SobolevHilbert (r : ℝ) => φ u) := φ.continuous.measurable
  have hae : ∀ᵐ ω ∂(gammaM38 m β),
      Summable (fun n : ℤ => sobolevModeWeight ((m - 1 : ℕ) : ℝ) n * ‖ω n‖ ^ 2) :=
    ae_summable38 (m := m) (β := β) hm (fun j hj => (hβ j hj).le) (hβ 0 (Nat.zero_le _))
      (hβ m le_rfl)
  have hae' : ∀ᵐ ω ∂(gammaM38 m β),
      Summable (fun n : ℤ => sobolevModeWeight (r : ℝ) n * ‖ω n‖ ^ 2) := by
    filter_upwards [hae] with ω hω
    have h1 : ω ∈ seqSobolev38 ((m - 1 : ℕ) : ℝ) := (mem_seqSobolev38_iff _ _).2 hω
    exact (mem_seqSobolev38_iff _ _).1 (seqSobolev38_mono (by exact_mod_cast hr) h1)
  have hconv : ∀ᵐ ω ∂(gammaM38 m β), Tendsto (fun N : ℕ =>
      φ (planeElement38 (r : ℝ) N (NlsGge.Ramer.windowProj N ω))) atTop
      (𝓝 (φ (seqRealization38 (sobolevModeWeight (r : ℝ)) ω))) := by
    filter_upwards [hae'] with ω hω
    exact (φ.continuous.tendsto _).comp (tendsto_planeElement38 (r : ℝ) ω hω)
  have h := F08_tests_tendsto38 B O hm hβ
    (Gs := fun N ω => φ (planeElement38 (r : ℝ) N (NlsGge.Ramer.windowProj N ω)))
    (G := fun ω => φ (seqRealization38 (sobolevModeWeight (r : ℝ)) ω)) (C := ‖φ‖)
    (fun N => hφm.comp ((measurable_finiteElement38 _ _).comp
      (NlsGge.Ramer.measurable_windowProj N)))
    (fun N ω => by simpa using φ.norm_coe_le_norm _) hconv
  have hlim : ∫ u, φ (reSob38 ((m - 1 : ℕ) : ℝ) (r : ℝ) u) ∂(muM38 B m β) =
      (∫ ω, φ (seqRealization38 (sobolevModeWeight (r : ℝ)) ω) * weightInf38 m β ω
        ∂(gammaM38 m β)) / ZM38 B m β := by
    rw [integral_muM38_eq B O hm hβ (fun u => φ (reSob38 ((m - 1 : ℕ) : ℝ) (r : ℝ) u))
      (hφm.comp (measurable_reSob38 _ _))]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    have := reSob38_realization ((m - 1 : ℕ) : ℝ) (r : ℝ) ω hω
    simp only [gaussianRealization38, this]
  rw [hlim]
  refine h.congr fun N => ?_
  rw [integral_nuBareS38 hm hβ N (r : ℝ) _ hφm]

end BirkhoffInput38

/-! ### Physical fields as Fourier coefficient sequences -/

/-- The physical field `u` as its Fourier coefficient sequence `(û(n))` in `H^r`
(`SobolevHilbert r`), through `𝓕⁻¹ ∘ physH38 r`; junk value `0` off `H^r` (a `μ_W`-null set, and
a `μ_m`-null set for `m ≥ r+1`). -/
def physFS38 (r : ℕ) (u : PhysicalL2) : SobolevHilbert (r : ℝ) :=
  ofCarrier38 (r : ℝ) (reflC38 (r : ℝ) (physH38 r u))

/-- Fidelity: on `H^r`, `physFS38 r u` has the Fourier coefficients `û(n)`. -/
theorem coeffSeq_physFS38 (r : ℕ) (u : PhysicalL2)
    (hu : SobolevSquareSummable (r : ℝ) (physicalFourier u)) (n : ℤ) :
    coeffSeq38 (r : ℝ) (physFS38 r u) n = physicalFourier u n := by
  unfold physFS38 coeffSeq38
  show -(carrierCoe38 (r : ℝ) (physH38 r u) (-n)) = _
  rw [physH38_of_mem r u ((fourierSeq38_mem_iff _ u).2 hu), carrierCoe38_mk, fourierSeq38_apply]
  simp

theorem coeffSeq38_injective (r : ℝ) : Function.Injective (coeffSeq38 r) :=
  fun _ _ h => carrierExt38 h

theorem continuous_physFS_comp38 (r : ℕ) :
    Continuous (fun x : SobolevCarrier38 (r : ℝ) => ofCarrier38 (r : ℝ) (reflC38 (r : ℝ) x)) :=
  (continuous_ofCarrier38 _).comp (continuous_reflC38 _)

theorem measurable_physFS38 (r : ℕ) : Measurable (physFS38 r) := by
  let _ : MeasurableSpace (SobolevCarrier38 (r : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 (r : ℝ)) := ⟨rfl⟩
  exact (continuous_physFS_comp38 r).measurable.comp (measurable_physH38 r)

namespace BirkhoffInput38

open BirkhoffTop38

variable (B : BirkhoffInput38)

theorem coeffSeq_PhiInvX38 (k : ℕ) (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 ((k - 1 : ℕ) : ℝ))
    (n : ℤ) : coeffSeq38 ((k - 1 : ℕ) : ℝ) (B.PhiInvX38 k z) n = -B.Tinv z (-n) := by
  unfold PhiInvX38 coeffSeq38
  show -(carrierCoe38 _ (B.cleanTinvC (k - 1) z) (-n)) = _
  rw [B.cleanTinvC_of_mem _ z hz, TinvC_coe, carrierCoe38_mk]

/-- `Φ⁻¹ z` in `H^{m-1}`-coordinates (F05) is the physical `Φ⁻¹ z` (H02). -/
theorem sobolevToL2_PhiInvX38 (k : ℕ) (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 ((k - 1 : ℕ) : ℝ)) :
    sobolevToL2_38 (k - 1) (B.PhiInvX38 k z) = B.cleanΦinv z := by
  apply fourierSeq38_injective
  rw [B.fourierSeq38_cleanΦinv z (seqSobolev38_natCast_mono hz)]
  funext n
  rw [fourierSeq38_apply, sobolevToL2_38_fourier]
  have := B.coeffSeq_PhiInvX38 k z hz (-n)
  change (show WeightedHilbert (sobolevModeWeight ((k - 1 : ℕ) : ℝ)) from
    B.PhiInvX38 k z) (-n) = _ at this
  rw [this]
  simp

theorem reSob38_PhiInvX38 (k : ℕ) (r : ℕ) (hr : r ≤ k - 1) (z : ℤ → ℂ)
    (hz : z ∈ seqSobolev38 ((k - 1 : ℕ) : ℝ)) :
    reSob38 ((k - 1 : ℕ) : ℝ) (r : ℝ) (B.PhiInvX38 k z) = physFS38 r (B.cleanΦinv z) := by
  have hr' : (r : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hr
  have hzr : z ∈ seqSobolev38 (r : ℝ) := seqSobolev38_mono hr' hz
  have hu : SobolevSquareSummable (r : ℝ) (physicalFourier (B.cleanΦinv z)) :=
    B.sobolev_cleanΦinv38 r z hzr
  apply coeffSeq38_injective
  funext n
  have hy : Summable (fun n : ℤ => sobolevModeWeight (r : ℝ) n *
      ‖coeffSeq38 ((k - 1 : ℕ) : ℝ) (B.PhiInvX38 k z) n‖ ^ 2) := by
    have h1 : coeffSeq38 ((k - 1 : ℕ) : ℝ) (B.PhiInvX38 k z) ∈ seqSobolev38 ((k - 1 : ℕ) : ℝ) :=
      (mem_seqSobolev38_iff _ _).2 (summable_coeffSeq38 _ _)
    exact (mem_seqSobolev38_iff _ _).1 (seqSobolev38_mono hr' h1)
  rw [coeffSeq_reSob38 _ _ _ hy n, coeffSeq_physFS38 r _ hu n, B.coeffSeq_PhiInvX38 k z hz n]
  have h2 := fourierSeq38_apply (B.cleanΦinv z) (-n)
  rw [B.fourierSeq38_cleanΦinv z (seqSobolev38_natCast_mono hz)] at h2
  rw [h2]
  simp

/-! ### Identification of the F05/F08 objects with the H02 objects -/

section Identify

variable (lower : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)

theorem hierRbar38_eq_Rm38 {k : ℕ} (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 ((k - 1 : ℕ) : ℝ)) :
    B.hierRbar38 c k z = Rm38 k (coefficient c) (B.PhiInvX38 k z) := by
  rw [B.hierRbar38_of_mem c k hz]
  unfold Rm38 hierRemainder38
  rw [B.sobolevToL2_PhiInvX38 k z hz]
  rfl

include hlower hbound in
theorem ae_mem_seqSobolev38_gammaM38 {k : ℕ} (hk : 2 ≤ k) :
    ∀ᵐ z ∂(gammaM38 k (coefficient c)), z ∈ seqSobolev38 ((k - 1 : ℕ) : ℝ) := by
  filter_upwards [ae_summable38 (m := k) (β := coefficient c) hk
    (fun j _ => (coefficient_pos lower c hlower hbound j).le)
    (coefficient_pos lower c hlower hbound 0) (coefficient_pos lower c hlower hbound k)] with z hz
  exact (mem_seqSobolev38_iff _ _).2 hz

include hlower hbound in
theorem ZM38_eq_hierZ38 {k : ℕ} (hk : 2 ≤ k) : ZM38 B k (coefficient c) = B.hierZ38 c k := by
  unfold ZM38 hierZ38
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_seqSobolev38_gammaM38 lower c hlower hbound hk] with z hz
  rw [B.hierRbar38_eq_Rm38 c z hz]

include hlower hbound in
theorem muHatM38_eq_hierMuHat38 {k : ℕ} (hk : 2 ≤ k) :
    muHatM38 B k (coefficient c) = B.hierMuHat38 c k := by
  unfold muHatM38 hierMuHat38
  rw [B.ZM38_eq_hierZ38 lower c hlower hbound hk]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_mem_seqSobolev38_gammaM38 lower c hlower hbound hk] with z hz
  rw [B.hierRbar38_eq_Rm38 c z hz]

include hlower hbound in
/-- The F05/F08 measure `μ_m` (on `H^{m-1}`, pushed to `H^r`) and the H02 measure `μ_m`
(on `L²`, read in `û`-coordinates by `physFS38 r`) have the same integrals. -/
theorem integral_muM38_reSob_eq_hierMu38 {k : ℕ} (hk : 2 ≤ k) (r : ℕ) (hr : r ≤ k - 1)
    (G : SobolevHilbert (r : ℝ) →ᵇ ℝ) :
    ∫ u, G (reSob38 ((k - 1 : ℕ) : ℝ) (r : ℝ) u) ∂(muM38 B k (coefficient c)) =
      ∫ u, G (physFS38 r u) ∂(B.hierMu38 c k) := by
  have hG : Measurable (fun u : SobolevHilbert (r : ℝ) => G u) := G.continuous.measurable
  have h1 : Measurable (fun u : Hm1 k => G (reSob38 ((k - 1 : ℕ) : ℝ) (r : ℝ) u)) :=
    hG.comp (measurable_reSob38 _ _)
  have h2 : Measurable (fun u : PhysicalL2 => G (physFS38 r u)) := hG.comp (measurable_physFS38 r)
  unfold muM38 hierMu38
  rw [integral_map (B.measurable_PhiInvX38 k).aemeasurable h1.aestronglyMeasurable,
    integral_map B.measurable_cleanΦinv.aemeasurable h2.aestronglyMeasurable,
    B.muHatM38_eq_hierMuHat38 lower c hlower hbound hk]
  refine integral_congr_ae ?_
  have hmu : ∀ᵐ z ∂(B.hierMuHat38 c k), z ∈ seqSobolev38 ((k - 1 : ℕ) : ℝ) := by
    unfold hierMuHat38
    exact withDensity_absolutelyContinuous _ _ (ae_mem_seqSobolev38_gammaM38 lower c hlower hbound hk)
  filter_upwards [hmu] with z hz
  simp only [B.reSob38_PhiInvX38 k r hr z hz]

end Identify

end BirkhoffInput38

end NlsGge.Birkhoff

end
