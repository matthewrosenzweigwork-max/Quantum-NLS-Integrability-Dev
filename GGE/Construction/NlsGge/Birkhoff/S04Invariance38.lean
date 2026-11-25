import NlsGge.Birkhoff.S04Moments38e
import NlsGge.NLS38.MeasureDetermination38

/-! # D2 (abstract part): weak-limit passage from `ν_Λ`-invariance to `μ_W`-invariance
(GWP plan `campaign/GWP_PLAN.md` §5.4 and §7 Part D, piece D2)

**This file is ABSTRACT in the flow `S`.**  `S : ℝ → PhysicalL2 → PhysicalL2` and its continuous
carrier model `SC` are arbitrary parameters.  By design risk R4 (`campaign/BIRKHOFF_LAYER_DESIGN.md`
§2.4), `BirkhoffNLSFlowInput38 B S` is NEVER mentioned here, and no declaration of this file is an
S04 statement.  S04.08 is `S04_08_nlsFlow_invariant_muW` (piece D3), which instantiates
`S := nlsFlowL2`.  The name `muW_invariant_aux` is an internal lemma, valid for every `S`
satisfying its stated hypotheses.

Mathematics (v2 l.447-453).  For `F ∈ C_b(h¹)` put `G = F ∘ SC_t ∈ C_b(h¹)`.  Along the standard
exhaustion `ν_{Λ_N} ⇀ μ_W` (S04.04) for both `F` and `G`; since `(S_t)_# ν_Λ = ν_Λ` and
`physH 1 ∘ S_t = SC_t ∘ physH 1` `ν_Λ`-a.e. (finite-gap fields are smooth),
`∫ G dν_{Λ_N} = ∫ F dν_{Λ_N}` for every `N`, so the limits agree:
`∫ F(SC_t(physH u)) dμ_W = ∫ F(physH u) dμ_W`.  Because `μ_W` is carried by `H¹`,
`physH 1 ∘ S_t = SC_t ∘ physH 1` `μ_W`-a.e., and C2a (`map_eq_of_carrier_invariance`) upgrades the
carrier identity to `(S_t)_# μ_W = μ_W` on `PhysicalL2`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.SpectralFoundations NlsGge.Weights
  NlsGge.Sobolev38 NlsGge.NLS38 Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace BirkhoffTop38

variable (B : BirkhoffTop38) (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
  (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper)

include hlower hbound hupper

/-- INTERNAL lemma (not S04): abstract `S` with a continuous carrier model `SC`.

If `S` is measurable, preserves `H¹`, is modelled on `H¹` by a continuous `SC t`
(`physH38 1 (S t u) = SC t (physH38 1 u)` for `u ∈ H¹`), and preserves every finite-gap law
`ν_Λ`, then it preserves `μ_W`.  (Sobolev indices are `((1 : ℕ) : ℝ)`, plan §6.0.) -/
theorem muW_invariant_aux (S : ℝ → PhysicalL2 → PhysicalL2) (hmeas : ∀ t, Measurable (S t))
    (SC : ℝ → SobolevCarrier38 ((1 : ℕ) : ℝ) → SobolevCarrier38 ((1 : ℕ) : ℝ))
    (hSC : ∀ t, Continuous (SC t))
    (hcompat : ∀ t u, fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ) →
      physH38 1 (S t u) = SC t (physH38 1 u))
    (hH1 : ∀ t u, fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ) →
      fourierSeq38 (S t u) ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    (hinv : ∀ t Λ, (B.nu38 c Λ).map (S t) = B.nu38 c Λ) (t : ℝ) :
    (B.muW38 c).map (S t) = B.muW38 c := by
  have : IsProbabilityMeasure (B.muW38 c) :=
    B.isProbabilityMeasure_muW38 lower upper c hlower hbound hupper
  -- `μ_W`-a.e. and `ν_Λ`-a.e. fields lie in `H¹`
  have hmuH1 : ∀ᵐ u ∂(B.muW38 c), fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ) := by
    filter_upwards [B.ae_muW38_allSobolev lower upper c hlower hbound hupper] with u hu
    exact (fourierSeq38_mem_iff _ u).2 (hu 1)
  have hnuH1 : ∀ Λ : Finset ℤ, ∀ᵐ u ∂(B.nu38 c Λ), fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    fun Λ => by
      filter_upwards [B.ae_nu38_allSobolev c Λ] with u hu
      exact (fourierSeq38_mem_iff _ u).2 (hu 1)
  -- the carrier identity for bounded continuous `F`
  have hcar : ∀ F : SobolevCarrier38 ((1 : ℕ) : ℝ) →ᵇ ℝ,
      ∫ u, F (physH38 1 (S t u)) ∂(B.muW38 c) = ∫ u, F (physH38 1 u) ∂(B.muW38 c) := by
    intro F
    let G : SobolevCarrier38 ((1 : ℕ) : ℝ) →ᵇ ℝ := F.compContinuous ⟨SC t, hSC t⟩
    have hG : ∀ x, G x = F (SC t x) := fun x => rfl
    -- finite-gap level: `∫ G dν_Λ = ∫ F dν_Λ`
    have hfin : ∀ Λ : Finset ℤ, ∫ u, G (physH38 1 u) ∂(B.nu38 c Λ) =
        ∫ u, F (physH38 1 u) ∂(B.nu38 c Λ) := fun Λ => by
      have h1 : ∫ u, G (physH38 1 u) ∂(B.nu38 c Λ) =
          ∫ u, F (physH38 1 (S t u)) ∂(B.nu38 c Λ) := by
        refine integral_congr_ae ?_
        filter_upwards [hnuH1 Λ] with u hu
        rw [hG, hcompat t u hu]
      have h2 : ∫ u, F (physH38 1 (S t u)) ∂(B.nu38 c Λ) =
          ∫ u, F (physH38 1 u) ∂((B.nu38 c Λ).map (S t)) :=
        (integral_map (hmeas t).aemeasurable (measurable_comp_physH38 1 F).aestronglyMeasurable).symm
      rw [h1, h2, hinv t Λ]
    -- weak limits
    have hF := (B.weak_convergence_S04_38 lower upper c hlower hbound hupper
      isExhaustion_stdExh38).2 1 F
    have hGl := (B.weak_convergence_S04_38 lower upper c hlower hbound hupper
      isExhaustion_stdExh38).2 1 G
    simp_rw [hfin] at hGl
    have hlim : ∫ u, G (physH38 1 u) ∂(B.muW38 c) = ∫ u, F (physH38 1 u) ∂(B.muW38 c) :=
      tendsto_nhds_unique hGl hF
    -- `μ_W`-a.e. compatibility
    have hae : ∫ u, F (physH38 1 (S t u)) ∂(B.muW38 c) =
        ∫ u, G (physH38 1 u) ∂(B.muW38 c) := by
      refine integral_congr_ae ?_
      filter_upwards [hmuH1] with u hu
      rw [hG, hcompat t u hu]
    rw [hae, hlim]
  exact map_eq_of_carrier_invariance (S t) (hmeas t) (B.muW38 c) hmuH1 (hH1 t) hcar

/-- Regression probe: `S = id` (with `SC = id`) satisfies every hypothesis of `muW_invariant_aux`
(so the hypotheses are satisfiable), and the conclusion is `Measure.map_id`. -/
theorem muW_invariant_aux_id (t : ℝ) : (B.muW38 c).map (id : PhysicalL2 → PhysicalL2) = B.muW38 c :=
  B.muW_invariant_aux lower upper c hlower hbound hupper (fun _ => id) (fun _ => measurable_id)
    (fun _ => id) (fun _ => continuous_id) (fun _ _ _ => rfl) (fun _ _ h => h)
    (fun _ _ => Measure.map_id) t

end BirkhoffTop38

end NlsGge.Birkhoff
