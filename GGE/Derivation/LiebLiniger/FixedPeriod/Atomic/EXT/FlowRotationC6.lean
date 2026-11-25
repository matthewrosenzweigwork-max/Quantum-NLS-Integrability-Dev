import LiebLiniger.FixedPeriod.Atomic.EXT.FlowRotationC5

/-! # The actual Birkhoff NLS-flow input

The same global measurable family constructed from the finite-support strata
works for every finite-support physical datum. The actual inverse identifies
its finite-plane initial field; exact support conservation handles all indices
outside that plane.
-/

set_option autoImplicit false
noncomputable section
namespace LiebLiniger.FixedPeriod.EXT

open NlsGge.Pilot NlsGge.Birkhoff NlsGge.NLS38

local notation "B0" =>
  NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.toBirkhoffTop38

/-- The actual spectral Birkhoff map intertwines the actual NLS flow with
one globally product-Borel action-dependent rotation on every finite-support
datum. There is no additional flow or frequency hypothesis. -/
theorem actualBirkhoffNLSFlowInput38 :
    BirkhoffNLSFlowInput38
      NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.toBirkhoffTop38 nlsFlowL2 := by
  classical
  obtain ⟨Ω, hmeas, hΩ⟩ := exists_measurable_finiteGap_frequencies38
  constructor
  refine ⟨Ω, hmeas, ?_⟩
  intro u hfin t n
  let Λ : Finset ℤ := hfin.toFinset
  let w : Λ → ℂ := fun i => (B0).Φ u i.1
  have hz (k : ℤ) (hk : k ∉ Λ) : (B0).Φ u k = 0 := by
    by_contra h
    exact hk (hfin.mem_toFinset.mpr h)
  have he : extZero38 Λ w = (B0).Φ u := by
    funext k
    by_cases hk : k ∈ Λ
    · rw [extZero38_apply_of_mem _ hk]
    · rw [extZero38_apply_of_not_mem _ hk, hz k hk]
  have hf : (B0).finiteGapField38 Λ w = u := by
    unfold BirkhoffTop38.finiteGapField38
    rw [he]
    exact (B0).cleanΦinv_Φ38 u
  by_cases hn : n ∈ Λ
  · have hr := finiteGap_actualRotation38 Ω hΩ Λ w t ⟨n, hn⟩
    simpa only [ZΛ, hf, he, w] using hr
  · have h0 := hz n hn
    have ht : (B0).Φ (nlsFlowL2 t u) n = 0 := by
      by_contra h
      have hs : n ∈ {k | (B0).Φ (nlsFlowL2 t u) k ≠ 0} := h
      rw [actualPhi_support_nlsFlow38 u hfin t] at hs
      exact hs h0
    rw [ht, h0, mul_zero]

end LiebLiniger.FixedPeriod.EXT
