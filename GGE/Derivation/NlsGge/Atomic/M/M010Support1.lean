import Mathlib
import NlsGge.Atomic.M.M010Host
import NlsGge.GK38.ActionBranchQuotientReflection
import NlsGge.GK38.MolnarLocalizationA
import NlsGge.GK38.RealTypeSpectrumLevels
import NlsGge.Spectral.ActualGapHeightSemicircleE02_38

/- M-010 SUPPORT01 (proof development, AUTHOR; not reviewed).  Local formulas for the symmetric primitive of a real potential
   in terms of the quasimomentum: sym = -I k on the upper half plane, = -I conj k(conj z) on the lower one,
   = -I k(x+i0) at every real point of the endpoint-filled fiber.  Route: M009 (P, L) with the limit property
   (copy of the proof of `symmetric_value_data`, with the extra limit conjunct), KO/GK38 primitive_hasDeriv_upper and
   discrim_deriv_div_root_lower (landed), uniqueness of primitives on connected half planes, and the base normalization
   k(lamMinus 0 + i0) = 0.  No hypothesis added. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.MPrimitive
noncomputable section
attribute [local instance] Classical.propDecidable

theorem lam_im_zero (u : PhysicalL2) (n : ℤ) :
    (lamMinus (realSlice u) n).im = 0 ∧ (lamPlus (realSlice u) n).im = 0 := by
  obtain ⟨h1, h2⟩ := lamPlus_real u n
  rw [h2, h1]; simp

theorem segment_im_zero (u : PhysicalL2) (n : ℤ) {z : ℂ}
    (hz : z ∈ segment ℝ (lamMinus (realSlice u) n) (lamPlus (realSlice u) n)) : z.im = 0 := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  obtain ⟨h1, h2⟩ := lam_im_zero u n
  simp only [Complex.add_im, Complex.smul_im, h1, h2, smul_zero, add_zero]

theorem nonreal_mem_cutFreeFiber (u : PhysicalL2) {z : ℂ} (hz : z.im ≠ 0) :
    z ∈ cutFreeFiber (realSlice u) := by
  intro h
  have h' : z ∈ ⋃ n : ℤ, segment ℝ (lamMinus (realSlice u) n) (lamPlus (realSlice u) n) := h
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h'
  exact hz (segment_im_zero u n hn)

theorem kb_im (u : PhysicalL2) (x : ℝ) :
    (actualQuasimomentumBoundaryE02_38 u x).im = actualGapHeightE02_38 u x :=
  boundaryLimit_im_E02_38 u x _ (tendsto_actualQuasimomentumBoundaryE02_38 u x)

theorem height_eq_zero_of_perChar (u : PhysicalL2) (x : ℝ)
    (h : perChar (realSlice u) (x : ℂ) = 0) : actualGapHeightE02_38 u x = 0 := by
  rw [actualGapHeightE02_38_eq_zero_iff]
  rw [perChar_eq, discrim_realSlice] at h
  have hsq : actualPhysicalUnitHalfTrace32 u (x : ℂ) ^ 2 = 1 := by
    linear_combination h / 4
  have hn : ‖actualPhysicalUnitHalfTrace32 u (x : ℂ)‖ ^ 2 = 1 := by
    rw [← norm_pow, hsq, norm_one]
  nlinarith [norm_nonneg (actualPhysicalUnitHalfTrace32 u (x : ℂ))]

theorem kb_gap_endpoint (u : PhysicalL2) (n : ℤ) :
    actualQuasimomentumBoundaryE02_38 u (actualGapLowerAllE02_38 u n) = ((n : ℝ) * Real.pi : ℝ) ∧
    actualQuasimomentumBoundaryE02_38 u (actualGapUpperAllE02_38 u n) = ((n : ℝ) * Real.pi : ℝ) := by
  obtain ⟨-, hl, hu⟩ := gap_endpoint_levels38 u n
  obtain ⟨hrl, hru⟩ := gap_endpoint_roots38 u n
  have e1 := height_eq_zero_of_perChar u _ hrl
  have e2 := height_eq_zero_of_perChar u _ hru
  constructor
  · apply Complex.ext
    · simpa [actualQuasimomentumRealPartE02_38] using hl
    · rw [kb_im, e1]; simp
  · apply Complex.ext
    · simpa [actualQuasimomentumRealPartE02_38] using hu
    · rw [kb_im, e2]; simp

theorem exists_const_eq_add {s : Set ℂ} (hs : IsOpen s) (hc : IsPreconnected s) (hne : s.Nonempty)
    {P g w : ℂ → ℂ}
    (hP : ∀ z ∈ s, HasDerivAt P (w z) z) (hg : ∀ z ∈ s, HasDerivAt g (w z) z) :
    ∃ c : ℂ, ∀ z ∈ s, P z = g z + c := by
  obtain ⟨y0, hy0⟩ := hne
  refine ⟨P y0 - g y0, fun z hz => ?_⟩
  have hd : ∀ z ∈ s, HasDerivAt (fun y => P y - g y) 0 z := by
    intro z hz
    have := (hP z hz).sub (hg z hz)
    rwa [sub_self] at this
  have h := hs.is_const_of_deriv_eq_zero hc (f := fun y => P y - g y)
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hd y hy).deriv) hz hy0
  have h' : P z - g z = P y0 - g y0 := h
  linear_combination h'

theorem symmetric_value_data_lim (φ : PotPair) (hφ : φ ∈ gkW) :
    ∃ (P L : ℂ → ℂ),
      (∀ z ∈ cutFreeFiber φ, HasDerivAt P (MContour.omega φ z) z) ∧
      (∀ z ∈ endpointClosureFiber φ, Tendsto P (𝓝[cutFreeFiber φ] z) (𝓝 (L z))) ∧
      ∀ (z : ℂ) (hz : z ∈ endpointClosureFiber φ),
        symmetricPrimitive ⟨(φ, z), ⟨hφ, hz⟩⟩ = L z - L (lamMinus φ 0) := by
  obtain ⟨P, hP⟩ := fiber_omega_primitive φ hφ
  obtain ⟨L, hLspec, hLchain⟩ := fiber_primitive_chain_values φ hφ hP
  have hbase : L (lamMinus φ 0) = L (lamPlus φ 0) :=
    fiber_primitive_gap_values_eq φ hφ hP 0 (hLspec _ (lower_endpoint_mem φ 0))
      (hLspec _ (upper_endpoint_mem φ 0))
  have hbe : ∀ upper : Bool, baseEndpoint φ upper ∈ endpointClosureFiber φ := by
    intro upper
    cases upper
    · rw [baseEndpoint_false]; exact lower_endpoint_mem φ 0
    · rw [baseEndpoint_true]; exact upper_endpoint_mem φ 0
  have hchain : ∀ (z : ℂ), z ∈ endpointClosureFiber φ → ∀ (upper : Bool) (m : ℕ)
      (c : Fin (m + 1) → ℝ → ℂ), AdmissiblePrimitiveChain φ (baseEndpoint φ upper) z m c →
      MContour.HasFiniteChainIntegral φ m c (L z - L (lamMinus φ 0)) := by
    intro z hz upper m c hc
    have h := hLchain _ _ (hbe upper) hz m c hc
    cases upper
    · rw [baseEndpoint_false] at h; exact h
    · rw [baseEndpoint_true, ← hbase] at h; exact h
  have hex : ∀ (z : ℂ), z ∈ endpointClosureFiber φ → ∀ (upper : Bool),
      HasBaseEndpointIntegral φ upper z (L z - L (lamMinus φ 0)) := by
    intro z hz upper
    obtain ⟨m, p, hp⟩ := exists_admissible_chain φ hφ (hbe upper) hz
    exact ⟨m, p, hp, hchain z hz upper m p hp⟩
  have hsym : ∀ z ∈ endpointClosureFiber φ,
      HasSymmetricPrimitiveValue φ z (L z - L (lamMinus φ 0)) := by
    intro z hz
    refine ⟨hφ, hz, L z - L (lamMinus φ 0), L z - L (lamMinus φ 0), hex z hz false, hex z hz true, ?_⟩
    ring
  exact ⟨P, L, hP, hLspec, fun z hz => symmetric_primitive_value_eq hφ hsym z hz⟩

theorem tendsto_conj_lower (x : ℝ) :
    Tendsto (fun z : ℂ => conj z) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h := (Complex.continuous_conj.tendsto (x : ℂ)).mono_left
      (nhdsWithin_le_nhds (s := {z : ℂ | z.im < 0}))
    simpa using h
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using hz

theorem upper_nhdsWithin_neBot (x : ℝ) : (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_upperHalfPlane_E02_38 (by simp))

theorem lower_nhdsWithin_neBot (x : ℝ) : (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)).NeBot := by
  apply mem_closure_iff_nhdsWithin_neBot.mp
  rw [Complex.closure_setOfPred_im_lt]
  simp

theorem primitive_formulas (u : PhysicalL2) :
    (∀ (z : ℂ) (hz : 0 < z.im),
      symmetricPrimitive ⟨(realSlice u, z),
        ⟨realSlice_mem_gkW u, Or.inl (nonreal_mem_cutFreeFiber u hz.ne')⟩⟩
        = -Complex.I * actualQuasimomentumE02_38 u z) ∧
    (∀ (z : ℂ) (hz : z.im < 0),
      symmetricPrimitive ⟨(realSlice u, z),
        ⟨realSlice_mem_gkW u, Or.inl (nonreal_mem_cutFreeFiber u hz.ne)⟩⟩
        = -Complex.I * conj (actualQuasimomentumE02_38 u (conj z))) ∧
    (∀ (x : ℝ) (hx : (x : ℂ) ∈ endpointClosureFiber (realSlice u)),
      symmetricPrimitive ⟨(realSlice u, (x : ℂ)), ⟨realSlice_mem_gkW u, hx⟩⟩
        = -Complex.I * actualQuasimomentumBoundaryE02_38 u x) := by
  have hφ : realSlice u ∈ gkW := realSlice_mem_gkW u
  obtain ⟨P, L, hP, hL, hsym⟩ := symmetric_value_data_lim (realSlice u) hφ
  set k := actualQuasimomentumE02_38 u with hk_def
  have hbr := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  set a0 : ℝ := actualGapLowerAllE02_38 u 0 with ha0
  have he0 : lamMinus (realSlice u) 0 = (a0 : ℂ) := (lamPlus_real u 0).2
  have hkb0 : actualQuasimomentumBoundaryE02_38 u a0 = 0 := by
    have := (kb_gap_endpoint u 0).1
    simpa using this
  have hLP : ∀ z ∈ cutFreeFiber (realSlice u), L z = P z := by
    intro z hz
    haveI := fiber_neBot (realSlice u) hφ (Or.inl hz : z ∈ endpointClosureFiber (realSlice u))
    exact tendsto_nhds_unique (hL z (Or.inl hz))
      ((hP z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hHpo : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hHmo : IsOpen {z : ℂ | z.im < 0} := isOpen_lt Complex.continuous_im continuous_const
  have hHpc : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  have hHmc : IsPreconnected {z : ℂ | z.im < 0} := (convex_halfSpace_im_lt (0 : ℝ)).isPreconnected
  have hfibp : ∀ z : ℂ, 0 < z.im → z ∈ cutFreeFiber (realSlice u) :=
    fun z hz => nonreal_mem_cutFreeFiber u hz.ne'
  have hfibm : ∀ z : ℂ, z.im < 0 → z ∈ cutFreeFiber (realSlice u) :=
    fun z hz => nonreal_mem_cutFreeFiber u hz.ne
  -- upper half plane: P = -I k + c
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ z ∈ {z : ℂ | 0 < z.im}, P z = -Complex.I * k z + c := by
    refine exists_const_eq_add hHpo hHpc ⟨Complex.I, by simp⟩
      (g := fun z => -Complex.I * k z) (w := MContour.omega (realSlice u))
      (fun z hz => hP z (hfibp z hz)) (fun z hz => ?_)
    exact (NlsGge.GK38.ActionBranch.primitive_hasDeriv_upper u z hz)
  -- lower half plane: P = -I conj k(conj z) + c'
  obtain ⟨c', hc'⟩ : ∃ c' : ℂ, ∀ z ∈ {z : ℂ | z.im < 0},
      P z = -Complex.I * conj (k (conj z)) + c' := by
    refine exists_const_eq_add hHmo hHmc ⟨-Complex.I, by simp⟩
      (g := fun z => -Complex.I * conj (k (conj z))) (w := MContour.omega (realSlice u))
      (fun z hz => hP z (hfibm z hz)) (fun z hz => ?_)
    have hzc : 0 < (conj z).im := by simpa using hz
    have hkd : HasDerivAt k (deriv k (conj z)) (conj z) :=
      (hbr.1 (conj z) hzc).differentiableAt.hasDerivAt
    have hcc := hkd.conj_conj
    rw [Complex.conj_conj] at hcc
    have h2 := hcc.const_mul (-Complex.I)
    have h3 := NlsGge.GK38.ActionBranch.discrim_deriv_div_root_lower u z hz
    exact h2.congr_deriv (by
      show -Complex.I * conj (deriv k (conj z)) = MContour.omega (realSlice u) z
      unfold MContour.omega
      rw [h3])
  -- the constants equal L e0
  have hLe : Tendsto P (𝓝[cutFreeFiber (realSlice u)] (a0 : ℂ)) (𝓝 (L (a0 : ℂ))) := by
    have := hL (lamMinus (realSlice u) 0) (lower_endpoint_mem (realSlice u) 0)
    rw [he0] at this
    exact this
  have hLe_eq : L (a0 : ℂ) = L (lamMinus (realSlice u) 0) := by rw [he0]
  have hcL : c = L (a0 : ℂ) := by
    haveI := upper_nhdsWithin_neBot a0
    have h1 : Tendsto P (𝓝[{z : ℂ | 0 < z.im}] (a0 : ℂ)) (𝓝 (L (a0 : ℂ))) :=
      hLe.mono_left (nhdsWithin_mono _ (fun z hz => hfibp z hz))
    have h2 : Tendsto (fun z => -Complex.I * k z + c) (𝓝[{z : ℂ | 0 < z.im}] (a0 : ℂ))
        (𝓝 (-Complex.I * actualQuasimomentumBoundaryE02_38 u a0 + c)) :=
      ((tendsto_actualQuasimomentumBoundaryE02_38 u a0).const_mul (-Complex.I)).add_const c
    have h3 : Tendsto P (𝓝[{z : ℂ | 0 < z.im}] (a0 : ℂ))
        (𝓝 (-Complex.I * actualQuasimomentumBoundaryE02_38 u a0 + c)) :=
      h2.congr' (eventually_nhdsWithin_of_forall fun z hz => (hc z hz).symm)
    have := tendsto_nhds_unique h1 h3
    rw [hkb0] at this
    simpa using this.symm
  have hc'L : c' = L (a0 : ℂ) := by
    haveI := lower_nhdsWithin_neBot a0
    have h1 : Tendsto P (𝓝[{z : ℂ | z.im < 0}] (a0 : ℂ)) (𝓝 (L (a0 : ℂ))) :=
      hLe.mono_left (nhdsWithin_mono _ (fun z hz => hfibm z hz))
    have hk1 : Tendsto (fun z : ℂ => k (conj z)) (𝓝[{z : ℂ | z.im < 0}] (a0 : ℂ))
        (𝓝 (actualQuasimomentumBoundaryE02_38 u a0)) :=
      (tendsto_actualQuasimomentumBoundaryE02_38 u a0).comp (tendsto_conj_lower a0)
    have h2 : Tendsto (fun z => -Complex.I * conj (k (conj z)) + c')
        (𝓝[{z : ℂ | z.im < 0}] (a0 : ℂ))
        (𝓝 (-Complex.I * conj (actualQuasimomentumBoundaryE02_38 u a0) + c')) :=
      (((Complex.continuous_conj.tendsto _).comp hk1).const_mul (-Complex.I)).add_const c'
    have h3 : Tendsto P (𝓝[{z : ℂ | z.im < 0}] (a0 : ℂ))
        (𝓝 (-Complex.I * conj (actualQuasimomentumBoundaryE02_38 u a0) + c')) :=
      h2.congr' (eventually_nhdsWithin_of_forall fun z hz => (hc' z hz).symm)
    have := tendsto_nhds_unique h1 h3
    rw [hkb0] at this
    simpa using this.symm
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [hsym z (Or.inl (hfibp z hz)), ← hLe_eq, hLP z (hfibp z hz), hc z hz, ← hcL]
    ring
  · intro z hz
    rw [hsym z (Or.inl (hfibm z hz)), ← hLe_eq, hLP z (hfibm z hz), hc' z hz, ← hc'L]
    ring
  · intro x hx
    haveI := upper_nhdsWithin_neBot x
    have h1 : Tendsto P (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (L (x : ℂ))) :=
      (hL (x : ℂ) hx).mono_left (nhdsWithin_mono _ (fun z hz => hfibp z hz))
    have h2 : Tendsto (fun z => -Complex.I * k z + c) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
        (𝓝 (-Complex.I * actualQuasimomentumBoundaryE02_38 u x + c)) :=
      ((tendsto_actualQuasimomentumBoundaryE02_38 u x).const_mul (-Complex.I)).add_const c
    have h3 : Tendsto P (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
        (𝓝 (-Complex.I * actualQuasimomentumBoundaryE02_38 u x + c)) :=
      h2.congr' (eventually_nhdsWithin_of_forall fun z hz => (hc z hz).symm)
    have h4 := tendsto_nhds_unique h1 h3
    rw [hsym (x : ℂ) hx, ← hLe_eq, h4, ← hcL]
    ring

end
end NlsGge.ThirdConsultation.MPrimitive
