import Mathlib
import NlsGge.Atomic.M.M010Support2

/- M-010 PRODUCTION01 (proof development, AUTHOR; not reviewed).  Head VERBATIM from Pro round 14
   (PRO_DEFINITION_RESPONSE_FP80_14.md, "### M-010").  Source: Molnar Lemma 3(ii)-(iv).
   Route: the boundary values of the primitive are -I k(x+i0) / -I conj k(x+i0) (M010Support2); on the closed labelled gap
   k(x+i0) = n pi + i v (level set = Icc, Im k(x+i0) = v), at gap endpoints v = 0 (perChar = 0), and for the free potential
   k(x+i0) = x.  The endpoint primitive value is -I k(x+i0) (M010Support1.primitive_formulas, third clause).
   `M.openGap` is the AllN body (see M010HOST_PRODUCTION01 comment / M010_NOTES.md). -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.M010Aux
noncomputable section

theorem kb_closedGap (u : PhysicalL2) (n : ℤ) (x : ℝ) (hx : x ∈ M.closedGap u n) :
    actualQuasimomentumBoundaryE02_38 u x =
      (((n : ℝ) * Real.pi : ℝ) : ℂ) + (actualGapHeightE02_38 u x : ℂ) * Complex.I := by
  have hlev : x ∈ actualGapLevelSetE02_38 u n := by
    rw [(actualGapLevelSet_eq_Icc_E02_38 u n).2]; exact hx
  apply Complex.ext
  · have : actualQuasimomentumRealPartE02_38 u x = (n : ℝ) * Real.pi := hlev
    simpa [actualQuasimomentumRealPartE02_38] using this
  · rw [MPrimitive.kb_im]; simp

theorem mem_endpointClosureFiber_zero (z : ℂ) :
    z ∈ MPrimitive.endpointClosureFiber (realSlice (0 : PhysicalL2)) := by
  by_cases hz : z ∈ MPrimitive.cutFreeFiber (realSlice (0 : PhysicalL2))
  · exact Or.inl hz
  · right
    have h' : z ∈ ⋃ n : ℤ, segment ℝ (lamMinus (realSlice (0 : PhysicalL2)) n)
        (lamPlus (realSlice (0 : PhysicalL2)) n) := by
      by_contra hn; exact hz hn
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h'
    refine ⟨n, Or.inl ?_⟩
    rw [realSlice_zero, lamMinus_zero38, lamPlus_zero38] at hn
    rw [realSlice_zero, lamMinus_zero38]
    rw [segment_same] at hn
    exact hn

end
end NlsGge.ThirdConsultation.M010Aux

namespace NlsGge.ThirdConsultation.M

theorem primitive_gap_values (u : PhysicalL2) (n : ℤ) :
    (∀ x : ℝ, x ∈ openGap u n →
      boundaryPrimitive u x true = (spectralHeight u n x : ℂ) -
        Complex.I * (((n : ℝ) * Real.pi : ℝ) : ℂ) ∧
      boundaryPrimitive u x false = -(spectralHeight u n x : ℂ) -
        Complex.I * (((n : ℝ) * Real.pi : ℝ) : ℂ)) ∧
    (∀ x : ℝ, x = periodicMinus u n ∨ x = periodicPlus u n →
      spectralHeight u n x = 0 ∧
      boundaryPrimitive u x true = -Complex.I * (((n : ℝ) * Real.pi : ℝ) : ℂ) ∧
      boundaryPrimitive u x false = -Complex.I * (((n : ℝ) * Real.pi : ℝ) : ℂ) ∧
      ∃ hx : realSlice u ∈ gkW ∧
          (x : ℂ) ∈ MPrimitive.endpointClosureFiber (realSlice u),
        primitive ⟨(realSlice u, (x : ℂ)), hx⟩ =
          -Complex.I * (((n : ℝ) * Real.pi : ℝ) : ℂ)) ∧
    (∀ z : ℂ,
      ∃ hz : realSlice (0 : PhysicalL2) ∈ gkW ∧
          z ∈ MPrimitive.endpointClosureFiber (realSlice (0 : PhysicalL2)),
        primitive ⟨(realSlice (0 : PhysicalL2), z), hz⟩ = -Complex.I * z) ∧
    (∀ x : ℝ, ∀ upper : Bool,
      boundaryPrimitive (0 : PhysicalL2) x upper = -Complex.I * (x : ℂ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    have hcl : x ∈ closedGap u n := ⟨hx.1.le, hx.2.le⟩
    have hkb := M010Aux.kb_closedGap u n x hcl
    unfold boundaryPrimitive spectralHeight
    refine ⟨?_, ?_⟩
    · rw [MPrimitive.boundaryValue_true, hkb]
      linear_combination (-(actualGapHeightE02_38 u x : ℂ)) * Complex.I_sq
    · rw [MPrimitive.boundaryValue_false, hkb]
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      linear_combination ((actualGapHeightE02_38 u x : ℂ)) * Complex.I_sq
  · intro x hx
    have hxe : x = actualGapLowerAllE02_38 u n ∨ x = actualGapUpperAllE02_38 u n := hx
    obtain ⟨hl, hu⟩ := MPrimitive.kb_gap_endpoint u n
    obtain ⟨hrl, hru⟩ := gap_endpoint_roots38 u n
    have hkb : actualQuasimomentumBoundaryE02_38 u x = (((n : ℝ) * Real.pi : ℝ) : ℂ) := by
      rcases hxe with rfl | rfl
      · exact hl
      · exact hu
    have hh : actualGapHeightE02_38 u x = 0 := by
      rcases hxe with rfl | rfl
      · exact MPrimitive.height_eq_zero_of_perChar u _ hrl
      · exact MPrimitive.height_eq_zero_of_perChar u _ hru
    have hmem : (x : ℂ) ∈ MPrimitive.endpointClosureFiber (realSlice u) := by
      right
      refine ⟨n, ?_⟩
      rcases hxe with rfl | rfl
      · exact Or.inl (lamPlus_real u n).2.symm
      · exact Or.inr (lamPlus_real u n).1.symm
    refine ⟨by unfold spectralHeight; exact hh, ?_, ?_, ⟨realSlice_mem_gkW u, hmem⟩, ?_⟩
    · unfold boundaryPrimitive; rw [MPrimitive.boundaryValue_true, hkb]
    · unfold boundaryPrimitive; rw [MPrimitive.boundaryValue_false, hkb]
      simp [Complex.conj_ofReal]
    · show MPrimitive.symmetricPrimitive _ = _
      rw [(MPrimitive.primitive_formulas u).2.2 x hmem, hkb]
  · intro z
    refine ⟨⟨realSlice_mem_gkW 0, M010Aux.mem_endpointClosureFiber_zero z⟩, ?_⟩
    show MPrimitive.symmetricPrimitive _ = _
    rcases lt_trichotomy z.im 0 with him | him | him
    · have h := (MPrimitive.primitive_formulas (0 : PhysicalL2)).2.1 z him
      rw [h, show actualQuasimomentumE02_38 0 (starRingEnd ℂ z) = starRingEnd ℂ z from
        quasimomentum_zero_eqOn38 (by simpa using him)]
      simp
    · obtain ⟨x, rfl⟩ : ∃ x : ℝ, z = (x : ℂ) := ⟨z.re, Complex.ext (by simp) (by simp [him])⟩
      rw [(MPrimitive.primitive_formulas (0 : PhysicalL2)).2.2 x (M010Aux.mem_endpointClosureFiber_zero _),
        quasimomentumBoundary_zero38]
    · have h := (MPrimitive.primitive_formulas (0 : PhysicalL2)).1 z him
      rw [h, show actualQuasimomentumE02_38 0 z = z from quasimomentum_zero_eqOn38 him]
  · intro x upper
    unfold boundaryPrimitive
    cases upper
    · rw [MPrimitive.boundaryValue_false, quasimomentumBoundary_zero38]
      simp [Complex.conj_ofReal]
    · rw [MPrimitive.boundaryValue_true, quasimomentumBoundary_zero38]

end NlsGge.ThirdConsultation.M
