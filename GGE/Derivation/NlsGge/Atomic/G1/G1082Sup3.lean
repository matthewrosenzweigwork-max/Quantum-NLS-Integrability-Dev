import Mathlib
import NlsGge.Atomic.G1.G1082Sup2
import NlsGge.GK38.RealTypeMultiplicityOrders
import NlsGge.GK38.RealTypeMultiplicityRealDeriv
import NlsGge.GK38.RealTypeMultiplicityWitnesses
import NlsGge.GK38.RealTypeSpectrumLevels
import NlsGge.Spectral.ActualGapActionAllNE02_38
import NlsGge.Spectral.ActualGapsActionsE02_38

/- G1-082 Sup3 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1082Sup3.lean.
   Gap-geometry facts and the assembled G1-082 head, CONDITIONAL on the explicit witness binder
   `hW : ∃ w : PhysicalL2, deltaMu w n ≠ 0` (not proved; see G1082_STOP.md).
   Facts proved: |Delta| > 2 strictly inside an open gap (semicircle bound + arcosh height), Delta = +-2 and Delta' != 0 at the
   endpoints of an open gap (order_at_gapEnd + perChar_order_one_noncritical38). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.Atomic.G1082Sup3
noncomputable section

theorem sq_gt_four_of_mem_open_gap (u : PhysicalL2) (n : ℤ) (x : ℝ)
    (hlo : actualGapLowerAllE02_38 u n < x) (hhi : x < actualGapUpperAllE02_38 u n) :
    4 < (discrim (realSlice u) (x : ℂ)).re ^ 2 := by
  have hs := actualGapHeight_ge_semicircle_all_E02_38 u n x ⟨hlo.le, hhi.le⟩
  have hpos : 0 < gapSemicircle (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) x :=
    Real.sqrt_pos.mpr (mul_pos (sub_pos.mpr hlo) (sub_pos.mpr hhi))
  have hh : actualGapHeightE02_38 u x ≠ 0 := (lt_of_lt_of_le hpos hs).ne'
  rw [Ne, actualGapHeightE02_38_eq_zero_iff, not_le] at hh
  have him := (dirichlet_real_characteristic38 u x).2.2
  have hnorm : ‖discrim (realSlice u) (x : ℂ)‖ = 2 * ‖actualPhysicalUnitHalfTrace32 u (x : ℂ)‖ := by
    rw [discrim_realSlice, norm_mul]; simp
  have habs : |(discrim (realSlice u) (x : ℂ)).re| = ‖discrim (realSlice u) (x : ℂ)‖ :=
    Complex.abs_re_eq_norm.mpr him
  have h2 : 2 < |(discrim (realSlice u) (x : ℂ)).re| := by rw [habs, hnorm]; linarith
  nlinarith [sq_abs (discrim (realSlice u) (x : ℂ)).re, abs_nonneg (discrim (realSlice u) (x : ℂ)).re]

theorem endpoint_values (u : PhysicalL2) (n : ℤ)
    (ho : actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n) (x : ℝ)
    (hx : x = actualGapLowerAllE02_38 u n ∨ x = actualGapUpperAllE02_38 u n) :
    (discrim (realSlice u) (x : ℂ)).re ^ 2 = 4 ∧
    (discrim (realSlice u) (x : ℂ) * deriv (discrim (realSlice u)) (x : ℂ)).re ≠ 0 := by
  have hv := gap_discrim_endpoint_values38 u n
  have hroot := gap_endpoint_roots38 u n
  have hc2 := real_cos_int_mul_pi_sq_E02_38 n
  have hcne : Real.cos ((n : ℝ) * Real.pi) ≠ 0 := by
    intro h; rw [h] at hc2; norm_num at hc2
  have hder : (deriv (discrim (realSlice u)) (x : ℂ)).im = 0 :=
    (discrim_realRestriction_deriv38 u x).2.2
  have hord : (x = actualGapLowerAllE02_38 u n →
      deriv (discrim (realSlice u)) (x : ℂ) ≠ 0) ∧
      (x = actualGapUpperAllE02_38 u n → deriv (discrim (realSlice u)) (x : ℂ) ≠ 0) := by
    constructor
    · intro h; subst h
      exact perChar_order_one_noncritical38 _ _ hroot.1 (by simpa only [ho, ite_true] using order_at_gapEnd u n)
    · intro h; subst h
      exact perChar_order_one_noncritical38 _ _ hroot.2 (by simpa only [ho, ite_true] using order_at_gapUpper38 u n)
  have hval : discrim (realSlice u) (x : ℂ) = 2 * (Real.cos ((n : ℝ) * Real.pi) : ℂ) := by
    rcases hx with h | h
    · rw [h]; exact hv.1
    · rw [h]; exact hv.2
  have hne : deriv (discrim (realSlice u)) (x : ℂ) ≠ 0 := by
    rcases hx with h | h
    · exact hord.1 h
    · exact hord.2 h
  have hre : (deriv (discrim (realSlice u)) (x : ℂ)).re ≠ 0 := by
    intro h0
    exact hne (Complex.ext h0 hder)
  have hDre : (discrim (realSlice u) (x : ℂ)).re = 2 * Real.cos ((n : ℝ) * Real.pi) := by
    rw [hval, show (2 : ℂ) * (Real.cos ((n : ℝ) * Real.pi) : ℂ) =
      ((2 * Real.cos ((n : ℝ) * Real.pi) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  refine ⟨?_, ?_⟩
  · rw [hDre]; nlinarith [hc2]
  · have him := (dirichlet_real_characteristic38 u x).2.2
    rw [Complex.mul_re, him, zero_mul, sub_zero, hDre]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hcne) hre

theorem deltaMu_flow_sq (n : ℤ) (u : PhysicalL2) (t : ℝ) :
    deltaMu (singleGapFlow n t u) n ^ 2 =
      (discrim (realSlice u) (gkMu (singleGapFlow n t u) n : ℂ)).re ^ 2 - 4 := by
  have h := deltaMu_squared38 (singleGapFlow n t u) n
  rw [NlsGge.Atomic.G1081Sup6.singleGapFlow_isospectral n t u (gkMu (singleGapFlow n t u) n : ℂ)] at h
  linarith

/-- The head of G1-082, conditional on the witness binder `hW`. -/
theorem G1_082_of_witness (n : ℤ) (hW : ∃ w : PhysicalL2, deltaMu w n ≠ 0) (u : PhysicalL2) :
    (∀ m : ℤ, m ≠ n → ∀ t : ℝ,
      gkMu (singleGapFlow n t u) m = gkMu u m) ∧
    (∀ t : ℝ,
      HasDerivAt (fun s : ℝ => gkMu (singleGapFlow n s u) n)
        (-(antiDiscrim (realSlice (singleGapFlow n t u))
          (gkMu (singleGapFlow n t u) n : ℂ)).re / 2) t) ∧
    (actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n →
      ∀ t : ℝ,
        HasDerivAt
          (fun s : ℝ => deriv (fun r : ℝ => gkMu (singleGapFlow n r u) n) s)
          ((discrim (realSlice u) (gkMu (singleGapFlow n t u) n : ℂ) *
            deriv (discrim (realSlice u))
              (gkMu (singleGapFlow n t u) n : ℂ)).re / 4) t ∧
        ((gkMu (singleGapFlow n t u) n = actualGapLowerAllE02_38 u n ∨
          gkMu (singleGapFlow n t u) n = actualGapUpperAllE02_38 u n) →
          deriv (deriv (fun r : ℝ => gkMu (singleGapFlow n r u) n)) t ≠ 0) ∧
        (actualGapLowerAllE02_38 u n < gkMu (singleGapFlow n t u) n →
          gkMu (singleGapFlow n t u) n < actualGapUpperAllE02_38 u n →
          deriv (fun r : ℝ => gkMu (singleGapFlow n r u) n) t ≠ 0)) := by
  refine ⟨fun m hm t => NlsGge.Atomic.G1082Sup1.gkMu_flow_other n m hm u t,
    fun t => ?_, fun ho t => ?_⟩
  · simpa using NlsGge.Atomic.G1082Sup1.hasDerivAt_gkMu_flow n n u t
  · have h3 := NlsGge.Atomic.G1082Sup2.hasDerivAt_deriv_gkMu_flow n hW u t
    refine ⟨h3, fun hend => ?_, fun hlo hhi => ?_⟩
    · rw [h3.deriv]
      have := (endpoint_values u n ho _ hend).2
      intro h0; apply this; linarith
    · rw [NlsGge.Atomic.G1082Sup1.deriv_gkMu_flow_self]
      have h4 := sq_gt_four_of_mem_open_gap u n _ hlo hhi
      have h5 := deltaMu_flow_sq n u t
      intro h0
      have h6 : deltaMu (singleGapFlow n t u) n = 0 := by
        have : (antiDiscrim (realSlice (singleGapFlow n t u)) (gkMu (singleGapFlow n t u) n : ℂ)).re = 0 := by
          linarith
        exact this
      rw [h6] at h5
      nlinarith [h5, h4]

end
end NlsGge.Atomic.G1082Sup3
