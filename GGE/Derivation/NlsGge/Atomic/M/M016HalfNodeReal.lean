import Mathlib
import NlsGge.Atomic.M.M010Support1
import NlsGge.Atomic.M.M009Support8
import NlsGge.Atomic.M.M051Host
import NlsGge.ThirdConsultation.KSPS.KSPS031Analytic
import NlsGge.ThirdConsultation.KSPS.KSPS031Host
import NlsGge.GK38.PairRealBridge
import NlsGge.Spectral.ActualQuasimomentumBoundaryFunctionE02_38

/- M-016 REAL HALF-NODE IDENTIFICATION, PRODUCTION02 (proof development, AUTHOR; not self-reviewed, not accepted).
   SUPPORT (no packet increment). Target NlsGge/Atomic/M/M016HalfNodeReal.lean, namespace
   NlsGge.ThirdConsultation.M016H.
   Real form of Pro round 16 §1.1 `exterior_primitive_halfNode_eq` (the complex form needs the complex
   primitive_discriminant_identity, owned elsewhere).  For a real potential realSlice u, an exterior representative F
   (given here by the unfolded second conjunct of ExteriorPrimitiveRepresentative, so the core does not import the
   pending M-052 host) with F z + i z → 0 at ∞, and any Sobolev lift ψ with toPotPair ψ = realSlice u: for all large
   |j| the KSPS chart condition holds at the half-node and F(halfNode j) = KSPSWKB.primitive N ψ ⟨(j, halfNode j), _⟩.
   Route (Pro §3 step 6, real case, no new estimate): on the real exterior F = −i kb (landed MPrimitive.primitive_formulas,
   boundary branch kb = actualQuasimomentumBoundaryE02_38), Δ = 2 cos kb (landed discrim_realSlice +
   actualQuasimomentumBoundaryE02_38_cos), δ := kb − halfNode → 0 from the value at infinity, and the landed chart
   comparison KSPS031Analytic.chart_core with D = 2 cos θ (error 0) gives the arcsinh chart value −i kb. -/
set_option autoImplicit false
open Filter Topology
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.M016H

/-- A value at infinity gives a uniform bound outside a large disc. -/
theorem eventually_large (f : ℂ → ℂ) (a : ℂ) (h : MPrimitive.HasValueAtInfinity f a)
    (ε : ℝ) (hε : 0 < ε) : ∃ R1 : ℝ, 0 < R1 ∧ ∀ z : ℂ, R1 < ‖z‖ → ‖f z - a‖ < ε := by
  have h2 := h.eventually (Metric.ball_mem_nhds a hε)
  unfold MPrimitive.infinityFilter at h2
  rw [Filter.eventually_comap, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h2
  obtain ⟨r, hr, hball⟩ := h2
  refine ⟨1 / r, by positivity, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hz; linarith [show 0 < 1 / r by positivity]
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hinv : dist z⁻¹ 0 < r := by
    rw [dist_zero_right, norm_inv]
    exact (inv_lt_comm₀ hzpos hr).2 (by rwa [one_div] at hz)
  have := hball hinv (inv_ne_zero hz0) z rfl
  rwa [dist_eq_norm] at this

theorem halfNode_real (u : PhysicalL2) (R : ℝ) (F : ℂ → ℂ)
    (hrep : ∀ z : ℂ, R < ‖z‖ →
      ∃ hz : realSlice u ∈ gkW ∧ z ∈ MPrimitive.endpointClosureFiber (realSlice u),
        F z = NlsGge.ThirdConsultation.M.primitive ⟨(realSlice u, z), hz⟩)
    (hval : MPrimitive.HasValueAtInfinity (fun z : ℂ => F z + Complex.I * z) 0)
    (N : ℕ) (ψ : KSPS.SobolevC N) (hψ : KSPS.toPotPair ψ = realSlice u) :
    ∃ J : ℕ, ∀ j : ℤ, J ≤ j.natAbs →
      ∃ hchart : KSPSWKB.NonresonantBranchDomain ψ j (KSPSWKB.halfNode j),
        F (KSPSWKB.halfNode j) = KSPSWKB.primitive N ψ ⟨(j, KSPSWKB.halfNode j), hchart⟩ := by
  obtain ⟨R1, -, hb⟩ := eventually_large _ 0 hval (Real.pi / 8) (by positivity)
  obtain ⟨J, hJ⟩ := exists_nat_gt (max R R1)
  refine ⟨J, fun j hj => ?_⟩
  set x : ℝ := ((j : ℝ) + 1 / 2) * Real.pi with hx_def
  have hxz : (x : ℂ) = ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) := by rw [hx_def]; push_cast; ring
  have hnorm : max R R1 < ‖(x : ℂ)‖ := by
    rw [hxz]
    refine lt_of_lt_of_le hJ (le_trans ?_ (NlsGge.ThirdConsultation.KSPS031Analytic.natAbs_le_norm_halfNode_expr j))
    exact_mod_cast hj
  obtain ⟨hz, hFz⟩ := hrep (x : ℂ) (lt_of_le_of_lt (le_max_left _ _) hnorm)
  set θ : ℂ := actualQuasimomentumBoundaryE02_38 u x with hθ_def
  have hFx : F (x : ℂ) = -Complex.I * θ := by
    rw [hFz]
    exact (MPrimitive.primitive_formulas u).2.2 x hz.2
  have hδ : ‖θ - ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)‖ < Real.pi / 8 := by
    have h := hb (x : ℂ) (lt_of_le_of_lt (le_max_right _ _) hnorm)
    rw [sub_zero, hFx] at h
    have e : -Complex.I * θ + Complex.I * (x : ℂ) =
        -Complex.I * (θ - ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ)) := by rw [hxz]; ring
    rw [e, norm_mul, norm_neg, Complex.norm_I, one_mul] at h
    exact h
  set D : ℂ := KSPS.discriminant ψ (KSPSWKB.halfNode j) with hD_def
  have hDθ : D = 2 * Complex.cos θ := by
    rw [hD_def]
    unfold KSPS.discriminant
    rw [hψ, show KSPSWKB.halfNode j = (x : ℂ) by rw [hxz]; rfl, discrim_realSlice,
      hθ_def, actualQuasimomentumBoundaryE02_38_cos]
  obtain ⟨δ, hδθ⟩ : ∃ δ : ℂ, θ = ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) + δ :=
    ⟨θ - ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ), by ring⟩
  have hδ' : ‖δ‖ < Real.pi / 8 := by
    have : δ = θ - ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) := by rw [hδθ]; ring
    rw [this]; exact hδ
  have hDhalf : ‖D / 2‖ < 1 / 2 := by
    rw [hDθ, show 2 * Complex.cos θ / 2 = Complex.cos θ by ring, hδθ,
      NlsGge.ThirdConsultation.KSPS031Analytic.cos_halfNode_add, norm_neg, norm_mul,
      NlsGge.ThirdConsultation.KSPS031Analytic.norm_neg_one_zpow, one_mul]
    exact NlsGge.ThirdConsultation.KSPS031Analytic.norm_sin_lt_half hδ'
  have hchart : KSPSWKB.NonresonantBranchDomain ψ j (KSPSWKB.halfNode j) := by
    refine ⟨?_, hDhalf⟩
    rw [sub_self, norm_zero]; positivity
  refine ⟨hchart, ?_⟩
  have hcc := NlsGge.ThirdConsultation.KSPS031Analytic.chart_core j D θ hDhalf hδ
  rw [hDθ, sub_self, norm_zero, mul_zero] at hcc
  have hzero := norm_le_zero_iff.1 hcc
  have hhalf : KSPSWKB.halfNode j = (x : ℂ) := by rw [hxz]; rfl
  have hFh : F (KSPSWKB.halfNode j) = -Complex.I * θ := by rw [hhalf]; exact hFx
  rw [hFh]
  show -Complex.I * θ = -Complex.I * KSPSWKB.halfNode j +
    Complex.log (Complex.I * (-1 : ℂ) ^ j * KSPS.discriminant ψ (KSPSWKB.halfNode j) / 2 +
      Complex.sqrt (1 + (Complex.I * (-1 : ℂ) ^ j * KSPS.discriminant ψ (KSPSWKB.halfNode j) / 2) ^ 2))
  rw [← hD_def, hDθ]
  have e : KSPSWKB.halfNode j = ((j : ℂ) + (1 / 2 : ℂ)) * (Real.pi : ℂ) := rfl
  rw [e]
  linear_combination -hzero

end NlsGge.ThirdConsultation.M016H
