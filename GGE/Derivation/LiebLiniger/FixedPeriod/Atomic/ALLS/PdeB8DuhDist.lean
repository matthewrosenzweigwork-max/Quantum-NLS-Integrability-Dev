import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB8Pair

/-! # Track B, contract 6, direction `IsHm1Duhamel ⇒ IsDistributionalNLS`

For a test function `φ`, both strip integrals of the approved `IsDistributionalNLS` are expanded
into Fourier modes in `x` (`strip_series`); mode by mode, the coefficient form of the `H⁻¹`
Duhamel identity (`isHm1Duhamel_iff_intA`) and integration by parts in `t` (`ibp_primitive`)
identify them.
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff
set_option autoImplicit false
noncomputable section

attribute [local instance] isProbabilityMeasure_spatial

theorem cf_const_mul (c : ℂ) (f : ℝ → ℂ) (m : ℤ) : cf (fun x => c * f x) m = c * cf f m := by
  unfold cf
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  ring

theorem cT_L {φ : ℝ × ℝ → ℂ} (hφ : IsSpacetimeTest φ) (m : ℤ) (t : ℝ) :
    cT (fun p => Dx (Dx φ) p - Complex.I * Dt φ p) m t =
      -((disp (-m) : ℝ) : ℂ) * cT φ m t - Complex.I * cT (Dt φ) m t := by
  have hc1 : Continuous fun x => Dx (Dx φ) (t, x) :=
    hφ.dx.dx.continuous.comp (continuous_const.prodMk continuous_id)
  have hc2 : Continuous fun x => Complex.I * Dt φ (t, x) :=
    continuous_const.mul (hφ.dt.continuous.comp (continuous_const.prodMk continuous_id))
  have h1 := cf_sub hc1 hc2 m
  unfold cT
  rw [h1, cf_const_mul, disp_neg]
  have h2 := cT_DxDx hφ m t
  unfold cT at h2
  rw [h2]

theorem continuous_freePhase_t (n : ℤ) : Continuous fun t => freePhase t n :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_freePhase n t).continuousAt

/-- One Fourier mode of the distributional identity, from the Duhamel identity. -/
theorem mode_duh {u : ℝ → PhysicalL2} {U : ℝ × PhysicalCircle → ℂ} (hU : IsSpacetimeRep u U)
    (h4 : IsL4Loc U) (hD : IsHm1Duhamel u U) {φ : ℝ × ℝ → ℂ} (hφ : IsSpacetimeTest φ) (m : ℤ) :
    ∫ t, cT (fun p => Dx (Dx φ) p - Complex.I * Dt φ p) m t *
        physicalFourier (fun y => U (t, y)) (-m) =
      ∫ t, cT φ m t * physicalFourier (fun y => cubicNL (U (t, y))) (-m) := by
  set n : ℤ := -m with hn
  have hae : ∀ᵐ t ∂(volume : Measure ℝ),
      cT (fun p => Dx (Dx φ) p - Complex.I * Dt φ p) m t *
        physicalFourier (fun y => U (t, y)) n =
      (-((disp n : ℝ) : ℂ) * cT φ m t - Complex.I * cT (Dt φ) m t) * physicalFourier (u t) n := by
    filter_upwards [hU.slice] with t ht
    rw [cT_L hφ m t, physicalFourier_congr_ae ht]
  rw [integral_congr_ae hae, mode_lhs_eq u n (cT φ m) (cT (Dt φ) m), mode_rhs_eq U n (cT φ m)]
  obtain ⟨T, hT⟩ := hφ.compact_time
  have hψ : ∀ t, HasDerivAt (fun s => cT φ m s * freePhase s n)
      (cT (Dt φ) m t * freePhase t n + cT φ m t * (-((disp n : ℝ) : ℂ) * Complex.I * freePhase t n))
      t := fun t => (cT_hasDerivAt hφ m t).mul (hasDerivAt_freePhase n t)
  have hψ' : Continuous fun t => cT (Dt φ) m t * freePhase t n +
      cT φ m t * (-((disp n : ℝ) : ℂ) * Complex.I * freePhase t n) :=
    ((continuous_cT hφ.dt m).mul (continuous_freePhase_t n)).add
      ((continuous_cT hφ m).mul (continuous_const.mul (continuous_freePhase_t n)))
  have hTv : ∀ t, T < |t| → cT φ m t * freePhase t n = 0 := fun t ht => by
    rw [cT_eq_zero hT m ht, zero_mul]
  have ha := (isHm1Duhamel_iff_intA h4).1 hD n
  have key := ibp_primitive (intervalIntegrable_intG_loc h4 n) ha hψ hψ' hTv
  rw [key]
  ring

/-- **Duhamel ⇒ distributional** (direction `⇐` of approved contract 6). -/
theorem isDistributionalNLS_of_duhamel {u : ℝ → PhysicalL2} {U : ℝ × PhysicalCircle → ℂ}
    (hU : IsSpacetimeRep u U) (h4 : IsL4Loc U) (hD : IsHm1Duhamel u U) :
    IsDistributionalNLS U := by
  intro φ hφ
  have hL : IsSpacetimeTest (fun p => Dx (Dx φ) p - Complex.I * Dt φ p) :=
    hφ.dx.dx.sub_smul hφ.dt Complex.I
  have hlhs : (fun p : ℝ × ℝ => U (p.1, (p.2 : PhysicalCircle)) *
      (iteratedDeriv 2 (fun y => φ (p.1, y)) p.2 -
        Complex.I * deriv (fun s => φ (s, p.2)) p.1)) =
      fun p : ℝ × ℝ => U (p.1, (p.2 : PhysicalCircle)) *
        (Dx (Dx φ) p - Complex.I * Dt φ p) := by
    funext p
    rw [iteratedDeriv_two_eq, deriv_t_eq]
  obtain ⟨hi1, he1⟩ := strip_series (isSlabInt_of_isL4Loc h4) hL
  obtain ⟨hi2, he2⟩ := strip_series (isSlabInt_cubic h4) hφ
  simp only
  rw [hlhs]
  refine ⟨hi1, hi2, ?_⟩
  rw [he1, he2]
  exact tsum_congr fun m => mode_duh hU h4 hD hφ m

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
