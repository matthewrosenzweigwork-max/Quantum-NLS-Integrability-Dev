import NlsGge.Spectral.ActualQuasimomentumBoundaryFunctionE02_38
import NlsGge.Spectral.ActualQuasimomentumGapConstantE02_38
import NlsGge.Spectral.ActualQuasimomentumBandMonotoneE02_38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # Monotonicity of the boundary quasimomentum real part (E02.38) -/

/-- (1) `Δh² ≠ 1` on a punctured real neighbourhood. -/
theorem halfTrace_sq_ne_one_eventually_E02_38 (u : PhysicalL2) (x : ℝ) :
    ∀ᶠ y : ℝ in 𝓝[≠] x, actualPhysicalUnitHalfTrace32 u (y:ℂ) ^ 2 ≠ 1 := by
  have hA := analyticOnNhd_actualPhysicalUnitBranchRadicand32 u
  have hx := hA (x:ℂ) (Set.mem_univ _)
  rcases hx.eventually_eq_zero_or_eventually_ne_zero with h0 | h1
  · exfalso
    have h0' : (fun z => actualPhysicalUnitHalfTrace32 u z ^ 2 - 1) =ᶠ[𝓝 (x:ℂ)] 0 := by
      filter_upwards [h0] with z hz using hz
    have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ _) h0' (Set.mem_univ Complex.I)
    exact actualPhysicalUnitBranchRadicand_upperHalfPlane_nonzero32 u Complex.I (by simp) this
  · have ht : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] x) (𝓝[≠] (x:ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto x).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact fun h => hy (Complex.ofReal_injective h)
    have h2 := ht.eventually h1
    filter_upwards [h2] with y hy
    exact fun h => hy (by simp [h])

/-- (2) Constant real part near a gap point. -/
theorem exists_const_near_gap_E02_38 (u : PhysicalL2) (x₀ : ℝ)
    (h : 1 < ‖actualPhysicalUnitHalfTrace32 u (x₀:ℂ)‖) :
    ∃ r > 0, ∀ y ∈ Set.Ioo (x₀ - r) (x₀ + r),
      actualQuasimomentumRealPartE02_38 u y = actualQuasimomentumRealPartE02_38 u x₀ := by
  have hcont : Continuous (fun y : ℝ => actualPhysicalUnitHalfTrace32 u (y:ℂ)) :=
    (analyticOnNhd_actualPhysicalUnitHalfTrace32 u).continuousOn.comp_continuous
      Complex.continuous_ofReal (fun _ => Set.mem_univ _)
  have hev : ∀ᶠ y : ℝ in 𝓝 x₀, 1 < ‖actualPhysicalUnitHalfTrace32 u (y:ℂ)‖ :=
    (hcont.norm.continuousAt).eventually (lt_mem_nhds h)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hI : ∀ y ∈ Set.Ioo (x₀ - r) (x₀ + r), 1 < ‖actualPhysicalUnitHalfTrace32 u (y:ℂ)‖ := by
    intro y hy
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  set p : ℝ → ℝ := fun x => actualQuasimomentumRealPartE02_38 u x / Real.pi with hp
  have hpc : Continuous p := (continuous_actualQuasimomentumRealPartE02_38 u).div_const _
  have hint : ∀ y ∈ Set.Ioo (x₀ - r) (x₀ + r), ∃ n : ℤ, p y = (n:ℝ) := by
    intro y hy
    have hcos := actualQuasimomentumBoundaryE02_38_cos u y
    have him : (Complex.cos (actualQuasimomentumBoundaryE02_38 u y)).im = 0 := by
      rw [hcos]; exact actualPhysicalUnitHalfTrace32_ofReal_im_E02_38 u y
    rw [complex_cos_im_E02_38] at him
    have hv : actualGapHeightE02_38 u y ≠ 0 := by
      rw [Ne, actualGapHeightE02_38_eq_zero_iff]
      exact not_le.mpr (hI y hy)
    have hLim : (actualQuasimomentumBoundaryE02_38 u y).im = actualGapHeightE02_38 u y :=
      boundaryLimit_im_E02_38 u y _ (tendsto_actualQuasimomentumBoundaryE02_38 u y)
    have hsinh : Real.sinh (actualQuasimomentumBoundaryE02_38 u y).im ≠ 0 := by
      rw [hLim]; exact fun h => hv (Real.sinh_eq_zero.mp h)
    have hsin : Real.sin (actualQuasimomentumBoundaryE02_38 u y).re = 0 := by
      have : Real.sin (actualQuasimomentumBoundaryE02_38 u y).re *
          Real.sinh (actualQuasimomentumBoundaryE02_38 u y).im = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hsinh
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
    refine ⟨n, ?_⟩
    simp only [hp, actualQuasimomentumRealPartE02_38]
    rw [← hn]; field_simp [Real.pi_ne_zero]
  have hd : IsDiscrete (range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range
  have hm : MapsTo p (Set.Ioo (x₀ - r) (x₀ + r)) (range ((↑) : ℤ → ℝ)) := by
    intro y hy
    obtain ⟨n, hn⟩ := hint y hy
    exact ⟨n, hn.symm⟩
  obtain ⟨v, -, hconst⟩ := isPreconnected_Ioo.eqOn_const_of_mapsTo hd hpc.continuousOn hm
    (show (range ((↑) : ℤ → ℝ)).Nonempty from ⟨0, 0, by simp⟩)
  refine ⟨r, hr, fun y hy => ?_⟩
  have h0 : x₀ ∈ Set.Ioo (x₀ - r) (x₀ + r) := ⟨by linarith, by linarith⟩
  have h1 := hconst hy
  have h2 := hconst h0
  simp only [hp] at h1 h2
  have := h1.trans h2.symm
  field_simp [Real.pi_ne_zero] at this
  exact this

/-- Generic local-to-global monotonicity on an open order-connected set. -/
theorem monotoneOn_of_locally_monotoneOn_E02_38 (f : ℝ → ℝ) (hf : Continuous f)
    (s : Set ℝ) (hs : s.OrdConnected)
    (hloc : ∀ x ∈ s, ∃ r > 0, MonotoneOn f (Set.Ioo (x - r) (x + r))) :
    MonotoneOn f s := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hlt
  · exact le_rfl
  have hcl : IsClosed {t : ℝ | f x ≤ f t} := isClosed_le continuous_const hf
  have key : Set.Icc x y ⊆ {t : ℝ | f x ≤ f t} := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin (s := {t : ℝ | f x ≤ f t}) (a := x) (b := y) (hcl.inter isClosed_Icc) ?_ ?_
    · exact le_refl (f x)
    · intro t ht
      have hts : t ∈ s := hs.out hx hy ⟨ht.2.1, ht.2.2.le⟩
      obtain ⟨r, hr, hmono⟩ := hloc t hts
      have : Set.Ioo t (t + r) ∈ 𝓝[>] t := Ioo_mem_nhdsGT (by linarith)
      filter_upwards [this] with t' ht'
      have := hmono (show t ∈ Set.Ioo (t - r) (t + r) from ⟨by linarith, by linarith⟩)
        (show t' ∈ Set.Ioo (t - r) (t + r) from ⟨by linarith [ht'.1], ht'.2⟩) ht'.1.le
      exact le_trans ht.1 this
  exact key ⟨hxy, le_rfl⟩

/-- (3), conditional on the band statement. -/
theorem monotone_of_band_E02_38 (u : PhysicalL2)
    (hband : ∀ (x₀ : ℝ), ‖actualPhysicalUnitHalfTrace32 u (x₀:ℂ)‖ < 1 →
      ∃ r > 0, MonotoneOn (actualQuasimomentumRealPartE02_38 u) (Set.Ioo (x₀ - r) (x₀ + r))) :
    Monotone (actualQuasimomentumRealPartE02_38 u) := by
  set f := actualQuasimomentumRealPartE02_38 u with hfdef
  have hf : Continuous f := continuous_actualQuasimomentumRealPartE02_38 u
  -- non-critical points
  have hnc : ∀ y : ℝ, ‖actualPhysicalUnitHalfTrace32 u (y:ℂ)‖ ≠ 1 →
      ∃ r > 0, MonotoneOn f (Set.Ioo (y - r) (y + r)) := by
    intro y hy
    rcases lt_or_gt_of_ne hy with hlt | hgt
    · exact hband y hlt
    · obtain ⟨r, hr, hc⟩ := exists_const_near_gap_E02_38 u y hgt
      refine ⟨r, hr, fun a ha b hb _ => ?_⟩
      simp only [hfdef]
      rw [hc a ha, hc b hb]
  have hloc : ∀ x : ℝ, ∃ r > 0, MonotoneOn f (Set.Ioo (x - r) (x + r)) := by
    intro x
    by_cases hx : ‖actualPhysicalUnitHalfTrace32 u (x:ℂ)‖ = 1
    · have hev : ∀ᶠ y : ℝ in 𝓝[≠] x, actualPhysicalUnitHalfTrace32 u (y:ℂ) ^ 2 ≠ 1 := halfTrace_sq_ne_one_eventually_E02_38 u x
      have hev' : ∀ᶠ y : ℝ in 𝓝[≠] x, ‖actualPhysicalUnitHalfTrace32 u (y:ℂ)‖ ≠ 1 := by
        filter_upwards [hev] with y hy h1
        apply hy
        have him := actualPhysicalUnitHalfTrace32_ofReal_im_E02_38 u y
        have hre : actualPhysicalUnitHalfTrace32 u (y:ℂ) =
            ((actualPhysicalUnitHalfTrace32 u (y:ℂ)).re : ℂ) :=
          Complex.ext (by simp) (by simp [him])
        rw [hre] at h1 ⊢
        rw [Complex.norm_real, Real.norm_eq_abs] at h1
        rw [← Complex.ofReal_pow, ← sq_abs, h1]; simp
      rw [eventually_nhdsWithin_iff] at hev'
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev'
      have hbx : ∀ y ∈ Set.Ioo (x - r) (x + r), y ≠ x →
          ∃ r' > 0, MonotoneOn f (Set.Ioo (y - r') (y + r')) := by
        intro y hy hne
        apply hnc
        apply hball y _ hne
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hy.1, hy.2]
      have hL : MonotoneOn f (Set.Ioo (x - r) x) :=
        monotoneOn_of_locally_monotoneOn_E02_38 f hf _ ordConnected_Ioo
          (fun y hy => hbx y ⟨hy.1, by linarith [hy.2]⟩ hy.2.ne)
      have hR : MonotoneOn f (Set.Ioo x (x + r)) :=
        monotoneOn_of_locally_monotoneOn_E02_38 f hf _ ordConnected_Ioo
          (fun y hy => hbx y ⟨by linarith [hy.1], hy.2⟩ hy.1.ne')
      have hLx : ∀ a ∈ Set.Ioo (x - r) x, f a ≤ f x := by
        intro a ha
        refine ge_of_tendsto ((hf.tendsto x).mono_left (nhdsWithin_le_nhds (s := Set.Iio x))) ?_
        filter_upwards [Ioo_mem_nhdsLT ha.2] with t ht using hL ha ⟨by linarith [ha.1, ht.1], ht.2⟩ ht.1.le
      have hRx : ∀ b ∈ Set.Ioo x (x + r), f x ≤ f b := by
        intro b hb
        refine le_of_tendsto ((hf.tendsto x).mono_left (nhdsWithin_le_nhds (s := Set.Ioi x))) ?_
        filter_upwards [Ioo_mem_nhdsGT hb.1] with t ht using hR ⟨ht.1, by linarith [hb.2, ht.2]⟩ hb ht.2.le
      refine ⟨r, hr, fun a ha b hb hab => ?_⟩
      rcases lt_trichotomy a x with h1 | h1 | h1 <;> rcases lt_trichotomy b x with h2 | h2 | h2
      · exact hL ⟨ha.1, h1⟩ ⟨hb.1, h2⟩ hab
      · subst h2; exact hLx a ⟨ha.1, h1⟩
      · exact (hLx a ⟨ha.1, h1⟩).trans (hRx b ⟨h2, hb.2⟩)
      · exact absurd (hab.trans_lt h2) (by linarith)
      · subst h1; subst h2; exact le_rfl
      · subst h1; exact hRx b ⟨h2, hb.2⟩
      · exact absurd (hab.trans_lt h2) (by linarith)
      · exact absurd (h1.trans_le hab |>.trans_eq h2) (lt_irrefl _)
      · exact hR ⟨h1, ha.2⟩ ⟨h2, hb.2⟩ hab
    · exact hnc x hx
  exact monotoneOn_univ.mp (monotoneOn_of_locally_monotoneOn_E02_38 f hf _ ordConnected_univ
    (fun x _ => hloc x))

/-- (3) The boundary quasimomentum real part is monotone. -/
theorem monotone_actualQuasimomentumRealPartE02_38 (u : PhysicalL2) :
    Monotone (actualQuasimomentumRealPartE02_38 u) :=
  monotone_of_band_E02_38 u (fun x₀ h => exists_monotoneOn_band_E02_38 u x₀ h)



end NlsGge.SpectralFoundations
end
