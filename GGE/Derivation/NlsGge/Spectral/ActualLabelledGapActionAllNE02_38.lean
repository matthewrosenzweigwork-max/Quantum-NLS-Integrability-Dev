import NlsGge.Spectral.ActualGapHeightSemicircleAllGapsE02_38
import NlsGge.Spectral.ActualQuasimomentumBoundaryFunctionE02_38
import NlsGge.Spectral.ActualQuasimomentumEndpointSqrtGeneralE02_38
import NlsGge.Spectral.ActualOppositeParityExclusionE02_38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # NEW-E01 for EVERY labelled gap `n ∈ ℤ` (campaign 38)

Labels: `g_n` is the closed level set `{x | p(x) = nπ}` of the nondecreasing boundary real part
`p = Re k(· + i0)`; it is a compact interval `[λ_n^-, λ_n^+]`, a point for a closed gap. The
open gap of the source is its interior. `Δh` is the half monodromy trace of the paper's `L_u`
(v2 Section 1 convention), so `k, p, v, g_n, I_n` here match v2 (A:eq:trace, F:eq:gapaction)
directly, with NO relabelling. A reflection `g_n ↦ -g_{-n}` arises only against the reflected
Dirac operator `𝖫_u = -L_{-u}` of v2 F:eq:Dirac (lines 1000-1012), which is the Schur/source
operator `actualSourcePerturbedDiracPMapAfterAE`; see `source_eigenvalue_neg_gapEndpoint_E02_38`. -/

def actualGapLevelSetE02_38 (u : PhysicalL2) (n : ℤ) : Set ℝ :=
  {x : ℝ | actualQuasimomentumRealPartE02_38 u x = (n:ℝ)*Real.pi}

def actualGapLowerAllE02_38 (u : PhysicalL2) (n : ℤ) : ℝ := sInf (actualGapLevelSetE02_38 u n)

def actualGapUpperAllE02_38 (u : PhysicalL2) (n : ℤ) : ℝ := sSup (actualGapLevelSetE02_38 u n)

/-- Source `I_n = (2/π)∫_{g_n} v` for every `n ∈ ℤ`. -/
def actualGapActionAllE02_38 (u : PhysicalL2) (n : ℤ) : ℝ :=
  (2/Real.pi) * ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
    actualGapHeightE02_38 u x

theorem actualGapLevelSet_eq_Icc_of_monotone_E02_38 (u : PhysicalL2)
    (hmono : Monotone (actualQuasimomentumRealPartE02_38 u)) (n : ℤ) :
    (actualGapLevelSetE02_38 u n).Nonempty ∧
    actualGapLevelSetE02_38 u n =
      Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
  set p := actualQuasimomentumRealPartE02_38 u
  have hp : Continuous p := continuous_actualQuasimomentumRealPartE02_38 u
  set c : ℝ := (n:ℝ)*Real.pi
  obtain ⟨R, hR, hb⟩ := actualQuasimomentumBoundaryE02_38_sub_le u 1 one_pos
  have hpx : ∀ x : ℝ, R ≤ |x| → |p x - x| ≤ 1 := by
    intro x hx
    have h := hb x hx
    have := Complex.abs_re_le_norm (actualQuasimomentumBoundaryE02_38 u x - x)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    exact this.trans h
  set L := -(|c| + R + 2)
  set H := |c| + R + 2
  have hL : p L < c := by
    have := hpx L (by rw [abs_of_neg (by simp only [L]; linarith [abs_nonneg c] : L < 0)]; simp only [L]; linarith [abs_nonneg c])
    linarith [(abs_le.mp this).2, neg_abs_le c]
  have hH : c < p H := by
    have := hpx H (by rw [abs_of_pos (by positivity : (0:ℝ) < H)]; simp only [H]; linarith [abs_nonneg c])
    linarith [(abs_le.mp this).1, le_abs_self c]
  have hLH : L ≤ H := by simp only [L, H]; linarith [abs_nonneg c]
  obtain ⟨x, -, hx⟩ := intermediate_value_Icc hLH hp.continuousOn ⟨hL.le, hH.le⟩
  have hne : (actualGapLevelSetE02_38 u n).Nonempty := ⟨x, hx⟩
  have hbdd : BddBelow (actualGapLevelSetE02_38 u n) := ⟨L, fun y hy => by
    by_contra h; push Not at h
    have := hmono h.le; rw [show p y = c from hy] at this; linarith⟩
  have hbddA : BddAbove (actualGapLevelSetE02_38 u n) := ⟨H, fun y hy => by
    by_contra h; push Not at h
    have := hmono h.le; rw [show p y = c from hy] at this; linarith⟩
  have hcl : IsClosed (actualGapLevelSetE02_38 u n) := isClosed_eq hp continuous_const
  refine ⟨hne, ?_⟩
  ext y
  constructor
  · intro hy; exact ⟨csInf_le hbdd hy, le_csSup hbddA hy⟩
  · rintro ⟨h1, h2⟩
    have ha : p (sInf (actualGapLevelSetE02_38 u n)) = c := hcl.csInf_mem hne hbdd
    have hb' : p (sSup (actualGapLevelSetE02_38 u n)) = c := hcl.csSup_mem hne hbddA
    show p y = c
    exact le_antisymm (by rw [← hb']; exact hmono h2) (by rw [← ha]; exact hmono h1)


/-- NEW-E01 for every labelled gap, from the three structural facts on `p` (monotonicity,
local constancy on gaps, isolated zeros of `Δh² - 1`). -/
theorem actualGapHeight_ge_semicircle_all_of_E02_38 (u : PhysicalL2)
    (hmono : Monotone (actualQuasimomentumRealPartE02_38 u))
    (hgapc : ∀ x₀ : ℝ, 1 < ‖actualPhysicalUnitHalfTrace32 u (x₀:ℂ)‖ → ∃ r > 0,
      ∀ y ∈ Set.Ioo (x₀ - r) (x₀ + r),
        actualQuasimomentumRealPartE02_38 u y = actualQuasimomentumRealPartE02_38 u x₀)
    (hiso : ∀ x : ℝ, ∀ᶠ y : ℝ in 𝓝[≠] x, actualPhysicalUnitHalfTrace32 u (y:ℂ) ^ 2 ≠ 1)
    (n : ℤ) :
    ∀ x ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      gapSemicircle (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) x ≤
        actualGapHeightE02_38 u x := by
  obtain ⟨hne, hIcc⟩ := actualGapLevelSet_eq_Icc_of_monotone_E02_38 u hmono n
  set a := actualGapLowerAllE02_38 u n
  set b := actualGapUpperAllE02_38 u n
  set p := actualQuasimomentumRealPartE02_38 u
  set κ := actualQuasimomentumBoundaryE02_38 u
  set Δ := actualPhysicalUnitHalfTrace32 u
  set c : ℝ := (n:ℝ)*Real.pi
  have hmem : ∀ x ∈ Set.Icc a b, p x = c := by
    intro x hx; rw [← hIcc] at hx; exact hx
  have hNe : ∀ x : ℝ, (𝓝[{z : ℂ | 0 < z.im}] (x:ℂ)).NeBot := fun x =>
    mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_upperHalfPlane_E02_38 (by simp))
  -- boundary value on the level set
  have hκ : ∀ x ∈ Set.Icc a b, κ x = (n:ℂ)*Real.pi + Complex.I*(actualGapHeightE02_38 u x : ℂ) := by
    intro x hx
    have him := boundaryLimit_im_E02_38 u x _ (tendsto_actualQuasimomentumBoundaryE02_38 u x)
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.ofReal_re,
        Complex.intCast_im, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
        zero_mul, one_mul]
      have := hmem x hx; simp only [p, actualQuasimomentumRealPartE02_38] at this
      simp only [κ]; linarith
    · simpa using him
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h]; simp [gapSemicircle, actualGapHeightE02_38_nonneg]
  rcases eq_or_lt_of_le hx.2 with h' | h'
  · rw [h']; simp [gapSemicircle, actualGapHeightE02_38_nonneg]
  have hab : a < b := lt_trans h h'
  -- endpoints: v = 0 there
  have hendv : ∀ e : ℝ, (e = a ∨ e = b) → actualGapHeightE02_38 u e = 0 := by
    intro e he
    apply (actualGapHeightE02_38_eq_zero_iff u e).mpr
    by_contra hgt; push Not at hgt
    obtain ⟨r, hr, hconst⟩ := hgapc e hgt
    have heI : e ∈ Set.Icc a b := by
      rcases he with he | he
      · rw [he]; exact ⟨le_rfl, hab.le⟩
      · rw [he]; exact ⟨hab.le, le_rfl⟩
    rcases he with he | he
    · have hy : e - r/2 ∈ Set.Icc a b := by
        rw [← hIcc]; show p (e - r/2) = c
        rw [hconst _ ⟨by linarith, by linarith⟩, hmem e heI]
      linarith [hy.1]
    · have hy : e + r/2 ∈ Set.Icc a b := by
        rw [← hIcc]; show p (e + r/2) = c
        rw [hconst _ ⟨by linarith, by linarith⟩, hmem e heI]
      linarith [hy.2]
  have hendlim : ∀ e : ℝ, (e = a ∨ e = b) →
      Tendsto (actualQuasimomentumE02_38 u) (𝓝[{z : ℂ | 0 < z.im}] (e:ℂ)) (𝓝 ((n:ℂ)*Real.pi)) ∧
      Δ e = (Real.cos ((n:ℝ)*Real.pi) : ℂ) := by
    intro e he
    have heI : e ∈ Set.Icc a b := by
      rcases he with he | he
      · rw [he]; exact ⟨le_rfl, hab.le⟩
      · rw [he]; exact ⟨hab.le, le_rfl⟩
    have hk0 : κ e = (n:ℂ)*Real.pi := by
      rw [hκ e heI, hendv e he]; simp
    refine ⟨by rw [← hk0]; exact tendsto_actualQuasimomentumBoundaryE02_38 u e, ?_⟩
    show actualPhysicalUnitHalfTrace32 u e = _
    rw [← actualQuasimomentumBoundaryE02_38_cos u e]
    show Complex.cos (κ e) = _
    rw [hk0, ← Complex.ofReal_intCast, ← Complex.ofReal_mul, ← Complex.ofReal_cos]
  have hgen : ∀ x₀ ∈ Set.Ioo a b, 1 < ‖Δ x₀‖ → gapSemicircle a b x₀ ≤ actualGapHeightE02_38 u x₀ := by
    intro x₀ hx₀ hD
    apply gapHeight_ge_semicircle_generic_E02_38 u n a b x₀ hx₀
    · intro y hy L hL
      have := tendsto_nhds_unique hL (tendsto_actualQuasimomentumBoundaryE02_38 u y)
      rw [this, show actualQuasimomentumBoundaryE02_38 u y = _ from hκ y ⟨hy.1.le, hy.2.le⟩]
      ring
    · exact actualQuasimomentum_sub_sq_le_of_tendsto_E02_38 u n a (hendlim a (Or.inl rfl)).2
        (hendlim a (Or.inl rfl)).1
    · exact actualQuasimomentum_sub_sq_le_of_tendsto_E02_38 u n b (hendlim b (Or.inr rfl)).2
        (hendlim b (Or.inr rfl)).1
    · exact hD
  -- density argument
  have hfc : Continuous (fun y => actualGapHeightE02_38 u y - gapSemicircle a b y) :=
    (continuous_actualGapHeightE02_38 u).sub (by unfold gapSemicircle; fun_prop)
  have hclosed : IsClosed {y : ℝ | 0 ≤ actualGapHeightE02_38 u y - gapSemicircle a b y} :=
    isClosed_le continuous_const hfc
  suffices hcl : x ∈ closure {y : ℝ | y ∈ Set.Ioo a b ∧ 1 < ‖Δ y‖} by
    have hsub : {y : ℝ | y ∈ Set.Ioo a b ∧ 1 < ‖Δ y‖} ⊆
        {y : ℝ | 0 ≤ actualGapHeightE02_38 u y - gapSemicircle a b y} := by
      intro y hy; have := hgen y hy.1 hy.2; simp only [Set.mem_setOf_eq]; linarith
    have := hclosed.closure_subset_iff.mpr hsub hcl
    simp only [Set.mem_setOf_eq] at this; linarith
  rw [mem_closure_iff_frequently]
  refine Frequently.filter_mono ?_ (nhdsWithin_le_nhds (s := {x}ᶜ))
  apply Eventually.frequently
  have hIoo : ∀ᶠ y in 𝓝[≠] x, y ∈ Set.Ioo a b :=
    nhdsWithin_le_nhds (Ioo_mem_nhds h h')
  filter_upwards [hiso x, hIoo] with y hy hyI
  refine ⟨hyI, ?_⟩
  -- on the level set, |Δ y| ≤ 1 forces Δ y = ±1
  by_contra hle; push Not at hle
  have hv : actualGapHeightE02_38 u y = 0 := (actualGapHeightE02_38_eq_zero_iff u y).mpr hle
  have hk0 : κ y = (n:ℂ)*Real.pi := by rw [hκ y ⟨hyI.1.le, hyI.2.le⟩, hv]; simp
  have hc := actualQuasimomentumBoundaryE02_38_cos u y
  apply hy
  show actualPhysicalUnitHalfTrace32 u y ^ 2 = 1
  rw [← hc]
  show Complex.cos (κ y) ^ 2 = 1
  rw [hk0, ← Complex.ofReal_intCast, ← Complex.ofReal_mul, ← Complex.ofReal_cos,
    ← Complex.ofReal_pow, real_cos_int_mul_pi_sq_E02_38, Complex.ofReal_one]

theorem actualGapAction_ge_sq_div_four_all_of_E02_38 (u : PhysicalL2)
    (hmono : Monotone (actualQuasimomentumRealPartE02_38 u))
    (hgapc : ∀ x₀ : ℝ, 1 < ‖actualPhysicalUnitHalfTrace32 u (x₀:ℂ)‖ → ∃ r > 0,
      ∀ y ∈ Set.Ioo (x₀ - r) (x₀ + r),
        actualQuasimomentumRealPartE02_38 u y = actualQuasimomentumRealPartE02_38 u x₀)
    (hiso : ∀ x : ℝ, ∀ᶠ y : ℝ in 𝓝[≠] x, actualPhysicalUnitHalfTrace32 u (y:ℂ) ^ 2 ≠ 1)
    (n : ℤ) :
    (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n)^2 / 4 ≤
      actualGapActionAllE02_38 u n := by
  obtain ⟨hne, hIcc⟩ := actualGapLevelSet_eq_Icc_of_monotone_E02_38 u hmono n
  set a := actualGapLowerAllE02_38 u n
  set b := actualGapUpperAllE02_38 u n
  have hab : a ≤ b := by
    obtain ⟨x, hx⟩ := hne; rw [hIcc] at hx; exact hx.1.trans hx.2
  have hsc : Continuous (gapSemicircle a b) := by unfold gapSemicircle; fun_prop
  have hint : ∫ x in a..b, gapSemicircle a b x ≤ ∫ x in a..b, actualGapHeightE02_38 u x :=
    intervalIntegral.integral_mono_on hab (hsc.intervalIntegrable a b)
      (intervalIntegrable_actualGapHeightE02_38 u a b)
      (actualGapHeight_ge_semicircle_all_of_E02_38 u hmono hgapc hiso n)
  rw [integral_gapSemicircle a b hab] at hint
  unfold actualGapActionAllE02_38
  have hpi := Real.pi_pos
  calc (b - a)^2/4 = (2/Real.pi) * ((Real.pi/8) * (b-a)^2) := by field_simp; ring
    _ ≤ (2/Real.pi) * ∫ x in a..b, actualGapHeightE02_38 u x :=
      mul_le_mul_of_nonneg_left hint (by positivity)


/-- The endpoints of every labelled gap are doubled-period eigenvalues: `Δh(λ_n^±) = cos(nπ)`
(closed gaps included). -/
theorem actualGapEndpoint_halfTrace_all_of_E02_38 (u : PhysicalL2)
    (hmono : Monotone (actualQuasimomentumRealPartE02_38 u))
    (hgapc : ∀ x₀ : ℝ, 1 < ‖actualPhysicalUnitHalfTrace32 u (x₀:ℂ)‖ → ∃ r > 0,
      ∀ y ∈ Set.Ioo (x₀ - r) (x₀ + r),
        actualQuasimomentumRealPartE02_38 u y = actualQuasimomentumRealPartE02_38 u x₀)
    (n : ℤ) :
    actualPhysicalUnitHalfTrace32 u (actualGapLowerAllE02_38 u n : ℂ) =
        (Real.cos ((n:ℝ)*Real.pi) : ℂ) ∧
    actualPhysicalUnitHalfTrace32 u (actualGapUpperAllE02_38 u n : ℂ) =
        (Real.cos ((n:ℝ)*Real.pi) : ℂ) := by
  obtain ⟨hne, hIcc⟩ := actualGapLevelSet_eq_Icc_of_monotone_E02_38 u hmono n
  set a := actualGapLowerAllE02_38 u n
  set b := actualGapUpperAllE02_38 u n
  set p := actualQuasimomentumRealPartE02_38 u
  set c : ℝ := (n:ℝ)*Real.pi
  have hab : a ≤ b := by obtain ⟨x, hx⟩ := hne; rw [hIcc] at hx; exact hx.1.trans hx.2
  have hmem : ∀ x ∈ Set.Icc a b, p x = c := by
    intro x hx; rw [← hIcc] at hx; exact hx
  have key : ∀ e : ℝ, e ∈ Set.Icc a b → (e = a ∨ e = b) →
      actualPhysicalUnitHalfTrace32 u (e:ℂ) = (Real.cos c : ℂ) := by
    intro e heI he
    have hv : actualGapHeightE02_38 u e = 0 := by
      apply (actualGapHeightE02_38_eq_zero_iff u e).mpr
      by_contra hgt; push Not at hgt
      obtain ⟨r, hr, hconst⟩ := hgapc e hgt
      rcases he with he | he
      · have hy : e - r/2 ∈ Set.Icc a b := by
          rw [← hIcc]; show p (e - r/2) = c
          rw [hconst _ ⟨by linarith, by linarith⟩, hmem e heI]
        linarith [hy.1]
      · have hy : e + r/2 ∈ Set.Icc a b := by
          rw [← hIcc]; show p (e + r/2) = c
          rw [hconst _ ⟨by linarith, by linarith⟩, hmem e heI]
        linarith [hy.2]
    have him := boundaryLimit_im_E02_38 u e _ (tendsto_actualQuasimomentumBoundaryE02_38 u e)
    have hk0 : actualQuasimomentumBoundaryE02_38 u e = ((c:ℝ):ℂ) := by
      apply Complex.ext
      · have := hmem e heI; simpa [p, actualQuasimomentumRealPartE02_38] using this
      · simp [him, hv]
    rw [← actualQuasimomentumBoundaryE02_38_cos u e, hk0, ← Complex.ofReal_cos]
  exact ⟨key a ⟨le_rfl, hab⟩ (Or.inl rfl), key b ⟨hab, le_rfl⟩ (Or.inr rfl)⟩

/-- Link with the reflected Dirac operator `𝖫_u = -L_{-u}` (v2 F:eq:Dirac), realized as the
sector-`n` operator `actualSourcePerturbedDiracPMapAfterAE n u (star u)`: `-λ_n^±` (the v2 labels
of `L_u`) are its eigenvalues. So the gap of `𝖫_u` labelled `n` in v2 Section F is `-(g_{-n})`;
the labels of `L_u` itself need no relabelling. -/
theorem source_eigenvalue_neg_gapEndpoint_E02_38 (u : PhysicalL2)
    (hmono : Monotone (actualQuasimomentumRealPartE02_38 u))
    (hgapc : ∀ x₀ : ℝ, 1 < ‖actualPhysicalUnitHalfTrace32 u (x₀:ℂ)‖ → ∃ r > 0,
      ∀ y ∈ Set.Ioo (x₀ - r) (x₀ + r),
        actualQuasimomentumRealPartE02_38 u y = actualQuasimomentumRealPartE02_38 u x₀)
    (n : ℤ) :
    (∃ X : TransportBridgeV4.recoveredActualSourceFreeWeightedDomain n, X.val ≠ 0 ∧
      actualSourcePerturbedDiracPMapAfterAE n u (star u) X =
        (-(actualGapLowerAllE02_38 u n : ℂ)) • X.val) ∧
    (∃ X : TransportBridgeV4.recoveredActualSourceFreeWeightedDomain n, X.val ≠ 0 ∧
      actualSourcePerturbedDiracPMapAfterAE n u (star u) X =
        (-(actualGapUpperAllE02_38 u n : ℂ)) • X.val) := by
  obtain ⟨hl, hu⟩ := actualGapEndpoint_halfTrace_all_of_E02_38 u hmono hgapc n
  constructor
  · rw [actualSourceEigenvalue_iff_halfTrace_E02_38, neg_neg, hl, spectralSign_eq_cos_E02_38]
  · rw [actualSourceEigenvalue_iff_halfTrace_E02_38, neg_neg, hu, spectralSign_eq_cos_E02_38]

end NlsGge.SpectralFoundations
end
