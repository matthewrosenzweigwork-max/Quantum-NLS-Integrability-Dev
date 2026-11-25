import NlsGge.Spectral.ActualQuasimomentumE02_38
import NlsGge.Spectral.ActualHalfTraceStripAsymptoticE02_38
import NlsGge.Spectral.ActualPhysicalUnitSmallRootCouplingContinuity36V1
import NlsGge.Spectral.ComplexQuadraticConnectedVacuumRootSelection36V2
import NlsGge.Spectral.ComplexQuadraticInsideUnitRootUnique36V1
import NlsGge.Batch37.ActualPhysicalVacuumInteractionHalfTrace37V2
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # E02.02 (campaign 38): full upper-half-plane normalization `k(z) - z → 0`

The conditional theorem takes the strip asymptotic of the actual half trace as an explicit
hypothesis (`ActualHalfTraceStripCosineAsymptoticE02_38`); it is realized concretely in
`ActualHalfTraceStripAsymptoticE02_38` (sub-target W1). -/

/-- Strip asymptotic of the actual half trace, uniform in coupling and bounded height. -/
def ActualHalfTraceStripCosineAsymptoticE02_38 (u : PhysicalL2) : Prop :=
  ∀ Y₀ : ℝ, 0 ≤ Y₀ → ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.cocompact ℝ,
    ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ Y ∈ Set.Icc (0:ℝ) Y₀,
      ‖actualPhysicalUnitHalfTrace32 ((τ:ℂ) • u) ((x:ℂ) + Complex.I*(Y:ℂ)) -
        Complex.cos ((x:ℂ) + Complex.I*(Y:ℂ))‖ < ε

/-- Integer constancy of a continuous logarithm on any preconnected set. -/
theorem complexLogarithm_integer_constant_preconnected_E02_38
    (S : Set ℂ) (hS : IsPreconnected S) (g : ℂ → ℂ) (hg : ContinuousOn g S)
    (he : ∀ z ∈ S, Complex.exp (g z) = 1) :
    ∃ m : ℤ, ∀ z ∈ S, g z = (m : ℂ)*(2*Real.pi*Complex.I) := by
  let p : ℂ → ℝ := fun Y => (g Y).im/(2*Real.pi)
  have hπ : (2 : ℝ)*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hperiod : ∀ Y ∈ S, ∃ n : ℤ, g Y=(n : ℂ)*(2*Real.pi*Complex.I) := by
    intro Y hY
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp
      ((he Y hY).trans Complex.exp_zero.symm)
    exact ⟨n, by simpa only [zero_add] using hn⟩
  have hscalar : ∀ (Y : ℂ) (n : ℤ), g Y=(n : ℂ)*(2*Real.pi*Complex.I) → p Y=(n : ℝ) := by
    intro Y n hn
    dsimp [p]
    rw [hn]
    simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.intCast_re, Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, mul_one, zero_add, add_zero, sub_zero]
    field_simp [hπ] <;> ring
  have hc : ContinuousOn p S :=
    (Complex.continuous_im.comp_continuousOn hg).div_const (2*Real.pi)
  have hd : IsDiscrete (range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range
  have hm : MapsTo p S (range ((↑) : ℤ → ℝ)) := by
    intro Y hY
    obtain ⟨n, hn⟩ := hperiod Y hY
    exact ⟨n, (hscalar Y n hn).symm⟩
  obtain ⟨v, ⟨m, rfl⟩, hconst⟩ := hS.eqOn_const_of_mapsTo hd hc hm
    (show (range ((↑) : ℤ → ℝ)).Nonempty from ⟨0, 0, by simp⟩)
  refine ⟨m, ?_⟩
  intro Y hY
  obtain ⟨n, hn⟩ := hperiod Y hY
  have hnm : n=m := by
    have hmcast : (n : ℝ)=(m : ℝ) := by
      simpa only [Function.const_apply] using (hscalar Y n hn).symm.trans (hconst hY)
    exact_mod_cast hmcast
  simpa only [hnm] using hn

/-- A continuous `g` on a preconnected set with `exp(i g)` uniformly `η`-close to one
(`η ≤ 1/2`) and `|g| < 1` at one point satisfies `|g| ≤ (3/2) η` everywhere. -/
theorem norm_le_of_exp_mul_I_near_one_E02_38
    (S : Set ℂ) (hS : IsPreconnected S) (g : ℂ → ℂ) (hg : ContinuousOn g S)
    (η : ℝ) (hη : η ≤ 1/2)
    (hnear : ∀ z ∈ S, ‖Complex.exp (Complex.I * g z) - 1‖ ≤ η)
    (z₁ : ℂ) (hz₁ : z₁ ∈ S) (hsmall : ‖g z₁‖ < 1) :
    ∀ z ∈ S, ‖g z‖ ≤ (3/2) * η := by
  let w : ℂ → ℂ := fun z => Complex.exp (Complex.I * g z)
  let L : ℂ → ℂ := fun z => Complex.log (w z)
  have hw : ContinuousOn w S :=
    Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hg)
  have hslit : ∀ z ∈ S, w z ∈ Complex.slitPlane := by
    intro z hz
    rw [Complex.mem_slitPlane_iff]
    left
    have h1 := hnear z hz
    have h2 : |(w z - 1).re| ≤ ‖w z - 1‖ := Complex.abs_re_le_norm _
    have h3 : (w z - 1).re = (w z).re - 1 := by simp
    rw [h3] at h2
    have := abs_le.mp (h2.trans h1)
    linarith
  have hL : ContinuousOn L S := hw.clog hslit
  have hLb : ∀ z ∈ S, ‖L z‖ ≤ (3/2) * η := by
    intro z hz
    have h := Complex.norm_log_one_add_half_le_self (z := w z - 1) ((hnear z hz).trans hη)
    simp only [add_sub_cancel] at h
    exact h.trans (by nlinarith [hnear z hz, norm_nonneg (w z - 1)])
  let h : ℂ → ℂ := fun z => Complex.I * g z - L z
  have hh : ContinuousOn h S := (continuousOn_const.mul hg).sub hL
  have hexp : ∀ z ∈ S, Complex.exp (h z) = 1 := by
    intro z hz
    simp only [h, L, Complex.exp_sub]
    rw [Complex.exp_log (Complex.exp_ne_zero _)]
    exact div_self (Complex.exp_ne_zero _)
  obtain ⟨m, hm⟩ := complexLogarithm_integer_constant_preconnected_E02_38 S hS h hh hexp
  have hgm : ∀ z ∈ S, g z - (m:ℂ)*(2*Real.pi) = -Complex.I * L z := by
    intro z hz
    have e := hm z hz
    simp only [h] at e
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (-Complex.I) * e + (g z - (m:ℂ)*(2*Real.pi)) * hI
  have hm0 : m = 0 := by
    by_contra hne
    have e := hgm z₁ hz₁
    have hn : ‖g z₁ - (m:ℂ)*(2*Real.pi)‖ ≤ 3/4 := by
      rw [e, norm_mul, norm_neg, Complex.norm_I, one_mul]
      exact (hLb z₁ hz₁).trans (by linarith)
    have hmn : ‖(m:ℂ)*(2*Real.pi)‖ = |(m:ℝ)| * (2*Real.pi) := by
      rw [norm_mul, Complex.norm_intCast]
      congr 1
      rw [show (2*(Real.pi:ℂ)) = ((2*Real.pi:ℝ):ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h1 : (1:ℝ) ≤ |(m:ℝ)| := by
      have : (1:ℤ) ≤ |m| := Int.one_le_abs hne
      exact_mod_cast this
    have htri : ‖(m:ℂ)*(2*Real.pi)‖ ≤ ‖g z₁‖ + ‖g z₁ - (m:ℂ)*(2*Real.pi)‖ := by
      calc ‖(m:ℂ)*(2*Real.pi)‖ = ‖g z₁ - (g z₁ - (m:ℂ)*(2*Real.pi))‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    rw [hmn] at htri
    nlinarith [Real.pi_gt_three]
  intro z hz
  have e := hgm z hz
  rw [hm0] at e
  simp only [Int.cast_zero, zero_mul, sub_zero] at e
  rw [e, norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact hLb z hz

/-- Coupling-path root selection: closeness of the actual half trace to `cos z` along the
whole real coupling path gives closeness of the Floquet multiplier `exp(i k)` to `exp(i z)`. -/
theorem norm_exp_actualQuasimomentum_sub_le_E02_38 (u : PhysicalL2) (z : ℂ)
    (hz : 0 < z.im) (δ : ℝ) (hδ : 0 ≤ δ)
    (htrace : ∀ τ ∈ Set.Icc (0:ℝ) 1,
      ‖actualPhysicalUnitHalfTrace32 ((τ:ℂ) • u) z - Complex.cos z‖ ≤ δ) :
    ‖Complex.exp (Complex.I * actualQuasimomentumE02_38 u z) - Complex.exp (Complex.I * z)‖ ≤
      3 * Real.sqrt (2*δ) := by
  obtain ⟨r, hr, hroot⟩ := actualPhysicalUnitSmallRoot_coupling_continuousExists36V1 u z hz
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  set k := actualQuasimomentumE02_38 u z with hkdef
  have hab : Complex.exp (Complex.I*z) * Complex.exp (-(Complex.I*z)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hsum : Complex.exp (Complex.I*z) + Complex.exp (-(Complex.I*z)) = 2 * Complex.cos z := by
    rw [Complex.cos]; ring_nf
  have hanorm : ‖Complex.exp (Complex.I*z)‖ < 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hz)
  have h0 : (((0:ℝ):ℂ) • u) = 0 := by simp
  have hstart : r 0 = Complex.exp (Complex.I*z) := by
    have h := hroot 0 (by simp)
    rw [h0, actualPhysicalUnitHalfTrace_zeroPotential37V2] at h
    exact complexQuadratic_vacuumInsideRoot36V1 (Complex.cos z) _ _ (r 0) hab hsum hanorm h.2 h.1
  have hdist := complexQuadratic_connectedVacuumRootDistance36V2 (Set.Icc (0:ℝ) 1)
    isPreconnected_Icc (fun τ => actualPhysicalUnitHalfTrace32 ((τ:ℂ) • u) z) r hr
    (Complex.cos z) (Complex.exp (Complex.I*z)) (Complex.exp (-(Complex.I*z))) δ hδ hab hsum
    (fun τ hτ => (hroot τ hτ).1) (fun τ hτ => (hroot τ hτ).2.le) htrace 0 (by simp) hstart
  have h1 : (((1:ℝ):ℂ) • u) = u := by simp
  have hend : r 1 = Complex.exp (Complex.I * k) := by
    have h := hroot 1 (by simp)
    rw [h1] at h
    have hkroot : Complex.exp (Complex.I*k)^2 - 2*actualPhysicalUnitHalfTrace32 u z *
        Complex.exp (Complex.I*k) + 1 = 0 := by
      rw [← hk.2.1 z hz, Complex.cos]
      have he : Complex.exp (Complex.I*k) * Complex.exp (-(Complex.I*k)) = 1 := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      rw [show k*Complex.I = Complex.I*k by ring, show -k*Complex.I = -(Complex.I*k) by ring]
      linear_combination -he
    have hknorm : ‖Complex.exp (Complex.I*k)‖ < 1 := by
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
      exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (hk.2.2.1 z hz))
    exact complexQuadratic_insideUnitRoot_unique36V1 _ _ _ h.1 hkroot h.2 hknorm
  have := hdist 1 (by simp)
  rwa [hend] at this

/-- Conditional full normalization: given the strip asymptotic, `k(z) - z → 0` as `|z| → ∞`
in the open upper half-plane. -/
theorem actualQuasimomentumE02_38_sub_tendsto_zero_of_strip (u : PhysicalL2)
    (hS : ActualHalfTraceStripCosineAsymptoticE02_38 u) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 0 < z.im → R ≤ ‖z‖ →
      ‖actualQuasimomentumE02_38 u z - z‖ < ε := by
  intro ε hε
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  set K := actualQuasimomentumE02_38 u with hKdef
  let η : ℝ := min (ε/2) (1/2)
  have hη0 : 0 < η := lt_min (by linarith) (by norm_num)
  have hηh : η ≤ 1/2 := min_le_right _ _
  have hηε : (3/2)*η < ε := by
    have : η ≤ ε/2 := min_le_left _ _
    linarith
  -- high height
  obtain ⟨R₁, hR₁, hhigh⟩ := hk.2.2.2 (η/2) (by linarith)
  have hzrep : ∀ z : ℂ, z = ((z.re:ℝ):ℂ) + Complex.I*((z.im:ℝ):ℂ) := by
    intro z; apply Complex.ext <;> simp
  have hhigh' : ∀ z : ℂ, R₁ ≤ z.im → ‖K z - z‖ < η/2 := by
    intro z hz
    have h := hhigh z.im hz z.re
    rwa [← hzrep z] at h
  -- strip
  let δ : ℝ := (η * Real.exp (-R₁) / 3)^2 / 2
  have hδ0 : 0 < δ := by positivity
  have hδb : 3 * Real.sqrt (2*δ) * Real.exp R₁ = η := by
    have h2 : 2*δ = (η * Real.exp (-R₁) / 3)^2 := by simp only [δ]; ring
    rw [h2, Real.sqrt_sq (by positivity)]
    rw [show 3 * (η * Real.exp (-R₁) / 3) * Real.exp R₁ = η * (Real.exp (-R₁) * Real.exp R₁)
      by ring, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hev := hS R₁ hR₁.le δ hδ0
  rw [cocompact_eq_atBot_atTop, eventually_sup] at hev
  obtain ⟨a, ha⟩ := eventually_atBot.mp hev.1
  obtain ⟨b, hb⟩ := eventually_atTop.mp hev.2
  let X : ℝ := max (max (-a) b) 0
  have hstrip : ∀ z : ℂ, 0 < z.im → z.im ≤ R₁ → X < |z.re| →
      ‖Complex.exp (Complex.I * (K z - z)) - 1‖ ≤ η := by
    intro z hz hzR hzX
    have hτ : ∀ τ ∈ Set.Icc (0:ℝ) 1,
        ‖actualPhysicalUnitHalfTrace32 ((τ:ℂ) • u) z - Complex.cos z‖ ≤ δ := by
      intro τ hτ
      have hmem : z.im ∈ Set.Icc (0:ℝ) R₁ := ⟨hz.le, hzR⟩
      rcases le_or_gt 0 z.re with hre | hre
      · have hx : b ≤ z.re := by
          have : b ≤ X := (le_max_right _ _).trans (le_max_left _ _)
          rw [abs_of_nonneg hre] at hzX; linarith
        have h := hb z.re hx τ hτ z.im hmem
        rw [← hzrep z] at h; exact h.le
      · have hx : z.re ≤ a := by
          have : -a ≤ X := (le_max_left _ _).trans (le_max_left _ _)
          rw [abs_of_neg hre] at hzX; linarith
        have h := ha z.re hx τ hτ z.im hmem
        rw [← hzrep z] at h; exact h.le
    have hc := norm_exp_actualQuasimomentum_sub_le_E02_38 u z hz δ hδ0.le hτ
    have hez : ‖Complex.exp (Complex.I*z)‖ = Real.exp (-z.im) := by
      rw [Complex.norm_exp]; simp
    have hfac : Complex.exp (Complex.I * (K z - z)) - 1 =
        (Complex.exp (Complex.I * K z) - Complex.exp (Complex.I * z)) *
          Complex.exp (-(Complex.I*z)) := by
      rw [sub_mul, ← Complex.exp_add, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      ring_nf
    rw [hfac, norm_mul]
    have hez' : ‖Complex.exp (-(Complex.I*z))‖ = Real.exp z.im := by
      rw [Complex.norm_exp]; simp
    rw [hez', ← hδb]
    apply mul_le_mul hc (Real.exp_le_exp.mpr hzR) (Real.exp_pos _).le (by positivity)
  -- integer argument on the two side regions
  have hside : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ z : ℂ, 0 < z.im → X < s * z.re →
      ‖K z - z‖ ≤ (3/2) * η := by
    intro s hs
    let S : Set ℂ := {z : ℂ | X < s * z.re} ∩ {z : ℂ | 0 < z.im}
    have hconv : Convex ℝ S := by
      apply Convex.inter
      · have : {z : ℂ | X < s * z.re} = (fun z : ℂ => s * z.re) ⁻¹' Set.Ioi X := rfl
        rw [this]
        exact (convex_Ioi X).linear_preimage
          ((s : ℝ) • (Complex.reLm : ℂ →ₗ[ℝ] ℝ))
      · exact convex_halfSpace_im_gt 0
    have hcont : ContinuousOn (fun z => K z - z) S :=
      (hk.1.continuousOn.mono (fun z hz => hz.2)).sub continuousOn_id
    have hnear : ∀ z ∈ S, ‖Complex.exp (Complex.I * (K z - z)) - 1‖ ≤ η := by
      intro z hz
      rcases le_or_gt R₁ z.im with hY | hY
      · have h := hhigh' z hY
        have h2 := Complex.norm_exp_sub_one_le (x := Complex.I * (K z - z))
          (by rw [norm_mul, Complex.norm_I, one_mul]; linarith)
        rw [norm_mul, Complex.norm_I, one_mul] at h2
        linarith
      · apply hstrip z hz.2 hY.le
        have hsz : X < s * z.re := hz.1
        rcases hs with rfl | rfl
        · rw [one_mul] at hsz; exact lt_of_lt_of_le hsz (le_abs_self _)
        · rw [neg_one_mul] at hsz; exact lt_of_lt_of_le hsz (neg_le_abs _)
    let z₁ : ℂ := (((X+1)*s : ℝ):ℂ) + Complex.I*((R₁:ℝ):ℂ)
    have hz₁ : z₁ ∈ S := by
      constructor
      · show X < s * z₁.re
        have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
        simp only [z₁, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
        have : s * ((X + 1) * s) = X + 1 := by
          rw [show s * ((X + 1) * s) = (X+1) * (s*s) by ring, hs2, mul_one]
        linarith
      · show 0 < z₁.im
        simp [z₁, hR₁]
    have hz₁s : ‖K z₁ - z₁‖ < 1 := by
      have := hhigh' z₁ (by simp [z₁])
      linarith
    intro z hz hzs
    exact norm_le_of_exp_mul_I_near_one_E02_38 S hconv.isPreconnected _ hcont η hηh hnear
      z₁ hz₁ hz₁s z ⟨hzs, hz⟩
  refine ⟨X + R₁ + 1, by positivity, ?_⟩
  intro z hz hzR
  rcases le_or_gt R₁ z.im with hY | hY
  · have := hhigh' z hY; linarith
  · have hre : X < |z.re| := by
      have hn : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos hz] at hn
      linarith
    rcases le_or_gt 0 z.re with h0 | h0
    · rw [abs_of_nonneg h0] at hre
      exact lt_of_le_of_lt (hside 1 (Or.inl rfl) z hz (by rwa [one_mul])) hηε
    · rw [abs_of_neg h0] at hre
      exact lt_of_le_of_lt (hside (-1) (Or.inr rfl) z hz (by rwa [neg_one_mul])) hηε

/-- The strip asymptotic hypothesis is realized for every actual rough potential. -/
theorem actualHalfTraceStripCosineAsymptoticE02_38_holds (u : PhysicalL2) :
    ActualHalfTraceStripCosineAsymptoticE02_38 u :=
  fun Y₀ hY₀ => actualPhysicalUnitHalfTrace_couplingStrip_cosineAsymptotic_E02_38 u Y₀ hY₀

/-- Source normalization `k(λ) = λ + o(1)`: `k(z) - z → 0` as `|z| → ∞` in the open
upper half-plane, for the concrete quasimomentum of every rough `u`. -/
theorem actualQuasimomentumE02_38_sub_tendsto_zero (u : PhysicalL2) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 0 < z.im → R ≤ ‖z‖ →
      ‖actualQuasimomentumE02_38 u z - z‖ < ε :=
  actualQuasimomentumE02_38_sub_tendsto_zero_of_strip u
    (actualHalfTraceStripCosineAsymptoticE02_38_holds u)

end NlsGge.SpectralFoundations
end
