import NlsGge.Spectral.ActualGapHeightSemicircleE02_38
import Mathlib.Topology.ExtendFrom
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # Constant real part of the boundary quasimomentum on a gap (E02.38, S1)

If `|Δh| > 1` on `(a,b)` and `|Δh| = 1` at `a, b`, then the boundary value of `k` is
`mπ + i v(x)` for one integer `m` on all of `[a,b]`. -/

theorem exists_int_boundary_on_gap_E02_38 (u : PhysicalL2) (a b : ℝ) (hab : a < b)
    (hgap : ∀ x ∈ Set.Ioo a b, 1 < ‖actualPhysicalUnitHalfTrace32 u x‖)
    (ha : ‖actualPhysicalUnitHalfTrace32 u a‖ = 1) (hb : ‖actualPhysicalUnitHalfTrace32 u b‖ = 1) :
    ∃ m : ℤ, (∀ x ∈ Set.Icc a b, Tendsto (actualQuasimomentumE02_38 u)
        (𝓝[{z : ℂ | 0 < z.im}] (x:ℂ))
        (𝓝 ((m:ℂ)*Real.pi + Complex.I * (actualGapHeightE02_38 u x : ℂ)))) ∧
      actualPhysicalUnitHalfTrace32 u a = (Real.cos (m*Real.pi) : ℂ) ∧
      actualPhysicalUnitHalfTrace32 u b = (Real.cos (m*Real.pi) : ℂ) := by
  set U : Set ℂ := {z : ℂ | 0 < z.im} with hU
  set k := actualQuasimomentumE02_38 u with hk
  set Δ := actualPhysicalUnitHalfTrace32 u with hΔ
  have hlim : ∀ x : ℝ, ∃ L : ℂ, Tendsto k (𝓝[U] (x:ℂ)) (𝓝 L) ∧ Complex.cos L = Δ x :=
    fun x => by
      obtain ⟨L, h1, h2, -⟩ := exists_tendsto_actualQuasimomentum_boundary_E02_38 u x
      exact ⟨L, h1, h2⟩
  set F := extendFrom U k with hF
  have hFc : ContinuousOn F (Set.range ((↑) : ℝ → ℂ)) :=
    continuousOn_extendFrom
      (by rintro _ ⟨x, rfl⟩; exact mem_closure_upperHalfPlane_E02_38 (by simp))
      (by rintro _ ⟨x, rfl⟩; obtain ⟨L, h, -⟩ := hlim x; exact ⟨L, h⟩)
  set L : ℝ → ℂ := fun x => F (x:ℂ) with hLdef
  have hLc : Continuous L := hFc.comp_continuous Complex.continuous_ofReal (fun x => ⟨x, rfl⟩)
  have hLt : ∀ x : ℝ, Tendsto k (𝓝[U] (x:ℂ)) (𝓝 (L x)) := by
    intro x
    obtain ⟨y, hy, -⟩ := hlim x
    have : L x = y := extendFrom_eq (mem_closure_upperHalfPlane_E02_38 (by simp)) hy
    rw [this]; exact hy
  have hLcos : ∀ x : ℝ, Complex.cos (L x) = Δ x := by
    intro x
    obtain ⟨y, hy, hc⟩ := hlim x
    have : L x = y := extendFrom_eq (mem_closure_upperHalfPlane_E02_38 (by simp)) hy
    rw [this]; exact hc
  have hLim : ∀ x : ℝ, (L x).im = actualGapHeightE02_38 u x :=
    fun x => boundaryLimit_im_E02_38 u x (L x) (hLt x)
  -- integrality on the open gap
  have hint : ∀ x ∈ Set.Ioo a b, ∃ n : ℤ, (L x).re / Real.pi = (n:ℝ) := by
    intro x hx
    have him : (Complex.cos (L x)).im = 0 := by
      rw [hLcos]; exact actualPhysicalUnitHalfTrace32_ofReal_im_E02_38 u x
    rw [complex_cos_im_E02_38] at him
    have hv : actualGapHeightE02_38 u x ≠ 0 := by
      rw [Ne, actualGapHeightE02_38_eq_zero_iff]
      exact not_le.mpr (hgap x hx)
    have hsinh : Real.sinh (L x).im ≠ 0 := by
      rw [hLim]; exact fun h => hv (Real.sinh_eq_zero.mp h)
    have hsin : Real.sin (L x).re = 0 := by
      have : Real.sin (L x).re * Real.sinh (L x).im = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hsinh
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
    exact ⟨n, by rw [← hn]; field_simp [Real.pi_ne_zero]⟩
  set p : ℝ → ℝ := fun x => (L x).re / Real.pi with hp
  have hpc : Continuous p := (Complex.continuous_re.comp hLc).div_const _
  have hd : IsDiscrete (range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range
  have hm : MapsTo p (Set.Ioo a b) (range ((↑) : ℤ → ℝ)) := by
    intro x hx
    obtain ⟨n, hn⟩ := hint x hx
    exact ⟨n, hn.symm⟩
  obtain ⟨v, ⟨m, rfl⟩, hconst⟩ := isPreconnected_Ioo.eqOn_const_of_mapsTo hd hpc.continuousOn hm
    (show (range ((↑) : ℤ → ℝ)).Nonempty from ⟨0, 0, by simp⟩)
  have hcl : ∀ x ∈ Set.Icc a b, p x = (m:ℝ) := by
    intro x hx
    have h := Set.EqOn.closure (f := p) (g := fun _ => (m:ℝ)) hconst hpc continuous_const
    rw [closure_Ioo hab.ne] at h
    exact h hx
  have hre : ∀ x ∈ Set.Icc a b, (L x).re = (m:ℝ) * Real.pi := by
    intro x hx
    have := hcl x hx
    simp only [hp] at this
    field_simp [Real.pi_ne_zero] at this
    linarith
  have hLeq : ∀ x ∈ Set.Icc a b,
      L x = (m:ℂ)*Real.pi + Complex.I * (actualGapHeightE02_38 u x : ℂ) := by
    intro x hx
    apply Complex.ext
    · simp [hre x hx]
    · simp [hLim x]
  have hendpt : ∀ x ∈ Set.Icc a b, ‖Δ x‖ = 1 → Δ x = (Real.cos (m*Real.pi) : ℂ) := by
    intro x hx h1
    have hv0 : actualGapHeightE02_38 u x = 0 :=
      (actualGapHeightE02_38_eq_zero_iff u x).mpr h1.le
    have hLx : L x = (m:ℂ)*Real.pi := by
      rw [hLeq x hx, hv0]; simp
    rw [← hLcos x, hLx, ← Complex.ofReal_intCast, ← Complex.ofReal_mul, ← Complex.ofReal_cos]
  refine ⟨m, fun x hx => ?_, hendpt a ⟨le_rfl, hab.le⟩ ha, hendpt b ⟨hab.le, le_rfl⟩ hb⟩
  rw [← hLeq x hx]
  exact hLt x

end NlsGge.SpectralFoundations
end

