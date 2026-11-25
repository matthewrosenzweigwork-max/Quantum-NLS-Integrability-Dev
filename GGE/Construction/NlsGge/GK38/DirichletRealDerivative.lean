import NlsGge.GK38.DirichletRealGreenParam
import NlsGge.GK38.DirichletRealGreenScalar
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Actual Dirichlet simplicity via the independently integrated Green kernel.
Private source anchor: book I.7 Lemma 7.2. -/
set_option autoImplicit false
open Set MeasureTheory Filter Topology
namespace NlsGge.GK38
noncomputable section
open NlsGge.Pilot NlsGge.SpectralFoundations

def dirichletEnergy38 (u : PhysicalL2) (x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, ‖actualPhysicalFloquetState33 u (x : ℂ) ![1, 1] s 0‖ ^ 2 +
    ‖actualPhysicalFloquetState33 u (x : ℂ) ![1, 1] s 1‖ ^ 2

theorem dirichletEnergy_pos38 (u : PhysicalL2) (x : ℝ) : 0 < dirichletEnergy38 u x := by
  apply actualPhysicalFloquet_energy_integral_pos33
  intro h
  have hh := congrArg (fun v : Fin 2 → ℂ => v 0) h
  simpa using hh

theorem dirichletGreenIntegral_eq_energy38 (u : PhysicalL2) (x : ℝ) :
    (∫ s in (0 : ℝ)..1, dirichletGreenKernel38 u (x : ℂ) (x : ℂ) s) =
      (dirichletEnergy38 u x : ℂ) := by
  rw [dirichletEnergy38, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro s hs
  have hmem : s ∈ Icc (0 : ℝ) 1 := by simpa only [Set.uIcc_of_le zero_le_one] using hs
  have hstar := dirichletState_real_star38 u x ⟨s, hmem⟩
  rw [dirichletState_eq_actual38] at hstar
  have hstar1 : star (actualPhysicalFloquetState33 u (x : ℂ) ![1, 1] s 1) =
      actualPhysicalFloquetState33 u (x : ℂ) ![1, 1] s 0 := by
    rw [← hstar, star_star]
  calc dirichletGreenKernel38 u (x : ℂ) (x : ℂ) s =
      actualPhysicalFloquetState33 u (x : ℂ) ![1, 1] s 0 * star (actualPhysicalFloquetState33 u (x : ℂ) ![1, 1] s 0) +
      actualPhysicalFloquetState33 u (x : ℂ) ![1, 1] s 1 * star (actualPhysicalFloquetState33 u (x : ℂ) ![1, 1] s 1) := by
        rw [hstar, hstar1]
        rfl
    _ = _ := by
      simp only [Complex.star_def, Complex.mul_conj', Complex.ofReal_add, Complex.ofReal_pow]

theorem dirichletGreen_factor38 (u : PhysicalL2) (x : ℝ)
    (hx : dirichletChar (realSlice u) (x : ℂ) = 0) (z : ℂ) :
    dirichletChar (realSlice u) z * dirichletState38 u (x : ℂ) ⟨1, zero_le_one, le_rfl⟩ 0 =
      (z - (x : ℂ)) * (∫ s in (0 : ℝ)..1, dirichletGreenKernel38 u (x : ℂ) z s) / 2 := by
  have hb := (dirichletChar_zero_iff_boundary38 (realSlice u) (x : ℂ)).mp hx
  rw [monodromyPair_realSlice] at hb
  have hb' : actualPhysicalFloquetState33 u (x : ℂ) ![1, 1] 1 0 =
      actualPhysicalFloquetState33 u (x : ℂ) ![1, 1] 1 1 := hb
  have h := dirichletGreen_identity38 u (x : ℂ) z 1 (by norm_num)
  rw [← hb'] at h
  rw [dirichletState_eq_actual38]
  unfold dirichletChar
  rw [monodromyPair_realSlice]
  exact dirichletGreen_scalar_factor38 _ _ _ _ _ h

/-- The actual derivative times its nonzero endpoint amplitude is positive energy/2. -/
theorem dirichlet_root_derivative38 (u : PhysicalL2) (x : ℝ)
    (hx : dirichletChar (realSlice u) (x : ℂ) = 0) :
    deriv (dirichletChar (realSlice u)) (x : ℂ) *
      dirichletState38 u (x : ℂ) ⟨1, zero_le_one, le_rfl⟩ 0 = (dirichletEnergy38 u x : ℂ) / 2 := by
  let α := dirichletState38 u (x : ℂ) ⟨1, zero_le_one, le_rfl⟩ 0
  have hχ := ((analyticOnNhd_dirichletChar_z (realSlice u)) (x : ℂ) (mem_univ _)).differentiableAt.hasDerivAt
  have hd := hχ.tendsto_slope.mul_const α
  have hInt : Tendsto
      (fun z : ℂ => (∫ s in (0 : ℝ)..1, dirichletGreenKernel38 u (x : ℂ) z s) / 2)
      (𝓝[≠] (x : ℂ))
      (𝓝 ((∫ s in (0 : ℝ)..1, dirichletGreenKernel38 u (x : ℂ) (x : ℂ) s) / 2)) :=
    ((dirichletGreenIntegral_continuous38 u (x : ℂ)).continuousAt.tendsto.div_const
      (2 : ℂ)).mono_left nhdsWithin_le_nhds
  have heq : (fun z => slope (dirichletChar (realSlice u)) (x : ℂ) z * α) =ᶠ[𝓝[≠] (x : ℂ)]
      (fun z => (∫ s in (0 : ℝ)..1, dirichletGreenKernel38 u (x : ℂ) z s) / 2) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have h := dirichletGreen_factor38 u x hx z
    simpa only [slope, hx, vsub_eq_sub, sub_zero, smul_eq_mul] using
      dirichletGreen_scalar_quotient38 _ α (z - (x : ℂ)) _ (sub_ne_zero.mpr hz) h
  have hlim := tendsto_nhds_unique hd (hInt.congr' heq.symm)
  rw [dirichletGreenIntegral_eq_energy38] at hlim
  exact hlim

theorem dirichlet_root_deriv_ne_zero38 (u : PhysicalL2) (x : ℝ)
    (hx : dirichletChar (realSlice u) (x : ℂ) = 0) :
    deriv (dirichletChar (realSlice u)) (x : ℂ) ≠ 0 := by
  intro hz
  have h := dirichlet_root_derivative38 u x hx
  rw [hz, zero_mul] at h
  have he : dirichletEnergy38 u x ≠ 0 := ne_of_gt (dirichletEnergy_pos38 u x)
  have hh : (dirichletEnergy38 u x : ℂ) = 0 := (div_eq_zero_iff.mp h.symm).resolve_right (by norm_num)
  exact he (by exact_mod_cast hh)

theorem muSeq_simple38 (u : PhysicalL2) (n : ℤ) :
    analyticOrderAt (dirichletChar (realSlice u)) (muSeq (realSlice u) n) = 1 := by
  rw [muSeq_eq_gkMu38]
  exact ((analyticOnNhd_dirichletChar_z (realSlice u)) _ (mem_univ _)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (gkMu_root38 u n) (dirichlet_root_deriv_ne_zero38 u (gkMu u n) (gkMu_root38 u n))

end
end NlsGge.GK38
