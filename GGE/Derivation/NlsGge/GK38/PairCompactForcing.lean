import NlsGge.GK38.PairCompactWeak
import NlsGge.GK38.PairCompactPrimitive

/-! # F6: compact spectral/time sets of Volterra tests

The plus/plus factorization of the accepted Volterra operator and the
smoothed primitive test produce a compact set in the scalar dual.
-/
set_option autoImplicit false
open Filter Topology
namespace NlsGge.GK38
noncomputable section

/-- The scalar test for applying the Volterra operator to the limit solution. -/
def compactVolterraTest38 (φ₀ : PotPair) (z : ℂ) (t : Set.Icc (0 : ℝ) 1)
    (i j : Fin 2) : PotPair →L[ℂ] ℂ :=
  freeE z t i i • primitiveTest38 (mulFree38 z (fundContP φ₀ z)) t i j

@[simp] theorem compactVolterraTest38_apply (φ₀ φ : PotPair) (z : ℂ)
    (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    compactVolterraTest38 φ₀ z t i j φ = volterraP φ z (fundContP φ₀ z) t i j := by
  simp only [compactVolterraTest38, smul_apply,
    primitiveTest38_apply, smul_eq_mul]
  conv_rhs => rw [volterraP_eq_mul, mul_apply_eq_comp, mul_apply_eq_comp, mulFree38_apply]

/-- Joint operator-norm continuity, including the whole compact time interval. -/
theorem continuous_compactVolterraTest38 (φ₀ : PotPair) (i j : Fin 2) :
    Continuous (fun p : ℂ × Set.Icc (0 : ℝ) 1 => compactVolterraTest38 φ₀ p.1 p.2 i j) := by
  have hFull : Continuous (fun p : PotPair × ℂ => fundContP p.1 p.2) :=
    continuousOn_univ.mp analyticOnNhd_fundContP.continuousOn
  have hM : Continuous (fun z : ℂ => fundContP φ₀ z) := by
    have hp : Continuous (fun z : ℂ => (φ₀, z)) := continuous_const.prodMk continuous_id
    change Continuous ((fun p : PotPair × ℂ => fundContP p.1 p.2) ∘ fun z : ℂ => (φ₀, z))
    exact hFull.comp hp
  have hE : Continuous (fun z : ℂ => mulFree38 z) :=
    continuousOn_univ.mp analyticOnNhd_mulFree38.continuousOn
  have hN : Continuous (fun z : ℂ => mulFree38 z (fundContP φ₀ z)) := hE.clm_apply hM
  have htest := (continuous_primitiveTest38 i j).comp
    ((hN.comp continuous_fst).prodMk continuous_snd)
  have hfree : Continuous (fun p : ℂ × Set.Icc (0 : ℝ) 1 => freeE p.1 p.2 i i) := by
    simp only [freeE_diag]
    fun_prop
  exact hfree.smul htest

/-- Weak convergence makes the forcing uniformly small on compact spectral sets,
simultaneously at all times and all matrix entries. -/
theorem weakLimComp_volterra_forcing38 {φ : ℕ → PotPair} {φ₀ : PotPair}
    (hw : IsWeakLimComp φ φ₀) {K : Set ℂ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ z ∈ K, ∀ t : Set.Icc (0 : ℝ) 1, ∀ i j : Fin 2,
      ‖volterraP (φ k - φ₀) z (fundContP φ₀ z) t i j‖ < ε := by
  have heach (i j : Fin 2) :
      ∀ᶠ k in atTop, ∀ z ∈ K, ∀ t : Set.Icc (0 : ℝ) 1,
        ‖volterraP (φ k - φ₀) z (fundContP φ₀ z) t i j‖ < ε := by
    let L : ℂ × Set.Icc (0 : ℝ) 1 → PotPair →L[ℂ] ℂ :=
      fun p => compactVolterraTest38 φ₀ p.1 p.2 i j
    have hS : IsCompact (L '' (K ×ˢ Set.univ)) :=
      (hK.prod isCompact_univ).image (continuous_compactVolterraTest38 φ₀ i j)
    have hu := Metric.tendstoUniformlyOn_iff.mp (weakLimComp_uniform_tests38 hw hS) ε hε
    filter_upwards [hu] with k hk z hz t
    have ht := hk (L (z, t)) (Set.mem_image_of_mem L ⟨hz, Set.mem_univ t⟩)
    rw [dist_eq_norm, norm_sub_rev, ← map_sub] at ht
    simpa only [L, compactVolterraTest38_apply] using ht
  have hu := eventually_all.mpr fun i => eventually_all.mpr fun j => heach i j
  filter_upwards [hu] with k hk z hz t i j
  exact hk i j z hz t

end
end NlsGge.GK38
