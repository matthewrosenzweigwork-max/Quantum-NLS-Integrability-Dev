import QuantumNLS.Ext025A2ODE

/-! Integral Gronwall from the primitive's right differential inequality.
Only continuity on the closed source interval is needed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.Ext025A3

theorem gp04_integral_gronwall {u : ℝ → ℝ} {a b α K : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn u (Icc a b)) (hn : ∀ t ∈ Icc a b, 0 ≤ u t)
    (hα : 0 ≤ α) (hK : 0 ≤ K)
    (hb : ∀ t ∈ Icc a b, u t ≤ α + K * ∫ s in a..t, u s) :
    ∀ t ∈ Icc a b, u t ≤ α * Real.exp (K * (t - a)) := by
  let v : ℝ → ℝ := fun t => α + K * ∫ s in a..t, u s
  have hd : ∀ t ∈ Icc a b, HasDerivWithinAt v (K * u t) (Icc a b) t := by
    intro t ht
    have hf : ContinuousOn (Function.uncurry (fun t (_ : ℝ) => K * u t))
        (Icc a b ×ˢ (univ : Set ℝ)) := by
      exact continuousOn_const.mul (hu.comp continuous_fst.continuousOn (fun p hp => hp.1))
    have h := ODE.hasDerivWithinAt_picard_Icc (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
      hf (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc a b))
      (fun t ht => mem_univ (0 : ℝ)) α ht
    change HasDerivWithinAt (fun t => α + ∫ s in a..t, K * u s) (K * u t) (Icc a b) t at h
    simp_rw [intervalIntegral.integral_const_mul] at h
    exact h
  have hv : ContinuousOn v (Icc a b) := HasDerivWithinAt.continuousOn hd
  have hvn : ∀ t ∈ Icc a b, 0 ≤ v t := by
    intro t ht
    have hi : 0 ≤ ∫ s in a..t, u s := intervalIntegral.integral_nonneg ht.1
      (fun s hs => hn s ⟨hs.1, hs.2.trans ht.2⟩)
    exact add_nonneg hα (mul_nonneg hK hi)
  have hright : ∀ t ∈ Ico a b, HasDerivWithinAt v (K * u t) (Ici t) t := by
    intro t ht
    apply (hd t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
    change Ici a ∩ Iic b ∈ 𝓝[Ici t] t
    apply inter_mem
    · exact mem_of_superset self_mem_nhdsWithin (Ici_subset_Ici.mpr ht.1)
    · exact mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht.2)
  have hbound : ∀ t ∈ Ico a b, ‖K * u t‖ ≤ K * ‖v t‖ := by
    intro t ht
    rw [Real.norm_of_nonneg (mul_nonneg hK (hn t ⟨ht.1, ht.2.le⟩)),
      Real.norm_of_nonneg (hvn t ⟨ht.1, ht.2.le⟩)]
    exact mul_le_mul_of_nonneg_left (hb t ⟨ht.1, ht.2.le⟩) hK
  have hinit : ‖v a‖ ≤ α := by
    simp only [v, intervalIntegral.integral_same, mul_zero, add_zero, Real.norm_of_nonneg hα]
    exact le_rfl
  have h := QuantumNLS.Ext025A2.gp04_exponential_norm hv hright hinit hbound
  intro t ht
  exact (hb t ht).trans ((le_abs_self (v t)).trans (h t ht))

end QuantumNLS.Ext025A3
#print axioms QuantumNLS.Ext025A3.gp04_integral_gronwall
