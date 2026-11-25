import NlsGge.GK38.RealTypeSpectrumContinuity

/-! # S5: free discriminant signs transported along the real homotopy -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem perChar_root_discrim_sign38 (φ : PotPair) (z : ℂ)
    (hz : perChar φ z = 0) : discrim φ z = 2 ∨ discrim φ z = -2 := by
  have h : (discrim φ z - 2) * (discrim φ z + 2) = 0 := by
    rw [perChar_eq] at hz
    linear_combination hz
  simpa only [sub_eq_zero, add_eq_zero_iff_eq_neg] using mul_eq_zero.mp h

/-- Connectedness of the real path fixes the sign without complex label continuity. -/
theorem periodic_real_sign_transport38 (u : PhysicalL2) (k : ℤ) :
    discrim (realSlice u) (lamSeq (realSlice u) k) = discrim 0 (lamSeq 0 k) := by
  let f : ℝ → ℂ := fun t => discrim (realSlice (t • u)) (lamSeq (realSlice (t • u)) k)
  have hc : ContinuousOn f (Icc 0 1) := by
    have hd : Continuous (fun p : PhysicalL2 × ℂ => discrim (realSlice p.1) p.2) :=
      continuousOn_univ.mp analyticOnNhd_discrim_real_joint.continuousOn
    have hphys : Continuous (fun t : ℝ => t • u) := continuous_id.smul continuous_const
    have hg : ContinuousOn (fun t : ℝ => (t • u, lamSeq (realSlice (t • u)) k)) (Icc 0 1) :=
      hphys.continuousOn.prodMk (periodic_real_path_continuous38 u k)
    dsimp only [f]
    exact hd.comp_continuousOn' (f := fun t : ℝ => (t • u, lamSeq (realSlice (t • u)) k)) hg
  have hp : IsPreconnected (f '' Icc 0 1) := isPreconnected_Icc.image f hc
  have hfin : (f '' Icc 0 1).Finite := by
    apply ((Set.finite_singleton (-2 : ℂ)).insert (2 : ℂ)).subset
    rintro z ⟨t, _ht, rfl⟩
    have hs := perChar_root_discrim_sign38 _ _ ((lamSeq_enumeration38 (realSlice (t • u))).1 k)
    simpa only [mem_insert_iff, mem_singleton_iff] using hs
  have hsub := hp.isDiscrete_iff_subsingleton.mp hfin.isDiscrete
  have he := hsub (mem_image_of_mem f (by norm_num : (1 : ℝ) ∈ Icc 0 1))
    (mem_image_of_mem f (by norm_num : (0 : ℝ) ∈ Icc 0 1))
  simpa only [f, one_smul, zero_smul, realSlice_zero] using he

theorem periodic_real_pair_signs38 (u : PhysicalL2) (n : ℤ) :
    discrim (realSlice u) (lamMinus (realSlice u) n) = 2 * (Real.cos ((n : ℝ) * Real.pi) : ℂ) ∧
    discrim (realSlice u) (lamPlus (realSlice u) n) = 2 * (Real.cos ((n : ℝ) * Real.pi) : ℂ) := by
  have hm := periodic_real_sign_transport38 u (2 * n)
  have hp := periodic_real_sign_transport38 u (2 * n + 1)
  change discrim (realSlice u) (lamMinus (realSlice u) n) = discrim 0 (lamMinus 0 n) at hm
  change discrim (realSlice u) (lamPlus (realSlice u) n) = discrim 0 (lamPlus 0 n) at hp
  rw [lamMinus_zero38, discrim_zero] at hm
  rw [lamPlus_zero38, discrim_zero] at hp
  simpa only [countingCenter38, ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
    ← Complex.ofReal_cos] using And.intro hm hp

end
end NlsGge.GK38
