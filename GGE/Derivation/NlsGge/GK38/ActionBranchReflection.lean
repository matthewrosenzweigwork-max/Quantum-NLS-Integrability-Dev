import NlsGge.GK38.ActionBranchDerivative
import Mathlib.Topology.Connected.TotallyDisconnected

set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open scoped ComplexConjugate
namespace NlsGge.GK38.ActionBranch
noncomputable section

theorem discrim_conj (u : PhysicalL2) (z : ℂ) :
    discrim (realSlice u) (conj z) = conj (discrim (realSlice u) z) := by
  simp only [discrim_realSlice, actualPhysicalUnitHalfTrace32_conj_E02_38, map_mul, map_ofNat]

theorem continuous_root_ray_nonreal (u : PhysicalL2) (z : ℂ) (hz : z.im ≠ 0) :
    Continuous (fun t : ℝ => canonRoot38 (realSlice (t • u)) z) := by
  have hpot : Continuous (fun t : ℝ => realSlice (t • u)) :=
    continuous_realSlice.comp (continuous_id.smul continuous_const)
  have hpath : Continuous (fun t : ℝ => (realSlice (t • u), z)) :=
    hpot.prodMk continuous_const
  apply continuous_iff_continuousAt.mpr
  intro t
  have hr : AnalyticAt ℂ (fun p : PotPair × ℂ => canonRoot38 p.1 p.2)
      (realSlice (t • u), z) :=
    canonRoot_analytic38 (realSlice (t • u), z)
      (rootDomain_realSlice_nonreal38 (t • u) z hz)
  exact ContinuousAt.comp (f := fun s : ℝ => (realSlice (s • u), z))
    (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2) (x := t)
    hr.continuousAt hpath.continuousAt

theorem root_conj_sq (u : PhysicalL2) (z : ℂ) (hz : z.im ≠ 0) :
    canonRoot38 (realSlice u) (conj z) ^ 2 =
      conj (canonRoot38 (realSlice u) z) ^ 2 := by
  have hzc : (conj z).im ≠ 0 := by simpa using hz
  have h1 := canonRoot_sq38 (realSlice u) (realSlice_mem_gkW u) (conj z)
    (rootDomain_realSlice_nonreal38 u (conj z) hzc).2
  have h2 := congrArg conj (canonRoot_sq38 (realSlice u) (realSlice_mem_gkW u) z
    (rootDomain_realSlice_nonreal38 u z hz).2)
  rw [perChar_eq, discrim_conj] at h1
  rw [perChar_eq] at h2
  simp only [map_sub, map_pow, map_ofNat] at h2
  exact h1.trans h2.symm

theorem canonical_root_conj (u : PhysicalL2) (z : ℂ) (hz : z.im ≠ 0) :
    canonRoot38 (realSlice u) (conj z) = -conj (canonRoot38 (realSlice u) z) := by
  have hzc : (conj z).im ≠ 0 := by simpa using hz
  have hn (t : ℝ) : conj (canonRoot38 (realSlice (t • u)) z) ≠ 0 := by
    exact (map_ne_zero (starRingEnd ℂ)).mpr (canonRoot_ne_zero38 _ (realSlice_mem_gkW _) z
      (rootDomain_realSlice_nonreal38 (t • u) z hz).2)
  let q : ℝ → ℂ := fun t => canonRoot38 (realSlice (t • u)) (conj z) /
    conj (canonRoot38 (realSlice (t • u)) z)
  have hc : Continuous q := (continuous_root_ray_nonreal u (conj z) hzc).div
    (Complex.continuous_conj.comp (continuous_root_ray_nonreal u z hz)) hn
  have hmaps : MapsTo q univ ({1, -1} : Set ℂ) := by
    intro t _
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (root_conj_sq (t • u) z hz) with h | h
    · apply Or.inl
      change canonRoot38 (realSlice (t • u)) (conj z) /
        conj (canonRoot38 (realSlice (t • u)) z) = 1
      rw [h, div_self (hn t)]
    · apply Or.inr
      change canonRoot38 (realSlice (t • u)) (conj z) /
        conj (canonRoot38 (realSlice (t • u)) z) = -1
      rw [h, neg_div, div_self (hn t)]
  have hq : q 1 = q 0 := isPreconnected_univ.constant_of_mapsTo
    ((Set.finite_singleton (-1 : ℂ)).insert 1).isDiscrete hc.continuousOn hmaps (mem_univ _) (mem_univ _)
  have hfree : canonRoot38 (realSlice ((0 : ℝ) • u)) (conj z) =
      -conj (canonRoot38 (realSlice ((0 : ℝ) • u)) z) := by
    simp only [zero_smul, realSlice_zero]
    rw [canonRoot_free38 (conj z) (by simpa only [realSlice_zero] using
      (rootDomain_realSlice_nonreal38 (0 : PhysicalL2) (conj z) hzc).2),
      canonRoot_free38 z (by simpa only [realSlice_zero] using
      (rootDomain_realSlice_nonreal38 (0 : PhysicalL2) z hz).2)]
    simp [map_mul, map_ofNat, Complex.sin_conj]
  have hzero : q 0 = -1 := by
    dsimp only [q]
    rw [hfree, neg_div, div_self (hn 0)]
  have hfinal := (div_eq_iff (hn 1)).mp (hq.trans hzero)
  simpa only [one_smul, neg_one_mul] using hfinal

end
end NlsGge.GK38.ActionBranch
