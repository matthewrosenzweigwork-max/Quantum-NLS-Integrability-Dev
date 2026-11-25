import NlsGge.GK38.StdRootBranchesConvergence

/-! Canonical square and exact free sign after genuine symmetric convergence. -/
set_option autoImplicit false
open Set Metric Filter Topology SummationFilter
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem canonRoot_sq38 (φ : PotPair) (hφ : φ ∈ gkW) (z : ℂ)
    (hz : z ∉ gapSegments38 φ) : canonRoot38 φ z ^ 2 = perChar φ z := by
  have hp : (φ,z) ∈ rootDomain38 := ⟨hφ, hz⟩
  have hprod := root_multipliable38 (φ,z) hp
  have hsprod := hprod.pow 2
  have hcharprod := perChar_multipliable φ z
  have hfac (n : ℤ) : rootFactor38 n (φ,z)^2 =
      (lamPlus φ n - z) * (lamMinus φ n - z) / (πn n : ℂ)^2 := by
    rw [rootFactor_sq38 n (φ,z) hp]
    change (lamMinus φ n - z) * (lamPlus φ n - z) / (Lib.piN n : ℂ)^2 =
      (lamPlus φ n - z) * (lamMinus φ n - z) / (Lib.piN n : ℂ)^2
    ring
  have hc : ((2 : ℂ) * Complex.I)^2 = -4 := by
    ring_nf
    norm_num [Complex.I_sq]
  unfold canonRoot38
  rw [mul_pow, hc, ← hprod.tprod_pow 2]
  simp_rw [hfac]
  exact (perChar_product φ z).symm

theorem canonRoot_ne_zero38 (φ : PotPair) (hφ : φ ∈ gkW) (z : ℂ)
    (hz : z ∉ gapSegments38 φ) : canonRoot38 φ z ≠ 0 := by
  have hp : (φ,z) ∈ rootDomain38 := ⟨hφ, hz⟩
  have hsum := root_pair_summable38 (φ,z) hp
  have hprod : (∏'[symmetricIcc ℤ] n : ℤ, rootFactor38 n (φ,z)) ≠ 0 := by
    intro he
    obtain ⟨n, hn⟩ := (Lib.tprod_symm_eq_zero_iff hsum).mp he
    exact rootFactor_ne_zero38 n (φ,z) hp hn
  exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hprod

theorem rootFactor_free38 (n : ℤ) (z : ℂ) :
    rootFactor38 n ((0 : PotPair),z) = Lib.prodFactor Lib.sigmaZero z n := by
  have hw : (0 : PotPair) ∈ gkW := by
    simpa only [realSlice_zero] using realSlice_mem_gkW (0 : PhysicalL2)
  have ht : tauN 0 n = countingCenter38 n := by
    rw [tauN_value38 0 hw n, lamPlus_zero38, lamMinus_zero38]
    ring
  have hg : gamma2 0 n = 0 := by
    rw [gamma2_value38 0 hw n, lamPlus_zero38, lamMinus_zero38]
    simp
  rw [rootFactor38, ht, hg, stdRoot_degenerate38]
  rfl

theorem canonRoot_free38 (z : ℂ) (_hz : z ∉ gapSegments38 0) :
    canonRoot38 0 z = -2 * Complex.I * Complex.sin z := by
  have hprod := (Lib.hasProd_sinProd z).multipliable
  have he := (Lib.hasProd_sinProd z).tprod_eq
  unfold canonRoot38
  simp_rw [rootFactor_free38]
  rw [he]
  ring

end
end NlsGge.GK38
