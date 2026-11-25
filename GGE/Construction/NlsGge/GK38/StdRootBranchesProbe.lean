import NlsGge.GK38.StdRootBranchesProducts
import NlsGge.GK38.StdRootBranchesDomainProbe
import NlsGge.GK38.StdRootBranchesScalarProbe
import NlsGge.GK38.TauGammaFactorProbe

/-! Canonical normalization and actual nonfree/complex-potential regressions. -/
set_option autoImplicit false
open Set Metric Filter Topology SummationFilter
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem rootDomain_realSlice_nonreal38 (u : PhysicalL2) (z : ℂ) (hz : z.im ≠ 0) :
    (realSlice u,z) ∈ rootDomain38 := by
  refine ⟨realSlice_mem_gkW u, ?_⟩
  intro hgap
  obtain ⟨n, hn⟩ := mem_iUnion.mp hgap
  obtain ⟨a, b, _ha, _hb, _hab, he⟩ := hn
  have hi := congrArg Complex.im he
  rw [(lamPlus_real u n).1, (lamPlus_real u n).2] at hi
  simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
    Complex.ofReal_re, mul_zero, zero_mul, add_zero] at hi
  exact hz hi.symm

theorem canonRoot_free_near_axis_probe38 (x ε : ℝ) (hε : 0 < ε) :
    let z : ℂ := (x : ℂ) + (ε : ℂ) * Complex.I
    canonRoot38 0 z = -2 * Complex.I * Complex.sin z ∧
      canonRoot38 0 z ^ 2 = perChar 0 z ∧ canonRoot38 0 z ≠ 0 := by
  have hp := rootDomain_free_near_axis_probe38 x ε hε
  exact ⟨canonRoot_free38 _ hp.2, canonRoot_sq38 _ hp.1 _ hp.2,
    canonRoot_ne_zero38 _ hp.1 _ hp.2⟩

theorem canonRoot_actual_nonfree_probe38 :
    rootFactor38 0 (realSlice (constL2 1), Complex.I)^2 = -2 ∧
      canonRoot38 (realSlice (constL2 1)) Complex.I^2 =
        perChar (realSlice (constL2 1)) Complex.I ∧
      canonRoot38 (realSlice (constL2 1)) Complex.I ≠ 0 ∧
      Summable (fun m : ℕ => ‖Lib.pairDev
        (fun n => rootFactor38 n (realSlice (constL2 1), Complex.I)) m‖) := by
  have hp := rootDomain_realSlice_nonreal38 (constL2 1) Complex.I (by simp)
  refine ⟨?_, canonRoot_sq38 _ hp.1 _ hp.2, canonRoot_ne_zero38 _ hp.1 _ hp.2,
    root_pair_summable38 _ hp⟩
  rw [rootFactor_sq38 0 _ hp, realType_const_central_labels38.1,
    realType_const_central_labels38.2, Lib.piN_zero]
  norm_num [Complex.I_sq]
  ring_nf
  norm_num [Complex.I_sq]

theorem canonRoot_actual_triangular_probe38 : ∃ a : ℝ, 0 < a ∧
    let φ : PotPair := (constL2 (a : ℂ), 0)
    φ ∈ gkW ∧ φ ≠ 0 ∧ φ ∉ range realSlice ∧
      (φ,Complex.I) ∈ rootDomain38 ∧
      canonRoot38 φ Complex.I = -2 * Complex.I * Complex.sin Complex.I ∧
      canonRoot38 φ Complex.I ≠ 0 := by
  obtain ⟨a, ha, hw, hne, hvalues⟩ := tauGamma_nonzero_triangular_in_W38
  let φ : PotPair := (constL2 (a : ℂ), 0)
  have hout : φ ∉ range realSlice := by
    rintro ⟨u, hu⟩
    have hs := congrArg Prod.snd hu
    change star u = 0 at hs
    have hstar := congrArg star hs
    rw [star_star] at hstar
    have hu0 : u = 0 := hstar.trans (map_zero starLp)
    apply hne
    simpa only [hu0, realSlice_zero] using hu.symm
  have hp : (φ,Complex.I) ∈ rootDomain38 := by
    refine ⟨hw, ?_⟩
    intro hgap
    obtain ⟨n, hn⟩ := mem_iUnion.mp hgap
    have hl := labelling_probe_triangular38 (constL2 (a : ℂ)) n
    rw [hl.1, hl.2, segment_same] at hn
    have hi := congrArg Complex.im hn
    norm_num [countingCenter38] at hi
  have hfac (n : ℤ) : rootFactor38 n (φ,Complex.I) =
      Lib.prodFactor Lib.sigmaZero Complex.I n := by
    rw [rootFactor38, (hvalues n).1, (hvalues n).2.1, stdRoot_degenerate38]
    rfl
  refine ⟨a, ha, hw, hne, hout, hp, ?_, canonRoot_ne_zero38 _ hw _ hp.2⟩
  change 2 * Complex.I * (∏'[symmetricIcc ℤ] n : ℤ, rootFactor38 n (φ,Complex.I)) = _
  rw [tprod_congr hfac]
  rw [(Lib.hasProd_sinProd Complex.I).tprod_eq]
  ring

end
end NlsGge.GK38
