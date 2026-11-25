import NlsGge.GK38.XiCommonDomainTargets

set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GK38

theorem isOpen_xiCommonDomain38 : IsOpen xiCommonDomain38 := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  intro φ hφ
  obtain ⟨U, hU, hUW, N, htail⟩ := xiSq38_near_one φ hφ.1
  have hhead : ∀ᶠ ψ in 𝓝 φ, ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      xiSq38 n ψ ∈ Complex.slitPlane :=
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).eventually_all.mpr (fun n _ =>
      (xiSq38_analytic n φ hφ.1).continuousAt.preimage_mem_nhds
        (Complex.isOpen_slitPlane.mem_nhds (hφ.2 n)))
  filter_upwards [hU, hhead] with ψ hψ hh
  refine ⟨hUW hψ, fun n => ?_⟩
  by_cases hn : N < n.natAbs
  · exact (htail ψ hψ n hn).1
  · have habs : n.natAbs ≤ N := le_of_not_gt hn
    have hpos : n ≤ (n.natAbs : ℤ) := Int.le_natAbs
    have hneg : -n ≤ (n.natAbs : ℤ) := by
      simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -n))
    have hcast : (n.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast habs
    exact hh n (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

theorem realSlice_mem_xiCommonDomain38 (u : PhysicalL2) :
    realSlice u ∈ xiCommonDomain38 := by
  refine ⟨realSlice_mem_gkW u, fun n => ?_⟩
  have h := xiSq38_real_ge_one u n
  exact Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [h.2]))

theorem xiN38_analytic_commonDomain (n : ℤ) :
    AnalyticOnNhd ℂ (xiN38 n) xiCommonDomain38 :=
  (xiN38_analytic n).mono (fun _ h => ⟨h.1, h.2 n⟩)

theorem xiCommonDomainTarget38_proved : XiCommonDomainTarget38 :=
  ⟨isOpen_xiCommonDomain38, realSlice_mem_xiCommonDomain38,
    xiN38_analytic_commonDomain⟩

end NlsGge.GK38
