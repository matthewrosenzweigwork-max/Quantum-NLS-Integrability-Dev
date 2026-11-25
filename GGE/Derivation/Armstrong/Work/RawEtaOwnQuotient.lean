import Armstrong.Work.RawBetaMagnitudeSameFamily
import NlsGge.GK38.AbelianInputDiscPlacement
import NlsGge.GK38.AbelianFullCompactInverseBound
import NlsGge.GK38.AbelianJacobianGeometry
import Mathlib.Order.Filter.Finite

/-!
# Own-gap quotient for the diagonal angle

The n-th numerator divided by the canonical root has an exact own-gap
factorization with no sigma_n denominator. This is the source-side quotient
needed for the diagonal eta/z_n^± construction.
-/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem gk16_own_factorization38
    (n : ℤ) (s : Lib.L2Seq) (phi : PotPair) (z : ℂ)
    (hp : (phi,z) ∈ rootDomain38) :
    p2FullNumerator38 n s z / canonRoot38 phi z =
      Complex.I * p2OmittedRatio38 n ((phi,s),z) /
        stdRoot38 (tauN phi n) (gamma2 phi n) z := by
  have hp' : (phi,z) ∈ a5OmittedRootDomain38 n :=
    ⟨hp.1, fun m _ => rootDomain_avoids38 hp m⟩
  have hD := a5OmittedRoot_ne_zero38 n (phi,z) hp'
  have hS : stdRoot38 (tauN phi n) (gamma2 phi n) z ≠ 0 := by
    have hs := stdRoot_ne_zero38 (lamMinus phi n) (lamPlus phi n) z
      (rootDomain_avoids38 hp n)
    simpa only [add_comm (lamMinus phi n), ← tauN_value38 phi hp.1 n,
      ← gamma2_value38 phi hp.1 n] using hs
  rw [a5CanonRoot_omitted_factorization38 n (phi,z) hp]
  unfold p2FullNumerator38 p2OmittedRatio38 rootFactor38
  field_simp [hD, hS,
    Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n), Complex.I_ne_zero]
  simp only [Complex.I_sq]
  ring

theorem gk16_own_ratio_analytic38
    (n : ℤ) (phi : PotPair) (hphi : phi ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 phi C R) (s : Lib.L2Seq) :
    AnalyticOnNhd ℂ
      (fun z => p2OmittedRatio38 n ((phi,s),z))
      (closedBall (C n) (R n)) :=
  p2OmittedRatio_own_disc_analytic38 n phi hphi C R hfam s

theorem gk16_own_ratio_ne_zero38
    (n : ℤ) (phi : PotPair) (hphi : phi ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 phi C R) (s : Lib.L2Seq)
    (hsigma : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k))
    (z : ℂ) (hz : z ∈ closedBall (C n) (R n)) :
    p2OmittedRatio38 n ((phi,s),z) ≠ 0 :=
  P3JacobianColumns.omittedRatio_ne_zero
    phi hphi C R hfam s hsigma n z hz

/-- Every real full-gap input lies strictly inside every original isolating
disc, not merely its closure. -/
theorem gk16_full_gap_strict_placement38
    (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R)
    (s : P6RealSpace38) (hs : s ∈ p5FullRealGapCube38 u) :
    ∀ k : ℤ, Lib.sigmaOf (p6RealInclude38 s) k ∈ ball (C k) (R k) := by
  obtain ⟨c,N,hgeom,hspec⟩ := hfam
  intro k
  have hk := (hspec.1 k).1 (hs k)
  simpa only [Lib.sigmaOf, countingCenter38,
    p6RealInclude_apply38, add_comm] using hk

/-- The compact real full-gap cube admits one open full-input neighborhood
whose every coordinate remains in the same original isolating disc. -/
theorem gk16_compact_input_all_own_disc_tube38
    (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) :
    ∃ V : Set Lib.L2Seq, IsOpen V ∧
      p6RealInclude38 '' p5FullRealGapCube38 u ⊆ V ∧
      ∀ s ∈ V, ∀ k : ℤ, Lib.sigmaOf s k ∈ ball (C k) (R k) := by
  classical
  have hfamCopy := hfam
  obtain ⟨c,N,hgeom,hspec⟩ := hfamCopy
  let K : Set Lib.L2Seq := p6RealInclude38 '' p5FullRealGapCube38 u
  have hK : IsCompact K :=
    (p5FullRealGapCube_isCompact38 u).image p6RealInclude38.continuous
  choose V hV hVplace using fun s0 : K =>
    p3Input_all_own_disc38 s0.1 C R c N hgeom
      (by
        obtain ⟨t, ht, he⟩ := s0.2
        rw [← he]
        exact gk16_full_gap_strict_placement38 u C R hfam t ht)
  have hcover : K ⊆ ⋃ s0 : K, interior (V s0) := by
    intro s hs
    let q : K := ⟨s, hs⟩
    exact mem_iUnion.mpr ⟨q, mem_interior_iff_mem_nhds.mpr (hV q)⟩
  let Vall : Set Lib.L2Seq := ⋃ s0 : K, interior (V s0)
  refine ⟨Vall, isOpen_iUnion (fun s0 => isOpen_interior),
    hcover, ?_⟩
  intro s hs k
  obtain ⟨s0, hs0⟩ := mem_iUnion.mp hs
  exact (hVplace s0) s (interior_subset hs0) k

end
end NlsGge.GK38
