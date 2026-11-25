import QuantumNLS.Q07UniformDifferentialsR16

/-! One named package for the verified analytic data of R-B90ACAE9.
The source's window-Hamiltonian Hessian still requires identifying and twice
differentiating its contour integral; this package states no such conclusion. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter Topology
namespace QuantumNLS.Q07UniformCutsR16
open PhysicalTensor (L2T)
open Q07LogDifferentialsR16
open Q07SobolevCutsR16 (sobolevClass)
open PROP017UniformN (cutSeq)
open ResolventNeighborhood (GammaN)
variable {L κ : ℝ} [Fact (0 < L)]

/-- Uniform strip decay, actual measure gaps, regular normalized logarithm
charts, and uniform full logarithm Hessians, with only the physical source
parameters as hypotheses. There is no Banach-bridge or estimate premise. -/
theorem q07_uniform_analytic_data (hκ : 0 < κ) {s : ℝ} (hs : 0 < s) (B : ℝ)
    {h : ℝ} (hh : 0 < h) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in cocompact ℝ,
      ∀ u ∈ sobolevClass (L := L) s B, ∀ y : ℝ, |y| ≤ h →
        ‖NormalizedTransfer.productSymbol L κ u (Q07StripInteractionR16.spectral t y)-1-
          Complex.exp (Complex.I*Q07StripInteractionR16.spectral t y*L)‖ < ε) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∃ l0 : ℕ, ∃ C d : ℝ, 0 ≤ C ∧ 0 < d ∧
      ∀ l : ℕ, l0 ≤ l → ∀ u ∈ sobolevClass (L := L) s B,
        ∀ v : L2T L, ‖v-u‖ < δ →
          (∀ a : ℝ, (a = cutSeq L l ∨ a = -cutSeq L l) →
            (∀ t : ℝ, |t| < 1/L → |PhysicalL2BandGeometry.d (κ := κ) v (a+t)| < 3/2) ∧
            FullMass.Mmeas κ v (Ioo (a-1/L) (a+1/L)) = 0) ∧
          ∀ z ∈ GammaN (cutSeq L l) h,
            RootCauchyJointR9.Regular κ (v,z) ∧ d ≤ ‖physicalDifference hκ z v‖ ∧
            AnalyticAt ℝ (logarithm hκ z) v ∧ ∀ w q : L2T L,
              ‖second (logarithm hκ z) v w q‖ ≤ C*‖w‖*‖q‖ := by
  refine ⟨fun ε hε => Q07StripUniformR16.uniform_sobolev_strip hκ.le hs B h hε, ?_⟩
  obtain ⟨δ1,h1,l1,R,d,hR,hd,hgeo⟩ := Q07UniformGeometryR16.uniform_contour_data (L := L) hκ hs B hh
  obtain ⟨δ2,h2,l2,C,hC,hH⟩ := Q07UniformDifferentialsR16.uniform_log_hessians (L := L) hκ hs B hh
  obtain ⟨δ3,h3,l3,hcuts⟩ := Q07SobolevCutsR16.uniform_sobolev_cuts_near (L := L) hκ hs B
  refine ⟨min δ1 (min δ2 δ3), lt_min h1 (lt_min h2 h3), max l1 (max l2 l3),
    C,d,hC,hd,?_⟩
  intro l hl u hu v hv
  have hl1 := le_trans (le_max_left l1 (max l2 l3)) hl
  have hl2 := le_trans (le_trans (le_max_left l2 l3) (le_max_right l1 (max l2 l3))) hl
  have hl3 := le_trans (le_trans (le_max_right l2 l3) (le_max_right l1 (max l2 l3))) hl
  have hv1 := hv.trans_le (min_le_left δ1 (min δ2 δ3))
  have hv2 := hv.trans_le ((min_le_right δ1 (min δ2 δ3)).trans (min_le_left δ2 δ3))
  have hv3 := hv.trans_le ((min_le_right δ1 (min δ2 δ3)).trans (min_le_right δ2 δ3))
  refine ⟨?_,?_⟩
  · intro a ha
    obtain ⟨hc,-,hg⟩ := hcuts l hl3 u hu v hv3 a ha
    exact ⟨hc,hg⟩
  · intro z hz
    obtain ⟨-,hg⟩ := hgeo l hl1 u hu v hv1
    obtain ⟨hp,hD⟩ := hg z hz
    exact ⟨hp,hD,logarithm_analytic hκ hp,(hH l hl2 u hu v hv2 z hz).2⟩

end QuantumNLS.Q07UniformCutsR16
