import Mathlib
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.StdRootBranchesDefs
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.ContourAction
import NlsGge.GK38.ContourActionDeformation
import NlsGge.GK38.TauGammaCircleMoments
import NlsGge.GK38.IsolatingRootMultisets
import NlsGge.Atomic.G2.G2045SupA1

/- G2-045 SUPPORT A3 (proof development, AUTHOR; not reviewed; semantic fidelity gate open).
   Geometry of the finite-gap contour sum on the concrete isolating family `discC/discR` of `φ ∈ gkW`:
   for a finite set `S`, `K = ⋃_{n∈S} [lamMinus n, lamPlus n]` and any `F` holomorphic off `K` that agrees with
   `deriv (discrim φ) / canonRoot38 φ` on the root domain,
   * (large circle) `∑_{n∈S} ∮_{C_n} z^k D/c = ∮_{|z|=ρ} z^k F`  for every `ρ` with `K ⊆ ball 0 ρ`;
   * (empty discs) `∮_{C_n} z^k D/c = 0` for `n ∉ S`.
   Inputs: landed isolating family, A1 (Dixon-cycle multi-circle deformation). No hypothesis beyond the display. -/
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.G2045SupA3
noncomputable section

/-- the cut set of the noncollapsed gaps in `S` (the body of `finiteGapCuts u S` at `φ = realSlice u`). -/
def cutsOf (φ : PotPair) (S : Finset ℤ) : Set ℂ :=
  ⋃ n ∈ (S : Set ℤ), segment ℝ (lamMinus φ n) (lamPlus φ n)

theorem isClosed_cutsOf (φ : PotPair) (S : Finset ℤ) : IsClosed (cutsOf φ S) := by
  unfold cutsOf
  have : ∀ n : ℤ, IsClosed (segment ℝ (lamMinus φ n) (lamPlus φ n)) := by
    intro n
    rw [segment_eq_image]
    exact (isCompact_Icc.image (by fun_prop)).isClosed
  simpa [Set.biUnion_eq_iUnion] using
    (isClosed_biUnion_finset (s := S) (f := fun n => segment ℝ (lamMinus φ n) (lamPlus φ n))
      (fun n _ => this n))

theorem cutsOf_subset (φ : PotPair) (S : Finset ℤ) : cutsOf φ S ⊆ gapSegments38 φ := by
  intro z hz
  obtain ⟨n, -, hn⟩ := Set.mem_iUnion₂.1 hz
  exact Set.mem_iUnion.2 ⟨n, hn⟩

theorem integrand_eq (φ : PotPair) (hφ : φ ∈ gkW) (F : ℂ → ℂ)
    (hFeq : ∀ z : ℂ, (φ, z) ∈ rootDomain38 → deriv (discrim φ) z / canonRoot38 φ z = F z)
    (k : ℕ) (n : ℤ) :
    circleIntegral (fun z : ℂ => z ^ k * deriv (discrim φ) z / canonRoot38 φ z)
        (discC φ n) (discR φ n) =
      circleIntegral (fun z : ℂ => z ^ k * F z) (discC φ n) (discR φ n) := by
  have hCR := isolating_family38 φ hφ
  have hρ : 0 < discR φ n := isolating_radius_pos38 hCR n
  apply circleIntegral.integral_congr hρ.le
  intro z hz
  have hz' : z ∈ actionCutDomain38 φ := fixed_sphere_subset φ (discC φ) (discR φ) hCR n hz
  rw [actionCutDomain_eq_fibre38 φ hφ] at hz'
  have := hFeq z hz'
  simp only
  rw [mul_div_assoc, this]

theorem sum_circles_eq_large (φ : PotPair) (hφ : φ ∈ gkW) (S : Finset ℤ) (F : ℂ → ℂ)
    (hFan : DifferentiableOn ℂ F (cutsOf φ S)ᶜ)
    (hFeq : ∀ z : ℂ, (φ, z) ∈ rootDomain38 → deriv (discrim φ) z / canonRoot38 φ z = F z)
    (ρ : ℝ) (hρ : 0 < ρ) (hKρ : cutsOf φ S ⊆ ball (0 : ℂ) ρ) (k : ℕ) :
    ∑ n ∈ S, circleIntegral (fun z : ℂ => z ^ k * deriv (discrim φ) z / canonRoot38 φ z)
        (discC φ n) (discR φ n) = circleIntegral (fun z : ℂ => z ^ k * F z) 0 ρ := by
  have hCR := isolating_family38 φ hφ
  obtain ⟨c, N, hgeom, hspec⟩ := hCR
  have hCR' := isolating_family38 φ hφ
  have hpos : ∀ n ∈ S, 0 < discR φ n := fun n _ => isolating_radius_pos38 hCR' n
  have hf : DifferentiableOn ℂ (fun z : ℂ => z ^ k * F z) (cutsOf φ S)ᶜ :=
    (differentiableOn_id.pow k).mul hFan
  have hsph : ∀ n ∈ S, sphere (discC φ n) (discR φ n) ⊆ (cutsOf φ S)ᶜ := by
    intro n _ z hz hzK
    have hz' : z ∈ actionCutDomain38 φ := fixed_sphere_subset φ (discC φ) (discR φ) hCR' n hz
    exact hz' (cutsOf_subset φ S hzK)
  have hidx : ∀ w ∈ cutsOf φ S, ∃ n ∈ S, ‖w - discC φ n‖ < discR φ n ∧
      ∀ m ∈ S, m ≠ n → discR φ m < ‖w - discC φ m‖ := by
    intro w hw
    obtain ⟨n, hn, hwn⟩ := Set.mem_iUnion₂.1 hw
    have hwb : w ∈ ball (discC φ n) (discR φ n) := (hspec.1 n).1 hwn
    refine ⟨n, hn, by rw [← dist_eq_norm]; exact mem_ball.1 hwb, fun m hm hmn => ?_⟩
    by_contra hle
    push Not at hle
    have hcl : w ∈ closedBall (discC φ m) (discR φ m) := by
      rw [mem_closedBall, dist_eq_norm]; exact hle
    exact hmn (isolating_closed_index38 (discC φ) (discR φ) c N hgeom n m hwb hcl).symm
  have := NlsGge.G2045SupA1.circle_eq_sum_circles (cutsOf φ S) (isClosed_cutsOf φ S) ρ hρ hKρ S
    (discC φ) (discR φ) hpos hsph hidx hf
  rw [this]
  exact Finset.sum_congr rfl fun n _ => integrand_eq φ hφ F hFeq k n

theorem circle_zero_of_not_mem (φ : PotPair) (hφ : φ ∈ gkW) (S : Finset ℤ) (F : ℂ → ℂ)
    (hFan : DifferentiableOn ℂ F (cutsOf φ S)ᶜ)
    (hFeq : ∀ z : ℂ, (φ, z) ∈ rootDomain38 → deriv (discrim φ) z / canonRoot38 φ z = F z)
    (k : ℕ) (n : ℤ) (hn : n ∉ S) :
    circleIntegral (fun z : ℂ => z ^ k * deriv (discrim φ) z / canonRoot38 φ z)
        (discC φ n) (discR φ n) = 0 := by
  have hCR := isolating_family38 φ hφ
  obtain ⟨c, N, hgeom, hspec⟩ := hCR
  have hpos : 0 < discR φ n := isolating_radius_pos38 (isolating_family38 φ hφ) n
  rw [integrand_eq φ hφ F hFeq k n]
  have hball : closedBall (discC φ n) (discR φ n) ⊆ (cutsOf φ S)ᶜ := by
    intro w hw hwK
    obtain ⟨j, hj, hwj⟩ := Set.mem_iUnion₂.1 hwK
    have hwb : w ∈ ball (discC φ j) (discR φ j) := (hspec.1 j).1 hwj
    have := isolating_closed_index38 (discC φ) (discR φ) c N hgeom j n hwb hw
    exact hn (this ▸ hj)
  have hf : DifferentiableOn ℂ (fun z : ℂ => z ^ k * F z) (cutsOf φ S)ᶜ :=
    (differentiableOn_id.pow k).mul hFan
  have hU : IsOpen (cutsOf φ S)ᶜ := (isClosed_cutsOf φ S).isOpen_compl
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hpos.le
    Set.countable_empty
  · exact hf.continuousOn.mono hball
  · intro z hz
    exact (hf.differentiableAt (hU.mem_nhds (hball (ball_subset_closedBall hz.1))))

end
end NlsGge.G2045SupA3
