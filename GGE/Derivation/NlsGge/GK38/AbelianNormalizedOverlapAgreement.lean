import NlsGge.GK38.AbelianNormalizedRealTrace
import NlsGge.GK38.AbelianRealSliceProjection

/-! Actual omitted normalized branches agree on overlaps of real-centered
complex balls. Every overlap point retracts to a real overlap point, where
genuine global real normalization is rigid. Connected continuation then earns
the whole overlap agreement. Full padded nth seed coordinates are not glued. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6Omitted_normalized_complex_ball_overlap_agreement38 (n : ℤ)
    (u v : PhysicalL2) (r s : ℝ)
    (S T : PotPair → Lib.L2Seq)
    (hS : ContinuousOn S (ball (realSlice u) r))
    (hT : ContinuousOn T (ball (realSlice v) s))
    (hW : ball (realSlice u) r ⊆ gkW)
    (hSz : ∀ φ ∈ ball (realSlice u) r, p2Fn38 n (φ,p2Restrict38 n (S φ))=0)
    (hTz : ∀ φ ∈ ball (realSlice v) s, p2Fn38 n (φ,p2Restrict38 n (T φ))=0)
    (hInv : ∀ φ ∈ ball (realSlice u) r,
      (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (φ,t))
        (p2Restrict38 n (S φ))).IsInvertible)
    (σ τ : PhysicalL2 → P3RealSpace38 n)
    (hσ : ∀ w, σ w ∈ p5RealGapCube38 n w ∧ p3RealFn38 n w (σ w)=0)
    (hτ : ∀ w, τ w ∈ p5RealGapCube38 n w ∧ p3RealFn38 n w (τ w)=0)
    (hSreal : ∀ w, realSlice w ∈ ball (realSlice u) r →
      p2Restrict38 n (S (realSlice w))=p3RealInclude38 n (σ w))
    (hTreal : ∀ w, realSlice w ∈ ball (realSlice v) s →
      p2Restrict38 n (T (realSlice w))=p3RealInclude38 n (τ w)) :
    ∀ φ ∈ ball (realSlice u) r ∩ ball (realSlice v) s,
      p2Restrict38 n (S φ)=p2Restrict38 n (T φ) := by
  intro φ hφ
  let O : Set PotPair := ball (realSlice u) r ∩ ball (realSlice v) s
  let X : Type := O
  let : PreconnectedSpace X := isPreconnected_iff_preconnectedSpace.mp
    (((convex_ball (realSlice u) r).inter (convex_ball (realSlice v) s)).isPreconnected)
  let χ : X → PotPair := fun x => x.val
  let f : X → P2Space38 n := fun x => p2Restrict38 n (S x.val)
  let g : X → P2Space38 n := fun x => p2Restrict38 n (T x.val)
  have hf : Continuous f := (p2Restrict38 n).continuous.comp
    (hS.comp_continuous continuous_subtype_val (fun x : X => x.property.1))
  have hg : Continuous g := (p2Restrict38 n).continuous.comp
    (hT.comp_continuous continuous_subtype_val (fun x : X => x.property.2))
  let w : PhysicalL2 := p6PotentialRealProjection38 φ
  have hwS : realSlice w ∈ ball (realSlice u) r :=
    p6RealSlice_projection_mem_ball38 φ u r hφ.1
  have hwT : realSlice w ∈ ball (realSlice v) s :=
    p6RealSlice_projection_mem_ball38 φ v s hφ.2
  have hστ : σ w=τ w := by
    obtain ⟨a,_ha,hu⟩ := p5Actual_gap_solution_pointwise_unique38 n w
    exact (hu (σ w) (hσ w)).trans (hu (τ w) (hτ w)).symm
  have hbase : f ⟨realSlice w,hwS,hwT⟩=g ⟨realSlice w,hwS,hwT⟩ := by
    change p2Restrict38 n (S (realSlice w))=p2Restrict38 n (T (realSlice w))
    rw [hSreal w hwS,hTreal w hwT,hστ]
  have heq : f=g := p6Omitted_zero_branches_eq_of_continuation38 n χ
    continuous_subtype_val (fun x => hW x.property.1) f g hf hg
    (fun x => hSz x.val x.property.1) (fun x => hTz x.val x.property.2)
    (fun x => hInv x.val x.property.1) ⟨realSlice w,hwS,hwT⟩ hbase
  exact congrFun heq ⟨φ,hφ⟩

end
end NlsGge.GK38
