import NlsGge.GK38.AbelianNormalizedRealTrace

/-! A genuine global normalized omitted zero branch agrees locally with ANY
actual local analytic normalized branch having a real gap-zero seed. This
transfers earned local estimates to the glued global branch using actual
inverse continuation, without asserting equality of full nth completions. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6Global_local_normalized_ball_agreement38 (n : ℤ) (W : Set PotPair)
    (_hW : IsOpen W) (hWW : W ⊆ gkW) (F : PotPair → P2Space38 n)
    (hF : ContinuousOn F W) (hFz : ∀ φ ∈ W, p2Fn38 n (φ,F φ)=0)
    (hFi : ∀ φ ∈ W,
      (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (φ,t)) (F φ)).IsInvertible)
    (u : PhysicalL2) (_huW : realSlice u ∈ W) (d : ℝ)
    (S : PotPair → Lib.L2Seq) (hS : ContinuousOn S (ball (realSlice u) d))
    (hSz : ∀ φ ∈ ball (realSlice u) d, p2Fn38 n (φ,p2Restrict38 n (S φ))=0)
    (ρ : ℝ) (hρ : 0 < ρ) (hρd : ρ ≤ d)
    (hρW : ball (realSlice u) ρ ⊆ W)
    (t q : P3RealSpace38 n)
    (ht : t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0)
    (hq : q ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u q=0)
    (hFt : F (realSlice u)=p3RealInclude38 n t)
    (hSq : p2Restrict38 n (S (realSlice u))=p3RealInclude38 n q) :
    ∀ φ ∈ ball (realSlice u) ρ, F φ=p2Restrict38 n (S φ) := by
  have hsub : ball (realSlice u) ρ ⊆ ball (realSlice u) d := ball_subset_ball hρd
  let X : Type := ball (realSlice u) ρ
  let : PreconnectedSpace X :=
    isPreconnected_iff_preconnectedSpace.mp (convex_ball (realSlice u) ρ).isPreconnected
  let χ : X → PotPair := fun x => x.val
  let f : X → P2Space38 n := fun x => F x.val
  let g : X → P2Space38 n := fun x => p2Restrict38 n (S x.val)
  have hf : Continuous f := hF.comp_continuous continuous_subtype_val
    (fun x : X => hρW x.property)
  have hg : Continuous g := (p2Restrict38 n).continuous.comp
    (hS.comp_continuous continuous_subtype_val (fun x : X => hsub x.property))
  have htq : t=q := by
    obtain ⟨b,_hb,hu⟩ := p5Actual_gap_solution_pointwise_unique38 n u
    exact (hu t ht).trans (hu q hq).symm
  have heq : f=g := p6Omitted_zero_branches_eq_of_continuation38 n χ
    continuous_subtype_val (fun x => hWW (hρW x.property)) f g hf hg
    (fun x => hFz x.val (hρW x.property)) (fun x => hSz x.val (hsub x.property))
    (fun x => hFi x.val (hρW x.property)) ⟨realSlice u,mem_ball_self hρ⟩
    (by change F (realSlice u)=p2Restrict38 n (S (realSlice u)); rw [hFt,hSq,htq])
  intro φ hφ
  exact congrFun heq ⟨φ,hφ⟩

end
end NlsGge.GK38
