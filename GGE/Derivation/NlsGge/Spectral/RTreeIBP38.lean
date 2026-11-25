import NlsGge.Spectral.RTreeCore38
import NlsGge.Spectral.R3cResolventL2_38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.HierarchyRiccati.Core

/-! # RTree piece T2a: integration by parts for resolvent-tree terms

`RTerm38.ibp`: for every tree `T` and root order `d0`,
`pair38 (∂^{d0+1}U) (eval T) + Σ_{T' ∈ bumps T} pair38 (∂^{d0}U) (eval T') = 0`.
It follows from the Leibniz derivative `RTree38.perC1` and the periodic integration by parts
`pair38_ibp`. -/

/-- finite sums of continuous functions are continuous -/
theorem list_sum_continuous38 {ι : Type*} (L : List ι) (F : ι → ℝ → ℂ)
    (hF : ∀ i ∈ L, Continuous (F i)) : Continuous (fun x => (L.map (fun i => F i x)).sum) := by
  induction L with
  | nil => simpa using continuous_const
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hF a (by simp)).add (ih (fun i hi => hF i (by simp [hi])))

/-- linearity of the pairing over a finite list of continuous functions -/
theorem pair38_list_sum_right {ι : Type*} (f : ℝ → ℂ) (hf : Continuous f) (L : List ι)
    (F : ι → ℝ → ℂ) (hF : ∀ i ∈ L, Continuous (F i)) :
    pair38 f (fun x => (L.map (fun i => F i x)).sum) = (L.map (fun i => pair38 f (F i))).sum := by
  induction L with
  | nil => simp [pair38]
  | cons a L ih =>
    have h1 : Continuous (F a) := hF a (by simp)
    have h2 := list_sum_continuous38 L F (fun i hi => hF i (by simp [hi]))
    have ih' := ih (fun i hi => hF i (by simp [hi]))
    simp only [List.map_cons, List.sum_cons]
    unfold pair38 at ih' ⊢
    have e : (fun x => f x * (F a x + (L.map (fun i => F i x)).sum)) =
        fun x => f x * F a x + f x * (L.map (fun i => F i x)).sum := by
      funext x; ring
    have hadd := intervalIntegral.integral_add (μ := volume) (a := (0:ℝ)) (b := 1)
      (f := fun x => f x * F a x) (g := fun x => f x * (L.map (fun i => F i x)).sum)
      ((hf.mul h1).intervalIntegrable 0 1) ((hf.mul h2).intervalIntegrable 0 1)
    rw [e]
    simp only at ih'
    rw [hadd, ih']

theorem RTerm38.ibp {η : ℝ} (hη : 0 < η) (N : ℕ) (z : FourierPlane N) (d0 : ℕ) (T : RTree38) :
    pair38 (leafU38 N z (d0+1)) (T.eval η N z) +
      ((T.bumps).map (fun T' => pair38 (leafU38 N z d0) (T'.eval η N z))).sum = 0 := by
  have hf := perC1_leafU38 N z d0
  have hg := RTree38.perC1 hη N z T
  have h := pair38_ibp hf hg
  rw [pair38_list_sum_right (leafU38 N z d0) hf.cont T.bumps (fun T' x => T'.eval η N z x)
    (fun T' _ => (RTree38.eval_cont_per hη N z T').1)] at h
  rw [h]
  ring

end NlsGge.SpectralFoundations
end
