import QuantumNLS.IndexedGlobalR27b
import QuantumNLS.Ext025A4HeldDependence

/-! LOCAL-016: initial-data regularity of the actual constructed flow.
The GP-04 initial-dependence proposition is a proved theorem, not a premise.
Only the compact image of one trajectory is used, never a compact ball. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Set Metric Topology
namespace QuantumNLS.IndexedRegularityR28b

/-- Every time map of a complete analytic autonomous flow is analytic. -/
theorem analytic_time_map {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {f : V → V} {φ : ℝ → V → V}
    (hf : AnalyticOnNhd ℝ f univ)
    (hd : ∀ x s, HasDerivAt (fun s => φ s x) (f (φ s x)) s)
    (h0 : ∀ x, φ 0 x = x) (t : ℝ) (u : V) : AnalyticAt ℝ (φ t) u := by
  let Ψ : Unit → ℝ → V → V := fun _ s x => φ (t*s) x
  let A : V →L[ℝ] V := t • ContinuousLinearMap.id ℝ V
  have hΨ (i : Unit) (x : V) (s : ℝ) :
      HasDerivAt (fun s => Ψ i s x) (A (f (Ψ i s x))) s := by
    have hh := (hd x (t*s)).scomp s ((hasDerivAt_id s).const_mul t)
    simpa only [Ψ,A,smul_apply,ContinuousLinearMap.id_apply,
      mul_one,Function.comp_def,id_eq] using hh
  let S : Set V := (fun s => Ψ () s u) '' Icc (0 : ℝ) 1
  have hS : IsCompact S := isCompact_Icc.image
    (continuous_iff_continuousAt.mpr fun s => (hΨ () u s).continuousAt)
  obtain ⟨r,hr,C,h⟩ := Ext025A4HeldDependence.held (V := V) (W := V)
    Unit f (fun _ => A) ‖A‖ Ψ S u hS (hf.mono (subset_univ _))
    (fun _ => le_rfl) hΨ (fun _ x => by simp [Ψ,h0])
    (fun _ s hs => ⟨s,hs,rfl⟩)
  obtain ⟨p,hp,_⟩ := h ()
  simpa only [Ψ,mul_one] using hp.analyticAt

open PhysicalTensor (L2T)
open IndexedFieldR27b IndexedGlobalR27b
attribute [local instance] InnerProductSpace.complexToReal
variable {L κ : ℝ} [Fact (0 < L)]

theorem analytic_flow (hκ : 0 < κ) (n : ℤ) (t : ℝ) (u : L2T L) :
    AnalyticAt ℝ (flow hκ n t) u :=
  analytic_time_map (fun x _ => analytic_field hκ n x)
    (flow_derivative hκ n) (flow_initial hκ n) t u

/-- C1 with respect to initial data, at every finite time. -/
theorem contDiff_flow (hκ : 0 < κ) (n : ℤ) (t : ℝ) :
    ContDiff ℝ 1 (flow (L := L) hκ n t) :=
  contDiff_iff_contDiffAt.mpr (fun u => (analytic_flow hκ n t u).contDiffAt)

/-- The full differential is invertible, with the differential of the
inverse time map as its bounded two-sided inverse. -/
theorem differential_inverse (hκ : 0 < κ) (n : ℤ) (t : ℝ) (u : L2T L) :
    (fderiv ℝ (flow hκ n (-t)) (flow hκ n t u)).comp
      (fderiv ℝ (flow hκ n t) u) = ContinuousLinearMap.id ℝ (L2T L) ∧
    (fderiv ℝ (flow hκ n t) u).comp
      (fderiv ℝ (flow hκ n (-t)) (flow hκ n t u)) =
        ContinuousLinearMap.id ℝ (L2T L) := by
  have hi (s : ℝ) (x : L2T L) : flow hκ n (-s) (flow hκ n s x) = x := by
    rw [← flow_add,add_neg_cancel,flow_initial]
  have hcomp (s : ℝ) : (flow (L := L) hκ n (-s)) ∘ (flow hκ n s) = id :=
    funext (hi s)
  have hd (s : ℝ) (x : L2T L) :=
    ((analytic_flow hκ n (-s) (flow hκ n s x)).differentiableAt.hasFDerivAt.comp x
      (analytic_flow hκ n s x).differentiableAt.hasFDerivAt).fderiv
  constructor
  · have hh := hd t u
    rw [hcomp,fderiv_id] at hh
    exact hh.symm
  · have hh := hd (-t) (flow hκ n t u)
    rw [hcomp,fderiv_id,neg_neg,hi] at hh
    exact hh.symm

end QuantumNLS.IndexedRegularityR28b
#print axioms QuantumNLS.IndexedRegularityR28b.analytic_flow
#print axioms QuantumNLS.IndexedRegularityR28b.contDiff_flow
#print axioms QuantumNLS.IndexedRegularityR28b.differential_inverse
