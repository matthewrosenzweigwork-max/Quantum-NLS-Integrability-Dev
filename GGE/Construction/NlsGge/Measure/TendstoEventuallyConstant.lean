import Mathlib.Topology.Instances.Real.Lemmas

/-! Minimal eventual-constant/unique-limit prerequisite isolated from the
third actual L2 cylinder proof; it is not an RN theorem. -/
set_option autoImplicit false
open Filter
open scoped Topology
namespace NlsGge.Measure
lemma tendsto_limit_eq_of_eventually_constant {α β : Type*}
    [TopologicalSpace β] [T2Space β] {l : Filter α} [NeBot l]
    (f : α → β) (a b : β)
    (hlim : Tendsto f l (nhds a)) (hevent : ∀ᶠ x in l, f x = b) : a = b := by
  have heq : f =ᶠ[l] (fun _ => b) := hevent
  have hc : Tendsto f l (nhds b) := tendsto_const_nhds.congr' heq.symm
  exact tendsto_nhds_unique hlim hc
end NlsGge.Measure
