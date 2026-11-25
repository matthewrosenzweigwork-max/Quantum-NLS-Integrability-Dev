import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# GK-A.6: zero alternatives on a complex disc

The scalar bridge is Mathlib's `AnalyticOnNhd.preimage_zero_mem_codiscreteWithin`.
It requires a witnessed nonzero value, so the identically-zero alternative is
proved first by classical case split.  Vector-valued common zeros are treated
coordinatewise: one coordinate with one nonzero value supplies the scalar
discreteness result, and the common zero set is a subset of that coordinate's
zero set.  Compact-subdisc finiteness is the pinned compact/codiscrete theorem.
-/

set_option autoImplicit false

namespace NlsGge.Atomic.G4

open Filter Set Topology

private theorem scalar_nonzero_codiscrete {c : ℂ} {r : ℝ} {f : ℂ → ℂ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (Metric.ball c r))
    {z : ℂ} (hz : z ∈ Metric.ball c r) (hfz : f z ≠ 0) :
    f ⁻¹' ({0}ᶜ) ∈ Filter.codiscreteWithin (Metric.ball c r) := by
  exact hf.preimage_zero_mem_codiscreteWithin hfz hz (Metric.isConnected_ball hr)

/-- On a connected open disc, a scalar analytic function either vanishes
identically or its zero set inside the disc is discrete in the ambient complex
plane. -/
theorem analytic_disc_zero_alternative {c : ℂ} {r : ℝ} {f : ℂ → ℂ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (Metric.ball c r)) :
    (∀ z ∈ Metric.ball c r, f z = 0) ∨
      IsDiscrete ({z | f z = 0} ∩ Metric.ball c r) := by
  by_cases hzero : ∀ z ∈ Metric.ball c r, f z = 0
  · exact Or.inl hzero
  · push Not at hzero
    obtain ⟨z, hz, hfz⟩ := hzero
    right
    apply isDiscrete_of_codiscreteWithin
    have hset : ({z | f z = 0}ᶜ) = f ⁻¹' ({0}ᶜ) := by
      ext w
      simp
    rw [hset]
    exact scalar_nonzero_codiscrete hr hf hz hfz

private theorem restrict_codiscreteWithin {D K A : Set ℂ} (hKD : K ⊆ D)
    (hA : A ∈ Filter.codiscreteWithin D) : A ∈ Filter.codiscreteWithin K := by
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hA ⊢
  intro z hz
  apply Filter.mem_of_superset (hA z (hKD hz))
  intro w hw
  rcases hw with hwA | hwK
  · exact Or.inl hwA
  · exact Or.inr (fun hwD => hwK (hKD hwD))

private theorem finite_complement_on_compact_of_codiscreteWithin {D K A : Set ℂ}
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hA : A ∈ Filter.codiscreteWithin D) : (K \ A).Finite := by
  exact hK.finite_sdiff_of_mem_codiscreteWithin (restrict_codiscreteWithin hKD hA)

/-- A nonzero value on the disc forces only finitely many zeros on any compact
subset of the disc.  In particular this applies to every compact smaller
closed disc. -/
theorem analytic_disc_zeros_finite_on_compact {c : ℂ} {r : ℝ} {f : ℂ → ℂ}
    (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (Metric.ball c r))
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ Metric.ball c r)
    (hnonzero : ∃ z ∈ Metric.ball c r, f z ≠ 0) :
    {z | z ∈ K ∧ f z = 0}.Finite := by
  obtain ⟨z, hz, hfz⟩ := hnonzero
  have hcod := scalar_nonzero_codiscrete hr hf hz hfz
  have hfinite := finite_complement_on_compact_of_codiscreteWithin hK hKD hcod
  have hset : {z | z ∈ K ∧ f z = 0} = K \ (f ⁻¹' ({0}ᶜ)) := by
    ext w
    simp [Set.preimage]
  rw [hset]
  exact hfinite

/-- A closed subdisc strictly contained in the analytic disc has finitely many
zeros unless the function is identically zero. -/
theorem analytic_disc_zeros_finite_on_smaller_closedBall {c : ℂ} {r r' : ℝ}
    {f : ℂ → ℂ} (hr : 0 < r) (hr' : r' < r)
    (hf : AnalyticOnNhd ℂ f (Metric.ball c r))
    (hnonzero : ∃ z ∈ Metric.ball c r, f z ≠ 0) :
    {z | z ∈ Metric.closedBall c r' ∧ f z = 0}.Finite := by
  apply analytic_disc_zeros_finite_on_compact hr hf (isCompact_closedBall c r')
  · intro z hz
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hr'
  · exact hnonzero

private theorem vector_nonzero_codiscrete {ι : Type*} [Fintype ι]
    {c : ℂ} {r : ℝ} {f : ℂ → ι → ℂ}
    (hr : 0 < r) (hf : ∀ i, AnalyticOnNhd ℂ (fun z => f z i) (Metric.ball c r))
    {z : ℂ} (hz : z ∈ Metric.ball c r) {i : ι} (hfi : f z i ≠ 0) :
    {w | ∃ i, f w i ≠ 0} ∈ Filter.codiscreteWithin (Metric.ball c r) := by
  have hcod := scalar_nonzero_codiscrete hr (hf i) hz hfi
  exact Filter.mem_of_superset hcod (by
    intro w hw
    exact ⟨i, hw⟩)

/-- For an analytic finite-dimensional coordinate vector, either all
coordinates vanish throughout the disc or the common zero set is discrete.
The finite index type is an explicit model of a finite-dimensional complex
vector space; any one nonzero coordinate suffices. -/
theorem analytic_vector_disc_zero_alternative {ι : Type*} [Fintype ι]
    {c : ℂ} {r : ℝ} {f : ℂ → ι → ℂ} (hr : 0 < r)
    (hf : ∀ i, AnalyticOnNhd ℂ (fun z => f z i) (Metric.ball c r)) :
    (∀ z ∈ Metric.ball c r, ∀ i, f z i = 0) ∨
      IsDiscrete ({z | ∀ i, f z i = 0} ∩ Metric.ball c r) := by
  by_cases hzero : ∀ z ∈ Metric.ball c r, ∀ i, f z i = 0
  · exact Or.inl hzero
  · push Not at hzero
    obtain ⟨z, hz, i, hfi⟩ := hzero
    right
    apply isDiscrete_of_codiscreteWithin
    have hset : ({z | ∀ i, f z i = 0}ᶜ) = {z | ∃ i, f z i ≠ 0} := by
      ext w
      simp
    rw [hset]
    exact vector_nonzero_codiscrete hr hf hz hfi

/-- The common zeros of an analytic finite-dimensional coordinate vector are
finite on any compact subset of the disc whenever one coordinate is nonzero
somewhere in the disc. -/
theorem analytic_vector_disc_zeros_finite_on_compact {ι : Type*} [Fintype ι]
    {c : ℂ} {r : ℝ} {f : ℂ → ι → ℂ}
    (hr : 0 < r) (hf : ∀ i, AnalyticOnNhd ℂ (fun z => f z i) (Metric.ball c r))
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ Metric.ball c r)
    (hnonzero : ∃ z ∈ Metric.ball c r, ∃ i, f z i ≠ 0) :
    {z | z ∈ K ∧ ∀ i, f z i = 0}.Finite := by
  obtain ⟨z, hz, i, hfi⟩ := hnonzero
  have hcod := vector_nonzero_codiscrete hr hf hz hfi
  have hfinite := finite_complement_on_compact_of_codiscreteWithin hK hKD hcod
  have hset : {z | z ∈ K ∧ ∀ i, f z i = 0} = K \ {z | ∃ i, f z i ≠ 0} := by
    ext w
    simp
  rw [hset]
  exact hfinite

/-- The common zeros of an analytic finite-dimensional coordinate vector are
finite on every smaller closed disc unless the vector vanishes identically. -/
theorem analytic_vector_disc_zeros_finite_on_smaller_closedBall {ι : Type*} [Fintype ι]
    {c : ℂ} {r r' : ℝ} {f : ℂ → ι → ℂ}
    (hr : 0 < r) (hr' : r' < r)
    (hf : ∀ i, AnalyticOnNhd ℂ (fun z => f z i) (Metric.ball c r))
    (hnonzero : ∃ z ∈ Metric.ball c r, ∃ i, f z i ≠ 0) :
    {z | z ∈ Metric.closedBall c r' ∧ ∀ i, f z i = 0}.Finite := by
  apply analytic_vector_disc_zeros_finite_on_compact hr hf (isCompact_closedBall c r')
  · intro z hz
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hr'
  · exact hnonzero

end NlsGge.Atomic.G4
