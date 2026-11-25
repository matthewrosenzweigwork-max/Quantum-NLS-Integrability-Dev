import Mathlib

/- T-013 PROOF01 (proof development). Proof of the H3 statement T-013_COMMAND01 (verbatim below).
   Packet: WORK_PACKETS/T/T-013.md (PARTIAL, parent NEW-F10).
   Route: |f - g| = f + g - 2 min(f, g). min(f_N, g) -> g in measure and is dominated by g, so its integrals
   converge along every subsequence (almost-sure subsequence + dominated convergence), hence along the whole
   sequence (subsequence principle). Then the integral identity gives the L1 convergence. No sorry. -/

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace NlsGge.Atomic.T.T013

theorem T013_helper : ((
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ),
    (∀ N : ℕ, ∀ ω : Ω, 0 ≤ f N ω) → (∀ ω : Ω, 0 ≤ g ω) →
    (∀ N : ℕ, MeasureTheory.Integrable (f N) μ) → MeasureTheory.Integrable g μ →
    MeasureTheory.TendstoInMeasure μ f Filter.atTop g →
    Filter.Tendsto (fun N : ℕ => ∫ ω, f N ω ∂μ) Filter.atTop (nhds (∫ ω, g ω ∂μ)) →
    Filter.Tendsto (fun N : ℕ => ∫ ω, |f N ω - g ω| ∂μ) Filter.atTop (nhds 0)
  : Prop)) := by
  intro Ω _ μ _ f g hf0 hg0 hfi hgi hconv hint
  -- Step 1: min(f_N, g) converges to g in measure.
  have hmc : MeasureTheory.TendstoInMeasure μ (fun N ω => min (f N ω) (g ω)) Filter.atTop g := by
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv ε hε)
      (fun N => zero_le) (fun N => ?_)
    apply MeasureTheory.measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    refine le_trans hω ?_
    rw [edist_dist, edist_dist]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total (f N ω) (g ω) with h | h
    · simp [min_eq_left h]
    · rw [min_eq_right h, sub_self, abs_zero]
      exact abs_nonneg _
  -- measurability and integrability of the minima
  have hmeas : ∀ N : ℕ, MeasureTheory.AEStronglyMeasurable (fun ω => min (f N ω) (g ω)) μ :=
    fun N => (continuous_fst.min continuous_snd).comp_aestronglyMeasurable
      ((hfi N).aestronglyMeasurable.prodMk hgi.aestronglyMeasurable)
  have hbnd : ∀ N : ℕ, ∀ ω : Ω, ‖min (f N ω) (g ω)‖ ≤ g ω := by
    intro N ω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hf0 N ω) (hg0 ω))]
    exact min_le_right _ _
  have hmint : ∀ N : ℕ, MeasureTheory.Integrable (fun ω => min (f N ω) (g ω)) μ :=
    fun N => hgi.mono' (hmeas N) (Filter.Eventually.of_forall (hbnd N))
  -- Step 2: the integrals of the minima converge along every subsequence.
  have hsub : ∀ ns : ℕ → ℕ, Filter.Tendsto ns Filter.atTop Filter.atTop →
      ∃ ms : ℕ → ℕ, Filter.Tendsto (fun n => ∫ ω, min (f (ns (ms n)) ω) (g ω) ∂μ) Filter.atTop
        (nhds (∫ ω, g ω ∂μ)) := by
    intro ns hns
    have hc : MeasureTheory.TendstoInMeasure μ (fun n ω => min (f (ns n) ω) (g ω)) Filter.atTop g :=
      fun ε hε => (hmc ε hε).comp hns
    obtain ⟨ms, _, hae⟩ := hc.exists_seq_tendsto_ae
    refine ⟨ms, ?_⟩
    exact MeasureTheory.tendsto_integral_of_dominated_convergence (fun ω => g ω)
      (fun n => hmeas (ns (ms n))) hgi
      (fun n => Filter.Eventually.of_forall (fun ω => hbnd (ns (ms n)) ω)) hae
  -- Step 3: the whole sequence (subsequence principle).
  have hmint_lim : Filter.Tendsto (fun N => ∫ ω, min (f N ω) (g ω) ∂μ) Filter.atTop
      (nhds (∫ ω, g ω ∂μ)) :=
    tendsto_of_subseq_tendsto (fun ns hns => hsub ns hns)
  -- Step 4: |a - b| = a + b - 2 min(a, b) pointwise.
  have hpt : ∀ N ω, |f N ω - g ω| = f N ω + g ω - 2 * min (f N ω) (g ω) := by
    intro N ω
    rcases le_total (f N ω) (g ω) with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]
      ring
  have hfun : (fun N : ℕ => ∫ ω, |f N ω - g ω| ∂μ) =
      fun N : ℕ => (∫ ω, f N ω ∂μ) + (∫ ω, g ω ∂μ) - 2 * ∫ ω, min (f N ω) (g ω) ∂μ := by
    funext N
    have e : ∫ ω, (f N ω + g ω - 2 * min (f N ω) (g ω)) ∂μ =
        ∫ ω, (f N ω + g ω) ∂μ - ∫ ω, 2 * min (f N ω) (g ω) ∂μ :=
      MeasureTheory.integral_sub ((hfi N).add hgi) ((hmint N).const_mul 2)
    simp_rw [hpt N]
    rw [e, MeasureTheory.integral_add (hfi N) hgi, MeasureTheory.integral_const_mul]
  rw [hfun]
  have hlim := (hint.add (tendsto_const_nhds (x := ∫ ω, g ω ∂μ))).sub (hmint_lim.const_mul 2)
  have hval : (∫ ω, g ω ∂μ) + (∫ ω, g ω ∂μ) - 2 * (∫ ω, g ω ∂μ) = 0 := by ring
  rw [hval] at hlim
  exact hlim

end NlsGge.Atomic.T.T013
