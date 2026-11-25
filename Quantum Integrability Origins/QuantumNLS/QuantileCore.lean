import Mathlib
import QuantumNLS.QuantileForm
import QuantumNLS.FormCoreMollifyFinal
import QuantumNLS.FormCoreFamilies

/-!
# R-8F7E0394: the core in quantile coordinates (`IsFormCore` for a `BulkMeasure`)

For `μ` with `BulkResponseForm.BulkMeasure μ` (probability, atomless, finite second moment, `CoreDensity` = the hypotheses of `CC:F03:core`):
* `coreHyp_of_coreDensity`: `CoreDensity μ` gives a density `ρ` with `FormCore.CoreHyp ρ` and `μ = ρ dx`.
* `isFormCore_bulk`: `BulkResponseForm.IsFormCore L κ (bulkQuantile μ) {F | IsSmoothQuantilePullback (bulkQuantile μ) F}`: the pullbacks `h ∘ Q`, `h ∈ C_c^∞(ℝ;ℝ)`, form a core of the quantile form
  (the lemma `CC:F03:core` transported by the isometry `h ↦ h∘Q`, `QuantileForm`; only atomlessness, the probability property and `CoreDensity` are used).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal ContDiff Real

noncomputable section

namespace QuantumNLS.QuantileCore

open QuantumNLS.QuantileTransport (quantile qm map_qm measurable_qm qm_of_mem leb01)
open QuantumNLS.BulkResponseForm
open QuantumNLS.QuantileForm
open QuantumNLS.FormCore (CoreHyp muRho formN formE formL2 dq core_density' formE_le_lip)

/-- `CoreDensity` yields `CoreHyp`. -/
theorem coreHyp_of_coreDensity (μ : Measure ℝ) (hp : IsProbabilityMeasure μ) (hc : CoreDensity μ) :
    ∃ ρ : ℝ → ℝ, CoreHyp ρ ∧ μ = muRho ρ := by
  obtain ⟨ρ, hcont, hnn, ⟨C, hC⟩, hμ, ι, a, b, hab, hunion, hdisj, hloc, hsmooth, hend⟩ := hc.exists_density
  refine ⟨ρ, ⟨hcont, hnn, ⟨C, hC⟩, ?_, ?_⟩, hμ⟩
  · have : muRho ρ = μ := hμ.symm
    rw [this]; infer_instance
  · intro R
    set P : Set ℝ := {x | 0 < ρ x} with hP
    have hPopen : IsOpen P := isOpen_lt continuous_const hcont
    set E : Set ℝ := range a ∪ range b with hE
    -- the frontier lies in the endpoint set
    have hfr : frontier P ⊆ E := by
      intro x hx
      by_contra hxE
      have hxP : x ∉ P := by
        have := hx.2; rw [hPopen.interior_eq] at this; exact this
      obtain ⟨U, hU, hUfin⟩ := hloc x
      set A : Set ℝ := U ∩ E with hA
      have hAcl : IsClosed A := hUfin.isClosed
      have hxA : x ∉ A := fun h => hxE h.2
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hU (hAcl.isOpen_compl.mem_nhds hxA))
      have hball_E : ∀ y ∈ Metric.ball x r, y ∉ E := fun y hy hyE => (hball hy).2 ⟨(hball hy).1, hyE⟩
      have hno : Metric.ball x r ∩ P = ∅ := by
        refine eq_empty_iff_forall_notMem.2 fun y ⟨hyb, hyP⟩ => ?_
        have hyP' : y ∈ ⋃ i, Ioo (a i) (b i) := hunion ▸ hyP
        obtain ⟨i, hi⟩ := mem_iUnion.1 hyP'
        have ha : a i ∉ Metric.ball x r := fun h => hball_E _ h (Or.inl ⟨i, rfl⟩)
        have hb : b i ∉ Metric.ball x r := fun h => hball_E _ h (Or.inr ⟨i, rfl⟩)
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hyb ha hb
        have hai : a i ≤ x - r := by
          by_contra h; push Not at h
          exact ha ⟨by linarith [hi.1], by linarith [hi.1, hyb.2]⟩
        have hbi : x + r ≤ b i := by
          by_contra h; push Not at h
          exact hb ⟨by linarith [hi.2, hyb.1], by linarith [hi.2]⟩
        have hxi : x ∈ Ioo (a i) (b i) := ⟨by linarith, by linarith⟩
        have : x ∈ P := by rw [hunion]; exact mem_iUnion.2 ⟨i, hxi⟩
        exact hxP this
      have : x ∈ closure P := hx.1
      rw [mem_closure_iff] at this
      obtain ⟨y, hy1, hy2⟩ := this (Metric.ball x r) Metric.isOpen_ball (Metric.mem_ball_self hr)
      exact (eq_empty_iff_forall_notMem.1 hno) y ⟨hy1, hy2⟩
    -- local finiteness on `Icc (-R) R`
    have hEfin : (E ∩ Icc (-R) R).Finite := by
      have hcomp : IsCompact (Icc (-R) R) := isCompact_Icc
      choose U hU hUfin using hloc
      obtain ⟨t, -, ht⟩ := hcomp.elim_nhds_subcover U (fun x _ => hU x)
      refine (t.finite_toSet.biUnion fun x _ => hUfin x).subset ?_
      intro y ⟨hyE, hyI⟩
      obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (ht hyI)
      exact mem_iUnion₂.2 ⟨x, hxt, hyx, hyE⟩
    exact hEfin.subset fun y ⟨hy1, hy2⟩ => ⟨hfr hy1, hy2⟩

/-- `h ∘ Q` of a smooth compactly supported `h` lies in the form domain. -/
theorem pullback_mem_formDomain (μ : Measure ℝ) [IsProbabilityMeasure μ] {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    formEnergy (qm μ) (fun t => h (qm μ t)) < ⊤ := by
  rw [formEnergy_pull μ hh.continuous.measurable]
  obtain ⟨ℓ, hℓ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) hc hh (by simp)
  have hl : ∀ x y, |h x - h y| ≤ (ℓ : ℝ) * |x - y| := fun x y => by
    have := hℓ.dist_le_mul x y
    simpa [Real.dist_eq] using this
  refine lt_of_le_of_lt (formE_le_lip hl) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

end QuantumNLS.QuantileCore

namespace QuantumNLS.QuantileCore

open QuantumNLS.QuantileTransport (quantile qm map_qm measurable_qm qm_of_mem leb01)
open QuantumNLS.BulkResponseForm
open QuantumNLS.QuantileForm
open QuantumNLS.FormCore (CoreHyp muRho formN formE formL2 dq core_density' formE_le_lip)

/-- **`CC:F03:core` in quantile coordinates**: the pullbacks `h ∘ Q`, `h ∈ C_c^∞(ℝ;ℝ)`, form a core of the bulk form for every `BulkMeasure`. -/
theorem isFormCore_bulk (L κ : ℝ) (hL : 0 < L) (hκ : 0 < κ) (μ : Measure ℝ) (hμ : BulkMeasure μ) :
    IsFormCore L κ (bulkQuantile μ) {F | IsSmoothQuantilePullback (bulkQuantile μ) F} := by
  haveI := hμ.isProbability
  have hna : ∀ x, μ {x} = 0 := fun x => hμ.noAtoms.measure_singleton x
  obtain ⟨ρ, H, hμρ⟩ := coreHyp_of_coreDensity μ hμ.isProbability hμ.coreDensity
  have hQ : bulkQuantile μ =ᵐ[uI] qm μ := quantile_ae_qm μ
  constructor
  · rintro F ⟨h, hh, hc, hFh⟩
    have h1 : (F : ℝ → ℝ) =ᵐ[uI] fun t => h (qm μ t) := by
      filter_upwards [hFh, hQ] with t a b
      simp only [Function.comp] at a
      rw [a, b]
    show formEnergy (bulkQuantile μ) (F : ℝ → ℝ) < ⊤
    rw [formEnergy_congr hQ h1]
    exact pullback_mem_formDomain μ hh hc
  · intro F hF ε hε
    have hFm := Lp.aestronglyMeasurable F
    set Fm : ℝ → ℝ := hFm.mk _ with hFmdef
    have hFmm : Measurable Fm := hFm.stronglyMeasurable_mk.measurable
    have hFae : (F : ℝ → ℝ) =ᵐ[uI] Fm := hFm.ae_eq_mk
    obtain ⟨h, hhm, hh⟩ := exists_pullback μ hna Fm hFmm
    have hFh : (F : ℝ → ℝ) =ᵐ[uI] fun t => h (qm μ t) := by
      filter_upwards [hFae, ae_restrict_mem measurableSet_Ioo] with t h1 h2
      rw [h1, hh t h2]
    have hN : formN μ h < ⊤ := by
      unfold formN
      refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
      · rw [← formL2_pull μ hhm]
        have : ∫⁻ t, ENNReal.ofReal (h (qm μ t) ^ 2) ∂leb01 =
            ∫⁻ t, ENNReal.ofReal ((F : ℝ → ℝ) t ^ 2) ∂uI := by
          refine lintegral_congr_ae ?_
          filter_upwards [hFh] with t ht
          rw [ht]
        rw [this, ← ofReal_norm_sq]
        exact ENNReal.ofReal_lt_top
      · rw [← formEnergy_pull μ hhm, ← formEnergy_congr hQ hFh]
        exact hF
    rw [hμρ] at hN
    have hcore := core_density' H hhm hN
    rw [← hμρ] at hcore
    obtain ⟨φ, hφ, hφc, hφN⟩ := hcore (ε / (2 * (L + κ))) (by positivity)
    obtain ⟨Cφ, hCφ⟩ := hφc.exists_bound_of_continuous hφ.continuous
    have hφm : Measurable fun t => φ (qm μ t) := hφ.continuous.measurable.comp (measurable_qm μ)
    have hmem : MemLp (fun t => φ (qm μ t)) 2 uI :=
      MemLp.of_bound hφm.aestronglyMeasurable Cφ (Eventually.of_forall fun t => hCφ _)
    set G : L2Unit := hmem.toLp _ with hG
    have hGae : (G : ℝ → ℝ) =ᵐ[uI] fun t => φ (qm μ t) := hmem.coeFn_toLp
    have hφh : Measurable fun x => h x - φ x := hhm.sub hφ.continuous.measurable
    have hd : ((F - G : L2Unit) : ℝ → ℝ) =ᵐ[uI] fun t => (h (qm μ t) - φ (qm μ t)) := by
      filter_upwards [Lp.coeFn_sub F G, hFh, hGae] with t a b c
      rw [a, Pi.sub_apply, b, c]
    refine ⟨G, ⟨φ, hφ, hφc, ?_⟩, ?_⟩
    · filter_upwards [hGae, hQ] with t a b
      simp only [Function.comp]
      rw [a, b]
    · have e1 : ENNReal.ofReal (‖F - G‖ ^ 2) = formL2 μ (fun x => h x - φ x) := by
        rw [ofReal_norm_sq, ← formL2_pull μ hφh]
        exact lintegral_congr_ae (by filter_upwards [hd] with t ht; rw [ht])
      have e2 : formEnergy (bulkQuantile μ) ((F - G : L2Unit) : ℝ → ℝ) = formE μ (fun x => h x - φ x) := by
        rw [formEnergy_congr hQ hd, ← formEnergy_pull μ hφh]
      rw [ENNReal.ofReal_mul hL.le, e1, e2]
      have hLκ : 0 < L + κ := by linarith
      calc ENNReal.ofReal L * formL2 μ (fun x => h x - φ x) + ENNReal.ofReal κ * formE μ (fun x => h x - φ x)
          ≤ ENNReal.ofReal (L + κ) * formL2 μ (fun x => h x - φ x) +
            ENNReal.ofReal (L + κ) * formE μ (fun x => h x - φ x) := by
            gcongr <;> linarith
        _ = ENNReal.ofReal (L + κ) * formN μ (fun x => h x - φ x) := by rw [formN, mul_add]
        _ ≤ ENNReal.ofReal (L + κ) * ENNReal.ofReal (ε / (2 * (L + κ))) := by gcongr
        _ = ENNReal.ofReal (ε / 2) := by
            rw [← ENNReal.ofReal_mul hLκ.le]; congr 1; field_simp
        _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)

end QuantumNLS.QuantileCore

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.QuantileCore.coreHyp_of_coreDensity
#print axioms QuantumNLS.QuantileCore.isFormCore_bulk
