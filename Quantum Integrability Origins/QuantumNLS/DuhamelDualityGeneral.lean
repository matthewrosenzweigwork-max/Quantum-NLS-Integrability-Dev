import QuantumNLS.DuhamelDuality

/-!
# R-02871DC6, last clause: agreement with the ordinary (Bochner) integral for integrable forcing

Source: `ROOT_L2_extension.tex`, lemma `lem:root-L4-duality` (lines 30-35): "The integral is understood
by duality, and agrees with the ordinary integral whenever the latter is defined."

Imports the frozen DD1 (`DuhamelDuality`, `40e83626…`) read-only. DD1's `V_eq_integral` covers
continuous `L²`-valued forcing; here the forcing `s ↦ F_s ∈ L²(𝕋_L)` is only Bochner integrable on
`J = (α, β]` (i.e. strongly measurable with `∫_J ‖F_s‖ < ∞`), which is exactly when the ordinary
integral `∫_a^t U(t−s) F_s ds` is defined. Route: weak equality (testing against `h ∈ L²` via DD1's
`inner_Sop` and `pairing_iterated`, i.e. the Riesz pairing plus Fubini), then nondegeneracy of the
inner product (`ext_inner_left`). The orientation for `t < a` is that of the interval integral.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate BigOperators Topology ENNReal InnerProductSpace
open MeasureTheory Filter QuantumNLS.Fourier QuantumNLS.LocalWellPosedness QuantumNLS.L4Strichartz
  QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality

namespace QuantumNLS.DuhamelDualityGeneral

-- `evol` is used only through its proved properties; keep it opaque for unification here.
attribute [local irreducible] QuantumNLS.L4StrichartzL2.evol

variable {L : ℝ} [Fact (0 < L)]

/-- Joint continuity of `(g, τ) ↦ U(τ)g` on `L² × ℝ`. -/
lemma continuous_evol_joint : Continuous fun p : HL L × ℝ => evol p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨g0, τ0⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ p : HL L × ℝ, ‖evol p.1 p.2 - evol g0 τ0‖ ≤
      ‖p.1 - g0‖ + ‖evol g0 p.2 - evol g0 τ0‖ := by
    intro p
    calc ‖evol p.1 p.2 - evol g0 τ0‖
        = ‖evol (p.1 - g0) p.2 + (evol g0 p.2 - evol g0 τ0)‖ := by
          rw [evol_sub]; congr 1; abel
      _ ≤ _ := by refine (norm_add_le _ _).trans ?_; rw [norm_evol]
  have h1 : Tendsto (fun p : HL L × ℝ => ‖p.1 - g0‖) (𝓝 (g0, τ0)) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (continuous_fst.tendsto (g0, τ0))
  have h2 : Tendsto (fun p : HL L × ℝ => ‖evol g0 p.2 - evol g0 τ0‖) (𝓝 (g0, τ0)) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp
      (((continuous_evol g0).comp continuous_snd).tendsto (g0, τ0))
  have h3 := h1.add h2
  rw [add_zero] at h3
  exact squeeze_zero (fun _ => norm_nonneg _) hb h3

#print axioms continuous_evol_joint

/-- Joint continuity with the time variable first. -/
lemma continuous_evol_joint' : Continuous fun p : ℝ × HL L => evol p.2 p.1 :=
  (continuous_evol_joint (L := L)).comp continuous_swap

lemma integrableOn_evol {S : Set ℝ} {Fc : ℝ → HL L} (hFc : IntegrableOn Fc S) (t : ℝ) :
    IntegrableOn (fun s => evol (Fc s) (t - s)) S := by
  have hτ : AEStronglyMeasurable (fun s : ℝ => t - s) (volume.restrict S) :=
    (continuous_const.sub continuous_id).aestronglyMeasurable
  have hp : AEStronglyMeasurable (fun s : ℝ => ((t - s, Fc s) : ℝ × HL L)) (volume.restrict S) :=
    AEStronglyMeasurable.prodMk hτ hFc.aestronglyMeasurable
  have hEm : AEStronglyMeasurable (fun s => evol (Fc s) (t - s)) (volume.restrict S) :=
    (continuous_evol_joint' (L := L)).comp_aestronglyMeasurable hp
  refine Integrable.mono' hFc.norm hEm (Eventually.of_forall fun s => ?_)
  rw [norm_evol]

lemma integrableOn_pair {S : Set ℝ} {Fc : ℝ → HL L} (hFc : IntegrableOn Fc S) (h : HL L) (t : ℝ) :
    IntegrableOn (fun s => ⟪evol h (s - t), Fc s⟫_ℂ) S := by
  have hm : AEStronglyMeasurable (fun s => evol h (s - t)) (volume.restrict S) :=
    ((continuous_evol h).comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun s => ⟪evol h (s - t), Fc s⟫_ℂ) (volume.restrict S) :=
    hm.inner hFc.aestronglyMeasurable
  refine Integrable.mono' (hFc.norm.const_mul ‖h‖) hgm (Eventually.of_forall fun s => ?_)
  refine (norm_inner_le_norm _ _).trans ?_
  rw [norm_evol]

#print axioms integrableOn_evol
#print axioms integrableOn_pair

section Agree

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (F : Lp ℂ (4 / 3) (μJ (L := L) α β))

/-- **"Agrees with the ordinary integral whenever the latter is defined"**: if `s ↦ F_s ∈ L²` is
Bochner integrable on `J = (α, β]` and `F(s,·) = F_s` for a.e. `s ∈ J`, then for `a, t ∈ [α, β]`,
`V(t) = ∫_a^t U(t−s) F_s ds` (Bochner integral in `L²`, oriented for `t < a`). -/
theorem V_eq_integral_general (Fc : ℝ → HL L) (hFc : IntegrableOn Fc (Set.Ioc α β))
    (hsl : ∀ᵐ s ∂(volume.restrict (Set.Ioc α β)),
      (fun x => F (s, x)) =ᵐ[volume] (Fc s : AddCircle L → ℂ))
    {a t : ℝ} (ha : a ∈ Set.Icc α β) (ht : t ∈ Set.Icc α β) :
    V hαβ hlen F a t = ∫ s in a..t, evol (Fc s) (t - s) := by
  refine ext_inner_left ℂ fun h => ?_
  set g : ℝ → ℂ := fun s => ⟪evol h (s - t), Fc s⟫_ℂ
  have hsubI : Set.uIoc a t ⊆ Set.Ioc α β :=
    Set.Ioc_subset_Ioc (le_min ha.1 ht.1) (max_le ha.2 ht.2)
  have hEint : IntegrableOn (fun s => evol (Fc s) (t - s)) (Set.Ioc α β) := integrableOn_evol hFc t
  have hEI : IntervalIntegrable (fun s => evol (Fc s) (t - s)) volume a t :=
    intervalIntegrable_iff.mpr (hEint.mono_set hsubI)
  -- the ordinary integral, tested against `h`
  have hR : ⟪h, ∫ s in a..t, evol (Fc s) (t - s)⟫_ℂ = ∫ s in a..t, g s := by
    have hc := (innerSL ℂ h).intervalIntegral_comp_comm hEI
    simp only [innerSL_apply_apply] at hc
    rw [← hc]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [g]
    rw [inner_evol, neg_sub]
  have hgi : IntegrableOn g (Set.Ioc α β) := integrableOn_pair hFc h t
  rw [hR, V, inner_evol, inner_Sop hαβ hlen F ha.1 ht.1,
    pairing_iterated hαβ hlen _ (memLp_cut F a t)]
  -- the inner integral is `σ(s) g(s)` for a.e. `s`
  have hin : ∀ᵐ s ∂(volume.restrict (Set.Ioc α β)),
      ∫ x, conj ((evol (evol h (-t)) s : AddCircle L → ℂ) x) *
        ((Set.Ioc a t ×ˢ Set.univ).indicator F (s, x) - (Set.Ioc t a ×ˢ Set.univ).indicator F (s, x)) =
      (Set.Ioc a t).indicator g s - (Set.Ioc t a).indicator g s := by
    filter_upwards [hsl] with s hs
    have hgs : g s = ∫ x, conj ((evol h (s - t) : AddCircle L → ℂ) x) * F (s, x) := by
      simp only [g]
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hs] with x hx
      rw [hx, RCLike.inner_apply, mul_comm]
    rw [evol_evol, ← sub_eq_add_neg]
    by_cases h1 : s ∈ Set.Ioc a t <;> by_cases h2 : s ∈ Set.Ioc t a <;>
      simp only [Set.indicator_apply, Set.mem_prod, Set.mem_univ, and_true, h1, h2, ↓reduceIte,
        sub_zero, zero_sub, mul_zero, mul_neg, integral_neg, integral_zero, hgs, sub_self]
  rw [integral_congr_ae hin]
  have hsub1 : Set.Ioc a t ⊆ Set.Ioc α β := Set.Ioc_subset_Ioc ha.1 ht.2
  have hsub2 : Set.Ioc t a ⊆ Set.Ioc α β := Set.Ioc_subset_Ioc ht.1 ha.2
  rw [integral_sub (hgi.indicator (measurableSet_Ioc : MeasurableSet (Set.Ioc a t)))
      (hgi.indicator (measurableSet_Ioc : MeasurableSet (Set.Ioc t a))),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_self_of_subset_left hsub1, Set.inter_eq_self_of_subset_left hsub2]
  rfl

#print axioms V_eq_integral_general

end Agree

end QuantumNLS.DuhamelDualityGeneral
