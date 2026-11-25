import QuantumNLS.DuhamelDualityGeneral

/-!
# R-02871DC6, last clause, local form (Terra r109 remainder)

"The integral ... agrees with the ordinary integral whenever the latter is defined"
(`ROOT_L2_extension.tex`, lemma `lem:root-L4-duality`, lines 30-35). Terra r109 asked for the
hypotheses only on the relevant subinterval: `IntegrableOn Fc (uIoc a t)` and slice identification
a.e. on `uIoc a t`. Proved directly (same weak-equality route as DDG1, which is imported read-only,
`d997b7ff…`): outside `uIoc a t` both oriented indicators vanish, so no information on `Fc` or on the
slices of `F` there is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate BigOperators Topology ENNReal InnerProductSpace
open MeasureTheory Filter QuantumNLS.Fourier QuantumNLS.LocalWellPosedness QuantumNLS.L4Strichartz
  QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality QuantumNLS.DuhamelDualityGeneral

namespace QuantumNLS.DuhamelDualityLocal

attribute [local irreducible] QuantumNLS.L4StrichartzL2.evol

variable {L : ℝ} [Fact (0 < L)]

section Agree

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (F : Lp ℂ (4 / 3) (μJ (L := L) α β))

set_option linter.unusedSimpArgs false in
/-- **"Agrees with the ordinary integral whenever the latter is defined", local form**: if
`s ↦ F_s ∈ L²` is Bochner integrable on `uIoc a t` and `F(s,·) = F_s` for a.e. `s ∈ uIoc a t`, then
for `a, t ∈ [α, β]`, `V(t) = ∫_a^t U(t−s) F_s ds` (Bochner, oriented for `t < a`). -/
theorem V_eq_integral_local (Fc : ℝ → HL L) {a t : ℝ} (hFc : IntegrableOn Fc (Set.uIoc a t))
    (hsl : ∀ᵐ s ∂(volume.restrict (Set.uIoc a t)),
      (fun x => F (s, x)) =ᵐ[volume] (Fc s : AddCircle L → ℂ))
    (ha : a ∈ Set.Icc α β) (ht : t ∈ Set.Icc α β) :
    V hαβ hlen F a t = ∫ s in a..t, evol (Fc s) (t - s) := by
  refine ext_inner_left ℂ fun h => ?_
  set g : ℝ → ℂ := fun s => ⟪evol h (s - t), Fc s⟫_ℂ
  have hsubI : Set.uIoc a t ⊆ Set.Ioc α β :=
    Set.Ioc_subset_Ioc (le_min ha.1 ht.1) (max_le ha.2 ht.2)
  have hEI : IntervalIntegrable (fun s => evol (Fc s) (t - s)) volume a t :=
    intervalIntegrable_iff.mpr (integrableOn_evol hFc t)
  -- the ordinary integral, tested against `h`
  have hR : ⟪h, ∫ s in a..t, evol (Fc s) (t - s)⟫_ℂ = ∫ s in a..t, g s := by
    have hc := (innerSL ℂ h).intervalIntegral_comp_comm hEI
    simp only [innerSL_apply_apply] at hc
    rw [← hc]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [g]
    rw [inner_evol, neg_sub]
  have hgi : IntegrableOn g (Set.uIoc a t) := integrableOn_pair hFc h t
  have hgi1 : Integrable ((Set.Ioc a t).indicator g) (volume.restrict (Set.Ioc α β)) :=
    ((hgi.mono_set Set.Ioc_subset_uIoc).integrable_indicator measurableSet_Ioc).restrict
  have hgi2 : Integrable ((Set.Ioc t a).indicator g) (volume.restrict (Set.Ioc α β)) :=
    ((hgi.mono_set Set.Ioc_subset_uIoc').integrable_indicator measurableSet_Ioc).restrict
  -- slice identification is only used on `uIoc a t`
  have hsl' : ∀ᵐ s ∂(volume.restrict (Set.Ioc α β)), s ∈ Set.uIoc a t →
      (fun x => F (s, x)) =ᵐ[volume] (Fc s : AddCircle L → ℂ) :=
    ae_restrict_of_ae ((ae_restrict_iff' measurableSet_uIoc).mp hsl)
  rw [hR, V, inner_evol, inner_Sop hαβ hlen F ha.1 ht.1,
    pairing_iterated hαβ hlen _ (memLp_cut F a t)]
  -- the inner integral is `σ(s) g(s)` for a.e. `s`
  have hin : ∀ᵐ s ∂(volume.restrict (Set.Ioc α β)),
      ∫ x, conj ((evol (evol h (-t)) s : AddCircle L → ℂ) x) *
        ((Set.Ioc a t ×ˢ Set.univ).indicator F (s, x) - (Set.Ioc t a ×ˢ Set.univ).indicator F (s, x)) =
      (Set.Ioc a t).indicator g s - (Set.Ioc t a).indicator g s := by
    filter_upwards [hsl'] with s hs'
    have hgs : s ∈ Set.uIoc a t →
        g s = ∫ x, conj ((evol h (s - t) : AddCircle L → ℂ) x) * F (s, x) := by
      intro hsI
      have hs := hs' hsI
      simp only [g]
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hs] with x hx
      rw [hx, RCLike.inner_apply, mul_comm]
    rw [evol_evol, ← sub_eq_add_neg]
    by_cases h1 : s ∈ Set.Ioc a t
    · have hg1 := hgs (Set.Ioc_subset_uIoc h1)
      by_cases h2 : s ∈ Set.Ioc t a <;>
        simp only [Set.indicator_apply, Set.mem_prod, Set.mem_univ, and_true, h1, h2, ↓reduceIte,
          sub_zero, zero_sub, mul_zero, mul_neg, integral_neg, integral_zero, hg1, sub_self]
    · by_cases h2 : s ∈ Set.Ioc t a
      · have hg2 := hgs (Set.Ioc_subset_uIoc' h2)
        simp only [Set.indicator_apply, Set.mem_prod, Set.mem_univ, and_true, h1, h2, ↓reduceIte,
          sub_zero, zero_sub, mul_zero, mul_neg, integral_neg, integral_zero, hg2, sub_self]
      · simp only [Set.indicator_apply, Set.mem_prod, Set.mem_univ, and_true, h1, h2, ↓reduceIte,
          sub_zero, mul_zero, integral_zero, sub_self]
  rw [integral_congr_ae hin]
  have hsub1 : Set.Ioc a t ⊆ Set.Ioc α β := Set.Ioc_subset_Ioc ha.1 ht.2
  have hsub2 : Set.Ioc t a ⊆ Set.Ioc α β := Set.Ioc_subset_Ioc ht.1 ha.2
  rw [integral_sub hgi1 hgi2,
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_self_of_subset_left hsub1, Set.inter_eq_self_of_subset_left hsub2]
  rfl

#print axioms V_eq_integral_local

end Agree

end QuantumNLS.DuhamelDualityLocal
