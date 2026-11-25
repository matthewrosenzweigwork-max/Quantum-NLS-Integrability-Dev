import QuantumNLS.L4Gluing

/-!
# EXT-003, Route Y stage (v), part D: autonomy (time translation)

Toward R-AEE17FD6 (`thm:root-L2-flow`): "Autonomy and uniqueness give the flow composition law and
the inverse at negative time."

Route Y deviates from Bourgain's `X^{0,b}` proof (Bourgain 1993, §4); everything rests on the
elementary linear estimates (LS1/LS2, DD1, SG1, DL4a/DL4b, LC1, UQ1, HB1, GLU1; read-only).

Here: the shift `(t, x) ↦ (t + s, x)` is measure preserving from `(α − s, β − s] × 𝕋_L` to
`(α, β] × 𝕋_L`; it intertwines the free evolution (`freeL4_tr`), the cubic nonlinearity and the
Duhamel integral (`V_tr`); hence **`sol_tr`**: if `u` solves on `(α, β]` with curve `w`, the shifted
class solves on `(α − s, β − s]` with curve `t ↦ w(t + s)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate BigOperators Topology ENNReal InnerProductSpace
open MeasureTheory Filter QuantumNLS.Fourier QuantumNLS.L4Strichartz
  QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality QuantumNLS.DuhamelL4 QuantumNLS.DuhamelL4Limit
  QuantumNLS.LocalL4Contraction QuantumNLS.L4Uniqueness QuantumNLS.H1Bridge QuantumNLS.L4Gluing

namespace QuantumNLS.L4Translate

attribute [local irreducible] QuantumNLS.L4StrichartzL2.evol

variable {L : ℝ} [Fact (0 < L)]

/-! ## 1. The shift -/

/-- `(t, x) ↦ (t + s, x)`. -/
def sh (s : ℝ) : ℝ × AddCircle L → ℝ × AddCircle L := Prod.map (fun t => t + s) id

lemma mp_time (α β s : ℝ) : MeasurePreserving (fun t : ℝ => t + s)
    (volume.restrict (Set.Ioc (α - s) (β - s))) (volume.restrict (Set.Ioc α β)) := by
  have h := (measurePreserving_add_right volume s).restrict_preimage
    (measurableSet_Ioc (a := α) (b := β))
  rwa [Set.preimage_add_const_Ioc] at h

lemma mp_sh (α β s : ℝ) :
    MeasurePreserving (sh (L := L) s) (μJ (L := L) (α - s) (β - s)) (μJ (L := L) α β) :=
  (mp_time α β s).prod (MeasurePreserving.id volume)

lemma me_sh (s : ℝ) : MeasurableEmbedding (sh (L := L) s) := by
  have e : sh (L := L) s =
      ⇑((MeasurableEquiv.addRight s).prodCongr (MeasurableEquiv.refl (AddCircle L))) := by
    funext p; rfl
  rw [e]
  exact MeasurableEquiv.measurableEmbedding _

/-- The shifted `Lᵖ` class: `(tr u)(t, x) = u(t + s, x)`. -/
def tr {α β : ℝ} {p : ℝ≥0∞} (s : ℝ) (u : Lp ℂ p (μJ (L := L) α β)) :
    Lp ℂ p (μJ (L := L) (α - s) (β - s)) :=
  Lp.compMeasurePreserving (sh s) (mp_sh α β s) u

lemma coeFn_tr {α β : ℝ} {p : ℝ≥0∞} (s : ℝ) (u : Lp ℂ p (μJ (L := L) α β)) :
    (tr s u : ℝ × AddCircle L → ℂ) =ᵐ[μJ (L := L) (α - s) (β - s)] fun q => u (sh s q) :=
  Lp.coeFn_compMeasurePreserving _ _

lemma tr_slice {α β : ℝ} {p : ℝ≥0∞} (s : ℝ) (u : Lp ℂ p (μJ (L := L) α β)) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc (α - s) (β - s))), ∀ᵐ x ∂(volume : Measure (AddCircle L)),
      tr s u (t, x) = u (t + s, x) :=
  Measure.ae_ae_of_ae_prod (coeFn_tr s u)

/-- Pull back an a.e. statement in time along the shift. -/
lemma ae_shift {α β s : ℝ} {P : ℝ → Prop} (h : ∀ᵐ t ∂(volume.restrict (Set.Ioc α β)), P t) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc (α - s) (β - s))), P (t + s) :=
  (mp_time α β s).quasiMeasurePreserving.ae h

/-! ## 2. Equivariance -/

lemma hαβ_tr {α β : ℝ} (hαβ : α ≤ β) (s : ℝ) : α - s ≤ β - s := by linarith

lemma hlen_tr {α β : ℝ} (hlen : β ≤ α + TL L) (s : ℝ) : β - s ≤ α - s + TL L := by linarith

section Equiv

variable {α β : ℝ} (hαβ : α ≤ β) (hlen : β ≤ α + TL L) (s : ℝ)

include hαβ hlen in
lemma freeL4_tr (h : HL L) :
    tr s (freeL4 α β h) =
      freeL4 (α - s) (β - s) (evol h s) := by
  refine Lp_eq_of_slices _ _ ?_
  filter_upwards [tr_slice s (freeL4 α β h), ae_shift (s := s) (freeL4_slice hαβ hlen h),
    freeL4_slice (hαβ_tr hαβ s) (hlen_tr hlen s) (evol h s)] with t e1 e2 e3
  filter_upwards [e1, e2, e3] with x x1 x2 x3
  rw [x1, x2, x3, evol_evol]

lemma cub_tr (u : Lp ℂ 4 (μJ (L := L) α β)) : cub (tr s u) = tr s (cub u) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_cub (tr s u), coeFn_tr s (cub u), coeFn_tr s u,
    (mp_sh (L := L) α β s).quasiMeasurePreserving.ae (coeFn_cub u)] with q e1 e2 e3 e4
  rw [e1, e2]
  simp only [cubF]
  rw [e3, e4]
  rfl

include hαβ hlen in
/-- **Autonomy of the Duhamel integral**: `∫_{a−s}^{t−s} U(t−s−r) F(r+s) dr = ∫_a^t U(t−r) F(r) dr`. -/
theorem V_tr (F : Lp ℂ (4 / 3) (μJ (L := L) α β)) {a t : ℝ} (ha : α ≤ a) (ht : α ≤ t) :
    V (hαβ_tr hαβ s) (hlen_tr hlen s) (tr s F) (a - s) (t - s) = V hαβ hlen F a t := by
  have hS : Sop (hαβ_tr hαβ s) (hlen_tr hlen s) (tr s F) (a - s) (t - s) =
      evol (Sop hαβ hlen F a t) s := by
    refine ext_inner_left ℂ fun h => ?_
    rw [inner_Sop (hαβ_tr hαβ s) (hlen_tr hlen s) (tr s F) (by linarith) (by linarith),
      inner_evol, inner_Sop hαβ hlen F ha ht]
    rw [← (mp_sh (L := L) α β s).integral_comp (me_sh s)]
    refine integral_congr_ae ?_
    have hfree : (freeL4 α β (evol h (-s)) : ℝ × AddCircle L → ℂ) ∘ sh s =ᵐ[μJ (L := L) (α - s) (β - s)]
        freeL4 (α - s) (β - s) h := by
      have e := freeL4_tr hαβ hlen s (evol h (-s))
      rw [evol_evol, add_neg_cancel, evol_zero_time] at e
      rw [← e]
      exact (coeFn_tr s _).symm
    filter_upwards [hfree, coeFn_tr s F] with q e1 e2
    simp only [Function.comp_apply] at e1
    rw [e1]
    congr 1
    obtain ⟨r, x⟩ := q
    have hm1 : (sh (L := L) s (r, x) ∈ Set.Ioc a t ×ˢ (Set.univ : Set (AddCircle L))) ↔
        ((r, x) ∈ Set.Ioc (a - s) (t - s) ×ˢ (Set.univ : Set (AddCircle L))) := by
      simp only [sh, Prod.map, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true, id]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    have hm2 : (sh (L := L) s (r, x) ∈ Set.Ioc t a ×ˢ (Set.univ : Set (AddCircle L))) ↔
        ((r, x) ∈ Set.Ioc (t - s) (a - s) ×ˢ (Set.univ : Set (AddCircle L))) := by
      simp only [sh, Prod.map, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true, id]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    simp only [Set.indicator_apply, hm1, hm2, e2]
  rw [V, V, hS, evol_evol, sub_add_cancel]

end Equiv

#print axioms V_tr

/-! ## 3. Translated solutions -/

/-- **Autonomy**: a solution on `(α, β]` with curve `w`, shifted by `s`, is a solution on
`(α − s, β − s]` with curve `t ↦ w(t + s)`. -/
theorem sol_tr {α β : ℝ} {hαβ : α ≤ β} {hlen : β ≤ α + TL L} {c : ℂ}
    {u : Lp ℂ 4 (μJ (L := L) α β)} {w : ℝ → HL L} (hu : Sol hαβ hlen c u w) (s : ℝ) :
    Sol (hαβ_tr hαβ s) (hlen_tr hlen s) c (tr s u) (fun t => w (t + s)) := by
  obtain ⟨hD, hw⟩ := hu.base (b := α) ⟨le_rfl, hαβ⟩
  have hdata : (fun t => w (t + s)) (α - s) = w α := by simp only [sub_add_cancel]
  have hVt : ∀ t, α ≤ t + s →
      V (hαβ_tr hαβ s) (hlen_tr hlen s) (cub (tr s u)) (α - s) t = V hαβ hlen (cub u) α (t + s) := by
    intro t ht
    rw [cub_tr, ← V_tr hαβ hlen s (cub u) le_rfl ht, add_sub_cancel_right]
  refine ⟨α - s, ⟨le_rfl, hαβ_tr hαβ s⟩, ?_, fun t ht => ?_⟩
  · rw [hdata]
    filter_upwards [tr_slice s u, ae_shift (s := s) hD, ae_restrict_mem measurableSet_Ioc]
      with t e1 e2 ht
    rw [hVt t (by linarith [ht.1]), show t - (α - s) = t + s - α by ring]
    filter_upwards [e1, e2] with x x1 x2
    rw [x1, x2]
  · rw [hdata]
    have e := hw (t + s) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [Dcurve] at e ⊢
    rw [hVt t (by linarith [ht.1]), show t - (α - s) = t + s - α by ring]
    exact e

#print axioms sol_tr

end QuantumNLS.L4Translate
