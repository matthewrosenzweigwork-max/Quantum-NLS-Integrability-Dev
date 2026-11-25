import NlsGge.Atomic.Support.ContourChain
import NlsGge.Atomic.Support.ContourCycleIndex
import NlsGge.Atomic.LIB.LIB015

/-!
# G1-103 M3 support: integer-weighted finite cycles and circle cycles

Pro round 10 (commit 178f84d6), section 8, M3: the cycle
`Γ = γ - ∑ w_j ∂D_j` with integer weights `w_j`. Integer multiples of a landed
`ContourChain.Cycle` are built by repetition (and `Cycle.reverse` for negative weights);
the finite weighted sum is built by `Finset` induction. Circle cycles are the landed
`LIB015.circleLoop` C1 leaf. No simplicity or Jordan input.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Set MeasureTheory Filter Metric
open scoped unitInterval Topology

namespace NlsGge.Atomic.G1103Circ
open NlsGge.Atomic.ContourChain
open NlsGge.GK38.Lib.SlitContours

section WeightedCycles
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma exists_rep_cycle (D : Cycle) (n : ℕ) :
    ∃ Θ : Cycle, Θ.range ⊆ D.range ∧
      (∀ w, w ∉ D.range → Θ.index w = (n : ℂ) * D.index w) ∧
      (∀ ω : ℂ → ℂ →L[ℂ] F, D.Integrable ω →
        Θ.Integrable ω ∧ Θ.integral ω = (n : ℂ) • D.integral ω) := by
  induction n with
  | zero =>
    refine ⟨Cycle.empty, by simp, fun w _ => by simp, fun ω _ => ⟨Cycle.integrable_empty ω, ?_⟩⟩
    simp
  | succ n ih =>
    obtain ⟨Θ, hr, hi, hint⟩ := ih
    refine ⟨D.append Θ, ?_, ?_, ?_⟩
    · rw [Cycle.range_append]; exact Set.union_subset subset_rfl hr
    · intro w hw
      rw [Cycle.index_append, hi w hw]; push_cast; ring
    · intro ω hω
      obtain ⟨h1, h2⟩ := hint ω hω
      refine ⟨hω.append h1, ?_⟩
      rw [Cycle.integral_append, h2]; push_cast; module

lemma exists_zsmul_cycle (C : Cycle) (k : ℤ) :
    ∃ Θ : Cycle, Θ.range ⊆ C.range ∧
      (∀ w, w ∉ C.range → Θ.index w = (k : ℂ) * C.index w) ∧
      (∀ ω : ℂ → ℂ →L[ℂ] F, C.Integrable ω →
        Θ.Integrable ω ∧ Θ.integral ω = (k : ℂ) • C.integral ω) := by
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨Θ, hr, hi, hint⟩ := exists_rep_cycle (F := F) C k.toNat
    have hc : ((k.toNat : ℕ) : ℂ) = (k : ℂ) := by
      have : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk
      exact_mod_cast this
    rw [hc] at hi hint
    exact ⟨Θ, hr, hi, hint⟩
  · obtain ⟨Θ, hr, hi, hint⟩ := exists_rep_cycle (F := F) C.reverse (-k).toNat
    have hc : (((-k).toNat : ℕ) : ℂ) = -(k : ℂ) := by
      have : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have h2 : ((((-k).toNat : ℕ) : ℤ) : ℂ) = ((-k : ℤ) : ℂ) := by rw [this]
      push_cast at h2
      exact h2
    rw [hc] at hi hint
    refine ⟨Θ, by rw [Cycle.range_reverse] at hr; exact hr, ?_, ?_⟩
    · intro w hw
      rw [Cycle.range_reverse] at hi
      rw [hi w hw, Cycle.index_reverse C hw]; ring
    · intro ω hω
      obtain ⟨h1, h2⟩ := hint ω hω.reverse
      refine ⟨h1, ?_⟩
      rw [h2, Cycle.integral_reverse hω]; module

lemma exists_weighted_cycle {ι : Type*} [DecidableEq ι] (S : Finset ι) (C : ι → Cycle) (k : ι → ℤ) :
    ∃ Θ : Cycle, (∀ z ∈ Θ.range, ∃ j ∈ S, z ∈ (C j).range) ∧
      (∀ w, (∀ j ∈ S, w ∉ (C j).range) →
        Θ.index w = ∑ j ∈ S, (k j : ℂ) * (C j).index w) ∧
      (∀ ω : ℂ → ℂ →L[ℂ] F, (∀ j ∈ S, (C j).Integrable ω) →
        Θ.Integrable ω ∧ Θ.integral ω = ∑ j ∈ S, (k j : ℂ) • (C j).integral ω) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨Cycle.empty, by simp, fun w _ => by simp, fun ω _ => ⟨Cycle.integrable_empty ω, ?_⟩⟩
    simp
  | insert j S hj ih =>
    obtain ⟨Θ, hr, hi, hint⟩ := ih
    obtain ⟨Θj, hjr, hji, hjint⟩ := exists_zsmul_cycle (F := F) (C j) (k j)
    refine ⟨Θj.append Θ, ?_, ?_, ?_⟩
    · intro z hz
      rw [Cycle.range_append] at hz
      rcases hz with hz | hz
      · exact ⟨j, Finset.mem_insert_self _ _, hjr hz⟩
      · obtain ⟨i, hi', hzi⟩ := hr z hz
        exact ⟨i, Finset.mem_insert_of_mem hi', hzi⟩
    · intro w hw
      rw [Cycle.index_append, Finset.sum_insert hj,
        hji w (hw j (Finset.mem_insert_self _ _)),
        hi w (fun i hi' => hw i (Finset.mem_insert_of_mem hi'))]
    · intro ω hω
      obtain ⟨h1, h2⟩ := hjint ω (hω j (Finset.mem_insert_self _ _))
      obtain ⟨h3, h4⟩ := hint ω (fun i hi' => hω i (Finset.mem_insert_of_mem hi'))
      refine ⟨h1.append h3, ?_⟩
      rw [Cycle.integral_append, Finset.sum_insert hj, h2, h4]

end WeightedCycles

section Circles

lemma circle_contDiffOn (c : ℂ) (ρ : ℝ) : ContDiffOn ℝ 1 (circleLoop c ρ).extend (Icc 0 1) := by
  have hd : ContDiff ℝ 1 (fun t : ℝ => circleMap c ρ (2 * Real.pi * t)) :=
    (contDiff_circleMap c ρ).comp (contDiff_const.mul contDiff_id)
  refine hd.contDiffOn.congr ?_
  intro t ht
  exact circleLoop_extend_eq c ρ ht

/-- The circle `‖z - c‖ = ρ` as one chain. -/
def circleChain (c : ℂ) (ρ : ℝ) : Chain (c + ρ) (c + ρ) :=
  Chain.leaf (circleLoop c ρ) (circle_contDiffOn c ρ)

/-- The circle as a single-chain cycle. -/
def circleCycle (c : ℂ) (ρ : ℝ) : Cycle :=
  Cycle.single ⟨c + ρ, circleChain c ρ⟩

lemma circleLoop_mem_sphere (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (t : I) :
    circleLoop c ρ t ∈ sphere c ρ := by
  have hE : circleLoop c ρ t = circleMap c ρ (2 * Real.pi * (t : ℝ)) :=
    (Path.extend_extends' (circleLoop c ρ) t).symm.trans (circleLoop_extend_eq c ρ t.2)
  rw [hE]
  exact circleMap_mem_sphere c hρ _

lemma circleCycle_range_subset (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (circleCycle c ρ).range ⊆ sphere c ρ := by
  rintro z hz
  have hz' : z ∈ (circleChain c ρ).trace := by simpa [circleCycle] using hz
  obtain ⟨t, rfl⟩ := hz'
  exact circleLoop_mem_sphere c hρ t

lemma circleCycle_integral (c : ℂ) (ρ : ℝ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ω : ℂ → ℂ →L[ℂ] F) :
    (circleCycle c ρ).integral ω = curveIntegral ω (circleLoop c ρ) := by
  simp [circleCycle, circleChain, Chain.integral]

lemma circleCycle_integrable (c : ℂ) (ρ : ℝ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (ω : ℂ → ℂ →L[ℂ] F) (h : CurveIntegrable ω (circleLoop c ρ)) :
    (circleCycle c ρ).Integrable ω := by
  intro i
  exact h

lemma toSpanSingleton_eq_complexForm (f : ℂ → ℂ) (z : ℂ) :
    ContinuousLinearMap.toSpanSingleton ℂ (f z) = complexForm f z := by
  ext; simp [complexForm, mul_comm]

lemma circleCycle_index_aux (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) (hw : w ∉ sphere c ρ) :
    (circleCycle c ρ).index w =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ * circleIntegral (fun z : ℂ => (z - w)⁻¹) c ρ := by
  have hcont : ContinuousOn (fun z : ℂ => (z - w)⁻¹) (sphere c ρ) := by
    refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
    intro z hz
    exact sub_ne_zero.2 (fun h => hw (h ▸ hz))
  have h1 : (circleCycle c ρ).index w =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹))
          (circleLoop c ρ) := by
    have h0 : (circleCycle c ρ).index w = (circleChain c ρ).index w := by
      show ∑ _i : Fin 1, (circleChain c ρ).index w = _
      rw [Fin.sum_univ_one]
    rw [h0]
    rfl
  rw [h1]
  congr 1
  have : (fun z : ℂ => ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) =
      complexForm (fun z : ℂ => (z - w)⁻¹) := by
    funext z; exact toSpanSingleton_eq_complexForm (fun z : ℂ => (z - w)⁻¹) z
  rw [this]
  exact curveIntegral_circleLoop _ c ρ hρ hcont

lemma circleCycle_index_inside (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : ‖w - c‖ < ρ) :
    (circleCycle c ρ).index w = 1 := by
  have hwb : w ∈ ball c ρ := by simpa [dist_eq_norm] using hw
  have hws : w ∉ sphere c ρ := fun h => by
    have := mem_sphere_iff_norm.1 h; linarith
  rw [circleCycle_index_aux c hρ w hws, circleIntegral.integral_sub_inv_of_mem_ball hwb]
  exact inv_mul_cancel₀ (by simp [Real.pi_ne_zero, Complex.I_ne_zero])

lemma circleCycle_index_outside (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : ρ < ‖w - c‖) :
    (circleCycle c ρ).index w = 0 := by
  have hws : w ∉ sphere c ρ := fun h => by
    have := mem_sphere_iff_norm.1 h; linarith
  rw [circleCycle_index_aux c hρ w hws]
  have hwn : w ∉ closedBall c ρ := by
    intro h
    have := mem_closedBall_iff_norm.1 h
    linarith
  have h0 : circleIntegral (fun z : ℂ => (z - w)⁻¹) c ρ = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hρ.le Set.countable_empty
      ?_ ?_
    · refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
      intro z hz
      exact sub_ne_zero.2 (fun h => hwn (h ▸ hz))
    · intro z hz
      have hzw : z - w ≠ 0 := sub_ne_zero.2 (fun h => hwn (h ▸ ball_subset_closedBall hz.1))
      exact ((differentiableAt_id.sub_const w).inv hzw)
  rw [h0, mul_zero]

end Circles

end NlsGge.Atomic.G1103Circ

end
