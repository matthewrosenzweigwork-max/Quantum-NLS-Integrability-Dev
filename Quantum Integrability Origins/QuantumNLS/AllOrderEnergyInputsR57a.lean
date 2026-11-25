import QuantumNLS.AllOrderEnergyMarginalToolsR56a

/-! Fixed-data predecessor interfaces for the physical energy upgrade. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Filter Topology MeasureTheory
open scoped ENNReal InnerProductSpace

namespace QuantumNLS.AllOrderEnergyInputsR57a
open PhysicalTensor Def033HierarchyR24m BetheCoefficientTransform HierarchyFlow
open ActualModelBindingR53a ActualModelTargetR53a ActualModelCorollaryR53a
open AllOrderEnergyInputsR56a ClassicalCharges CommonBethePacket
open BetheLabels BulkResponseActual SmoothScalarMomentsPhysical AuditWeightedProbabilityR49a

variable {L κ : ℝ} [Fact (0 < L)]

/-- R-E679E41D fixes the charge family, rank and both boxes before the error sequence. -/
abbrev ActualModelRE679E41DInput (hκ : 0 < κ)
    (H : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ) : Prop :=
  AllOrderEnergyInputsR56a.ActualModelRE679E41DInput hκ H

/-- R56a's rebound actual-model corollary has the fixed-data input type used here. -/
theorem actualModelInput_of_PROP025 (hκ : 0 < κ)
    (H : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (PROP025Input : ActualModelCorollaryR56a.PROP025Input (L := L) hκ) :
    ActualModelRE679E41DInput hκ H :=
  ActualModelCorollaryR56a.cor_MP_actual_model_intermediate hκ PROP025Input H

private theorem jet_le {u v : Smooth L} (a : ℕ) (x : ℝ) :
    ‖iteratedDeriv a u.val x - iteratedDeriv a v.val x‖ ≤ ‖jet L u a - jet L v a‖ := by
  let hL := Fact.out (p := 0 < L)
  let y := toIcoMod hL 0 x
  have hy : y ∈ Set.Icc (0 : ℝ) L :=
    Set.Ico_subset_Icc_self (toIcoMod_mem_Ico' hL x)
  have hx : y + toIcoDiv hL 0 x • L = x := by simpa only [y, add_comm] using toIcoDiv_zsmul_sub_toIcoMod hL 0 x
  rw [← hx, (Def024LowFlows.iteratedDeriv_periodic u.property.periodic a).zsmul _ _,
    (Def024LowFlows.iteratedDeriv_periodic v.property.periodic a).zsmul _ _]
  exact ContinuousMap.norm_coe_le_norm (jet L u a - jet L v a) ⟨y, hy⟩

private theorem jet_bound (u : Smooth L) (a : ℕ) (x : ℝ) :
    ‖iteratedDeriv a u.val x‖ ≤ ‖jet L u a‖ := by
  let hL := Fact.out (p := 0 < L)
  let y := toIcoMod hL 0 x
  have hy : y ∈ Set.Icc (0 : ℝ) L :=
    Set.Ico_subset_Icc_self (toIcoMod_mem_Ico' hL x)
  have hx : y + toIcoDiv hL 0 x • L = x := by simpa only [y, add_comm] using toIcoDiv_zsmul_sub_toIcoMod hL 0 x
  rw [← hx, (Def024LowFlows.iteratedDeriv_periodic u.property.periodic a).zsmul _ _]
  exact ContinuousMap.norm_coe_le_norm (jet L u a) ⟨y, hy⟩

private theorem low_step_continuous (F : HigherFlows L κ) {R : Finset ℕ} {r : ℕ}
    (hr : r ∈ R) (hlow : r < 2) :
    Continuous (fun p : ℝ × Smooth L => smoothStep (hamFlows F R) r p.1 p.2) := by
  let G := fun p : ℝ × Smooth L => smoothStep (hamFlows F R) r p.1 p.2
  apply continuous_induced_rng.2
  apply continuous_pi
  intro a
  apply continuous_iff_continuousAt.2
  intro p
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  let A : ℝ := if r = 0 then ‖jet L p.2 a‖ else ‖jet L p.2 (a + 1)‖
  have hA : 0 ≤ A := by dsimp [A]; split <;> positivity
  have hj : Continuous (fun q : ℝ × Smooth L => jet L q.2 a) :=
    ((continuous_apply a).comp (continuous_induced_dom : Continuous (fun u : Smooth L => jet L u))).comp continuous_snd
  have ht : Continuous (fun q : ℝ × Smooth L => q.1) := continuous_fst
  have hb : Continuous (fun q : ℝ × Smooth L => A * |p.1 - q.1| + ‖jet L p.2 a - jet L q.2 a‖) :=
    (continuous_const.mul (continuous_const.sub ht).abs).add (continuous_const.sub hj).norm
  have hev := hb.continuousAt.eventually (gt_mem_nhds (show A * |p.1 - p.1| + ‖jet L p.2 a - jet L p.2 a‖ < ε by simpa))
  filter_upwards [hev] with q hq
  calc
    dist (jet L (G q) a) (jet L (G p) a) ≤ A * |p.1 - q.1| + ‖jet L p.2 a - jet L q.2 a‖ := by
      rw [dist_comm, dist_eq_norm]
      apply (ContinuousMap.norm_le _ (by positivity)).2
      intro x
      have hδ (y : ℝ) := jet_le (u := p.2) (v := q.2) a y
      have hcases : r = 0 ∨ r = 1 := by omega
      rcases hcases with rfl | rfl
      · simpa [G, A, smoothStep, hr, hamFlows, flowMap, jet] using
          Def024LowFlows.phase_continuity a p.2.property.smooth q.2.property.smooth
            (jet_bound p.2 a) hδ p.1 q.1 x.val
      · simpa [G, A, smoothStep, hr, hamFlows, flowMap, jet] using
          Def024LowFlows.trans_continuity a p.2.property.smooth
            (jet_bound p.2 (a + 1)) hδ p.1 q.1 x.val
    _ < ε := hq

private theorem high_step_continuous (hκ : 0 < κ)
    (H : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (R : Finset ℕ) (K : Set (ℕ → ℝ)) (hK : IsCompact K)
    {r : ℕ} (hr : r ∈ R) (hr₂ : 2 ≤ r) (v : K → Smooth L) (hv : Continuous v) :
    Continuous (fun t : K => smoothStep (hamFlows (flows hκ H) R) r (t.val r) (v t)) := by
  classical
  let F := flows hκ H
  obtain ⟨Φ, hΦ, hUnique, _, _, _, hCont, _, _, _⟩ := hierarchy hκ H
  let S : Finset ℕ := {r}
  have hS : ∀ j ∈ S, 2 ≤ j := fun j hj => (by simpa [S] using hj : j = r) ▸ hr₂
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn ((continuous_apply r).continuousOn)
  let T : ℕ → ℝ := fun _ => max B 0
  let t' (t : K) (j : ℕ) : ℝ := if j = r then t.val r else 0
  have ht' : Continuous t' := by
    apply continuous_pi
    intro j
    by_cases h : j = r
    · exact (by simpa [t', h, Function.comp_def] using (continuous_apply r).comp (continuous_subtype_val : Continuous (fun t : K => t.val)))
    · simpa [t', h] using (continuous_const : Continuous (fun _ : K => (0 : ℝ)))
  have hvK : IsCompact (Set.range v) := by
    letI := isCompact_iff_compactSpace.mp hK
    exact isCompact_range hv
  have h := hCont S hS (Set.range v) hvK T (fun _ => le_max_right _ _)
  have hp (t : K) : (v t, t' t) ∈
      (Set.range v) ×ˢ Set.pi Set.univ (fun j => if j ∈ S then Set.Icc (-T j) (T j) else {0}) := by
    refine ⟨⟨t, rfl⟩, fun j _ => ?_⟩
    by_cases hj : j = r
    · subst j
      have hb : |t.val r| ≤ T r :=
        (by simpa only [Real.norm_eq_abs] using hB t t.property : |t.val r| ≤ B).trans (le_max_left _ _)
      simpa [S, t', abs_le.mp hb]
    · simp [S, t', hj]
  refine (h.comp_continuous (hv.prodMk ht') hp).congr ?_
  intro t
  apply Subtype.ext
  have he := hUnique r hr₂ (flowMap F r) (flow_isHam F r) (v t).val (v t).property (t.val r)
  simpa [jointSmooth, S, smoothStep, hr, t', hamFlows, F] using he.symm

/-- The full compact-time continuity uses the higher-flow continuity clause
of the shared input and the explicit phase and translation at orders zero and one. -/
theorem joint_smooth_continuous (hκ : 0 < κ)
    (H : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (R : Finset ℕ) (u : Smooth L) (K : Set (ℕ → ℝ)) (hK : IsCompact K) :
    Continuous (fun t : K => jointSmooth (hamFlows (flows hκ H) R) t.val u) := by
  let F := hamFlows (flows hκ H) R
  have hfold (l : List ℕ) : (∀ r ∈ l, r ∈ R) →
      Continuous (fun t : K => l.foldr (fun r v => smoothStep F r (t.val r) v) u) := by
    induction l with
    | nil => exact fun _ => continuous_const
    | cons r l ih =>
      intro hmem
      let v (t : K) := l.foldr (fun r v => smoothStep F r (t.val r) v) u
      have hv := ih (fun j hj => hmem j (List.mem_cons_of_mem _ hj))
      have hr := hmem r (List.mem_cons_self ..)
      change Continuous (fun t : K => smoothStep F r (t.val r) (v t))
      by_cases hlow : r < 2
      · exact (low_step_continuous (flows hκ H) hr hlow).comp
          (((continuous_apply r).comp continuous_subtype_val).prodMk hv)
      · exact high_step_continuous hκ H R K hK hr (by omega) v hv
  exact hfold _ (fun r hr => (Finset.mem_sort (· ≤ ·)).1 hr)

end QuantumNLS.AllOrderEnergyInputsR57a
