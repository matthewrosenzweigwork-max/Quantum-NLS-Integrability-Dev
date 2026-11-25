import QuantumNLS.Def044InterfacesR51a

/-! DEF-044 window adapter. Prove the formerly assumed ball formulation from
Q07's existing model estimate, at the common real H^(2d+4) dual norm.
This also supplies the weaker fixed-profile scope without a new hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Topology
namespace QuantumNLS.Def044WindowR26m
open PhysicalTensor Def044InterfacesR51a Q07TailBindingR24
variable {L κ : ℝ} [Fact (0 < L)]

/-- Restrict the actual Q07 tail through both canonical continuous linear
maps. Their norm bounds are one, including after restriction to real scalars. -/
theorem common_order_bound (hκ : 0 < κ) (d r : ℕ) (hr : r ≤ d)
    (B : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ l0 : ℕ, ∀ l, l0 ≤ l →
      ∀ u : Sobolev.H02 L (regularity d), ‖u‖ ≤ B →
        DifferentiableAt ℝ (windowError hκ d r hr h l) u ∧
        ‖fderiv ℝ (windowError hκ d r hr h l) u‖ ≤
          C * (PROP017UniformN.cutSeq L l)^(-(1/2 : ℝ)) := by
  obtain ⟨C, hC, l0, hb⟩ := Q07GradientRemovalR24.model_bound (L := L) hκ r B hh
  let A := ((Q07SobolevModelR24.coordinates (L := L) (regularity_pos r).le).toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  let J := (Sobolev.H02.mono (L := L) (regularity_mono hr)).restrictScalars ℝ
  have hnorm : ∀ u, ‖(A.comp J) u‖ ≤ ‖u‖ := by
    intro u
    change ‖Q07SobolevModelR24.coordinates (regularity_pos r).le
      (Sobolev.H02.mono (regularity_mono hr) u)‖ ≤ ‖u‖
    rw [(Q07SobolevModelR24.coordinates (regularity_pos r).le).norm_map]
    exact Sobolev.H02.norm_mono_le _ u
  refine ⟨C, hC, l0, fun l hl u hu => ?_⟩
  obtain ⟨hD, hbound⟩ := hb l hl ((A.comp J) u) ((hnorm u).trans hu)
  have hd := hD.hasFDerivAt.comp u (A.comp J).hasFDerivAt
  have he : windowError hκ d r hr h l =
      Q07TailBindingR24.tail (L := L) hκ r h l ∘ (A.comp J) := rfl
  rw [he]
  refine ⟨hd.differentiableAt, ?_⟩
  rw [hd.fderiv]
  have ha : 0 ≤ PROP017UniformN.cutSeq L l := by
    unfold PROP017UniformN.cutSeq
    exact div_nonneg (mul_nonneg (by positivity) Real.pi_pos.le) (Fact.out : 0 < L).le
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (Real.rpow_nonneg ha _))
  intro v
  calc
    ‖(fderiv ℝ (Q07TailBindingR24.tail (L := L) hκ r h l) ((A.comp J) u)).comp
        (A.comp J) v‖ ≤
      ‖fderiv ℝ (Q07TailBindingR24.tail (L := L) hκ r h l) ((A.comp J) u)‖ *
        ‖(A.comp J) v‖ := by
          change ‖fderiv ℝ (Q07TailBindingR24.tail (L := L) hκ r h l) ((A.comp J) u) ((A.comp J) v)‖ ≤ _
          exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ (C * (PROP017UniformN.cutSeq L l)^(-(1/2 : ℝ))) * ‖v‖ :=
      mul_le_mul hbound (hnorm v) (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg ha _))

/-- One constant and one cutoff for every order at most d, including 0 and 1.
No broad window estimate remains an assumed field. -/
theorem window_differentials (hκ : 0 < κ) : WindowDifferentials (L := L) hκ := by
  intro d _hd B h hh
  have hex := fun r : Fin (d+1) => common_order_bound (L := L) hκ d r.val
    (by omega : r.val ≤ d) B hh
  choose C hC l0 hb using hex
  refine ⟨∑ r : Fin (d+1), C r, Finset.sum_nonneg (fun r _ => hC r),
    Finset.univ.sup l0, ?_⟩
  intro l hl r hr
  let i : Fin (d+1) := ⟨r, by omega⟩
  have hli : l0 i ≤ l := (Finset.le_sup (f := l0) (Finset.mem_univ i)).trans hl
  have hCi : C i ≤ ∑ j : Fin (d+1), C j :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  have ha : 0 ≤ PROP017UniformN.cutSeq L l := by
    unfold PROP017UniformN.cutSeq
    exact div_nonneg (mul_nonneg (by positivity) Real.pi_pos.le) (Fact.out : 0 < L).le
  refine ⟨fun u hu => (hb i l hli u hu).1, fun u hu => ?_⟩
  exact (hb i l hli u hu.1).2.trans
    (mul_le_mul_of_nonneg_right hCi (Real.rpow_nonneg ha _))

/-- The printed fixed smooth profile estimate is a consequence. All real
Hilbert directions, including the radial vector u itself, are tested. -/
theorem fixed_profile (hκ : 0 < κ) (d : ℕ) (hd : 2 ≤ d)
    (u : Sobolev.H02 L (regularity d))
    (hu : ∃ f : ℝ → ℂ, ∃ hf : ClassicalCharges.SmoothPeriodic L f,
      u.val = SmoothScalarMomentsPhysical.smoothL2 hf)
    {h : ℝ} (hh : 0 < h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ l0 : ℕ, ∀ l, l0 ≤ l → ∀ r, ∀ hr : r ≤ d,
      DifferentiableAt ℝ (windowError hκ d r hr h l) u ∧
      ∀ v : Sobolev.H02 L (regularity d),
        ‖fderiv ℝ (windowError hκ d r hr h l) u v‖ ≤
          (C * (PROP017UniformN.cutSeq L l)^(-(1/2 : ℝ))) * ‖v‖ := by
  obtain ⟨C, hC, l0, hb⟩ := window_differentials (L := L) hκ d hd ‖u‖ h hh
  refine ⟨C, hC, l0, fun l hl r hr => ?_⟩
  obtain ⟨hD, hbound⟩ := hb l hl r hr
  refine ⟨hD u le_rfl, fun v => ?_⟩
  exact (ContinuousLinearMap.le_opNorm _ v).trans
    (mul_le_mul_of_nonneg_right (hbound u ⟨le_rfl, hu⟩) (norm_nonneg v))

end QuantumNLS.Def044WindowR26m
#print axioms QuantumNLS.Def044WindowR26m.common_order_bound
#print axioms QuantumNLS.Def044WindowR26m.window_differentials
#print axioms QuantumNLS.Def044WindowR26m.fixed_profile
