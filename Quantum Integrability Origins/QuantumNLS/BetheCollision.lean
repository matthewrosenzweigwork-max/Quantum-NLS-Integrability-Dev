import QuantumNLS.CollisionIdentification

/-!
Actual Bethe collision restrictions on the source's ordinary diagonal measure.
Frozen inputs: CollisionIdentification ffd608f4, BetheH1 faf64019,
BetheWeakGradient 237c4704, BetheExtension c92af850.
Source PR11 3b1f701a, periodic_basis.tex:24–41,245–259; A01.tex:13.
No normalization, nonvanishing, U5, or completeness hypothesis is introduced.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal ComplexConjugate Topology
open MeasureTheory QuantumNLS.PhysicalEnergy QuantumNLS.PhysicalTensor
  QuantumNLS.CollisionTrace QuantumNLS.ProductWeakDerivatives QuantumNLS.Fourier
  QuantumNLS.BetheExtension QuantumNLS.BetheWeakGradient QuantumNLS.BetheH1
  QuantumNLS.CollisionIdentification

namespace QuantumNLS.BetheCollision

/-- FTC and averaging with a measurable square-integrable derivative and a
countable exceptional set. The actual Bethe slices have finite collision sets. -/
theorem point_estimate_off_countable {L : ℝ} (hL : 0 < L) {v dv : ℝ → ℂ}
    (hv : Continuous v) (hdv : Measurable dv)
    (hi : IntervalIntegrable (fun s => ‖dv s‖ ^ 2) volume 0 L)
    {E : Set ℝ} (hE : E.Countable)
    (hd : ∀ s ∈ Set.Ioo 0 L \ E, HasDerivAt v (dv s) s)
    {a : ℝ} (ha : a ∈ Set.Icc 0 L) {ε : ℝ} (hε : 0 < ε) :
    ‖v a‖ ^ 2 ≤ ε * (∫ s in (0 : ℝ)..L, ‖dv s‖ ^ 2) +
      (L⁻¹ + ε⁻¹) * (∫ s in (0 : ℝ)..L, ‖v s‖ ^ 2) := by
  let g : ℝ → ℝ := fun s => ε * ‖dv s‖ ^ 2 + ε⁻¹ * ‖v s‖ ^ 2
  have hgi : IntervalIntegrable g volume 0 L :=
    (hi.const_mul ε).add (((hv.norm.pow 2).intervalIntegrable 0 L).const_mul ε⁻¹)
  have hg0 : ∀ s, 0 ≤ g s := fun s => by dsimp [g]; positivity

  have hbound : ∀ s, |2 * inner ℝ (v s) (dv s)| ≤ g s := by
    intro s
    have h := abs_real_inner_le_norm (v s) (dv s)
    have ht := two_mul_le_aux hε (a := ‖v s‖) (b := ‖dv s‖)
    calc |2 * inner ℝ (v s) (dv s)| = 2 * |inner ℝ (v s) (dv s)| := by rw [abs_mul]; norm_num
      _ ≤ 2 * (‖v s‖ * ‖dv s‖) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ ≤ g s := ht
  have hdi : IntervalIntegrable (fun s => 2 * inner ℝ (v s) (dv s)) volume 0 L :=
    hgi.mono_fun' ((measurable_const.mul (hv.measurable.inner hdv)).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun s => by simpa only [Real.norm_eq_abs] using hbound s))
  have hs : ∀ s ∈ Set.Icc (0 : ℝ) L,
      ‖v a‖ ^ 2 ≤ ‖v s‖ ^ 2 + ∫ t in (0 : ℝ)..L, g t := by
    intro s hs
    have hf : ∀ u w, 0 ≤ u → u ≤ w → w ≤ L →
        |‖v w‖ ^ 2 - ‖v u‖ ^ 2| ≤ ∫ t in (0 : ℝ)..L, g t := by
      intro u w hu huw hw
      have hsub : Set.uIcc u w ⊆ Set.uIcc (0 : ℝ) L := by
        rw [Set.uIcc_of_le huw, Set.uIcc_of_le hL.le]
        intro t ht; exact ⟨hu.trans ht.1, ht.2.trans hw⟩
      have he := integral_eq_of_hasDerivAt_off_countable
        (fun s => ‖v s‖ ^ 2) (fun s => 2 * inner ℝ (v s) (dv s)) hE
        ((hv.norm.pow 2).continuousOn)
        (fun t ht => by
          simp only [min_eq_left huw, max_eq_right huw] at ht
          exact (hd t ⟨⟨hu.trans_lt ht.1.1, ht.1.2.trans_le hw⟩, ht.2⟩).norm_sq)
        (hdi.mono_set hsub)
      have h1 : |∫ t in u..w, 2 * inner ℝ (v t) (dv t)| ≤ ∫ t in u..w, g t := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_of_norm_le
            (f := fun t => 2 * inner ℝ (v t) (dv t)) (μ := volume) huw
            (Filter.Eventually.of_forall (fun t _ => by simpa only [Real.norm_eq_abs] using hbound t))
            (hgi.mono_set hsub)
      have h2 := intervalIntegral.integral_mono_interval (μ := volume) hu huw hw
        (Filter.Eventually.of_forall hg0) hgi
      rw [he] at h1
      exact h1.trans h2
    rcases le_total s a with hsa | has
    · have h := hf s a hs.1 hsa ha.2
      linarith [le_abs_self (‖v a‖ ^ 2 - ‖v s‖ ^ 2)]
    · have h := hf a s ha.1 has hs.2
      linarith [neg_abs_le (‖v s‖ ^ 2 - ‖v a‖ ^ 2)]
  have hvc : Continuous (fun s => ‖v s‖ ^ 2) := by fun_prop
  have hm : (∫ s in (0 : ℝ)..L, ‖v a‖ ^ 2) ≤
      ∫ s in (0 : ℝ)..L, (‖v s‖ ^ 2 + ∫ t in (0 : ℝ)..L, g t) :=
    intervalIntegral.integral_mono_on hL.le intervalIntegrable_const
      ((hvc.intervalIntegrable 0 L).add intervalIntegrable_const) hs
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hvc.intervalIntegrable 0 L) intervalIntegrable_const, intervalIntegral.integral_const] at hm
  have hgint : (∫ s in (0 : ℝ)..L, g s) =
      ε * (∫ s in (0 : ℝ)..L, ‖dv s‖ ^ 2) + ε⁻¹ * (∫ s in (0 : ℝ)..L, ‖v s‖ ^ 2) := by
    dsimp [g]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    · exact hi.const_mul ε
    · exact (by fun_prop : Continuous (fun s => ε⁻¹ * ‖v s‖ ^ 2)).intervalIntegrable _ _
  simp only [sub_zero, smul_eq_mul] at hm
  rw [hgint] at hm
  have hm2 : L * ‖v a‖ ^ 2 ≤ L * (ε * (∫ s in (0 : ℝ)..L, ‖dv s‖ ^ 2) +
      (L⁻¹ + ε⁻¹) * (∫ s in (0 : ℝ)..L, ‖v s‖ ^ 2)) := by
    calc L * ‖v a‖ ^ 2 ≤ (∫ s in (0 : ℝ)..L, ‖v s‖ ^ 2) +
      L * (ε * (∫ s in (0 : ℝ)..L, ‖dv s‖ ^ 2) + ε⁻¹ * (∫ s in (0 : ℝ)..L, ‖v s‖ ^ 2)) := hm
      _ = L * (ε * (∫ s in (0 : ℝ)..L, ‖dv s‖ ^ 2) +
        (L⁻¹ + ε⁻¹) * (∫ s in (0 : ℝ)..L, ‖v s‖ ^ 2)) := by field_simp; ring
  exact le_of_mul_le_mul_left hm2 hL


/-- Bounded measurable gradients have integrable squared norm on the ordinary
finite product measures, without any continuity premise on the gradient. -/
theorem integrable_norm_sq_of_bound {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsFiniteMeasure μ] {G : A → ℂ}
    (hG : Measurable G) (C : ℝ) (hC : ∀ x, ‖G x‖ ≤ C) :
    Integrable (fun x => ‖G x‖ ^ 2) μ := by
  apply (integrable_const (C ^ 2)).mono' (hG.norm.pow_const 2).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖G x‖)]
  nlinarith [hC x, norm_nonneg (G x)]

section Restriction
variable {L : ℝ} [Fact (0 < L)] {N : ℕ} (i j : Fin N) (hij : i ≠ j)

/-- The real-space collision estimate for continuous values and bounded
measurable gradients, with exceptional sets allowed in each normal slice. -/
theorem restriction_integral_estimate_off_countable {F G : (Fin N → AddCircle L) → ℂ}
    (hF : Continuous F) (hG : Measurable G)
    (C : ℝ) (hC : ∀ x, ‖G x‖ ≤ C)
    (hd : ∀ z : DCoord i j → AddCircle L, ∃ E : Set ℝ, E.Countable ∧
      ∀ a ∈ Set.Ioo (0 : ℝ) L \ E,
      HasDerivAt (fun s : ℝ => F (assemble i j hij (s : AddCircle L) z))
        (G (assemble i j hij (a : AddCircle L) z)) a)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ z, ‖F (diagonal i j z)‖ ^ 2
      ∂(Measure.pi fun _ : DCoord i j => (volume : Measure (AddCircle L)))) ≤
      ε * (∫ x, ‖G x‖ ^ 2 ∂torusPiMeasure L N) +
        (L⁻¹ + ε⁻¹) * (∫ x, ‖F x‖ ^ 2 ∂torusPiMeasure L N) := by
  let μ := Measure.pi fun _ : DCoord i j => (volume : Measure (AddCircle L))
  have hcF : Continuous (fun p : AddCircle L × (DCoord i j → AddCircle L) =>
      ‖F (assemble i j hij p.1 p.2)‖ ^ 2) := (hF.comp (continuous_assemble i j hij)).norm.pow 2
  have hintF : Integrable (fun p : AddCircle L × (DCoord i j → AddCircle L) =>
      ‖F (assemble i j hij p.1 p.2)‖ ^ 2) ((volume : Measure (AddCircle L)).prod μ) :=
    hcF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hintG : Integrable (fun p : AddCircle L × (DCoord i j → AddCircle L) =>
      ‖G (assemble i j hij p.1 p.2)‖ ^ 2) ((volume : Measure (AddCircle L)).prod μ) :=
    integrable_norm_sq_of_bound (hG.comp (continuous_assemble i j hij).measurable)
      C (fun p => hC _)
  have hpoint : ∀ z : DCoord i j → AddCircle L,
      ‖F (diagonal i j z)‖ ^ 2 ≤
        ε * (∫ a, ‖G (assemble i j hij a z)‖ ^ 2 ∂(volume : Measure (AddCircle L))) +
        (L⁻¹ + ε⁻¹) * (∫ a, ‖F (assemble i j hij a z)‖ ^ 2 ∂(volume : Measure (AddCircle L))) := by
    intro z
    have hcp : Continuous (fun s : ℝ => assemble i j hij (s : AddCircle L) z) :=
      (continuous_assemble i j hij).comp
        (by fun_prop : Continuous (fun s : ℝ => ((s : AddCircle L), z)))
    obtain ⟨E, hE, hdE⟩ := hd z
    have hm := hG.comp hcp.measurable
    have hi : IntervalIntegrable
        (fun s : ℝ => ‖G (assemble i j hij (s : AddCircle L) z)‖ ^ 2) volume 0 L := by
      apply (intervalIntegrable_const (c := C ^ 2)).mono_fun'
        (by exact (hm.norm.pow_const 2).aestronglyMeasurable)
      filter_upwards with s
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖G (assemble i j hij (s : AddCircle L) z)‖)]
      nlinarith [hC (assemble i j hij (s : AddCircle L) z),
        norm_nonneg (G (assemble i j hij (s : AddCircle L) z))]
    have h := point_estimate_off_countable (Fact.out : 0 < L) (hF.comp hcp) hm hi hE hdE
      (rep_mem (z (.inl ()))) hε
    simp only [Function.comp_apply] at h
    have hGI := AddCircle.intervalIntegral_preimage L 0
      (fun a : AddCircle L => ‖G (assemble i j hij a z)‖ ^ 2)
    have hFI := AddCircle.intervalIntegral_preimage L 0
      (fun a : AddCircle L => ‖F (assemble i j hij a z)‖ ^ 2)
    simp only [zero_add] at hGI hFI
    rw [hGI, hFI] at h
    simpa only [coe_rep, assemble_diagonal] using h
  have hleft : Integrable (fun z => ‖F (diagonal i j z)‖ ^ 2) μ :=
    ((hF.comp (continuous_diagonal i j)).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmain := integral_mono hleft
    ((hintG.integral_prod_right.const_mul ε).add
      (hintF.integral_prod_right.const_mul (L⁻¹ + ε⁻¹))) hpoint
  simp only [Pi.add_apply] at hmain
  rw [integral_add (hintG.integral_prod_right.const_mul ε)
      (hintF.integral_prod_right.const_mul (L⁻¹ + ε⁻¹)), integral_const_mul, integral_const_mul] at hmain
  have hGI : (∫ x, ‖G x‖ ^ 2 ∂torusPiMeasure L N) =
      ∫ z, (∫ a, ‖G (assemble i j hij a z)‖ ^ 2 ∂(volume : Measure (AddCircle L))) ∂μ := by
    rw [← (measurePreserving_normalChart (L := L) i j hij).symm.integral_comp'
      (fun x => ‖G x‖ ^ 2)]
    exact integral_prod_symm _ hintG
  rw [hGI, integral_normalChart i j hij (f := fun x => ‖F x‖ ^ 2) (hF.norm.pow 2)]
  exact hmain


end Restriction

section Identification
variable {L : ℝ} [Fact (0 < L)] {N : ℕ} (i j : Fin N) (hij : i ≠ j)

/-- H¹ trigonometric approximation identifies the literal restriction for a
bounded measurable normal gradient, allowing countable slice exceptions. -/
theorem physicalTrace_eq_literalRestriction_off_countable (x : PhysH1 L N)
    {F G : (Fin N → AddCircle L) → ℂ} (hF : Continuous F) (hG : Measurable G)
    (C : ℝ) (hC : ∀ x, ‖G x‖ ≤ C)
    (hx : (x.val : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N] F)
    (hg : (gradientCLM i x : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N] G)
    (hd : ∀ z : DCoord i j → AddCircle L, ∃ E : Set ℝ, E.Countable ∧
      ∀ a ∈ Set.Ioo (0 : ℝ) L \ E,
      HasDerivAt (fun s : ℝ => F (assemble i j hij (s : AddCircle L) z))
        (G (assemble i j hij (a : AddCircle L) z)) a) :
    physicalTrace i j hij x = literalRestriction i j hF := by
  let P := fun S : Finset (Fin N → ℤ) => trigElem (L := L) S (coeffFun x)
  have hp : Filter.Tendsto P Filter.atTop (nhds x) := trigElem_tendsto x
  have hdiff : Filter.Tendsto (fun S => x - P S) Filter.atTop (nhds 0) := by
    have hc : Filter.Tendsto (fun _ : Finset (Fin N → ℤ) => x) Filter.atTop (nhds x) := tendsto_const_nhds
    simpa only [sub_self] using hc.sub hp
  have hg0 := ((gradientCLM i (L := L)).continuous.tendsto 0).comp hdiff
  have hv0 := ((PhysH1.valCLM (L := L) (k := N)).continuous.tendsto 0).comp hdiff
  simp only [map_zero] at hg0 hv0
  have hrhs : Filter.Tendsto
      (fun S => ‖gradientCLM i (x - P S)‖ ^ 2 + (L⁻¹ + 1) * ‖(x - P S).val‖ ^ 2)
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero,
      PhysH1.valCLM_apply] using (hg0.norm.pow 2).add ((hv0.norm.pow 2).const_mul (L⁻¹ + 1))
  have hbound : ∀ S : Finset (Fin N → ℤ),
      ‖literalRestriction i j hF - physicalTrace i j hij (P S)‖ ^ 2 ≤
        ‖gradientCLM i (x - P S)‖ ^ 2 + (L⁻¹ + 1) * ‖(x - P S).val‖ ^ 2 := by
    intro S
    let c := coeffFun x
    let d := fun w : Fin N → ℤ => WeakDerivatives.ikn L (w i) * c w
    have hxP : ((x - P S).val : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N]
        (fun z => F z - poly (L := L) S c z) := by
      have he : (x - P S).val = x.val - (P S).val := (PhysH1.valₗ (L := L)).map_sub _ _
      rw [he]
      filter_upwards [Lp.coeFn_sub x.val (P S).val, hx, trigElem_ae (L := L) S c] with z hz hzx hzp
      rw [hz, Pi.sub_apply, hzx, hzp]
      rfl
    have hgP : (gradientCLM i (x - P S) : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N]
        (fun z => G z - poly (L := L) S d z) := by
      rw [map_sub, gradientCLM_trigElem]
      filter_upwards [Lp.coeFn_sub (gradientCLM i x) (trigElem (L := L) S d).val,
        hg, trigElem_ae (L := L) S d] with z hz hzx hzp
      rw [hz, Pi.sub_apply, hzx, hzp]
      rfl
    have htP : ((literalRestriction i j hF - physicalTrace i j hij (P S) : CollisionL2 (L := L) i j) :
        (DCoord i j → AddCircle L) → ℂ) =ᵐ[Measure.pi fun _ : DCoord i j => (volume : Measure (AddCircle L))]
        (fun z => F (diagonal i j z) - poly (L := L) S c (diagonal i j z)) := by
      filter_upwards [Lp.coeFn_sub (literalRestriction i j hF) (physicalTrace i j hij (P S)),
        literalRestriction_ae i j hF, physicalTrace_trigElem_ae (L := L) i j hij S c] with z hz hzx hzp
      rw [hz, Pi.sub_apply, hzx, hzp]
    rw [lp_norm_sq_of_ae _ htP, lp_norm_sq_of_ae _ hgP, lp_norm_sq_of_ae _ hxP]
    obtain ⟨B, hB⟩ := (isCompact_univ.image (continuous_poly (L := L) S d)).isBounded.exists_norm_le
    have hBP : ∀ z, ‖poly (L := L) S d z‖ ≤ B :=
      fun z => hB _ (Set.mem_image_of_mem _ (Set.mem_univ z))
    have h := restriction_integral_estimate_off_countable i j hij
      (hF.sub (continuous_poly S c)) (hG.sub (continuous_poly S d).measurable)
      (C + B) (fun z => (norm_sub_le _ _).trans (add_le_add (hC z) (hBP z)))
      (fun z => by
        obtain ⟨E, hE, hdE⟩ := hd z
        exact ⟨E, hE, fun a ha => (hdE a ha).sub (poly_hasDerivAt i j hij S c z a)⟩) one_pos
    simpa only [Pi.sub_apply, one_mul, inv_one] using h

  have hsq : Filter.Tendsto
      (fun S => ‖literalRestriction i j hF - physicalTrace i j hij (P S)‖ ^ 2)
      Filter.atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun S => sq_nonneg _)
      (Filter.Eventually.of_forall hbound) hrhs
  have hn := (Real.continuous_sqrt.tendsto 0).comp hsq
  change Filter.Tendsto
    (fun S => Real.sqrt (‖literalRestriction i j hF - physicalTrace i j hij (P S)‖ ^ 2))
    Filter.atTop (nhds (Real.sqrt 0)) at hn
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  have ht : Filter.Tendsto (fun S => physicalTrace i j hij (P S)) Filter.atTop
      (nhds (literalRestriction i j hF)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [norm_sub_rev] using hn
  exact tendsto_nhds_unique (((physicalTrace i j hij).continuous.tendsto x).comp hp) ht

end Identification
section Bethe
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The finite exceptional set for a normal slice, including repeated
spectator values. No generic-position premise is needed. -/
def sliceCollisions (i j : Fin N) (hij : i ≠ j)
    (z : DCoord i j → AddCircle L) : Finset ℝ :=
  Finset.univ.image (representatives L (assemble i j hij (0 : AddCircle L) z))

/-- Off the explicit finite collision set and away from the periodic seam,
the literal Bethe function has its constructed measurable gradient. -/
theorem torusExtension_slice_hasDerivAt (c : ℝ) (n : Fin N → ℤ)
    (i j : Fin N) (hij : i ≠ j) (z : DCoord i j → AddCircle L)
    {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) L) (he : a ∉ sliceCollisions i j hij z) :
    HasDerivAt (fun s : ℝ => torusExtension L c n (assemble i j hij (s : AddCircle L) z))
      (torusGradient L c n i (assemble i j hij (a : AddCircle L) z)) a := by
  classical
  let X := representatives L (assemble i j hij (0 : AddCircle L) z)
  have hrep : ∀ s ∈ Set.Ico (0 : ℝ) L,
      representatives L (assemble i j hij (s : AddCircle L) z) = Function.update X i s := by
    intro s hs
    funext l
    by_cases hl : l = i
    · subst l
      simp only [representatives, assemble_i, Function.update_self]
      exact AddCircle.equivIco_coe_of_mem (by simpa using hs)
    · rw [Function.update_of_ne hl]
      change rep (assemble i j hij (s : AddCircle L) z l) =
        rep (assemble i j hij (0 : AddCircle L) z l)
      rw [assemble_ne i j hij hl (s : AddCircle L) 0 z]
  have hnot : a ∉ Set.range X := by
    simpa only [sliceCollisions, Finset.mem_image, Finset.mem_univ, true_and,
      Set.mem_range, X] using he
  have hd := BetheWeakGradient.slice_hasDerivAt L c n i X hnot
  have heq : (fun s : ℝ => torusExtension L c n (assemble i j hij (s : AddCircle L) z))
      =ᶠ[nhds a] (fun s => symmetricExtension L c n (Function.update X i s)) := by
    filter_upwards [Ioo_mem_nhds ha.1 ha.2] with s hs
    change symmetricExtension L c n (representatives L (assemble i j hij (s : AddCircle L) z)) = _
    rw [hrep s ⟨hs.1.le, hs.2⟩]
  have h := hd.congr_of_eventuallyEq heq
  simpa only [torusGradient, hrep a ⟨ha.1.le, ha.2⟩] using h

/-- Identification of the existing H¹ kinetic derivative map with the actual
bounded measurable Bethe gradient. -/
theorem gradientCLM_waveH1 {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ}
    (hn : Antitone n) (i : Fin (N+1)) :
    gradientCLM i (waveH1 (L := L) hc hn) = weakGradient c n i := by
  apply gradientCLM_eq_of_weak
  rw [waveH1_val]
  exact wave_hasWeakPartial hc hn i

/-- The actual unnormalized Bethe wall value is the continuous extension
trace in physical L²(dy_ij). All H¹ and derivative facts are proved inputs. -/
theorem physicalTrace_waveH1 {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ}
    (hn : Antitone n) (i j : Fin (N+1)) (hij : i ≠ j) :
    physicalTrace i j hij (waveH1 (L := L) hc hn) =
      literalRestriction i j (continuous_torusExtension (L := L) hc hn) := by
  apply physicalTrace_eq_literalRestriction_off_countable i j hij
    (waveH1 (L := L) hc hn) (continuous_torusExtension hc hn)
    (measurable_torusGradient L c n i)
    (gradientBound c (BetheSmooth.sourceRoots L n c))
    (fun y => norm_gradient_le L c n i (representatives L y))
    (coe_waveH1_val hc hn)
  · rw [gradientCLM_waveH1 hc hn]
    exact coe_weakGradient c n i
  · intro z
    refine ⟨(sliceCollisions i j hij z : Set ℝ), (sliceCollisions i j hij z).finite_toSet.countable, ?_⟩
    intro a ha
    exact torusExtension_slice_hasDerivAt c n i j hij z ha.1 ha.2

/-- The physical trace of the Bethe H¹ vector equals its literal restriction
almost everywhere on the actual collision coordinates. -/
theorem physicalTrace_waveH1_ae {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ}
    (hn : Antitone n) (i j : Fin (N+1)) (hij : i ≠ j) :
    (physicalTrace i j hij (waveH1 (L := L) hc hn) : (DCoord i j → AddCircle L) → ℂ)
      =ᵐ[Measure.pi fun _ : DCoord i j => (volume : Measure (AddCircle L))]
      (fun z => torusExtension L c n (diagonal i j z)) := by
  rw [physicalTrace_waveH1 hc hn]
  exact literalRestriction_ae i j (continuous_torusExtension hc hn)

/-- The coefficient-valued frozen traceCLM is the inverse physical unitary
applied to the actual Bethe wall restriction. -/
theorem traceCLM_waveH1 {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ}
    (hn : Antitone n) (i j : Fin (N+1)) (hij : i ≠ j) :
    traceCLM i j hij (waveH1 (L := L) hc hn) =
      (collisionUnitary i j).symm
        (literalRestriction i j (continuous_torusExtension (L := L) hc hn)) := by
  apply (collisionUnitary (L := L) i j).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact physicalTrace_waveH1 hc hn i j hij

end Bethe
section PhysicalPairings
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The actual Bethe restriction on the precise common-coordinate times
spectator product measure dy_ij; there is no surface-measure factor. -/
theorem productTrace_waveH1_ae {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ}
    (hn : Antitone n) (i j : Fin (N+1)) (hij : i ≠ j) :
    (productTrace (L := L) i j hij (waveH1 hc hn) :
      (AddCircle L × (Rest (N+1) i j → AddCircle L)) → ℂ) =ᵐ[dyij (L := L) i j]
      (fun p => torusExtension L c n (diagPoint i j p.1 p.2)) := by
  let e := unitSumPositions L (Rest (N+1) i j)
  have he := measurePreserving_unitSumPositions L (Rest (N+1) i j)
  change ((lpCongr e he).symm (physicalTrace i j hij (waveH1 hc hn)) :
    (AddCircle L × (Rest (N+1) i j → AddCircle L)) → ℂ) =ᵐ[_] _
  rw [lpCongr_symm_apply]
  have h1 := Lp.coeFn_compMeasurePreserving (physicalTrace i j hij (waveH1 hc hn)) he.symm
  have h2 := he.symm.quasiMeasurePreserving.ae_eq_comp (physicalTrace_waveH1_ae hc hn i j hij)
  filter_upwards [h1, h2] with p hp1 hp2
  rw [hp1, hp2]
  rfl

/-- Exact norm of the frozen coefficient trace as the ordinary collision
integral of the unnormalized Bethe formula. -/
theorem traceCLM_waveH1_norm_sq {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ}
    (hn : Antitone n) (i j : Fin (N+1)) (hij : i ≠ j) :
    ‖traceCLM i j hij (waveH1 (L := L) hc hn)‖ ^ 2 =
      ∫ p, ‖torusExtension L c n (diagPoint i j p.1 p.2)‖ ^ 2 ∂dyij (L := L) i j := by
  rw [← productTrace_norm i j hij]
  exact lp_norm_sq_of_ae _ (productTrace_waveH1_ae hc hn i j hij)

/-- The source epsilon estimate, now for the literal Bethe wall values and
actual bounded measurable Bethe gradient on the ordinary measures. -/
theorem bethe_wall_estimate {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ}
    (hn : Antitone n) (i j : Fin (N+1)) (hij : i ≠ j)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ p, ‖torusExtension L c n (diagPoint i j p.1 p.2)‖ ^ 2 ∂dyij (L := L) i j) ≤
      ε * (∫ x, ‖torusGradient L c n i x‖ ^ 2 ∂torusPiMeasure L (N+1)) +
        (L⁻¹ + ε⁻¹) * (∫ x, ‖torusExtension L c n x‖ ^ 2 ∂torusPiMeasure L (N+1)) := by
  rw [← traceCLM_waveH1_norm_sq hc hn i j hij, ← productTrace_norm i j hij]
  have hw : HasWeakPartial i (waveH1 (L := L) hc hn).val (weakGradient c n i) := by
    rw [waveH1_val]
    exact wave_hasWeakPartial hc hn i
  have h := productTrace_estimate_realspace i j hij hε (waveH1 (L := L) hc hn)
    (weakGradient c n i) hw
  rw [lp_norm_sq_of_ae _ (coe_weakGradient c n i),
    lp_norm_sq_of_ae _ (coe_waveH1_val hc hn)] at h
  exact h

/-- Inner products can use any representatives of the two actual L² classes. -/
theorem inner_eq_integral_of_ae {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (f g : Lp ℂ 2 μ) {F G : A → ℂ} (hf : (f : A → ℂ) =ᵐ[μ] F)
    (hg : (g : A → ℂ) =ᵐ[μ] G) :
    ⟪f, g⟫_ℂ = ∫ x, conj (F x) * G x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf, hg] with x hx hy
  rw [RCLike.inner_apply', hx, hy]

/-- The actual Bethe kinetic and contact pairings for an arbitrary H¹ test.
The coefficient is exactly 2c and the collision measure is exactly dy_ij. -/
theorem q_waveH1_physical {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ}
    (hn : Antitone n) (v : PhysH1 L (N+1)) :
    ContactForm.q c (waveH1 (L := L) hc hn) v =
      (∑ i, ⟪weakGradient (L := L) c n i, gradientCLM i v⟫_ℂ) +
      ((2 * c : ℝ) : ℂ) * ∑ p : ContactForm.Pair (N+1),
        (∫ y, conj (torusExtension L c n (diagPoint p.1.1 p.1.2 y.1 y.2)) *
          (productTrace p.1.1 p.1.2 (ne_of_lt p.2) v :
            (AddCircle L × (Rest (N+1) p.1.1 p.1.2 → AddCircle L)) → ℂ) y
          ∂dyij (L := L) p.1.1 p.1.2) := by
  rw [q_eq_physical_pairings]
  simp only [gradientCLM_waveH1 hc hn]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact inner_eq_integral_of_ae _ _ (productTrace_waveH1_ae hc hn _ _ _) Filter.EventuallyEq.rfl

/-- A smooth test's actual weak derivative, as a pointwise classical lift. -/
theorem gradientCLM_smooth_ae {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ)
    (i : Fin N) :
    (gradientCLM i (smoothH1 hφ) : (Fin N → AddCircle L) → ℂ)
      =ᵐ[torusPiMeasure L N] liftK (L := L) (pderiv i φ) := by
  have hw := smooth_hasWeakPartial hφ i
  rw [← smoothH1_val hφ] at hw
  rw [gradientCLM_eq_of_weak i (smoothH1 hφ) _ hw]
  exact (memLp_liftK (continuous_pderiv hφ i)).coeFn_toLp

/-- The fully literal left-hand side of the Bethe weak contact eigenidentity
against every smooth periodic test. A second integration by parts is still
needed to identify this with the energy times the bulk pairing. -/
theorem q_waveH1_smooth {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ}
    (hn : Antitone n) {φ : (Fin (N+1) → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    ContactForm.q c (waveH1 (L := L) hc hn) (smoothH1 hφ) =
      (∑ i, ∫ x, conj (torusGradient L c n i x) * liftK (L := L) (pderiv i φ) x
        ∂torusPiMeasure L (N+1)) +
      ((2 * c : ℝ) : ℂ) * ∑ p : ContactForm.Pair (N+1),
        (∫ y, conj (torusExtension L c n (diagPoint p.1.1 p.1.2 y.1 y.2)) *
          liftK (L := L) φ (diagPoint p.1.1 p.1.2 y.1 y.2) ∂dyij (L := L) p.1.1 p.1.2) := by
  rw [q_eq_physical_pairings]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [gradientCLM_waveH1 hc hn]
    exact inner_eq_integral_of_ae _ _ (coe_weakGradient c n i) (gradientCLM_smooth_ae hφ i)
  · congr 1
    apply Finset.sum_congr rfl
    intro p _
    exact inner_eq_integral_of_ae _ _ (productTrace_waveH1_ae hc hn _ _ _)
      (productTrace_smooth _ _ _ hφ)

/-- The right-hand bulk pairing uses the same actual Bethe extension and
ordinary mass-L^(N+1) measure as the contact identity. -/
theorem inner_waveH1_smooth {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ}
    (hn : Antitone n) {φ : (Fin (N+1) → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    ⟪(waveH1 (L := L) hc hn).val, (smoothH1 hφ).val⟫_ℂ =
      ∫ x, conj (torusExtension L c n x) * liftK (L := L) φ x ∂torusPiMeasure L (N+1) := by
  apply inner_eq_integral_of_ae _ _ (coe_waveH1_val hc hn)
  rw [smoothH1_val]
  exact (memLp_liftK hφ.smooth.continuous).coeFn_toLp

end PhysicalPairings
section ChamberBoundary
open QuantumNLS.BetheWavefunctions QuantumNLS.BetheContact

/-- The source's adjacent-wall contact equation, expressed in the actual
coordinate partials needed for the jumps in a second integration by parts. -/
theorem ansatzPartial_contact {N : ℕ} (c : ℝ) (q x : Fin N → ℝ)
    (hq : Function.Injective q) {a b : Fin N} (hadj : b.val = a.val + 1)
    (hx : x a = x b) :
    ansatzPartial c q a x - ansatzPartial c q b x =
      (c : ℂ) * coordinateAnsatz c q x := by
  classical
  apply sub_eq_zero.mp
  calc
    _ = ∑ σ : Equiv.Perm (Fin N), contactResidual c (q ∘ σ) x a b := by
      unfold ansatzPartial coordinateAnsatz
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro σ _
      unfold contactResidual
      simp only [Function.comp_apply, Complex.ofReal_sub]
      ring
    _ = 0 := sum_contactResidual_eq_zero c q x hq hadj hx

/-- The actual roots satisfy the partial-coordinate wall equation with
coefficient c; no contact condition is supplied by the caller. -/
theorem wavefunction_partial_contact {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {N : ℕ} {n : Fin N → ℤ} (hn : Antitone n) (x : Fin N → ℝ)
    {a b : Fin N} (hadj : b.val = a.val + 1) (hx : x a = x b) :
    ansatzPartial c (BetheSmooth.sourceRoots L n c) a x -
      ansatzPartial c (BetheSmooth.sourceRoots L n c) b x =
      (c : ℂ) * wavefunction L c n x :=
  ansatzPartial_contact c _ x (BetheSmooth.sourceRoots_strictAnti hL hc hn).injective hadj hx

/-- A chamber gradient is continuous as a literal finite exponential sum. -/
theorem continuous_ansatzPartial {N : ℕ} (c : ℝ) (q : Fin N → ℝ) (i : Fin N) :
    Continuous (ansatzPartial c q i) := by
  unfold ansatzPartial planeWave
  fun_prop

/-- Each chamber's second partial is also a literal continuous finite sum. -/
theorem continuous_ansatzSecondPartial {N : ℕ} (c : ℝ) (q : Fin N → ℝ) (i : Fin N) :
    Continuous (ansatzSecondPartial c q i) := by
  unfold ansatzSecondPartial planeWave
  fun_prop

/-- Second integration by parts on each individual coordinate chamber
piece, retaining both endpoint gradient terms with the correct conjugation.
The global finite-piece jump and outer-face cancellation is a separate step. -/
theorem chamber_second_integrationByParts {N : ℕ} (c : ℝ) (q x : Fin N → ℝ)
    (i : Fin N) (a b : ℝ) (φ : ℝ → ℂ) (hφ : ContDiff ℝ 1 φ) :
    (∫ t in a..b, conj (ansatzPartial c q i (Function.update x i t)) * deriv φ t) =
      conj (ansatzPartial c q i (Function.update x i b)) * φ b -
      conj (ansatzPartial c q i (Function.update x i a)) * φ a -
      ∫ t in a..b, conj (ansatzSecondPartial c q i (Function.update x i t)) * φ t := by
  have hf : Continuous (fun t => conj (ansatzPartial c q i (Function.update x i t))) :=
    continuous_star.comp ((continuous_ansatzPartial c q i).comp
      (by fun_prop : Continuous (fun t : ℝ => Function.update x i t)))
  have hg : Continuous (fun t => conj (ansatzSecondPartial c q i (Function.update x i t))) :=
    continuous_star.comp ((continuous_ansatzSecondPartial c q i).comp
      (by fun_prop : Continuous (fun t : ℝ => Function.update x i t)))
  have hi₁ := (hg.intervalIntegrable (μ := volume) a b).mul_continuousOn hφ.continuous.continuousOn
  have hi₂ := (hφ.continuous_deriv_one.intervalIntegrable (μ := volume) a b).continuousOn_mul hf.continuousOn
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => (ansatzPartial_update_hasDerivAt c q x i t).star.mul
      ((hφ.differentiable (by norm_num)) t).hasDerivAt) (hi₁.add hi₂)
  change (∫ t in a..b, conj (ansatzSecondPartial c q i (Function.update x i t)) * φ t +
      conj (ansatzPartial c q i (Function.update x i t)) * deriv φ t) = _ at he
  rw [intervalIntegral.integral_add hi₁ hi₂] at he
  change (∫ t in a..b, conj (ansatzSecondPartial c q i (Function.update x i t)) * φ t) +
      (∫ t in a..b, conj (ansatzPartial c q i (Function.update x i t)) * deriv φ t) =
      conj (ansatzPartial c q i (Function.update x i b)) * φ b -
      conj (ansatzPartial c q i (Function.update x i a)) * φ a at he
  linear_combination he

end ChamberBoundary

end QuantumNLS.BetheCollision

#print axioms QuantumNLS.BetheCollision.point_estimate_off_countable
#print axioms QuantumNLS.BetheCollision.integrable_norm_sq_of_bound
#print axioms QuantumNLS.BetheCollision.restriction_integral_estimate_off_countable
#print axioms QuantumNLS.BetheCollision.physicalTrace_eq_literalRestriction_off_countable
#print axioms QuantumNLS.BetheCollision.sliceCollisions
#print axioms QuantumNLS.BetheCollision.torusExtension_slice_hasDerivAt
#print axioms QuantumNLS.BetheCollision.gradientCLM_waveH1
#print axioms QuantumNLS.BetheCollision.physicalTrace_waveH1
#print axioms QuantumNLS.BetheCollision.physicalTrace_waveH1_ae
#print axioms QuantumNLS.BetheCollision.traceCLM_waveH1
#print axioms QuantumNLS.BetheCollision.productTrace_waveH1_ae
#print axioms QuantumNLS.BetheCollision.traceCLM_waveH1_norm_sq
#print axioms QuantumNLS.BetheCollision.bethe_wall_estimate
#print axioms QuantumNLS.BetheCollision.inner_eq_integral_of_ae
#print axioms QuantumNLS.BetheCollision.q_waveH1_physical
#print axioms QuantumNLS.BetheCollision.gradientCLM_smooth_ae
#print axioms QuantumNLS.BetheCollision.q_waveH1_smooth
#print axioms QuantumNLS.BetheCollision.inner_waveH1_smooth
#print axioms QuantumNLS.BetheCollision.ansatzPartial_contact
#print axioms QuantumNLS.BetheCollision.wavefunction_partial_contact
#print axioms QuantumNLS.BetheCollision.continuous_ansatzPartial
#print axioms QuantumNLS.BetheCollision.continuous_ansatzSecondPartial
#print axioms QuantumNLS.BetheCollision.chamber_second_integrationByParts
