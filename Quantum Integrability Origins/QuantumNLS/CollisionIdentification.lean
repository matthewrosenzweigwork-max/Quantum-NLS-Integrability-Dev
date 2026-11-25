import QuantumNLS.BetheH1

/-!
Physical realization of the frozen collision trace, on the coordinate measure dy_ij.
Source: PR11 3b1f701a, A01.tex:13 (R-C21B75F5).
Frozen CollisionTrace and Bethe modules are imported, never changed.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal ComplexConjugate
open QuantumNLS.Energy
open MeasureTheory QuantumNLS.PhysicalEnergy QuantumNLS.PhysicalTensor
  QuantumNLS.CollisionTrace QuantumNLS.ProductWeakDerivatives QuantumNLS.Fourier

namespace QuantumNLS.CollisionIdentification

/-- Reindexing square-summable coefficients preserves their unweighted norm. -/
def seqCongr {A B : Type*} (e : A ≃ B) : L2 A ≃ₗᵢ[ℂ] L2 B where
  toFun c := ⟨fun b => c (e.symm b), memL2_iff.2
    (e.symm.summable_iff.2 (summable_sq c))⟩
  invFun c := ⟨fun a => c (e a), memL2_iff.2 (e.summable_iff.2 (summable_sq c))⟩
  left_inv c := by ext a; simp
  right_inv c := by ext b; simp
  map_add' c d := rfl
  map_smul' z c := rfl
  norm_map' c := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
    exact e.symm.tsum_eq (fun a => ‖c a‖ ^ 2)

/-- Pullback by a measure-preserving measurable equivalence is unitary on L². -/
def lpCongr {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} (e : A ≃ᵐ B) (he : MeasurePreserving e μ ν) :
    Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ e he) (by
    intro c
    refine ⟨Lp.compMeasurePreserving e.symm he.symm c, ?_⟩
    change Lp.compMeasurePreserving e he (Lp.compMeasurePreserving e.symm he.symm c) = c
    rw [← Lp.compMeasurePreserving_comp_apply]
    have hid : (e.symm ∘ e) = id := funext e.symm_apply_apply
    simp only [hid, Lp.compMeasurePreserving_id_apply])

theorem lpCongr_symm_apply {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} (e : A ≃ᵐ B) (he : MeasurePreserving e μ ν)
    (c : Lp ℂ 2 μ) :
    (lpCongr e he).symm c = Lp.compMeasurePreserving e.symm he.symm c := by
  apply (lpCongr e he).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  change c = Lp.compMeasurePreserving e he (Lp.compMeasurePreserving e.symm he.symm c)
  rw [← Lp.compMeasurePreserving_comp_apply]
  have hid : (e.symm ∘ e) = id := funext e.symm_apply_apply
  simp only [hid, Lp.compMeasurePreserving_id_apply]

section FiniteProduct
variable (L : ℝ) [Fact (0 < L)] (I : Type*) [Fintype I]

abbrev PiL2 := Lp ℂ 2 (Measure.pi fun _ : I => (volume : Measure (AddCircle L)))

/-- The already constructed finite-product Fourier unitary, with arbitrary finite labels. -/
def piFourier : PiL2 L I ≃ₗᵢ[ℂ] L2 (I → ℤ) :=
  let e := Fintype.equivFin I
  (lpCongr (MeasurableEquiv.piCongrLeft (fun _ : I => AddCircle L) e.symm)
    (measurePreserving_piCongrLeft (fun _ : I => (volume : Measure (AddCircle L))) e.symm)).trans
    ((momUnitary L (Fintype.card I)).trans
      (seqCongr (Equiv.arrowCongr e.symm (Equiv.refl ℤ))))

/-- The inverse product Fourier unitary sends δ_w to the literal product mode. -/
theorem piFourier_symm_single_ae (w : I → ℤ) :
    ((piFourier L I).symm (lp.single 2 w 1) : (I → AddCircle L) → ℂ) =ᵐ[Measure.pi fun _ : I => (volume : Measure (AddCircle L))]
      (fun z => ∏ l, mode L (w l) (z l)) := by
  let e := Fintype.equivFin I
  let eP := MeasurableEquiv.piCongrLeft (fun _ : I => AddCircle L) e.symm
  have heP := measurePreserving_piCongrLeft (fun _ : I => (volume : Measure (AddCircle L))) e.symm
  let U := lpCongr eP heP
  let w' : Fin (Fintype.card I) → ℤ := fun l => w (e.symm l)
  have hmode : piFourier L I (U.symm (prodMode L (Fintype.card I) w')) = lp.single 2 w 1 := by
    change seqCongr (Equiv.arrowCongr e.symm (Equiv.refl ℤ))
      (momUnitary L (Fintype.card I) (U (U.symm (prodMode L (Fintype.card I) w')))) = _
    rw [U.apply_symm_apply, momUnitary_prodMode]
    apply Subtype.ext; funext z
    change (lp.single 2 w' 1 : L2 (Fin (Fintype.card I) → ℤ))
      ((Equiv.arrowCongr e.symm (Equiv.refl ℤ)).symm z) = (lp.single 2 w 1 : L2 (I → ℤ)) z
    simp only [lp.single_apply, Pi.single_apply]
    have heq : (Equiv.arrowCongr e.symm (Equiv.refl ℤ)).symm z = w' ↔ z = w := by
      rw [Equiv.symm_apply_eq]
      have hw : Equiv.arrowCongr e.symm (Equiv.refl ℤ) w' = w := by
        funext l; simp [Equiv.arrowCongr, w']
      rw [hw]
    simp only [heq]
  have hv : (piFourier L I).symm (lp.single 2 w 1) = U.symm (prodMode L (Fintype.card I) w') :=
    (piFourier L I).injective (by rw [LinearIsometryEquiv.apply_symm_apply, hmode])
  rw [hv, lpCongr_symm_apply]
  have h1 := Lp.coeFn_compMeasurePreserving (prodMode L (Fintype.card I) w') heP.symm
  have h2 := heP.symm.quasiMeasurePreserving.ae_eq_comp (prodMode_ae (L := L) w')
  filter_upwards [h1, h2] with z hz1 hz2
  rw [hz1, hz2]
  change (∏ l : Fin (Fintype.card I), mode L (w (e.symm l)) (z (e.symm l))) = _
  exact e.symm.prod_comp (fun l => mode L (w l) (z l))

end FiniteProduct

section Collision
variable {L : ℝ} [Fact (0 < L)] {N : ℕ} (i j : Fin N) (hij : i ≠ j)

/-- One common coordinate and the N-2 spectator coordinates. -/
abbrev DCoord := Unit ⊕ Rest N i j

/-- The literal coordinate measure dy_ij, with each circle of mass L. -/
abbrev CollisionL2 := PiL2 L (DCoord i j)

/-- Momentum coordinates (s,m) in the same finite coordinate labels. -/
def diagIndex : TIdx N i j ≃ (DCoord i j → ℤ) where
  toFun p := Sum.elim (fun _ => p.1) p.2
  invFun w := (w (.inl ()), fun l => w (.inr l))
  left_inv p := rfl
  right_inv w := by funext l; cases l with
    | inl u => cases u; rfl
    | inr l => rfl

/-- Explicit unitary from the frozen coefficient target to the physical collision L². -/
def collisionUnitary : L2 (TIdx N i j) ≃ₗᵢ[ℂ] CollisionL2 (L := L) i j :=
  (seqCongr (diagIndex i j)).trans (piFourier L (DCoord i j)).symm

/-- The collision trace with its physical, unweighted L² target. -/
def physicalTrace : PhysH1 L N →L[ℂ] CollisionL2 (L := L) i j :=
  (collisionUnitary i j).toContinuousLinearEquiv.toContinuousLinearMap ∘L traceCLM i j hij

@[simp] theorem physicalTrace_norm (x : PhysH1 L N) :
    ‖physicalTrace i j hij x‖ = ‖traceCLM i j hij x‖ :=
  (collisionUnitary i j).norm_map _

/-- Exact printed estimate with the actual distributional derivative and physical target. -/
theorem physicalTrace_estimate {ε : ℝ} (hε : 0 < ε) (x : PhysH1 L N)
    (G : L2TN L N) (hG : HasWeakPartial i x.val G) :
    ‖physicalTrace i j hij x‖ ^ 2 ≤
      ε * ‖G‖ ^ 2 + (L⁻¹ + ε⁻¹) * ‖x.val‖ ^ 2 := by
  rw [physicalTrace_norm, traceCLM_apply, norm_sq_of_hasWeakPartial hG]
  exact trace_estimate i j hij hε x

/-- Uniqueness of the physical continuous extension from trigonometric polynomials. -/
theorem physicalTrace_unique (T : PhysH1 L N →L[ℂ] CollisionL2 (L := L) i j)
    (h : ∀ (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ),
      T (trigElem (L := L) S c) = physicalTrace i j hij (trigElem (L := L) S c)) :
    T = physicalTrace i j hij := by
  refine ContinuousLinearMap.ext fun x => ?_
  have h1 := (T.continuous.tendsto x).comp (trigElem_tendsto x)
  have h2 := ((physicalTrace i j hij).continuous.tendsto x).comp (trigElem_tendsto x)
  have he : (T ∘ fun S : Finset (Fin N → ℤ) => trigElem (L := L) S (coeffFun x)) =
      (physicalTrace i j hij ∘ fun S : Finset (Fin N → ℤ) => trigElem (L := L) S (coeffFun x)) :=
    funext fun S => h S _
  rw [he] at h1
  exact tendsto_nhds_unique h1 h2

/-- Labels for the normal coordinate, common coordinate and spectators. -/
def splitIndex : Fin N ≃ Unit ⊕ DCoord i j where
  toFun l := if h : l = i then .inl () else
    if h' : l = j then .inr (.inl ()) else .inr (.inr ⟨l, h, h'⟩)
  invFun l := match l with
    | .inl _ => i
    | .inr (.inl _) => j
    | .inr (.inr l) => l.val
  left_inv l := by
    by_cases h : l = i
    · simp [h]
    · by_cases h' : l = j <;> simp [h, h', hij.symm]
  right_inv l := by
    rcases l with u | (u | ⟨l, hi, hj⟩)
    · cases u; simp
    · cases u; simp [hij.symm]
    · simp [hi, hj]

/-- The collision carrier has exactly N-1 circle coordinates. -/
theorem card_DCoord (hij : i ≠ j) : Fintype.card (DCoord i j) = N - 1 := by
  have h := Fintype.card_congr (splitIndex i j hij)
  simp only [DCoord, Fintype.card_fin, Fintype.card_sum, Fintype.card_unit] at h ⊢
  omega

/-- The common-coordinate parametrization of the actual diagonal. -/
def diagonal (z : DCoord i j → AddCircle L) : Fin N → AddCircle L :=
  diagPoint i j (z (.inl ())) (fun l => z (.inr l))

omit [Fact (0 < L)] in
theorem continuous_diagonal : Continuous (diagonal (L := L) i j) := by
  apply continuous_pi; intro l
  unfold diagonal diagPoint
  split_ifs <;> fun_prop

/-- Fourier label remaining after the two colliding momenta are added. -/
def collapse (w : Fin N → ℤ) : TIdx N i j := (w i + w j, fun l => w l.val)

theorem fib_eq_iff (τ : TIdx N i j) (a : ℤ) (w : Fin N → ℤ) :
    fib i j hij τ a = w ↔ τ = collapse i j w ∧ a = w i := by
  have he : fibEquiv i j hij w = (collapse i j w, w i) := rfl
  rw [← fibEquiv_symm_apply, Equiv.symm_apply_eq, he, Prod.mk.injEq]

/-- The trace of one actual product mode has the source's factor L^(-1/2). -/
theorem traceCLM_single (w : Fin N → ℤ) :
    traceCLM i j hij (trigElem (L := L) {w} (fun _ => 1)) =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) • lp.single 2 (collapse i j w) 1 := by
  apply Subtype.ext; funext τ
  rw [traceCLM_apply, traceMap_apply]
  unfold traceCoeff
  simp only [coeffFun_trigElem, Finset.mem_singleton, fib_eq_iff]
  by_cases hτ : τ = collapse i j w
  · simp [hτ, lp.single_apply]
  · simp [hτ, lp.single_apply]

theorem collisionUnitary_single_ae (τ : TIdx N i j) :
    (collisionUnitary (L := L) i j (lp.single 2 τ 1) : (DCoord i j → AddCircle L) → ℂ) =ᵐ[Measure.pi fun _ : DCoord i j => (volume : Measure (AddCircle L))]
      (fun z => Ediag i j τ (z (.inl ())) (fun l => z (.inr l))) := by
  have hs : seqCongr (diagIndex i j) (lp.single 2 τ 1) = lp.single 2 (diagIndex i j τ) 1 := by
    apply Subtype.ext; funext w
    change (lp.single 2 τ 1 : L2 (TIdx N i j)) ((diagIndex i j).symm w) = _
    simp only [lp.single_apply, Pi.single_apply, Equiv.symm_apply_eq]
  change ((piFourier L (DCoord i j)).symm (seqCongr (diagIndex i j) (lp.single 2 τ 1)) :
    (DCoord i j → AddCircle L) → ℂ) =ᵐ[_] _
  rw [hs]
  have h := piFourier_symm_single_ae L (DCoord i j) (diagIndex i j τ)
  filter_upwards [h] with z hz
  rw [hz]
  simp only [DCoord, Fintype.prod_sum_type, Fintype.prod_unique, Ediag]
  rfl

/-- A finite Fourier polynomial, as an actual everywhere-defined function. -/
def poly (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ)
    (x : Fin N → AddCircle L) : ℂ := ∑ w ∈ S, c w * ∏ l, mode L (w l) (x l)

omit [Fact (0 < L)] in
theorem continuous_poly (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ) :
    Continuous (poly (L := L) S c) := by
  exact continuous_finsetSum _ fun w _ => continuous_const.mul (continuous_prodModeFun w)

theorem trigElem_sum (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ) :
    trigElem (L := L) S c = ∑ w ∈ S, c w • trigElem (L := L) {w} (fun _ => 1) := by
  apply PhysH1.val_injective
  change (trigElem (L := L) S c).val = (PhysH1.valₗ (L := L)) _
  rw [val_trigElem, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_smul]
  change c w • prodMode L N w = c w • (trigElem (L := L) {w} (fun _ => 1)).val
  simp only [val_trigElem, Finset.sum_singleton, one_smul]

theorem physicalTrace_single_ae (w : Fin N → ℤ) :
    (physicalTrace (L := L) i j hij (trigElem (L := L) {w} (fun _ => 1)) :
      (DCoord i j → AddCircle L) → ℂ) =ᵐ[Measure.pi fun _ : DCoord i j => (volume : Measure (AddCircle L))]
      (fun z => ∏ l, mode L (w l) (diagonal i j z l)) := by
  have he : physicalTrace (L := L) i j hij (trigElem (L := L) {w} (fun _ => 1)) =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) • collisionUnitary (L := L) i j (lp.single 2 (collapse i j w) 1) := by
    change collisionUnitary i j (traceCLM i j hij _) = _
    rw [traceCLM_single, map_smul]
  rw [he]
  filter_upwards [Lp.coeFn_smul (((Real.sqrt L)⁻¹ : ℝ) : ℂ)
      (collisionUnitary (L := L) i j (lp.single 2 (collapse i j w) 1)),
    collisionUnitary_single_ae (L := L) i j (collapse i j w)] with z hz1 hz2
  rw [hz1, Pi.smul_apply, smul_eq_mul, hz2]
  exact (prodMode_diag i j hij w _ _).symm

/-- Physical L² agreement with the literal restriction for all Fourier polynomials. -/
theorem physicalTrace_trigElem_ae (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ) :
    (physicalTrace (L := L) i j hij (trigElem (L := L) S c) :
      (DCoord i j → AddCircle L) → ℂ) =ᵐ[Measure.pi fun _ : DCoord i j => (volume : Measure (AddCircle L))]
      (fun z => poly (L := L) S c (diagonal i j z)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have he : trigElem (L := L) ∅ c = 0 := by rw [trigElem_sum]; simp
    simp only [he, map_zero, poly, Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 _
  | insert w S hw ih =>
    have he : trigElem (L := L) (insert w S) c =
        c w • trigElem (L := L) {w} (fun _ => 1) + trigElem (L := L) S c := by
      rw [trigElem_sum, Finset.sum_insert hw, trigElem_sum S c]
    rw [he, map_add, map_smul]
    filter_upwards [Lp.coeFn_add
        (c w • physicalTrace (L := L) i j hij (trigElem (L := L) {w} (fun _ => 1)))
        (physicalTrace i j hij (trigElem (L := L) S c)),
      Lp.coeFn_smul (c w) (physicalTrace (L := L) i j hij (trigElem (L := L) {w} (fun _ => 1))),
      physicalTrace_single_ae (L := L) i j hij w, ih] with z hz1 hz2 hz3 hz4
    rw [hz1, Pi.add_apply, hz2, Pi.smul_apply, smul_eq_mul, hz3, hz4]
    simp only [poly, Finset.sum_insert hw]

end Collision

/-- Splitting off a single common coordinate preserves ordinary product measure. -/
def unitSumPositions (L : ℝ) (I : Type*) [Fintype I] :
    (Unit ⊕ I → AddCircle L) ≃ᵐ (AddCircle L × (I → AddCircle L)) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ I => AddCircle L)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique Unit (AddCircle L))
      (MeasurableEquiv.refl _))

theorem measurePreserving_unitSumPositions (L : ℝ) [Fact (0 < L)]
    (I : Type*) [Fintype I] :
    MeasurePreserving (unitSumPositions L I)
      (Measure.pi fun _ : Unit ⊕ I => (volume : Measure (AddCircle L)))
      ((volume : Measure (AddCircle L)).prod
        (Measure.pi fun _ : I => (volume : Measure (AddCircle L)))) :=
  ((measurePreserving_funUnique (volume : Measure (AddCircle L)) Unit).prod
    (MeasurePreserving.id _)).comp
      (measurePreserving_sumPiEquivProdPi (fun _ : Unit ⊕ I => (volume : Measure (AddCircle L))))

section CircleEstimate
variable {L : ℝ}

/-- The source's FTC and averaging inequality for an arbitrary C¹ circle slice.
The value may be taken at any a in [0,L]. -/
theorem point_estimate (hL : 0 < L) {v dv : ℝ → ℂ}
    (hv : Continuous v) (hdv : Continuous dv) (hd : ∀ s, HasDerivAt v (dv s) s)
    {a : ℝ} (ha : a ∈ Set.Icc 0 L) {ε : ℝ} (hε : 0 < ε) :
    ‖v a‖ ^ 2 ≤ ε * (∫ s in (0 : ℝ)..L, ‖dv s‖ ^ 2) +
      (L⁻¹ + ε⁻¹) * (∫ s in (0 : ℝ)..L, ‖v s‖ ^ 2) := by
  let g : ℝ → ℝ := fun s => ε * ‖dv s‖ ^ 2 + ε⁻¹ * ‖v s‖ ^ 2
  have hgc : Continuous g := by fun_prop
  have hg0 : ∀ s, 0 ≤ g s := fun s => by dsimp [g]; positivity
  have hdc : Continuous (fun s => 2 * inner ℝ (v s) (dv s)) := by fun_prop
  have hder : ∀ s, HasDerivAt (fun s => ‖v s‖ ^ 2) (2 * inner ℝ (v s) (dv s)) s :=
    fun s => (hd s).norm_sq
  have hbound : ∀ s, |2 * inner ℝ (v s) (dv s)| ≤ g s := by
    intro s
    have h := abs_real_inner_le_norm (v s) (dv s)
    have ht := two_mul_le_aux hε (a := ‖v s‖) (b := ‖dv s‖)
    calc |2 * inner ℝ (v s) (dv s)| = 2 * |inner ℝ (v s) (dv s)| := by rw [abs_mul]; norm_num
      _ ≤ 2 * (‖v s‖ * ‖dv s‖) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ ≤ g s := ht
  have hs : ∀ s ∈ Set.Icc (0 : ℝ) L,
      ‖v a‖ ^ 2 ≤ ‖v s‖ ^ 2 + ∫ t in (0 : ℝ)..L, g t := by
    intro s hs
    have hf : ∀ u w, 0 ≤ u → u ≤ w → w ≤ L →
        |‖v w‖ ^ 2 - ‖v u‖ ^ 2| ≤ ∫ t in (0 : ℝ)..L, g t := by
      intro u w hu huw hw
      have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hder t) (hdc.intervalIntegrable u w)
      have h1 : |∫ t in u..w, 2 * inner ℝ (v t) (dv t)| ≤ ∫ t in u..w, g t := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_of_norm_le
            (f := fun t => 2 * inner ℝ (v t) (dv t)) (μ := volume) huw
            (Filter.Eventually.of_forall (fun t _ => by simpa only [Real.norm_eq_abs] using hbound t))
            (hgc.intervalIntegrable u w)
      have h2 := intervalIntegral.integral_mono_interval (μ := volume) hu huw hw
        (Filter.Eventually.of_forall hg0) (hgc.intervalIntegrable 0 L)
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
    · exact (by fun_prop : Continuous (fun s => ε * ‖dv s‖ ^ 2)).intervalIntegrable _ _
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

end CircleEstimate
/-- The physical L² norm is the integral of the squared norm of any representative. -/
theorem lp_norm_sq_of_ae {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (f : Lp ℂ 2 μ) {F : A → ℂ} (hF : (f : A → ℂ) =ᵐ[μ] F) :
    ‖f‖ ^ 2 = ∫ a, ‖F a‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq f, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF] with a ha
  rw [ha, real_inner_self_eq_norm_sq]

section SmoothRestriction
variable {L : ℝ} [Fact (0 < L)] {N : ℕ} (i j : Fin N) (hij : i ≠ j)

/-- The actual product chart separating x_i from all other coordinates. -/
def normalChart : (Fin N → AddCircle L) ≃ᵐ
    (AddCircle L × (DCoord i j → AddCircle L)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Unit ⊕ DCoord i j => AddCircle L)
    (splitIndex i j hij)).trans (unitSumPositions L (DCoord i j))

theorem measurePreserving_normalChart : MeasurePreserving (normalChart (L := L) i j hij)
    (torusPiMeasure L N) ((volume : Measure (AddCircle L)).prod
      (Measure.pi fun _ : DCoord i j => (volume : Measure (AddCircle L)))) :=
  (measurePreserving_unitSumPositions L (DCoord i j)).comp
    (measurePreserving_piCongrLeft (fun _ : Unit ⊕ DCoord i j =>
      (volume : Measure (AddCircle L))) (splitIndex i j hij))

/-- Inserting a normal coordinate and the unaltered spectator coordinates. -/
def assemble (a : AddCircle L) (z : DCoord i j → AddCircle L) : Fin N → AddCircle L :=
  fun l => Sum.elim (fun _ => a) z (splitIndex i j hij l)

omit [Fact (0 < L)] in
theorem normalChart_symm_apply (a : AddCircle L) (z : DCoord i j → AddCircle L) :
    (normalChart i j hij).symm (a, z) = assemble i j hij a z := rfl

omit [Fact (0 < L)] in
theorem continuous_assemble : Continuous (fun p : AddCircle L × (DCoord i j → AddCircle L) =>
    assemble i j hij p.1 p.2) := by
  apply continuous_pi; intro l
  dsimp only [assemble]
  cases splitIndex i j hij l <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

omit [Fact (0 < L)] in
theorem assemble_diagonal (z : DCoord i j → AddCircle L) :
    assemble i j hij (z (.inl ())) z = diagonal i j z := by
  funext l
  simp only [assemble, splitIndex, Equiv.coe_fn_mk, diagonal, diagPoint]
  split_ifs <;> rfl

/-- Fubini in the source's common-coordinate and spectator parametrization. -/
theorem integral_normalChart {f : (Fin N → AddCircle L) → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂torusPiMeasure L N) =
      ∫ z, (∫ a, f (assemble i j hij a z) ∂(volume : Measure (AddCircle L)))
        ∂(Measure.pi fun _ : DCoord i j => (volume : Measure (AddCircle L))) := by
  have hmp := (measurePreserving_normalChart (L := L) i j hij).symm
  rw [← hmp.integral_comp' f]
  exact integral_prod_symm _ ((hf.comp (continuous_assemble i j hij)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))

/-- The literal restriction estimate for every continuous function with continuous
classical derivative in x_i. This is independent of the Fourier trace construction. -/
theorem restriction_integral_estimate {F G : (Fin N → AddCircle L) → ℂ}
    (hF : Continuous F) (hG : Continuous G)
    (hd : ∀ (z : DCoord i j → AddCircle L) (a : ℝ),
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
  have hcG : Continuous (fun p : AddCircle L × (DCoord i j → AddCircle L) =>
      ‖G (assemble i j hij p.1 p.2)‖ ^ 2) := (hG.comp (continuous_assemble i j hij)).norm.pow 2
  have hintF : Integrable (fun p : AddCircle L × (DCoord i j → AddCircle L) =>
      ‖F (assemble i j hij p.1 p.2)‖ ^ 2) ((volume : Measure (AddCircle L)).prod μ) :=
    hcF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hintG : Integrable (fun p : AddCircle L × (DCoord i j → AddCircle L) =>
      ‖G (assemble i j hij p.1 p.2)‖ ^ 2) ((volume : Measure (AddCircle L)).prod μ) :=
    hcG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpoint : ∀ z : DCoord i j → AddCircle L,
      ‖F (diagonal i j z)‖ ^ 2 ≤
        ε * (∫ a, ‖G (assemble i j hij a z)‖ ^ 2 ∂(volume : Measure (AddCircle L))) +
        (L⁻¹ + ε⁻¹) * (∫ a, ‖F (assemble i j hij a z)‖ ^ 2 ∂(volume : Measure (AddCircle L))) := by
    intro z
    have hcp : Continuous (fun s : ℝ => assemble i j hij (s : AddCircle L) z) :=
      (continuous_assemble i j hij).comp
        (by fun_prop : Continuous (fun s : ℝ => ((s : AddCircle L), z)))
    have h := point_estimate (Fact.out : 0 < L) (hF.comp hcp) (hG.comp hcp) (hd z)
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
  rw [integral_normalChart i j hij (f := fun x => ‖G x‖ ^ 2) (hG.norm.pow 2),
    integral_normalChart i j hij (f := fun x => ‖F x‖ ^ 2) (hF.norm.pow 2)]
  exact hmain

/-- The actual weak partial on H¹, with a physical L² target. -/
def gradientCLM (i : Fin N) : PhysH1 L N →L[ℂ] L2TN L N :=
  (momUnitary L N).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (Complex.I • ContactForm.Dj i)

theorem gradientCLM_eq_of_weak (x : PhysH1 L N) (G : L2TN L N)
    (hG : HasWeakPartial i x.val G) : gradientCLM i x = G := by
  apply (momUnitary L N).injective
  change momUnitary L N ((momUnitary L N).symm (Complex.I • ContactForm.Dj i x)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Subtype.ext; funext w
  change Complex.I * (ContactForm.Dj i x : (Fin N → ℤ) → ℂ) w = _
  rw [ContactForm.Dj_apply, momUnitary_of_hasWeakPartial hG]
  simp only [WeakDerivatives.ikn, coeffFun, mul_assoc]

theorem gradientCLM_trigElem (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ) :
    gradientCLM i (trigElem (L := L) S c) =
      (trigElem (L := L) S (fun w => WeakDerivatives.ikn L (w i) * c w)).val := by
  apply (momUnitary L N).injective
  change momUnitary L N ((momUnitary L N).symm (Complex.I • ContactForm.Dj i (trigElem S c))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, momUnitary_trigElem]
  apply Subtype.ext; funext w
  change Complex.I * (ContactForm.Dj i (trigElem S c) : (Fin N → ℤ) → ℂ) w = _
  rw [ContactForm.Dj_apply, coeffFun_trigElem, finVec_apply]
  split_ifs <;> simp [WeakDerivatives.ikn, mul_assoc]

omit [Fact (0 < L)] in
theorem assemble_i (a : AddCircle L) (z : DCoord i j → AddCircle L) :
    assemble i j hij a z i = a := by simp [assemble, splitIndex]

omit [Fact (0 < L)] in
theorem assemble_ne {l : Fin N} (hl : l ≠ i) (a b : AddCircle L)
    (z : DCoord i j → AddCircle L) :
    assemble i j hij a z l = assemble i j hij b z l := by
  simp only [assemble, splitIndex, Equiv.coe_fn_mk, dite_eq_right hl]
  split_ifs <;> rfl

omit [Fact (0 < L)] in
/-- Every finite Fourier polynomial has its literal classical slice derivative. -/
theorem poly_hasDerivAt (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ)
    (z : DCoord i j → AddCircle L) (a : ℝ) :
    HasDerivAt (fun s : ℝ => poly (L := L) S c (assemble i j hij (s : AddCircle L) z))
      (poly (L := L) S (fun w => WeakDerivatives.ikn L (w i) * c w)
        (assemble i j hij (a : AddCircle L) z)) a := by
  classical
  unfold poly
  apply HasDerivAt.fun_sum
  intro w hw
  have he : (fun s : ℝ => ∏ l, mode L (w l) (assemble i j hij (s : AddCircle L) z l)) =
      fun s : ℝ => mode L (w i) (s : AddCircle L) *
        ∏ l ∈ Finset.univ.erase i, mode L (w l) (assemble i j hij (0 : AddCircle L) z l) := by
    funext s
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), assemble_i]
    congr 1
    apply Finset.prod_congr rfl
    intro l hl
    rw [assemble_ne i j hij (Finset.ne_of_mem_erase hl) (s : AddCircle L) 0 z]
  have hd := ((WeakDerivatives.hasDerivAt_emode (L := L) (w i) a).mul_const
    (∏ l ∈ Finset.univ.erase i, mode L (w l) (assemble i j hij (0 : AddCircle L) z l))).const_mul (c w)
  have hfun : (fun s : ℝ => c w * ∏ l, mode L (w l) (assemble i j hij (s : AddCircle L) z l)) =
      (fun s : ℝ => c w * (mode L (w i) (s : AddCircle L) *
        ∏ l ∈ Finset.univ.erase i, mode L (w l) (assemble i j hij (0 : AddCircle L) z l))) :=
    congrArg (fun f : ℝ → ℂ => fun s => c w * f s) he
  rw [hfun]
  convert hd using 1
  · rfl
  · rw [congrFun he a]
    unfold WeakDerivatives.emode
    ring

/-- The literal continuous restriction as an AE class in physical collision L². -/
def literalRestriction {F : (Fin N → AddCircle L) → ℂ} (hF : Continuous F) :
    CollisionL2 (L := L) i j :=
  ContinuousMap.toLp 2 (Measure.pi fun _ : DCoord i j => (volume : Measure (AddCircle L))) ℂ
    ⟨fun z => F (diagonal i j z), hF.comp (continuous_diagonal i j)⟩

theorem literalRestriction_ae {F : (Fin N → AddCircle L) → ℂ} (hF : Continuous F) :
    (literalRestriction i j hF : (DCoord i j → AddCircle L) → ℂ) =ᵐ[Measure.pi fun _ : DCoord i j => (volume : Measure (AddCircle L))]
      (fun z => F (diagonal i j z)) :=
  ContinuousMap.coeFn_toLp _ _

/-- Smooth restriction agreement, proved by actual trigonometric H¹ approximation
and the independent real-space FTC bound. F and G are actual continuous representatives,
with G the classical and distributional partial in the normal coordinate. -/
theorem physicalTrace_eq_literalRestriction (x : PhysH1 L N)
    {F G : (Fin N → AddCircle L) → ℂ} (hF : Continuous F) (hG : Continuous G)
    (hx : (x.val : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N] F)
    (hg : (gradientCLM i x : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N] G)
    (hd : ∀ (z : DCoord i j → AddCircle L) (a : ℝ),
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
    have h := restriction_integral_estimate i j hij (hF.sub (continuous_poly S c))
      (hG.sub (continuous_poly S d))
      (fun z a => (hd z a).sub (poly_hasDerivAt i j hij S c z a)) one_pos
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

omit [Fact (0 < L)] in
/-- Classical differentiation preserves the actual period lattice. -/
theorem latticePeriodic_pderiv {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) (k : Fin N) :
    LatticePeriodic L (pderiv k φ) := by
  have hdiff : Differentiable ℝ φ :=
    (hφ.smooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))).differentiable one_ne_zero
  intro x m
  let v : Fin N → ℝ := fun l => m l * L
  have he : (fun y => φ (y + v)) = φ := funext fun y => hφ.periodic y m
  have hf := congrArg (fun f => fderiv ℝ f x) he
  rw [fderiv_comp_add_right] at hf
  simp only [pderiv_eq_fderiv hdiff]
  exact congrArg (fun A : (Fin N → ℝ) →L[ℝ] ℂ => A (Pi.single k 1)) hf

/-- Actual smooth periodic lifts have the classical derivative in every normal slice. -/
theorem liftK_hasDerivAt {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ)
    (z : DCoord i j → AddCircle L) (a : ℝ) :
    HasDerivAt (fun s : ℝ => liftK (L := L) φ (assemble i j hij (s : AddCircle L) z))
      (liftK (L := L) (pderiv i φ) (assemble i j hij (a : AddCircle L) z)) a := by
  let X : Fin N → ℝ := fun l => rep (assemble i j hij (0 : AddCircle L) z l)
  have hc : ∀ s : ℝ, (fun l => (Function.update X i s l : AddCircle L)) =
      assemble i j hij (s : AddCircle L) z := by
    intro s; funext l
    by_cases hl : l = i
    · subst l; simp only [Function.update_self, assemble_i]
    · rw [Function.update_of_ne hl, coe_rep]
      exact assemble_ne i j hij hl 0 (s : AddCircle L) z
  have he : ∀ (ψ : (Fin N → ℝ) → ℂ), LatticePeriodic L ψ →
      (fun s : ℝ => liftK (L := L) ψ (assemble i j hij (s : AddCircle L) z)) =
        fun s => ψ (Function.update X i s) := by
    intro ψ hp; funext s
    rw [← hc s, liftK_coe hp]
  rw [he φ hφ.periodic, congrFun (he (pderiv i φ) (latticePeriodic_pderiv hφ i)) a]
  have hdiff : Differentiable ℝ φ :=
    (hφ.smooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))).differentiable one_ne_zero
  rw [pderiv_eq_fderiv hdiff]
  exact (hdiff _).hasFDerivAt.comp_hasDerivAt a (hasDerivAt_update X i a)

/-- Product Fourier coefficients are pairK with the opposite integer momentum. -/
theorem momUnitary_eq_pairK (F : L2TN L N) (w : Fin N → ℤ) :
    (momUnitary L N F : (Fin N → ℤ) → ℂ) w = pairK (F : (Fin N → AddCircle L) → ℂ) (fun l => -w l) := by
  rw [momUnitary_apply_eq_inner, MeasureTheory.L2.inner_def]
  unfold pairK
  apply integral_congr_ae
  filter_upwards [prodMode_ae (L := L) w] with z hz
  rw [RCLike.inner_apply', hz, map_prod]
  simp only [conj_mode]

theorem pairK_congr_ae {F G : (Fin N → AddCircle L) → ℂ}
    (h : F =ᵐ[torusPiMeasure L N] G) (w : Fin N → ℤ) : pairK F w = pairK G w := by
  apply integral_congr_ae
  filter_upwards [h] with z hz
  rw [hz]

/-- The classical partial of every smooth periodic function is its weak partial.
No trace agreement or normalization hypothesis is used. -/
theorem smooth_hasWeakPartial {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) (k : Fin N) :
    HasWeakPartial k ((memLp_liftK hφ.smooth.continuous).toLp (liftK (L := L) φ))
      ((memLp_liftK (continuous_pderiv hφ k)).toLp (liftK (L := L) (pderiv k φ))) := by
  apply hasWeakPartial_of_momUnitary
  intro w
  rw [momUnitary_eq_pairK, momUnitary_eq_pairK,
    pairK_congr_ae (memLp_liftK (continuous_pderiv hφ k)).coeFn_toLp,
    pairK_congr_ae (memLp_liftK hφ.smooth.continuous).coeFn_toLp]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := k.pos; omega⟩
  rw [pairK_pderiv k hφ]
  simp only [WeakDerivatives.ikn, freq, Int.cast_neg, neg_div, mul_neg, Complex.ofReal_neg, neg_neg]

/-- Every smooth periodic lift actually belongs to the existing physical H¹. -/
theorem smooth_mem_range {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    (memLp_liftK hφ.smooth.continuous).toLp (liftK (L := L) φ) ∈
      Set.range (PhysH1.val : PhysH1 L N → L2TN L N) := by
  apply (mem_range_physH1_iff _).2
  intro k
  exact ⟨_, smooth_hasWeakPartial hφ k⟩

/-- The physical H¹ realization of an actual arbitrary smooth periodic function. -/
def smoothH1 {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) : PhysH1 L N :=
  (smooth_mem_range hφ).choose

theorem smoothH1_val {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    (smoothH1 hφ).val = (memLp_liftK hφ.smooth.continuous).toLp (liftK (L := L) φ) :=
  (smooth_mem_range hφ).choose_spec

/-- G1: the constructed continuous trace is the literal restriction for EVERY
smooth lattice-periodic function, proved via trigonometric approximation. -/
theorem physicalTrace_smooth {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    (physicalTrace (L := L) i j hij (smoothH1 hφ) : (DCoord i j → AddCircle L) → ℂ) =ᵐ[Measure.pi fun _ : DCoord i j => (volume : Measure (AddCircle L))]
      (fun z => liftK (L := L) φ (diagonal i j z)) := by
  have hF := BetheH1.continuous_liftK hφ.smooth.continuous hφ.periodic
  have hG := BetheH1.continuous_liftK (continuous_pderiv hφ i) (latticePeriodic_pderiv hφ i)
  have hx : ((smoothH1 hφ).val : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N]
      liftK (L := L) φ := by
    rw [smoothH1_val]
    exact (memLp_liftK hφ.smooth.continuous).coeFn_toLp
  have hg : (gradientCLM i (smoothH1 hφ) : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N]
      liftK (L := L) (pderiv i φ) := by
    have hw := smooth_hasWeakPartial hφ i
    rw [← smoothH1_val hφ] at hw
    rw [gradientCLM_eq_of_weak i (smoothH1 hφ) _ hw]
    exact (memLp_liftK (continuous_pderiv hφ i)).coeFn_toLp
  rw [physicalTrace_eq_literalRestriction i j hij (smoothH1 hφ) hF hG hx hg
    (liftK_hasDerivAt i j hij hφ)]
  exact literalRestriction_ae i j hF

/-- The printed source argument on actual Fourier polynomials: FTC in x_i,
averaging and Young, then real-space Fubini in the remaining coordinates. -/
theorem physicalTrace_trig_estimate_realspace {ε : ℝ} (hε : 0 < ε)
    (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ) :
    ‖physicalTrace i j hij (trigElem (L := L) S c)‖ ^ 2 ≤
      ε * ‖gradientCLM i (trigElem (L := L) S c)‖ ^ 2 +
        (L⁻¹ + ε⁻¹) * ‖(trigElem (L := L) S c).val‖ ^ 2 := by
  let d := fun w : Fin N → ℤ => WeakDerivatives.ikn L (w i) * c w
  rw [lp_norm_sq_of_ae _ (physicalTrace_trigElem_ae i j hij S c),
    gradientCLM_trigElem,
    lp_norm_sq_of_ae _ (trigElem_ae (L := L) S d),
    lp_norm_sq_of_ae _ (trigElem_ae (L := L) S c)]
  exact restriction_integral_estimate i j hij (continuous_poly S c) (continuous_poly S d)
    (poly_hasDerivAt i j hij S c) hε

/-- The source's complete real-space argument, extended by actual H¹ trig density.
This proof of the estimate does not use Fourier-fiber summation. -/
theorem physicalTrace_estimate_realspace {ε : ℝ} (hε : 0 < ε) (x : PhysH1 L N)
    (G : L2TN L N) (hG : HasWeakPartial i x.val G) :
    ‖physicalTrace i j hij x‖ ^ 2 ≤
      ε * ‖G‖ ^ 2 + (L⁻¹ + ε⁻¹) * ‖x.val‖ ^ 2 := by
  rw [← gradientCLM_eq_of_weak i x G hG]
  have hp := trigElem_tendsto x
  have ht := (((physicalTrace i j hij).continuous.tendsto x).comp hp).norm.pow 2
  have hg := (((gradientCLM i).continuous.tendsto x).comp hp).norm.pow 2
  have hv := (((PhysH1.valCLM (L := L) (k := N)).continuous.tendsto x).comp hp).norm.pow 2
  have hr := (hg.const_mul ε).add (hv.const_mul (L⁻¹ + ε⁻¹))
  exact le_of_tendsto_of_tendsto ht hr
    (Filter.Eventually.of_forall fun S => physicalTrace_trig_estimate_realspace i j hij hε S (coeffFun x))

end SmoothRestriction

section LiteralProductTarget
variable {L : ℝ} [Fact (0 < L)] {N : ℕ} (i j : Fin N) (hij : i ≠ j)

/-- The printed dy_ij measure: common coordinate times the other N-2 circles. -/
abbrev dyij : Measure (AddCircle L × (Rest N i j → AddCircle L)) :=
  (volume : Measure (AddCircle L)).prod (Measure.pi fun _ : Rest N i j => volume)

abbrev CollisionProductL2 := Lp ℂ 2 (dyij (L := L) i j)

/-- Literal G2, including the explicit coordinate measure, not just a coefficient carrier. -/
def collisionProductUnitary : L2 (TIdx N i j) ≃ₗᵢ[ℂ] CollisionProductL2 (L := L) i j :=
  (collisionUnitary i j).trans
    (lpCongr (unitSumPositions L (Rest N i j))
      (measurePreserving_unitSumPositions L (Rest N i j))).symm

def productTrace : PhysH1 L N →L[ℂ] CollisionProductL2 (L := L) i j :=
  (collisionProductUnitary i j).toContinuousLinearEquiv.toContinuousLinearMap ∘L traceCLM i j hij

@[simp] theorem productTrace_norm (x : PhysH1 L N) :
    ‖productTrace i j hij x‖ = ‖traceCLM i j hij x‖ :=
  (collisionProductUnitary i j).norm_map _

theorem productTrace_estimate {ε : ℝ} (hε : 0 < ε) (x : PhysH1 L N) (G : L2TN L N)
    (hG : HasWeakPartial i x.val G) :
    ‖productTrace i j hij x‖ ^ 2 ≤ ε * ‖G‖ ^ 2 + (L⁻¹ + ε⁻¹) * ‖x.val‖ ^ 2 := by
  rw [productTrace_norm, traceCLM_apply, norm_sq_of_hasWeakPartial hG]
  exact trace_estimate i j hij hε x

/-- The exact physical-target estimate via the printed FTC, Fubini and density argument. -/
theorem productTrace_estimate_realspace {ε : ℝ} (hε : 0 < ε) (x : PhysH1 L N)
    (G : L2TN L N) (hG : HasWeakPartial i x.val G) :
    ‖productTrace i j hij x‖ ^ 2 ≤ ε * ‖G‖ ^ 2 + (L⁻¹ + ε⁻¹) * ‖x.val‖ ^ 2 := by
  rw [productTrace_norm, ← physicalTrace_norm i j hij]
  exact physicalTrace_estimate_realspace i j hij hε x G hG

/-- Literal G1 on the exact printed product target and its coordinate measure. -/
theorem productTrace_smooth {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    (productTrace (L := L) i j hij (smoothH1 hφ) :
      (AddCircle L × (Rest N i j → AddCircle L)) → ℂ) =ᵐ[dyij (L := L) i j]
      (fun p => liftK (L := L) φ (diagPoint i j p.1 p.2)) := by
  let e := unitSumPositions L (Rest N i j)
  have he := measurePreserving_unitSumPositions L (Rest N i j)
  change ((lpCongr e he).symm (physicalTrace i j hij (smoothH1 hφ)) :
    (AddCircle L × (Rest N i j → AddCircle L)) → ℂ) =ᵐ[_] _
  rw [lpCongr_symm_apply]
  have h1 := Lp.coeFn_compMeasurePreserving (physicalTrace i j hij (smoothH1 hφ)) he.symm
  have h2 := he.symm.quasiMeasurePreserving.ae_eq_comp (physicalTrace_smooth i j hij hφ)
  filter_upwards [h1, h2] with p hp1 hp2
  rw [hp1, hp2]
  rfl

theorem productTrace_unique (T : PhysH1 L N →L[ℂ] CollisionProductL2 (L := L) i j)
    (h : ∀ (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ),
      T (trigElem (L := L) S c) = productTrace i j hij (trigElem (L := L) S c)) :
    T = productTrace i j hij := by
  refine ContinuousLinearMap.ext fun x => ?_
  have h1 := (T.continuous.tendsto x).comp (trigElem_tendsto x)
  have h2 := ((productTrace i j hij).continuous.tendsto x).comp (trigElem_tendsto x)
  have he : (T ∘ fun S : Finset (Fin N → ℤ) => trigElem (L := L) S (coeffFun x)) =
      (productTrace i j hij ∘ fun S : Finset (Fin N → ℤ) => trigElem (L := L) S (coeffFun x)) :=
    funext fun S => h S _
  rw [he] at h1
  exact tendsto_nhds_unique h1 h2

/-- The frozen contact pairing is exactly the physical collision L² pairing. -/
theorem productTrace_inner (φ ψ : PhysH1 L N) :
    ⟪productTrace i j hij φ, productTrace i j hij ψ⟫_ℂ =
      ⟪traceCLM i j hij φ, traceCLM i j hij ψ⟫_ℂ :=
  (collisionProductUnitary i j).inner_map_map _ _

/-- Source-faithful trace package: physical target, exact epsilon bound, and
agreement with the actual restriction of every smooth periodic function. -/
theorem exists_physical_collision_trace (hij : i ≠ j) :
    ∃ T : PhysH1 L N →L[ℂ] CollisionProductL2 (L := L) i j,
      (∀ (ε : ℝ), 0 < ε → ∀ (x : PhysH1 L N) (G : L2TN L N),
        HasWeakPartial i x.val G →
        ‖T x‖ ^ 2 ≤ ε * ‖G‖ ^ 2 + (L⁻¹ + ε⁻¹) * ‖x.val‖ ^ 2) ∧
      (∀ (φ : (Fin N → ℝ) → ℂ) (hφ : IsTorusTest L φ),
        (T (smoothH1 hφ) : (AddCircle L × (Rest N i j → AddCircle L)) → ℂ) =ᵐ[dyij (L := L) i j]
          (fun p => liftK (L := L) φ (diagPoint i j p.1 p.2))) ∧
      (∀ T' : PhysH1 L N →L[ℂ] CollisionProductL2 (L := L) i j,
        (∀ (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ),
          T' (trigElem (L := L) S c) = T (trigElem (L := L) S c)) → T' = T) := by
  refine ⟨productTrace i j hij, ?_, ?_, ?_⟩
  · intro ε hε x G hG
    exact productTrace_estimate_realspace i j hij hε x G hG
  · intro φ hφ
    exact productTrace_smooth i j hij hφ
  · intro T' hT'
    exact productTrace_unique i j hij T' hT'

end LiteralProductTarget

section ContactPairings
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

theorem gradientCLM_inner (i : Fin N) (φ ψ : PhysH1 L N) :
    ⟪gradientCLM i φ, gradientCLM i ψ⟫_ℂ = ⟪ContactForm.Dj i φ, ContactForm.Dj i ψ⟫_ℂ := by
  change ⟪(momUnitary L N).symm (Complex.I • ContactForm.Dj i φ),
    (momUnitary L N).symm (Complex.I • ContactForm.Dj i ψ)⟫_ℂ = _
  rw [LinearIsometryEquiv.inner_map_map, inner_smul_left, inner_smul_right]
  simp only [Complex.conj_I, ← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

/-- The existing contact form is literally its physical kinetic and collision pairings.
This supplies the interface to ContactOperator without changing its owned module. -/
theorem q_eq_physical_pairings (c : ℝ) (φ ψ : PhysH1 L N) :
    ContactForm.q c φ ψ = (∑ i, ⟪gradientCLM i φ, gradientCLM i ψ⟫_ℂ) +
      ((2 * c : ℝ) : ℂ) * ∑ p : ContactForm.Pair N,
        ⟪productTrace p.1.1 p.1.2 (ne_of_lt p.2) φ,
          productTrace p.1.1 p.1.2 (ne_of_lt p.2) ψ⟫_ℂ := by
  simp only [gradientCLM_inner, productTrace_inner]
  rfl

end ContactPairings

end QuantumNLS.CollisionIdentification

#print axioms QuantumNLS.CollisionIdentification.seqCongr
#print axioms QuantumNLS.CollisionIdentification.lpCongr
#print axioms QuantumNLS.CollisionIdentification.lpCongr_symm_apply
#print axioms QuantumNLS.CollisionIdentification.PiL2
#print axioms QuantumNLS.CollisionIdentification.piFourier
#print axioms QuantumNLS.CollisionIdentification.piFourier_symm_single_ae
#print axioms QuantumNLS.CollisionIdentification.DCoord
#print axioms QuantumNLS.CollisionIdentification.CollisionL2
#print axioms QuantumNLS.CollisionIdentification.diagIndex
#print axioms QuantumNLS.CollisionIdentification.collisionUnitary
#print axioms QuantumNLS.CollisionIdentification.physicalTrace
#print axioms QuantumNLS.CollisionIdentification.physicalTrace_norm
#print axioms QuantumNLS.CollisionIdentification.physicalTrace_estimate
#print axioms QuantumNLS.CollisionIdentification.physicalTrace_unique
#print axioms QuantumNLS.CollisionIdentification.splitIndex
#print axioms QuantumNLS.CollisionIdentification.card_DCoord
#print axioms QuantumNLS.CollisionIdentification.diagonal
#print axioms QuantumNLS.CollisionIdentification.continuous_diagonal
#print axioms QuantumNLS.CollisionIdentification.collapse
#print axioms QuantumNLS.CollisionIdentification.fib_eq_iff
#print axioms QuantumNLS.CollisionIdentification.traceCLM_single
#print axioms QuantumNLS.CollisionIdentification.collisionUnitary_single_ae
#print axioms QuantumNLS.CollisionIdentification.poly
#print axioms QuantumNLS.CollisionIdentification.continuous_poly
#print axioms QuantumNLS.CollisionIdentification.trigElem_sum
#print axioms QuantumNLS.CollisionIdentification.physicalTrace_single_ae
#print axioms QuantumNLS.CollisionIdentification.physicalTrace_trigElem_ae
#print axioms QuantumNLS.CollisionIdentification.unitSumPositions
#print axioms QuantumNLS.CollisionIdentification.measurePreserving_unitSumPositions
#print axioms QuantumNLS.CollisionIdentification.point_estimate
#print axioms QuantumNLS.CollisionIdentification.lp_norm_sq_of_ae
#print axioms QuantumNLS.CollisionIdentification.normalChart
#print axioms QuantumNLS.CollisionIdentification.measurePreserving_normalChart
#print axioms QuantumNLS.CollisionIdentification.assemble
#print axioms QuantumNLS.CollisionIdentification.normalChart_symm_apply
#print axioms QuantumNLS.CollisionIdentification.continuous_assemble
#print axioms QuantumNLS.CollisionIdentification.assemble_diagonal
#print axioms QuantumNLS.CollisionIdentification.integral_normalChart
#print axioms QuantumNLS.CollisionIdentification.restriction_integral_estimate
#print axioms QuantumNLS.CollisionIdentification.gradientCLM
#print axioms QuantumNLS.CollisionIdentification.gradientCLM_eq_of_weak
#print axioms QuantumNLS.CollisionIdentification.gradientCLM_trigElem
#print axioms QuantumNLS.CollisionIdentification.assemble_i
#print axioms QuantumNLS.CollisionIdentification.assemble_ne
#print axioms QuantumNLS.CollisionIdentification.poly_hasDerivAt
#print axioms QuantumNLS.CollisionIdentification.literalRestriction
#print axioms QuantumNLS.CollisionIdentification.literalRestriction_ae
#print axioms QuantumNLS.CollisionIdentification.physicalTrace_eq_literalRestriction
#print axioms QuantumNLS.CollisionIdentification.latticePeriodic_pderiv
#print axioms QuantumNLS.CollisionIdentification.liftK_hasDerivAt
#print axioms QuantumNLS.CollisionIdentification.momUnitary_eq_pairK
#print axioms QuantumNLS.CollisionIdentification.pairK_congr_ae
#print axioms QuantumNLS.CollisionIdentification.smooth_hasWeakPartial
#print axioms QuantumNLS.CollisionIdentification.smooth_mem_range
#print axioms QuantumNLS.CollisionIdentification.smoothH1
#print axioms QuantumNLS.CollisionIdentification.smoothH1_val
#print axioms QuantumNLS.CollisionIdentification.physicalTrace_smooth
#print axioms QuantumNLS.CollisionIdentification.physicalTrace_trig_estimate_realspace
#print axioms QuantumNLS.CollisionIdentification.physicalTrace_estimate_realspace
#print axioms QuantumNLS.CollisionIdentification.dyij
#print axioms QuantumNLS.CollisionIdentification.CollisionProductL2
#print axioms QuantumNLS.CollisionIdentification.collisionProductUnitary
#print axioms QuantumNLS.CollisionIdentification.productTrace
#print axioms QuantumNLS.CollisionIdentification.productTrace_norm
#print axioms QuantumNLS.CollisionIdentification.productTrace_estimate
#print axioms QuantumNLS.CollisionIdentification.productTrace_estimate_realspace
#print axioms QuantumNLS.CollisionIdentification.productTrace_smooth
#print axioms QuantumNLS.CollisionIdentification.productTrace_unique
#print axioms QuantumNLS.CollisionIdentification.productTrace_inner
#print axioms QuantumNLS.CollisionIdentification.exists_physical_collision_trace
#print axioms QuantumNLS.CollisionIdentification.gradientCLM_inner
#print axioms QuantumNLS.CollisionIdentification.q_eq_physical_pairings
