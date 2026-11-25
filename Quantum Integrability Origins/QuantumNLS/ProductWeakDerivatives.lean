/-
QuantumNLS.ProductWeakDerivatives — weak partial derivatives on the product torus `𝕋_L^k` and
their Fourier identification (owner: opus_tensor).

Source: DEF-005 (definitions.tex:31) kinetic part `Σⱼ ‖∂ⱼψ‖²` on `H¹(𝕋_L^N)`; DEF-031 (:187)
`A_k = 1 − Σ_{j≤k} ∂²_{x_j}`; DEF-001/002 normalization (mass-`L` per coordinate,
`E_w = ∏ⱼ e_{wⱼ}`, `F̂(w) = ⟨E_w, F⟩`).

Definitions (no equivalence assumed):
* test functions: `φ : ℝ^k → ℂ`, `ContDiff ℝ ∞`, invariant under the period lattice `Lℤ^k`
  (`LatticePeriodic`, i.e. periodic in each coordinate);
* `pderiv j φ x = d/dt φ(x with xⱼ := t)` at `t = xⱼ` (the classical partial derivative `∂_{x_j}φ`);
* `liftK φ : 𝕋_L^k → ℂ`, the lattice-periodic function read on the torus through the
  representatives `[0, L)` (`AddCircle.equivIco`);
* `HasWeakPartial j F G` (F, G ∈ `L²(𝕋_L^k)`): `∫ F · ∂ⱼφ = −∫ G · φ` for every test `φ`.

Frozen imports, read-only: PhysicalEnergy 01370715 (`momUnitary`, `prodMode`, `PhysH1`,
`kinWeight`); WeakDerivatives WD1 030e4611 (1D characters `chi`, `ikn`, `conj_mode_coe`,
integration by parts).  No CollisionTrace or BetheWeakGradient edits; no S2 work.

Results (all proved, standard axioms only):
* (A) `momUnitary_of_hasWeakPartial`: `HasWeakPartial j F G → Ĝ(w) = (2πi wⱼ/L) F̂(w)`;
  `hasWeakPartial_unique`.
* (B) `hasWeakPartial_of_momUnitary` (k-dim Parseval `integral_mul_eq_tsumK`, Fubini along
  coordinate `j` `pairK_liftK_eq`, slice integration by parts `pairK_pderiv`);
  `hasWeakPartial_iff`.
* (C) `exists_hasWeakPartial_iff`, `mem_range_physH1_iff` (`F ∈ range PhysH1.val ↔ ∀ j, ∃ ∂ⱼF ∈ L²`),
  `kinetic_norm_identity` (`Σ_w a_k(w)|F̂(w)|² = ‖F‖² + Σⱼ‖∂ⱼF‖²`), `PhysH1.norm_sq_eq_weak`.
* `latticePeriodic_iff`: lattice invariance ↔ periodicity in each coordinate.
-/
import QuantumNLS.PhysicalEnergy
import QuantumNLS.WeakDerivatives

open scoped InnerProductSpace ENNReal ComplexConjugate ContDiff
open MeasureTheory QuantumNLS.Fourier QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy
  QuantumNLS.Energy QuantumNLS.WeakDerivatives

noncomputable section

namespace QuantumNLS.ProductWeakDerivatives

variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

/-! ## Test functions, partial derivatives, lifts -/

/-- Invariance under the period lattice `Lℤ^k` (periodic in each coordinate). -/
def LatticePeriodic (L : ℝ) (φ : (Fin k → ℝ) → ℂ) : Prop :=
  ∀ (x : Fin k → ℝ) (m : Fin k → ℤ), φ (fun i => x i + m i * L) = φ x

/-- Smooth lattice-periodic test functions on `ℝ^k`. -/
structure IsTorusTest (L : ℝ) (φ : (Fin k → ℝ) → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  periodic : LatticePeriodic L φ

/-- The partial derivative `∂_{x_j} φ`. -/
def pderiv (j : Fin k) (φ : (Fin k → ℝ) → ℂ) (x : Fin k → ℝ) : ℂ :=
  deriv (fun t : ℝ => φ (Function.update x j t)) (x j)

/-- The representative in `[0, L)` of a point of `𝕋_L`. -/
def rep (y : AddCircle L) : ℝ := (AddCircle.equivIco L 0 y : ℝ)

theorem coe_rep (y : AddCircle L) : ((rep y : ℝ) : AddCircle L) = y := AddCircle.coe_equivIco

theorem rep_coe (x : ℝ) : ∃ m : ℤ, rep (x : AddCircle L) = x + m * L := by
  have h := coe_rep (L := L) (x : AddCircle L)
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp h)
  refine ⟨-m, ?_⟩
  rw [zsmul_eq_mul] at hm
  push_cast
  linarith

/-- A lattice-periodic function read on the torus. -/
def liftK (φ : (Fin k → ℝ) → ℂ) (y : Fin k → AddCircle L) : ℂ := φ (fun i => rep (y i))

theorem liftK_coe {φ : (Fin k → ℝ) → ℂ} (hφ : LatticePeriodic L φ) (x : Fin k → ℝ) :
    liftK φ (fun i => (x i : AddCircle L)) = φ x := by
  choose m hm using fun i => rep_coe (L := L) (x i)
  unfold liftK
  simp_rw [hm]
  exact hφ x m

/-- **Weak partial derivative on `𝕋_L^k`.** -/
def HasWeakPartial (j : Fin k) (F G : L2TN L k) : Prop :=
  ∀ φ : (Fin k → ℝ) → ℂ, IsTorusTest L φ →
    ∫ y, (F : (Fin k → AddCircle L) → ℂ) y * liftK (L := L) (pderiv j φ) y ∂(torusPiMeasure L k) =
      -∫ y, (G : (Fin k → AddCircle L) → ℂ) y * liftK (L := L) φ y ∂(torusPiMeasure L k)

/-! ## Product characters -/

/-- `χ_w(x) = ∏ᵢ e^{−2πi wᵢ xᵢ/L}`. -/
def chiK (L : ℝ) (w : Mom k) (x : Fin k → ℝ) : ℂ := ∏ i, chi L (w i) (x i)

theorem chiK_isTest (w : Mom k) : IsTorusTest L (chiK L w) where
  smooth := contDiff_prod fun i _ => (chi_isTest (L := L) (w i)).smooth.comp (contDiff_apply ℝ ℝ i)
  periodic := by
    intro x m
    unfold chiK
    refine Finset.prod_congr rfl fun i _ => ?_
    exact ((chi_isTest (L := L) (w i)).periodic.int_mul (m i)) (x i)

omit [Fact (0 < L)] in
theorem chiK_update (w : Mom k) (x : Fin k → ℝ) (j : Fin k) (t : ℝ) :
    chiK L w (Function.update x j t) =
      chi L (w j) t * ∏ i ∈ Finset.univ.erase j, chi L (w i) (x i) := by
  unfold chiK
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

omit [Fact (0 < L)] in
theorem pderiv_chiK (w : Mom k) (j : Fin k) (x : Fin k → ℝ) :
    pderiv j (chiK L w) x = -(ikn L (w j)) * chiK L w x := by
  unfold pderiv
  have e : (fun t : ℝ => chiK L w (Function.update x j t)) =
      fun t => chi L (w j) t * ∏ i ∈ Finset.univ.erase j, chi L (w i) (x i) :=
    funext fun t => chiK_update w x j t
  rw [e, ((hasDerivAt_chi (w j) (x j)).mul_const _).deriv]
  have hx : chiK L w x = chi L (w j) (x j) * ∏ i ∈ Finset.univ.erase j, chi L (w i) (x i) := by
    conv_lhs => rw [← Function.update_eq_self j x]
    exact chiK_update w x j (x j)
  rw [hx]; ring

theorem coeFn_prodMode (w : Mom k) :
    (prodMode L k w : (Fin k → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L k]
      fun y => ∏ i, mode L (w i) (y i) := by
  have h1 := (memLp_prodFun (fun j => modeLp L (w j))).coeFn_toLp
  have h2 : ∀ᵐ y ∂(torusPiMeasure L k), ∀ i,
      (modeLp L (w i) : AddCircle L → ℂ) (y i) = mode L (w i) (y i) := by
    rw [ae_all_iff]
    intro i
    exact (Measure.quasiMeasurePreserving_eval (fun _ => (volume : Measure (AddCircle L))) i).ae
      (coeFn_modeLp L (w i))
  filter_upwards [h1, h2] with y hy1 hy2
  rw [prodMode, prodLp, hy1, prodFun]
  exact Finset.prod_congr rfl fun i _ => hy2 i

/-- `F̂(w) = L^{-k/2} ∫_{𝕋_L^k} χ_w F`. -/
theorem momUnitary_eq_integral (F : L2TN L k) (w : Mom k) :
    (momUnitary L k F : Mom k → ℂ) w = ((((Real.sqrt L)⁻¹ : ℝ) : ℂ)) ^ k *
      ∫ y, liftK (L := L) (chiK L w) y * (F : (Fin k → AddCircle L) → ℂ) y
        ∂(torusPiMeasure L k) := by
  rw [momUnitary_apply_eq_inner, MeasureTheory.L2.inner_def, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_prodMode (L := L) w] with y hy
  rw [RCLike.inner_apply', hy, map_prod]
  have : ∀ i, conj (mode L (w i) (y i)) = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * chi L (w i) (rep (y i)) := by
    intro i
    conv_lhs => rw [← coe_rep (y i)]
    exact conj_mode_coe (w i) (rep (y i))
  simp_rw [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold liftK chiK
  ring

/-! ## (A) Weak partial derivative ⇒ product Fourier multiplier -/

/-- **(A)** `HasWeakPartial j F G ⇒ Ĝ(w) = (2πi wⱼ/L) F̂(w)` for all `w ∈ ℤ^k`. -/
theorem momUnitary_of_hasWeakPartial {j : Fin k} {F G : L2TN L k} (h : HasWeakPartial j F G)
    (w : Mom k) :
    (momUnitary L k G : Mom k → ℂ) w = ikn L (w j) * (momUnitary L k F : Mom k → ℂ) w := by
  have hw := h (chiK L w) (chiK_isTest w)
  have hl : (liftK (L := L) (pderiv j (chiK L w))) =
      fun y => -(ikn L (w j)) * liftK (L := L) (chiK L w) y := by
    funext y; unfold liftK; rw [pderiv_chiK]
  rw [hl] at hw
  have e1 : ∫ y, (F : (Fin k → AddCircle L) → ℂ) y * (-(ikn L (w j)) * liftK (L := L) (chiK L w) y)
      ∂(torusPiMeasure L k) = -(ikn L (w j)) *
      ∫ y, liftK (L := L) (chiK L w) y * (F : (Fin k → AddCircle L) → ℂ) y ∂(torusPiMeasure L k) := by
    rw [← integral_const_mul]; congr 1; funext y; ring
  have e2 : ∫ y, (G : (Fin k → AddCircle L) → ℂ) y * liftK (L := L) (chiK L w) y
      ∂(torusPiMeasure L k) =
      ∫ y, liftK (L := L) (chiK L w) y * (G : (Fin k → AddCircle L) → ℂ) y ∂(torusPiMeasure L k) := by
    congr 1; funext y; ring
  rw [e1, e2] at hw
  rw [momUnitary_eq_integral, momUnitary_eq_integral]
  have hg : ∫ y, liftK (L := L) (chiK L w) y * (G : (Fin k → AddCircle L) → ℂ) y
      ∂(torusPiMeasure L k) = ikn L (w j) *
      ∫ y, liftK (L := L) (chiK L w) y * (F : (Fin k → AddCircle L) → ℂ) y ∂(torusPiMeasure L k) := by
    linear_combination hw
  rw [hg]; ring

/-- Weak partial derivatives are unique. -/
theorem hasWeakPartial_unique {j : Fin k} {F G₁ G₂ : L2TN L k} (h₁ : HasWeakPartial j F G₁)
    (h₂ : HasWeakPartial j F G₂) : G₁ = G₂ := by
  apply (momUnitary L k).injective
  ext w
  rw [momUnitary_of_hasWeakPartial h₁, momUnitary_of_hasWeakPartial h₂]

/-! ## Lifts: measurability, boundedness, `L²` -/

theorem measurable_rep : Measurable (rep (L := L)) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco L 0).measurable

theorem rep_mem (y : AddCircle L) : rep y ∈ Set.Icc 0 L := by
  have h : rep y ∈ Set.Ico (0 : ℝ) (0 + L) := (AddCircle.equivIco L 0 y).2
  rw [zero_add] at h
  exact Set.Ico_subset_Icc_self h

theorem measurable_liftK {Φ : (Fin k → ℝ) → ℂ} (hΦ : Measurable Φ) :
    Measurable (liftK (L := L) Φ) :=
  hΦ.comp (measurable_pi_iff.mpr fun i => measurable_rep.comp (measurable_pi_apply i))

theorem exists_bound_liftK {Φ : (Fin k → ℝ) → ℂ} (hΦ : Continuous Φ) :
    ∃ C, ∀ y, ‖liftK (L := L) Φ y‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Fin k → ℝ)) (b := fun _ => L)).exists_bound_of_continuousOn
    hΦ.continuousOn
  exact ⟨C, fun y => hC _ ⟨fun i => (rep_mem (y i)).1, fun i => (rep_mem (y i)).2⟩⟩

theorem memLp_liftK {Φ : (Fin k → ℝ) → ℂ} (hΦ : Continuous Φ) :
    MemLp (liftK (L := L) Φ) 2 (torusPiMeasure L k) := by
  obtain ⟨C, hC⟩ := exists_bound_liftK (L := L) hΦ
  exact MemLp.of_bound (measurable_liftK hΦ.measurable).aestronglyMeasurable C (ae_of_all _ hC)

omit [Fact (0 < L)] in
theorem continuous_prodModeFun (w : Mom k) :
    Continuous fun y : Fin k → AddCircle L => ∏ i, mode L (w i) (y i) :=
  continuous_finsetProd _ fun i _ => (continuous_mode (L := L) (w i)).comp (continuous_apply i)

theorem integrable_mode_mul_liftK (w : Mom k) {Φ : (Fin k → ℝ) → ℂ} (hΦ : Continuous Φ) :
    Integrable (fun y => (∏ i, mode L (w i) (y i)) * liftK (L := L) Φ y) (torusPiMeasure L k) := by
  obtain ⟨C, hC⟩ := exists_bound_liftK (L := L) hΦ
  obtain ⟨C1, hC1⟩ := (isCompact_univ (X := Fin k → AddCircle L)).exists_bound_of_continuousOn
    (continuous_prodModeFun (L := L) w).continuousOn
  refine Integrable.of_bound (((continuous_prodModeFun w).measurable.mul
    (measurable_liftK hΦ.measurable)).aestronglyMeasurable) (C1 * C) (ae_of_all _ fun y => ?_)
  rw [norm_mul]
  exact mul_le_mul (hC1 y (Set.mem_univ _)) (hC y) (norm_nonneg _)
    ((norm_nonneg _).trans (hC1 y (Set.mem_univ _)))

/-! ## Parseval pairing on `𝕋_L^k` -/

/-- `D_w(ψ) = ∫ E_w ψ` (unconjugated pairing with the product mode). -/
def pairK (ψ : (Fin k → AddCircle L) → ℂ) (w : Mom k) : ℂ :=
  ∫ y, (∏ i, mode L (w i) (y i)) * ψ y ∂(torusPiMeasure L k)

/-- **Parseval pairing.** `∫ F ψ = Σ_w D_w(ψ) F̂(w)` for `F, ψ ∈ L²(𝕋_L^k)`. -/
theorem integral_mul_eq_tsumK (F : L2TN L k) {ψ : (Fin k → AddCircle L) → ℂ}
    (hψ : MemLp ψ 2 (torusPiMeasure L k)) :
    ∫ y, (F : (Fin k → AddCircle L) → ℂ) y * ψ y ∂(torusPiMeasure L k) =
      ∑' w, pairK ψ w * (momUnitary L k F : Mom k → ℂ) w := by
  let Ψ : L2TN L k := hψ.star.toLp _
  have hΨ : (Ψ : (Fin k → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L k] star ψ := hψ.star.coeFn_toLp
  have h1 : ⟪Ψ, F⟫_ℂ = ∫ y, (F : (Fin k → AddCircle L) → ℂ) y * ψ y ∂(torusPiMeasure L k) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hΨ] with y hy
    rw [RCLike.inner_apply', hy]
    simp [mul_comm]
  have h2 : ⟪Ψ, F⟫_ℂ = ∑' w, pairK ψ w * (momUnitary L k F : Mom k → ℂ) w := by
    rw [← (momUnitary L k).inner_map_map, lp.inner_eq_tsum]
    congr 1; funext w
    rw [RCLike.inner_apply', momUnitary_apply_eq_inner (F := Ψ)]
    congr 1
    rw [MeasureTheory.L2.inner_def, ← integral_conj]
    unfold pairK
    refine integral_congr_ae ?_
    filter_upwards [hΨ, coeFn_prodMode (L := L) w] with y hy1 hy2
    rw [RCLike.inner_apply', hy1, hy2]
    simp [map_prod]
  rw [← h1, h2]

/-! ## Integration by parts along one coordinate -/

theorem pderiv_insertNth {n : ℕ} (j : Fin (n + 1)) (φ : (Fin (n + 1) → ℝ) → ℂ) (s : ℝ)
    (r : Fin n → ℝ) :
    pderiv j φ (Fin.insertNth j s r) = deriv (fun u => φ (Fin.insertNth j u r)) s := by
  unfold pderiv
  simp only [Fin.update_insertNth, Fin.insertNth_apply_same]

theorem pderiv_eq_fderiv {φ : (Fin k → ℝ) → ℂ} (hφ : Differentiable ℝ φ) (j : Fin k)
    (x : Fin k → ℝ) : pderiv j φ x = fderiv ℝ φ x (Pi.single j 1) := by
  unfold pderiv
  have h := (hφ (Function.update x j (x j))).hasFDerivAt.comp_hasDerivAt (x j)
    (hasDerivAt_update x j (x j))
  rw [Function.update_eq_self] at h
  exact h.deriv

omit [Fact (0 < L)] in
theorem continuous_pderiv {φ : (Fin k → ℝ) → ℂ} (hφ : IsTorusTest L φ) (j : Fin k) :
    Continuous (pderiv j φ) := by
  have h1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have e : pderiv j φ = fun x => fderiv ℝ φ x (Pi.single j 1) :=
    funext (pderiv_eq_fderiv (h1.differentiable one_ne_zero) j)
  rw [e]
  exact (h1.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem integral_mode_rep {g : ℝ → ℂ} (hg : Function.Periodic g L) (m : ℤ) :
    ∫ t, mode L m t * g (rep t) ∂(volume : Measure (AddCircle L)) =
      ∫ s in (0 : ℝ)..L, emode L m s * g s := by
  rw [← AddCircle.intervalIntegral_preimage L 0, zero_add]
  congr 1; funext s
  obtain ⟨q, hq⟩ := rep_coe (L := L) s
  rw [hq, (hg.int_mul q) s]
  rfl

theorem integral_mode_rep_deriv {ψ : ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ) (hp : Function.Periodic ψ L)
    (m : ℤ) :
    ∫ t, mode L m t * deriv ψ (rep t) ∂(volume : Measure (AddCircle L)) =
      -(ikn L m) * ∫ t, mode L m t * ψ (rep t) ∂(volume : Measure (AddCircle L)) := by
  rw [integral_mode_rep (periodic_deriv hp), integral_mode_rep hp, integral_emode_mul_deriv hψ hp]

theorem rep_insertNth {n : ℕ} (j : Fin (n + 1)) (t : AddCircle L) (z : Fin n → AddCircle L) :
    (fun i => rep (Fin.insertNth (α := fun _ => AddCircle L) j t z i)) = Fin.insertNth j (rep t) fun i => rep (z i) := by
  funext i
  refine Fin.succAboveCases j ?_ (fun i => ?_) i <;> simp

omit [Fact (0 < L)] in
theorem slice_isTest {n : ℕ} (j : Fin (n + 1)) {φ : (Fin (n + 1) → ℝ) → ℂ}
    (hφ : IsTorusTest L φ) (r : Fin n → ℝ) :
    ContDiff ℝ 1 (fun s => φ (Fin.insertNth j s r)) ∧
      Function.Periodic (fun s => φ (Fin.insertNth j s r)) L := by
  refine ⟨?_, ?_⟩
  · have e : (fun s => φ (Fin.insertNth j s r)) = φ ∘ Function.update (Fin.insertNth j 0 r) j := by
      funext s; simp [Fin.update_insertNth]
    rw [e]
    exact (hφ.smooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))).comp
      (contDiff_update _ _ _)
  · intro s
    simp only
    rw [← hφ.periodic (Fin.insertNth j s r) (Pi.single j 1)]
    congr 1
    funext i
    refine Fin.succAboveCases j ?_ (fun i => ?_) i <;> simp

theorem pairK_liftK_eq {n : ℕ} (j : Fin (n + 1)) (w : Mom (n + 1))
    {Φ : (Fin (n + 1) → ℝ) → ℂ} (hΦ : Continuous Φ) :
    pairK (liftK (L := L) Φ) w =
      ∫ z, (∏ i, mode L (w (j.succAbove i)) (z i)) *
        ∫ t, mode L (w j) t * Φ (Fin.insertNth j (rep t) fun i => rep (z i))
          ∂(volume : Measure (AddCircle L))
        ∂(Measure.pi fun _ : Fin n => (volume : Measure (AddCircle L))) := by
  have hmp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => (volume : Measure (AddCircle L))) j).symm
  set g : (Fin (n + 1) → AddCircle L) → ℂ :=
    fun y => (∏ i, mode L (w i) (y i)) * liftK (L := L) Φ y with hg
  have hint : Integrable (fun p => g ((MeasurableEquiv.piFinSuccAbove (fun _ => AddCircle L) j).symm p))
      ((volume : Measure (AddCircle L)).prod
        (Measure.pi fun _ : Fin n => (volume : Measure (AddCircle L)))) :=
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr
      (integrable_mode_mul_liftK w hΦ)
  unfold pairK
  rw [← hmp.integral_comp' g, integral_prod_symm _ hint]
  congr 1; funext z
  rw [← integral_const_mul]
  congr 1; funext t
  simp only [hg, MeasurableEquiv.piFinSuccAbove_symm_apply, liftK, Fin.insertNthEquiv_apply]
  rw [rep_insertNth, Fin.prod_univ_succAbove _ j]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  ring

/-- **Integration by parts on `𝕋_L^k`:** `D_w(∂ⱼφ) = −(2πi wⱼ/L) D_w(φ)`. -/
theorem pairK_pderiv {n : ℕ} (j : Fin (n + 1)) {φ : (Fin (n + 1) → ℝ) → ℂ}
    (hφ : IsTorusTest L φ) (w : Mom (n + 1)) :
    pairK (liftK (L := L) (pderiv j φ)) w = -(ikn L (w j)) * pairK (liftK (L := L) φ) w := by
  rw [pairK_liftK_eq j w (continuous_pderiv hφ j), pairK_liftK_eq j w hφ.smooth.continuous,
    ← integral_const_mul]
  congr 1; funext z
  simp_rw [pderiv_insertNth]
  obtain ⟨h1, hp⟩ := slice_isTest j hφ fun i => rep (z i)
  rw [integral_mode_rep_deriv h1 hp]
  ring

/-! ## (B) Product Fourier multiplier ⇒ weak partial derivative -/

/-- **(B)** If `Ĝ(w) = (2πi wⱼ/L) F̂(w)` for all `w`, then `G` is the weak `∂ⱼ` of `F`. -/
theorem hasWeakPartial_of_momUnitary {j : Fin k} {F G : L2TN L k}
    (h : ∀ w, (momUnitary L k G : Mom k → ℂ) w = ikn L (w j) * (momUnitary L k F : Mom k → ℂ) w) :
    HasWeakPartial j F G := by
  intro φ hφ
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := j.pos; omega⟩
  rw [integral_mul_eq_tsumK F (memLp_liftK (continuous_pderiv hφ j)),
    integral_mul_eq_tsumK G (memLp_liftK hφ.smooth.continuous), ← tsum_neg]
  congr 1; funext w
  rw [pairK_pderiv j hφ w, h w]
  ring

/-- **Identification.** `G` is the weak `∂ⱼ` of `F` iff `Ĝ(w) = (2πi wⱼ/L) F̂(w)` for all
`w ∈ ℤ^k`. -/
theorem hasWeakPartial_iff (j : Fin k) (F G : L2TN L k) :
    HasWeakPartial j F G ↔
      ∀ w, (momUnitary L k G : Mom k → ℂ) w = ikn L (w j) * (momUnitary L k F : Mom k → ℂ) w :=
  ⟨momUnitary_of_hasWeakPartial, hasWeakPartial_of_momUnitary⟩

/-! ## (C) `H¹(𝕋_L^k)` = all weak partials in `L²`; kinetic norm identity -/

/-- `‖∂ⱼF‖² = Σ_w (2πwⱼ/L)² |F̂(w)|²`. -/
theorem norm_sq_of_hasWeakPartial {j : Fin k} {F G : L2TN L k} (h : HasWeakPartial j F G) :
    ‖G‖ ^ 2 = ∑' w, freq L (w j) ^ 2 * ‖(momUnitary L k F : Mom k → ℂ) w‖ ^ 2 := by
  rw [← (momUnitary L k).norm_map, QuantumNLS.Energy.norm_sq_eq_tsum]
  congr 1; funext w
  rw [momUnitary_of_hasWeakPartial h w, norm_ikn_mul_sq]

/-- `F` has an `L²` weak `∂ⱼ` iff `Σ_w (2πwⱼ/L)² |F̂(w)|² < ∞`. -/
theorem exists_hasWeakPartial_iff (j : Fin k) (F : L2TN L k) :
    (∃ G, HasWeakPartial j F G) ↔
      Summable fun w => freq L (w j) ^ 2 * ‖(momUnitary L k F : Mom k → ℂ) w‖ ^ 2 := by
  constructor
  · rintro ⟨G, hG⟩
    refine (summable_sq (momUnitary L k G)).congr fun w => ?_
    rw [momUnitary_of_hasWeakPartial hG w, norm_ikn_mul_sq]
  · intro hs
    have hm : Memℓp (fun w : Mom k => ikn L (w j) * (momUnitary L k F : Mom k → ℂ) w) 2 :=
      memL2_iff.2 (hs.congr fun w => (norm_ikn_mul_sq _ _).symm)
    refine ⟨(momUnitary L k).symm ⟨_, hm⟩, hasWeakPartial_of_momUnitary fun w => ?_⟩
    rw [LinearIsometryEquiv.apply_symm_apply]

/-- **`H¹(𝕋_L^k)` identification.**  `F ∈ L²(𝕋_L^k)` lies in the frozen energy space
(`PhysH1`, defined spectrally through `momUnitary` and `kinWeight`) iff every coordinate weak
partial derivative `∂ⱼF` exists in `L²`. -/
theorem mem_range_physH1_iff (F : L2TN L k) :
    F ∈ Set.range (PhysH1.val : PhysH1 L k → L2TN L k) ↔ ∀ j, ∃ G, HasWeakPartial j F G := by
  rw [PhysH1.range_val, Set.mem_ofPred_eq]
  simp_rw [exists_hasWeakPartial_iff]
  constructor
  · intro hs j
    refine Summable.of_nonneg_of_le (fun w => by positivity) (fun w => ?_) hs
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    unfold kinWeight
    have : freq L (w j) ^ 2 ≤ ∑ i, freq L (w i) ^ 2 :=
      Finset.single_le_sum (f := fun i => freq L (w i) ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ j)
    linarith
  · intro hs
    have h := (summable_sq (momUnitary L k F)).add
      (summable_sum (s := Finset.univ) fun j _ => hs j)
    refine h.congr fun w => ?_
    unfold kinWeight
    rw [add_mul, one_mul, Finset.sum_mul]

/-- **Kinetic norm identity.**  If `Gⱼ` is the weak `∂ⱼF` for every `j`, then
`Σ_w a_k(w)|F̂(w)|² = ‖F‖² + Σⱼ ‖Gⱼ‖²`, `a_k(w) = 1 + Σⱼ (2πwⱼ/L)²`. -/
theorem kinetic_norm_identity (F : L2TN L k) (G : Fin k → L2TN L k)
    (hG : ∀ j, HasWeakPartial j F (G j)) :
    ∑' w, kinWeight L k w * ‖(momUnitary L k F : Mom k → ℂ) w‖ ^ 2 =
      ‖F‖ ^ 2 + ∑ j, ‖G j‖ ^ 2 := by
  have hs : ∀ j, Summable fun w => freq L (w j) ^ 2 * ‖(momUnitary L k F : Mom k → ℂ) w‖ ^ 2 :=
    fun j => (exists_hasWeakPartial_iff j F).1 ⟨G j, hG j⟩
  simp_rw [norm_sq_of_hasWeakPartial (hG _)]
  rw [← (momUnitary L k).norm_map, QuantumNLS.Energy.norm_sq_eq_tsum,
    ← Summable.tsum_finsetSum (fun j _ => hs j),
    ← Summable.tsum_add (summable_sq _) (summable_sum fun j _ => hs j)]
  congr 1; funext w
  unfold kinWeight
  rw [add_mul, one_mul, Finset.sum_mul]

/-- Every element of the energy space has all `L²` weak partial derivatives. -/
theorem PhysH1.exists_hasWeakPartial (x : PhysH1 L k) (j : Fin k) :
    ∃ G, HasWeakPartial j x.val G :=
  (mem_range_physH1_iff x.val).1 ⟨x, rfl⟩ j

/-- **Energy norm via weak partials:** `‖x‖²_{H¹} = ‖x‖²_{L²} + Σⱼ ‖∂ⱼx‖²_{L²}`. -/
theorem PhysH1.norm_sq_eq_weak (x : PhysH1 L k) (G : Fin k → L2TN L k)
    (hG : ∀ j, HasWeakPartial j x.val (G j)) :
    ‖x‖ ^ 2 = ‖x.val‖ ^ 2 + ∑ j, ‖G j‖ ^ 2 := by
  rw [PhysH1.norm_sq_eq, kinetic_norm_identity x.val G hG]

/-! ## Per-coordinate periodicity -/

omit [Fact (0 < L)] in
/-- Lattice invariance is periodicity in each coordinate separately. -/
theorem latticePeriodic_iff {φ : (Fin k → ℝ) → ℂ} :
    LatticePeriodic L φ ↔
      ∀ (j : Fin k) (x : Fin k → ℝ), φ (Function.update x j (x j + L)) = φ x := by
  classical
  constructor
  · intro h j x
    rw [← h x (Pi.single j 1)]
    congr 1; funext i
    by_cases hi : i = j
    · subst hi; simp
    · simp [Function.update_of_ne hi, Pi.single_eq_of_ne hi]
  · intro h x m
    have h1 : ∀ j x, Function.Periodic (fun t => φ (Function.update x j t)) L := by
      intro j x t
      simpa [Function.update_idem] using h j (Function.update x j t)
    have hq : ∀ j (q : ℤ) (x : Fin k → ℝ), φ (Function.update x j (x j + q * L)) = φ x := by
      intro j q x
      simpa [Function.update_eq_self] using (h1 j x).int_mul q (x j)
    have key : ∀ s : Finset (Fin k),
        φ (fun i => if i ∈ s then x i + m i * L else x i) = φ x := by
      intro s
      refine Finset.induction_on s (by simp) ?_
      intro a s ha ih
      rw [← ih, ← hq a (m a) (fun i => if i ∈ s then x i + m i * L else x i)]
      congr 1; funext i
      by_cases hi : i = a
      · subst hi; simp [ha]
      · simp [hi]
    simpa using key Finset.univ

end QuantumNLS.ProductWeakDerivatives

#print axioms QuantumNLS.ProductWeakDerivatives.momUnitary_eq_integral
#print axioms QuantumNLS.ProductWeakDerivatives.momUnitary_of_hasWeakPartial
#print axioms QuantumNLS.ProductWeakDerivatives.hasWeakPartial_unique
#print axioms QuantumNLS.ProductWeakDerivatives.hasWeakPartial_iff
#print axioms QuantumNLS.ProductWeakDerivatives.mem_range_physH1_iff
#print axioms QuantumNLS.ProductWeakDerivatives.kinetic_norm_identity
#print axioms QuantumNLS.ProductWeakDerivatives.PhysH1.norm_sq_eq_weak
#print axioms QuantumNLS.ProductWeakDerivatives.latticePeriodic_iff
