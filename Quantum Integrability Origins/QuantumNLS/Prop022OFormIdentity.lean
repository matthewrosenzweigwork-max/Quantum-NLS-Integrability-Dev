import QuantumNLS.Prop022OWeakIdentity

/-! PROP-022 takeover, stage O5. The commutator form identity on the whole
common smooth domain:
  <Q z, phi(g) w> - <phi(g) z, Q w> = i <z, phi(Lambda g) w>
for all smooth z, w and every square-summable g. It is obtained from the
proved ket identity by finite occupation truncations, using only the
field's first-moment bound and the symmetry of Q. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
namespace QuantumNLS.Prop022OFormIdentity
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments
open Occupation Prop022OQuadraticKet Prop022OWeakIdentity
open Ext006BogoliubovAlg Ext006SmoothOperatorsR34a Ext006StrongFieldR41a Ext006FieldBoundsR42a
open Ext006IdentityCyclicR35a Ext006PhysFockCoord Ext006ModeDomainR33a
variable {L : ℝ} [Fact (0 < L)]

local notation "OF" => Ext006VacuumRecurrence.Fock

/-- Smooth occupation vectors lie in every physical moment domain. -/
lemma smooth_mem (w : D) (j : ℕ) : (Phi (L := L)).symm w.1 ∈ momentDomain (L := L) j := by
  have hc : Ext006PhysicalVacuum.coefficient ((Phi (L := L)).symm w.1) = w.1 := by
    funext m
    rw [← Phi_apply, LinearIsometryEquiv.apply_symm_apply]
  have hs : Smooth (Ext006PhysicalVacuum.coefficient ((Phi (L := L)).symm w.1)) := by
    rw [hc]; exact w.2
  exact (Prop022SmoothDomainR126.smooth_iff_moments _).mp hs j

/-- Symmetry of Q on the smooth domain, occupation coordinates. -/
lemma Qo_symm (a : HN L 1 →L[ℂ] HN L 1) (ha : a.adjoint = a) (b : HN L 2) (x y : D) :
    ⟪Qo (L := L) a b x.1, y.1⟫_ℂ = ⟪x.1, Qo (L := L) a b y.1⟫_ℂ := by
  rw [Qo, Qo, inner_Phi_left, inner_Phi_right,
    Qp_symm a ha b _ _ (smooth_mem (L := L) x 2) (smooth_mem (L := L) y 2)]

/-- The number-weighted mass. -/
def T (v : OF) : ℝ := ∑' m, (total m : ℝ) * ‖v m‖^2

lemma T_nonneg (v : OF) : 0 ≤ T v := tsum_nonneg (fun _ => by positivity)

/-- First-moment field bound. -/
lemma field_bound (h : H) (v : D) :
    ‖(field h v).1‖ ≤ 2 * ‖h‖ * Real.sqrt (T v.1 + ‖v.1‖^2) := by
  have hA : ‖(A h v).1‖^2 ≤ ‖h‖^2 * T v.1 := A_norm_sq_le_mass h v
  have hC := C_norm_sq h v
  have hT := T_nonneg v.1
  have hS : 0 ≤ T v.1 + ‖v.1‖^2 := by positivity
  have hA' : ‖(A h v).1‖ ≤ ‖h‖ * Real.sqrt (T v.1 + ‖v.1‖^2) := by
    rw [← Real.sqrt_sq (norm_nonneg (A h v).1), ← Real.sqrt_sq (norm_nonneg h),
      ← Real.sqrt_mul (sq_nonneg _)]
    apply Real.sqrt_le_sqrt
    change ‖(A h v).1‖^2 ≤ ‖h‖^2 * (T v.1 + ‖v.1‖^2)
    nlinarith [sq_nonneg ‖h‖, sq_nonneg ‖v.1‖]
  have hC' : ‖(C h v).1‖ ≤ ‖h‖ * Real.sqrt (T v.1 + ‖v.1‖^2) := by
    rw [← Real.sqrt_sq (norm_nonneg (C h v).1), ← Real.sqrt_sq (norm_nonneg h),
      ← Real.sqrt_mul (sq_nonneg _)]
    apply Real.sqrt_le_sqrt
    rw [hC]
    change ‖(A h v).1‖^2 + ‖h‖^2*‖v.1‖^2 ≤ ‖h‖^2 * (T v.1 + ‖v.1‖^2)
    nlinarith [sq_nonneg ‖h‖, sq_nonneg ‖v.1‖]
  calc ‖(field h v).1‖ = ‖(A h v).1 + (C h v).1‖ := rfl
    _ ≤ ‖(A h v).1‖ + ‖(C h v).1‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-! ### Finite occupation truncations -/

/-- Truncation to a finite set of occupations. -/
def trunc (F : Finset Occ) (w : D) : D := ∑ m ∈ F, w.1 m • ketD m

lemma trunc_val (F : Finset Occ) (w : D) :
    (trunc F w).1 = ∑ m ∈ F, (lp.single 2 m (w.1 m) : OF) := by
  rw [trunc, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Submodule.coe_smul]
  change w.1 m • (lp.single 2 m (1 : ℂ) : OF) = _
  rw [← lp.single_smul, smul_eq_mul, mul_one]

lemma trunc_apply (F : Finset Occ) (w : D) (x : Occ) :
    (trunc F w).1 x = if x ∈ F then w.1 x else 0 := by
  rw [trunc_val, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq]

lemma trunc_tendsto (w : D) : Tendsto (fun F => (trunc F w).1) atTop (𝓝 w.1) := by
  have h := lp.hasSum_single (p := 2) (by norm_num) w.1
  refine (show Tendsto (fun F : Finset Occ => ∑ m ∈ F, (lp.single 2 m (w.1 m) : OF)) atTop
    (𝓝 w.1) from h).congr ?_
  intro F
  rw [trunc_val]

lemma sub_trunc_apply (F : Finset Occ) (w : D) (x : Occ) :
    (w - trunc F w).1 x = ({y | y ∉ F} : Set Occ).indicator (fun y => w.1 y) x := by
  rw [Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, trunc_apply, Set.indicator_apply]
  by_cases hx : x ∈ F
  · simp [hx]
  · simp [hx]

lemma T_sub_trunc_tendsto (w : D) : Tendsto (fun F => T (w - trunc F w).1) atTop (𝓝 0) := by
  have h := tendsto_tsum_compl_atTop_zero (fun m : Occ => (total m : ℝ) * ‖w.1 m‖^2)
  refine h.congr (fun F => ?_)
  refine Eq.trans (tsum_subtype ({y : Occ | y ∉ F})
    (fun m => (total m : ℝ) * ‖w.1 m‖^2)) ?_
  unfold T
  apply tsum_congr
  intro x
  rw [sub_trunc_apply, Set.indicator_apply, Set.indicator_apply]
  split_ifs <;> simp

lemma norm_sub_trunc_tendsto (w : D) :
    Tendsto (fun F => ‖(w - trunc F w).1‖) atTop (𝓝 0) := by
  have h := (tendsto_iff_norm_sub_tendsto_zero.mp (trunc_tendsto w))
  refine h.congr (fun F => ?_)
  rw [Submodule.coe_sub, norm_sub_rev]

lemma moment_tendsto (w : D) :
    Tendsto (fun F => Real.sqrt (T (w - trunc F w).1 + ‖(w - trunc F w).1‖^2)) atTop (𝓝 0) := by
  have h := ((T_sub_trunc_tendsto w).add ((norm_sub_trunc_tendsto w).pow 2)).sqrt
  simpa using h

lemma zero_of_bound (c : ℂ) (r : Finset Occ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (h : ∀ F, ‖c‖ ≤ r F) : c = 0 :=
  norm_le_zero_iff.mp (ge_of_tendsto' hr h)

lemma field_trunc (g : H) (F : Finset Occ) (w : D) :
    (field g (trunc F w)).1 = ∑ m ∈ F, w.1 m • (field g (ketD m)).1 := by
  rw [trunc, map_sum, Submodule.coe_sum]
  simp only [map_smul, Submodule.coe_smul]

lemma field_sub (g : H) (z w : D) : (field g (z - w)).1 = (field g z).1 - (field g w).1 := by
  rw [map_sub, Submodule.coe_sub]

/-! ### The form identity -/

theorem form_identity (a : HN L 1 →L[ℂ] HN L 1) (ha : a.adjoint = a) (b : HN L 2)
    (g : H) (z w : D) :
    ⟪Qo (L := L) a b z.1, (field g w).1⟫_ℂ - ⟪(field g z).1, Qo (L := L) a b w.1⟫_ℂ =
      Complex.I * ⟪z.1, (field (LamH (L := L) a b g) w).1⟫_ℂ := by
  -- Step 1: a ket in the first slot, arbitrary smooth vector in the second.
  have step1 : ∀ (k : Occ) (w : D),
      ⟪Qo (L := L) a b (ketD k).1, (field g w).1⟫_ℂ -
        ⟪Qo (L := L) a b (field g (ketD k)).1, w.1⟫_ℂ -
        Complex.I * ⟪(ketD k).1, (field (LamH (L := L) a b g) w).1⟫_ℂ = 0 := by
    intro k w
    let G : D → ℂ := fun v => ⟪Qo (L := L) a b (ketD k).1, (field g v).1⟫_ℂ -
        ⟪Qo (L := L) a b (field g (ketD k)).1, v.1⟫_ℂ -
        Complex.I * ⟪(ketD k).1, (field (LamH (L := L) a b g) v).1⟫_ℂ
    have hket : ∀ m, G (ketD m) = 0 := by
      intro m
      simp only [G]
      rw [Qo_symm a ha b (field g (ketD k)) (ketD m), wk a ha b g k m, sub_self]
    have htr : ∀ F, G (trunc F w) = 0 := by
      intro F
      simp only [G, field_trunc, trunc_val, inner_sum, inner_smul_right]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_eq_zero
      intro m _
      have := hket m
      simp only [G] at this
      rw [show (lp.single 2 m (w.1 m) : OF) = w.1 m • (ketD m).1 by
        change _ = w.1 m • (lp.single 2 m (1 : ℂ) : OF)
        rw [← lp.single_smul, smul_eq_mul, mul_one]]
      simp only [inner_smul_right]
      linear_combination w.1 m * this
    apply zero_of_bound _ (fun F => ‖Qo (L := L) a b (ketD k).1‖ * (2 * ‖g‖ *
        Real.sqrt (T (w - trunc F w).1 + ‖(w - trunc F w).1‖^2)) +
        ‖Qo (L := L) a b (field g (ketD k)).1‖ * ‖(w - trunc F w).1‖ +
        ‖(ketD k).1‖ * (2 * ‖LamH (L := L) a b g‖ *
          Real.sqrt (T (w - trunc F w).1 + ‖(w - trunc F w).1‖^2)))
    · have h1 := (moment_tendsto w).const_mul (2 * ‖g‖) |>.const_mul ‖Qo (L := L) a b (ketD k).1‖
      have h2 := (norm_sub_trunc_tendsto w).const_mul ‖Qo (L := L) a b (field g (ketD k)).1‖
      have h3 := (moment_tendsto w).const_mul (2 * ‖LamH (L := L) a b g‖) |>.const_mul ‖(ketD k).1‖
      simpa using (h1.add h2).add h3
    · intro F
      have hdiff : G w = G (w - trunc F w) := by
        have := htr F
        simp only [G, field_sub, Submodule.coe_sub, inner_sub_right, inner_sub_left] at this ⊢
        linear_combination this
      change ‖G w‖ ≤ _
      rw [hdiff]
      simp only [G]
      refine (norm_sub_le _ _).trans ?_
      refine add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_
      · exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (field_bound _ _)
          (norm_nonneg _))
      · exact norm_inner_le_norm _ _
      · rw [norm_mul, Complex.norm_I, one_mul]
        exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (field_bound _ _)
          (norm_nonneg _))
  -- Step 2: arbitrary smooth vector in the first slot.
  let H2 : D → ℂ := fun v => ⟪v.1, Qo (L := L) a b (field g w).1⟫_ℂ -
      ⟪(field g v).1, Qo (L := L) a b w.1⟫_ℂ -
      Complex.I * ⟪v.1, (field (LamH (L := L) a b g) w).1⟫_ℂ
  have hket2 : ∀ m, H2 (ketD m) = 0 := by
    intro m
    have h := step1 m w
    simp only [H2]
    have e1 := Qo_symm a ha b (ketD m) (field g w)
    have e2 : ⟪(field g (ketD m)).1, Qo (L := L) a b w.1⟫_ℂ =
        ⟪Qo (L := L) a b (field g (ketD m)).1, w.1⟫_ℂ := (Qo_symm a ha b _ w).symm
    rw [← e1, e2]
    exact h
  have htr2 : ∀ F, H2 (trunc F z) = 0 := by
    intro F
    simp only [H2, field_trunc, trunc_val, sum_inner, inner_smul_left]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro m _
    have := hket2 m
    simp only [H2] at this
    rw [show (lp.single 2 m (z.1 m) : OF) = z.1 m • (ketD m).1 by
      change _ = z.1 m • (lp.single 2 m (1 : ℂ) : OF)
      rw [← lp.single_smul, smul_eq_mul, mul_one]]
    simp only [inner_smul_left]
    linear_combination conj (z.1 m) * this
  have hH2 : H2 z = 0 := by
    apply zero_of_bound _ (fun F => ‖(z - trunc F z).1‖ * ‖Qo (L := L) a b (field g w).1‖ +
        (2 * ‖g‖ * Real.sqrt (T (z - trunc F z).1 + ‖(z - trunc F z).1‖^2)) *
          ‖Qo (L := L) a b w.1‖ +
        ‖(z - trunc F z).1‖ * ‖(field (LamH (L := L) a b g) w).1‖)
    · have h1 := (norm_sub_trunc_tendsto z).mul_const ‖Qo (L := L) a b (field g w).1‖
      have h2 := ((moment_tendsto z).const_mul (2 * ‖g‖)).mul_const ‖Qo (L := L) a b w.1‖
      have h3 := (norm_sub_trunc_tendsto z).mul_const ‖(field (LamH (L := L) a b g) w).1‖
      simpa using (h1.add h2).add h3
    · intro F
      have hdiff : H2 z = H2 (z - trunc F z) := by
        have := htr2 F
        simp only [H2, field_sub, Submodule.coe_sub, inner_sub_right, inner_sub_left] at this ⊢
        linear_combination this
      rw [hdiff]
      simp only [H2]
      refine (norm_sub_le _ _).trans ?_
      refine add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_
      · exact norm_inner_le_norm _ _
      · exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (field_bound _ _)
          (norm_nonneg _))
      · rw [norm_mul, Complex.norm_I, one_mul]
        exact norm_inner_le_norm _ _
  simp only [H2] at hH2
  rw [Qo_symm a ha b z (field g w)]
  linear_combination hH2

end QuantumNLS.Prop022OFormIdentity

#print axioms QuantumNLS.Prop022OFormIdentity.form_identity
