/-
QuantumNLS.ProductPermutation — permutation covariance of weak partial derivatives, restriction of
`A_k = 1 − Σⱼ∂ⱼ²` to the symmetric sector with its weak domain, and the box-integral form of the
torus test pairing (owner: opus_tensor).

Source: DEF-004 (definitions.tex:25) `H_N = Sym^N L²(𝕋_L)` (permutation-invariant wave functions);
DEF-005 (:31) `H¹_sym`; DEF-031 (:187) `A_k = 1 − Σ_{j≤k} ∂²_{x_j}`; DEF-001 mass-`L` torus.

Frozen imports, read-only: ProductSecondDerivatives PSD1 fca540b6, ProductWeakDerivatives PWD1
91ec7338, PhysicalEnergy 01370715 (`physAk`, `physAk_comm_perm`, `physPerm_mem_physAk_domain_iff`,
`momUnitary_physPerm`), PhysicalTensor e774c776 (`physPerm`, `coordPerm`).
No contact/Bethe/collision edits; no S2 decision; no dynamics claimed.

Results (all proved, standard axioms only):
* Box conversion: `measurePreserving_coeBox` (`x ↦ (xᵢ mod L)ᵢ` pushes Lebesgue on `[0,L]^k` to
  the torus measure); `integral_torus_eq_box`; `integral_mul_liftK_eq_box`;
  `hasWeakPartial_iff_box`, `hasWeakSecondPartial_iff_box` (test pairings as ordinary integrals
  over the box `[0,L]^k` of the lattice-periodic test and the periodic lift of `F`).
* Covariance: `hasWeakPartial_physPerm`, `hasWeakSecondPartial_physPerm`
  (`∂ⱼ` of `F∘σ` is `(∂_{σ j}F)∘σ`, in `physPerm` form).
* Symmetric sector: `symL2` (permutation-invariant `L²`), `physAk_mem_symL2`, the restriction
  `physAkSym : symL2 →ₗ.[ℂ] symL2`; `mem_physAkSym_domain_iff` (all weak `∂ⱼ²` in `L²`),
  `mem_physAkSym_domain_iff_one` (one coordinate suffices), `physAkSym_eq_sub_sum`,
  `inner_physAkSym_self_eq`, `inner_physAk_comm` / `inner_physAkSym_comm` (symmetry).
-/
import QuantumNLS.ProductSecondDerivatives

open scoped InnerProductSpace ENNReal ComplexConjugate ContDiff
open MeasureTheory QuantumNLS.Fourier QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy
  QuantumNLS.Energy QuantumNLS.WeakDerivatives QuantumNLS.ProductWeakDerivatives
  QuantumNLS.ProductSecondDerivatives

noncomputable section

namespace QuantumNLS.ProductPermutation

variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

/-! ## Box `[0,L]^k` versus torus -/

/-- The box `[0,L]^k ⊂ ℝ^k`. -/
abbrev box (L : ℝ) (k : ℕ) : Set (Fin k → ℝ) := Set.Icc 0 (fun _ => L)

/-- Reduction mod `L` coordinatewise pushes Lebesgue measure on the box to the torus measure. -/
theorem measurePreserving_coeBox :
    MeasurePreserving (fun (x : Fin k → ℝ) (i : Fin k) => (x i : AddCircle L))
      ((volume : Measure (Fin k → ℝ)).restrict (box L k)) (torusPiMeasure L k) := by
  have h1 : MeasurePreserving ((↑) : ℝ → AddCircle L)
      ((volume : Measure ℝ).restrict (Set.Ioc 0 L)) volume := by
    simpa using AddCircle.measurePreserving_mk L 0
  have h := measurePreserving_pi (fun _ : Fin k => (volume : Measure ℝ).restrict (Set.Ioc 0 L))
    (fun _ => (volume : Measure (AddCircle L))) (fun _ => h1)
  have e : Measure.pi (fun _ : Fin k => (volume : Measure ℝ).restrict (Set.Ioc 0 L)) =
      (volume : Measure (Fin k → ℝ)).restrict (box L k) := by
    rw [← Measure.restrict_pi_pi]
    exact Measure.restrict_congr_set Measure.univ_pi_Ioc_ae_eq_Icc
  rw [e] at h
  exact h

/-- **Torus integral = box integral** of the periodic lift. -/
theorem integral_torus_eq_box {g : (Fin k → AddCircle L) → ℂ}
    (hg : AEStronglyMeasurable g (torusPiMeasure L k)) :
    ∫ y, g y ∂(torusPiMeasure L k) = ∫ x in box L k, g (fun i => (x i : AddCircle L)) := by
  have hmp := measurePreserving_coeBox (L := L) (k := k)
  have h := integral_map (μ := (volume : Measure (Fin k → ℝ)).restrict (box L k))
    hmp.measurable.aemeasurable (f := g) (by rw [hmp.map_eq]; exact hg)
  rw [hmp.map_eq] at h
  exact h

/-- Test pairing as a box integral: `∫_{𝕋^k} F · ψ = ∫_{[0,L]^k} F(x mod L) ψ(x) dx`. -/
theorem integral_mul_liftK_eq_box (F : L2TN L k) {ψ : (Fin k → ℝ) → ℂ}
    (hψ : IsTorusTest L ψ) :
    ∫ y, (F : (Fin k → AddCircle L) → ℂ) y * liftK (L := L) ψ y ∂(torusPiMeasure L k) =
      ∫ x in box L k, (F : (Fin k → AddCircle L) → ℂ) (fun i => (x i : AddCircle L)) * ψ x := by
  rw [integral_torus_eq_box (g := fun y => (F : (Fin k → AddCircle L) → ℂ) y * liftK (L := L) ψ y)
    ((Lp.aestronglyMeasurable F).mul
      (measurable_liftK hψ.smooth.continuous.measurable).aestronglyMeasurable)]
  congr 1; funext x
  rw [liftK_coe hψ.periodic]

/-- **Weak partial derivative, box form.** -/
theorem hasWeakPartial_iff_box (j : Fin k) (F G : L2TN L k) :
    HasWeakPartial j F G ↔ ∀ φ : (Fin k → ℝ) → ℂ, IsTorusTest L φ →
      ∫ x in box L k, (F : (Fin k → AddCircle L) → ℂ) (fun i => (x i : AddCircle L)) *
          pderiv j φ x =
        -∫ x in box L k, (G : (Fin k → AddCircle L) → ℂ) (fun i => (x i : AddCircle L)) * φ x := by
  refine forall_congr' fun φ => forall_congr' fun hφ => ?_
  rw [integral_mul_liftK_eq_box F (pderiv_isTest hφ j), integral_mul_liftK_eq_box G hφ]

/-- **Weak second partial derivative, box form.** -/
theorem hasWeakSecondPartial_iff_box (i j : Fin k) (F H : L2TN L k) :
    HasWeakSecondPartial i j F H ↔ ∀ φ : (Fin k → ℝ) → ℂ, IsTorusTest L φ →
      ∫ x in box L k, (F : (Fin k → AddCircle L) → ℂ) (fun i => (x i : AddCircle L)) *
          pderiv i (pderiv j φ) x =
        ∫ x in box L k, (H : (Fin k → AddCircle L) → ℂ) (fun i => (x i : AddCircle L)) * φ x := by
  refine forall_congr' fun φ => forall_congr' fun hφ => ?_
  rw [integral_mul_liftK_eq_box F (pderiv_isTest (pderiv_isTest hφ j) i),
    integral_mul_liftK_eq_box H hφ]

/-! ## Permutation covariance -/

/-- **Covariance of weak partials.** With `(V_σF)(x) = F(x∘σ)`: if `∂ᵢF = G` weakly then
`∂_{σ i}(V_σF) = V_σG` weakly. -/
theorem hasWeakPartial_physPerm (σ : Equiv.Perm (Fin k)) {i : Fin k} {F G : L2TN L k}
    (h : HasWeakPartial i F G) : HasWeakPartial (σ i) (physPerm σ F) (physPerm σ G) := by
  rw [hasWeakPartial_iff] at h ⊢
  intro w
  rw [momUnitary_physPerm, momUnitary_physPerm, h]
  rfl

/-- **Covariance of weak second partials.** -/
theorem hasWeakSecondPartial_physPerm (σ : Equiv.Perm (Fin k)) {i j : Fin k} {F H : L2TN L k}
    (h : HasWeakSecondPartial i j F H) :
    HasWeakSecondPartial (σ i) (σ j) (physPerm σ F) (physPerm σ H) := by
  rw [hasWeakSecondPartial_iff] at h ⊢
  intro w
  rw [momUnitary_physPerm, momUnitary_physPerm, h]
  rfl

/-! ## The symmetric sector -/

/-- Permutation-invariant wave functions in `L²(𝕋_L^k)` (DEF-004 position form). -/
def symL2 (L : ℝ) [Fact (0 < L)] (k : ℕ) : Submodule ℂ (L2TN L k) where
  carrier := {F | ∀ σ : Equiv.Perm (Fin k), physPerm σ F = F}
  add_mem' {a b} ha hb σ := by
    rw [map_add, ha σ, hb σ]
  zero_mem' σ := map_zero _
  smul_mem' c x hx σ := by
    rw [map_smul, hx σ]

theorem mem_symL2_iff (F : L2TN L k) :
    F ∈ symL2 L k ↔ ∀ σ : Equiv.Perm (Fin k), physPerm σ F = F := Iff.rfl

/-- `A_k` preserves the symmetric sector (from the frozen commutation `physAk_comm_perm`). -/
theorem physAk_mem_symL2 (F : (physAk L k).domain) (hF : (F : L2TN L k) ∈ symL2 L k) :
    physAk L k F ∈ symL2 L k := by
  intro σ
  rw [← physAk_comm_perm σ F]
  congr 1
  exact Subtype.ext (hF σ)

/-- Domain of the symmetric restriction: symmetric vectors in `D(A_k)`. -/
def symDom (L : ℝ) [Fact (0 < L)] (k : ℕ) : Submodule ℂ (symL2 L k) :=
  (physAk L k).domain.comap (symL2 L k).subtype

/-- Inclusion of the symmetric domain into `D(A_k)`. -/
def symDomIncl : symDom L k →ₗ[ℂ] (physAk L k).domain where
  toFun x := ⟨((x : symL2 L k) : L2TN L k), x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **`A_k` restricted to the symmetric sector**, `A_k^{sym} : symL2 →ₗ.[ℂ] symL2`. -/
def physAkSym (L : ℝ) [Fact (0 < L)] (k : ℕ) : symL2 L k →ₗ.[ℂ] symL2 L k where
  domain := symDom L k
  toFun := LinearMap.codRestrict (symL2 L k) ((physAk L k).toFun.comp symDomIncl)
    fun x => physAk_mem_symL2 (symDomIncl x) (x : symL2 L k).2

theorem physAkSym_apply (x : (physAkSym L k).domain) :
    ((physAkSym L k x : symL2 L k) : L2TN L k) =
      physAk L k ⟨((x : symL2 L k) : L2TN L k), x.2⟩ := rfl

/-- **Weak domain of `A_k^{sym}`:** a symmetric `F` is in the domain iff every weak `∂ⱼ²F ∈ L²`. -/
theorem mem_physAkSym_domain_iff (x : symL2 L k) :
    x ∈ (physAkSym L k).domain ↔ ∀ j, ∃ H, HasWeakSecondPartial j j (x : L2TN L k) H :=
  mem_physAk_domain_iff_second (x : L2TN L k)

/-- For symmetric `F`, weak second partials in different coordinates are permutation images. -/
theorem hasWeakSecondPartial_of_sym {F H : L2TN L k} (hF : F ∈ symL2 L k) {j : Fin k}
    (h : HasWeakSecondPartial j j F H) (σ : Equiv.Perm (Fin k)) :
    HasWeakSecondPartial (σ j) (σ j) F (physPerm σ H) := by
  have := hasWeakSecondPartial_physPerm σ h
  rwa [hF σ] at this

/-- **One coordinate suffices on the symmetric sector:** `F ∈ D(A_k^{sym})` iff `∂_{j₀}²F ∈ L²`
weakly, for any fixed `j₀`. -/
theorem mem_physAkSym_domain_iff_one (x : symL2 L k) (j₀ : Fin k) :
    x ∈ (physAkSym L k).domain ↔ ∃ H, HasWeakSecondPartial j₀ j₀ (x : L2TN L k) H := by
  rw [mem_physAkSym_domain_iff]
  refine ⟨fun h => h j₀, fun ⟨H, hH⟩ j => ⟨physPerm (Equiv.swap j₀ j) H, ?_⟩⟩
  have := hasWeakSecondPartial_of_sym x.2 hH (Equiv.swap j₀ j)
  rwa [Equiv.swap_apply_left] at this

/-- **`A_k^{sym} F = F − Σⱼ ∂ⱼ²F`** on the symmetric sector. -/
theorem physAkSym_eq_sub_sum (x : (physAkSym L k).domain) (H : Fin k → L2TN L k)
    (hH : ∀ j, HasWeakSecondPartial j j ((x : symL2 L k) : L2TN L k) (H j)) :
    ((physAkSym L k x : symL2 L k) : L2TN L k) = ((x : symL2 L k) : L2TN L k) - ∑ j, H j :=
  physAk_eq_sub_sum ⟨((x : symL2 L k) : L2TN L k), x.2⟩ H hH

/-- **Form identity on the symmetric sector:** `⟪F, A_k^{sym}F⟫ = ‖F‖² + Σⱼ‖∂ⱼF‖²`. -/
theorem inner_physAkSym_self_eq (x : (physAkSym L k).domain) (G : Fin k → L2TN L k)
    (hG : ∀ j, HasWeakPartial j ((x : symL2 L k) : L2TN L k) (G j)) :
    ⟪(x : symL2 L k), physAkSym L k x⟫_ℂ =
      ((‖((x : symL2 L k) : L2TN L k)‖ ^ 2 + ∑ j, ‖G j‖ ^ 2 : ℝ) : ℂ) := by
  rw [Submodule.coe_inner, physAkSym_apply]
  exact inner_physAk_self_eq ⟨((x : symL2 L k) : L2TN L k), x.2⟩ G hG

/-- **`A_k` is symmetric:** `⟪A_kF, G⟫ = ⟪F, A_kG⟫` on `D(A_k)`. -/
theorem inner_physAk_comm (F G : (physAk L k).domain) :
    ⟪physAk L k F, (G : L2TN L k)⟫_ℂ = ⟪(F : L2TN L k), physAk L k G⟫_ℂ := by
  rw [← (momUnitary L k).inner_map_map, ← (momUnitary L k).inner_map_map (F : L2TN L k),
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1; funext w
  rw [RCLike.inner_apply', RCLike.inner_apply', momUnitary_physAk, momUnitary_physAk, map_mul,
    Complex.conj_ofReal]
  ring

/-- **`A_k^{sym}` is symmetric** on its domain. -/
theorem inner_physAkSym_comm (x y : (physAkSym L k).domain) :
    ⟪physAkSym L k x, (y : symL2 L k)⟫_ℂ = ⟪(x : symL2 L k), physAkSym L k y⟫_ℂ := by
  rw [Submodule.coe_inner, Submodule.coe_inner, physAkSym_apply, physAkSym_apply]
  exact inner_physAk_comm ⟨_, x.2⟩ ⟨_, y.2⟩

end QuantumNLS.ProductPermutation

#print axioms QuantumNLS.ProductPermutation.measurePreserving_coeBox
#print axioms QuantumNLS.ProductPermutation.integral_torus_eq_box
#print axioms QuantumNLS.ProductPermutation.hasWeakPartial_iff_box
#print axioms QuantumNLS.ProductPermutation.hasWeakSecondPartial_iff_box
#print axioms QuantumNLS.ProductPermutation.hasWeakPartial_physPerm
#print axioms QuantumNLS.ProductPermutation.hasWeakSecondPartial_physPerm
#print axioms QuantumNLS.ProductPermutation.physAk_mem_symL2
#print axioms QuantumNLS.ProductPermutation.mem_physAkSym_domain_iff
#print axioms QuantumNLS.ProductPermutation.mem_physAkSym_domain_iff_one
#print axioms QuantumNLS.ProductPermutation.physAkSym_eq_sub_sum
#print axioms QuantumNLS.ProductPermutation.inner_physAkSym_self_eq
#print axioms QuantumNLS.ProductPermutation.inner_physAkSym_comm
