import Mathlib
import QuantumNLS.REF88Regular
import QuantumNLS.REF88Chart
import QuantumNLS.REF88Reg015Input

/-!
# REF88Finite: finite-support commutation from the finite-action field identity (R-EF8C2837)

Source: `source-text/chapters/global/physical_cubic.tex`, proof paragraph "Physical rotations on
finite action supports" (printed lines 142 to 175):

  "... Thus the inverse image of `z_n(t) = e^{-it ∂_{a_n}h_F(a)} z_n(0)` (`n ∈ F`), `z_n(t) = 0`
  (`n ∉ F`) has the physical vector field (global-finite-action-field) at each time.  The coordinate
  curve is continuous in every `h^s`, and its inverse image is continuous in every `H^s` by the proved
  Sobolev homeomorphisms.  It is differentiable in `L²` by the full analytic inverse.  Consequently it
  is a regular solution of the physical NLS equation.  The physical uniqueness from Theorem
  `thm:root-L2-flow` identifies it with `S^t u`."

This module proves exactly this "Consequently" step, as an INTERMEDIATE theorem:

* `FieldRotation` (named obligation, NOT proved here, NOT REG-015): the printed identity
  (global-finite-action-field) in the chart, `DΦ⁻¹(z)[ -i λ_n(a) z_n ]_n = i u'' - 2iκ|u|²u` at
  `u = Φ⁻¹(z)` for every finitely supported `z`, with frequencies `λ_n = ∂_{a_n}h_F` depending only on the
  action array `a = (|z_n|²)`.  It is produced by the finite-action Hamiltonian calculation (paragraphs
  "Bounded contour energies near arbitrary mass" and the first half of "Physical rotations on finite
  action supports"): contour energy `E_F`, `{E_F, I_n} = 0`, `H_κ ≥ E_F` with equality at the point,
  rotation invariance.
* `finiteCommutation_of_fieldRotation`: `Reg015Input` (Sobolev homeomorphisms, finite action in every
  `H^s`) + `FieldRotation` give the finite-support commutation `REF88Chart.FiniteCommutation`, through the
  regular-solution identification `REF88Regular.regular_eq_flow` (accepted `F04:thm-global` uniqueness
  and `L2Flow.flowMap_H1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate ENNReal Topology
open Filter

namespace QuantumNLS.REF88Finite

open QuantumNLS.REF88Rotations QuantumNLS.RephasingFlow QuantumNLS.ChartFrequencies
open QuantumNLS.StrongSymplectic QuantumNLS.L2Flow QuantumNLS.REF88Chart QuantumNLS.REF88Reg015
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.Fourier QuantumNLS.H1Bridge
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull QuantumNLS.REF88Regular
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.REF88Chart (K)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- `(ρ_t z)_n = e^{-itλ_n} z_n`. -/
def rotFreq (lam : ℤ → ℝ) (t : ℝ) (z : K) : K := rotE (fun n => -(t * lam n)) z

lemma rotFreq_apply (lam : ℤ → ℝ) (t : ℝ) (z : K) (n : ℤ) :
    rotFreq lam t z n = Complex.exp (-Complex.I * ((t * lam n : ℝ) : ℂ)) * z n := by
  unfold rotFreq
  rw [rotE_apply]
  congr 2
  push_cast; ring

lemma rotFreq_zero (lam : ℤ → ℝ) (z : K) : rotFreq lam 0 z = z := by
  apply lp.ext; funext n
  simp [rotFreq_apply]

lemma norm_rotFreq_apply (lam : ℤ → ℝ) (t : ℝ) (z : K) (n : ℤ) :
    ‖rotFreq lam t z n‖ = ‖z n‖ := by
  rw [rotFreq_apply, norm_mul, norm_exp_neg_I_mul, one_mul]

/-- The `L²` element `i u'' - 2iκ|u|²u` for `u ∈ H²`, as the F04 field `Gder` at `s = 2`
(junk value `0` when `u ∉ H²`). -/
def g2 {u : L2T L} (hu : MemHsLp L 2 u) : h04 L 2 :=
  h02EquivH04 L (by norm_num : (0 : ℝ) ≤ 2) (h02.ofMem hu)

open Classical in
def physField (κ : ℝ) (u : L2T L) : L2T L :=
  if hu : MemHsLp L 2 u then
    (fourierL2 L).symm (toL2ᵢ (f04W L (2 - 2)) (Gder (by norm_num : (1 : ℝ) ≤ 2) κ (g2 hu)))
  else 0

/-- The named obligation `FieldRotation`: the printed identity (global-finite-action-field) in the chart,
for every finitely supported point, with frequencies depending only on the action array. -/
def FieldRotation {Φ : L2T L → K} (hΦ : IsStronglySymplectic Φ) (κ : ℝ) : Prop :=
  ∃ lam : (ℤ → ℝ) → ℤ → ℝ, ∀ (F : Finset ℤ) (z : K), (∀ n, n ∉ F → z n = 0) →
    fderiv ℝ (chartInv hΦ) z
      (∑ n ∈ F, lp.single (E := fun _ : ℤ => ℂ) 2 n
        (-Complex.I * ((lam (act z) n : ℝ) : ℂ) * z n)) = physField κ (chartInv hΦ z)


/-! ### Coordinates of `physField` and the `H²` representative -/

lemma toL2ᵢ_apply_zero (x : h04 L (2 - 2)) (n : ℤ) :
    (toL2ᵢ (f04W L (2 - 2)) x : ℤ → ℂ) n = x.val n := by
  show (toL2 (f04W L (2 - 2)) x : ℤ → ℂ) n = _
  rw [toL2_apply]
  have h1 : (f04W L (2 - 2)).w n = 1 := by
    show f04Weight L (2 - 2) n = 1
    simp [f04Weight]
  rw [h1]; simp

lemma g2_val {u : L2T L} (hu : MemHsLp L 2 u) (n : ℤ) : (g2 hu).val n = fourierL2 L u n := rfl

lemma fourier_physField {u : L2T L} (hu : MemHsLp L 2 u) :
    fourierL2 L (physField κ u) =
      toL2ᵢ (f04W L (2 - 2)) (Gder (by norm_num : (1 : ℝ) ≤ 2) κ (g2 hu)) := by
  unfold physField
  rw [dif_pos hu, LinearIsometryEquiv.apply_symm_apply]

lemma emb_m21_g2 {u : L2T L} (hu : MemHsLp L 2 u) : emb (m21 (g2 hu)) = u := by
  apply (fourierL2 L).injective
  apply lp.ext; funext n
  rw [fourierL2_emb, m21_val]
  rfl

/-! ### The coordinate curve and its derivative -/

lemma rotFreq_eq_sum (lam : ℤ → ℝ) (t : ℝ) (F : Finset ℤ) (z : K) (hz : ∀ n, n ∉ F → z n = 0) :
    rotFreq lam t z = ∑ n ∈ F, lp.single (E := fun _ : ℤ => ℂ) 2 n
      (Complex.exp (-Complex.I * ((t * lam n : ℝ) : ℂ)) * z n) := by
  apply lp.ext; funext m
  rw [lp.coeFn_sum, Finset.sum_apply, rotFreq_apply]
  simp only [lp.coeFn_single]
  by_cases hm : m ∈ F
  · rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
    · intro h; exact absurd hm h
  · rw [hz m hm, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    have : m ≠ b := fun e => hm (e ▸ hb)
    simp [Pi.single_apply, this]

lemma hasDerivAt_rotFreq (lam : ℤ → ℝ) (F : Finset ℤ) (z : K) (hz : ∀ n, n ∉ F → z n = 0) (t : ℝ) :
    HasDerivAt (fun t => rotFreq lam t z)
      (∑ n ∈ F, lp.single (E := fun _ : ℤ => ℂ) 2 n
        (-Complex.I * ((lam n : ℝ) : ℂ) * rotFreq lam t z n)) t := by
  have hfun : (fun t => rotFreq lam t z) = fun t => ∑ n ∈ F, lp.single (E := fun _ : ℤ => ℂ) 2 n
      (Complex.exp (-Complex.I * ((t * lam n : ℝ) : ℂ)) * z n) := by
    funext t; exact rotFreq_eq_sum lam t F z hz
  rw [hfun]
  apply HasDerivAt.fun_sum
  intro n hn
  have hc : HasDerivAt (fun t : ℝ => Complex.exp (-Complex.I * ((t * lam n : ℝ) : ℂ)) * z n)
      (-Complex.I * ((lam n : ℝ) : ℂ) * rotFreq lam t z n) t := by
    have h0 : HasDerivAt (fun t : ℝ => ((t * lam n : ℝ) : ℂ)) ((lam n : ℝ) : ℂ) t := by
      have := ((hasDerivAt_id t).mul_const (lam n)).ofReal_comp
      simpa using this
    have h1 := (h0.const_mul (-Complex.I)).cexp.mul_const (z n)
    convert h1 using 1
    rw [rotFreq_apply]; ring
  have hs : ∀ c : ℂ, HasDerivAt (fun _ : ℝ => c) 0 t := fun c => hasDerivAt_const t c
  have hL := ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).restrictScalars ℝ).hasFDerivAt
    (x := (Complex.exp (-Complex.I * ((t * lam n : ℝ) : ℂ)) * z n))
  have := hL.comp_hasDerivAt t hc
  simpa [Function.comp_def] using this


lemma toL2ᵢ_apply (W : PosWeight) (x : WSeq W) (m : ℤ) :
    (toL2ᵢ W x : ℤ → ℂ) m = (Real.sqrt (W.w m) : ℂ) * x.val m := rfl

section Main
variable {Φ : L2T L → K}

/-- **The regular-solution step.**  If the field identity holds at every finitely supported point, the
coordinate rotation curve `t ↦ ρ_t z` (frequencies depending only on the action array of `z`) is
exactly the chart conjugate `A^t z` of the physical flow. -/
theorem chartFlow_eq_rotFreq (hκ : 0 < κ) (hR : Reg015Input L κ hκ) (hΦ : IsStronglySymplectic Φ)
    (hcΦ : Continuous Φ) (hcΨ : Continuous (chartInv hΦ))
    (hmod : ∀ (u : L2T L) (n : ℤ), ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n)
    {lam : (ℤ → ℝ) → ℤ → ℝ}
    (hlam : ∀ (F : Finset ℤ) (z : K), (∀ n, n ∉ F → z n = 0) →
      fderiv ℝ (chartInv hΦ) z (∑ n ∈ F, lp.single (E := fun _ : ℤ => ℂ) 2 n
        (-Complex.I * ((lam (act z) n : ℝ) : ℂ) * z n)) = physField κ (chartInv hΦ z))
    (F : Finset ℤ) (z : K) (hz : ∀ n, n ∉ F → z n = 0) (t : ℝ) :
    chartFlow hΦ hκ.le t z = rotFreq (lam (act z)) t z := by
  set a := act z with ha
  set w : ℝ → K := fun t => rotFreq (lam a) t z with hw
  have hw_supp : ∀ t n, n ∉ F → w t n = 0 := by
    intro t n hn; simp only [hw]; rw [rotFreq_apply, hz n hn, mul_zero]
  have hw_act : ∀ t, act (w t) = a := by
    intro t; funext n; simp only [act, hw, norm_rotFreq_apply, ha]
  set u : ℝ → L2T L := fun t => chartInv hΦ (w t) with hu
  have hΦu : ∀ t, Φ (u t) = w t := fun t => chartInv_right hΦ _
  have hfin : ∀ t, ∃ F' : Finset ℤ, ∀ n, n ∉ F' → (RootIndexedMasses.masses hκ (u t)).1 n = 0 := by
    intro t
    refine ⟨F, fun n hn => ?_⟩
    rw [← hmod (u t) n, hΦu, hw_supp t n hn]; simp
  have hmem : ∀ t, MemHsLp L 2 (u t) := fun t =>
    finite_action_mem_Hs hκ hR (u t) (hfin t) 2 (by norm_num)
  -- continuity into `h¹`, through the proved Sobolev homeomorphism at `s = 1`
  obtain ⟨e, he⟩ := sobolev_homeomorphism hκ hR hΦ hcΦ hcΨ hmod 1 (by norm_num)
  have hmem1 : ∀ t, MemHs L 1 (w t) := fun t => by
    apply summable_of_ne_finset_zero (s := F)
    intro n hn; rw [hw_supp t n hn]; simp
  let w1 : ℝ → h02 L 1 := fun t => h02.ofMem (hmem1 t)
  have hwc : ∀ n, Continuous fun t : ℝ => w t n := by
    intro n
    have : (fun t : ℝ => w t n) =
        fun t : ℝ => Complex.exp (-Complex.I * ((t * lam a n : ℝ) : ℂ)) * z n := by
      funext t; simp only [hw]; rw [rotFreq_apply]
    rw [this]; fun_prop
  have hw1c : Continuous w1 := by
    rw [(toL2ᵢ (def002 L 1)).toHomeomorph.isInducing.continuous_iff]
    have hsum : ∀ t, (toL2ᵢ (def002 L 1)) (w1 t) = ∑ n ∈ F, lp.single (E := fun _ : ℤ => ℂ) 2 n
        ((Real.sqrt ((def002 L 1).w n) : ℂ) * w t n) := by
      intro t
      apply lp.ext; funext m
      rw [lp.coeFn_sum, Finset.sum_apply]
      simp only [lp.coeFn_single]
      show (Real.sqrt ((def002 L 1).w m) : ℂ) * w t m = _
      by_cases hm : m ∈ F
      · rw [Finset.sum_eq_single m]
        · simp
        · intro b _ hb; simp [Pi.single_apply, Ne.symm hb]
        · intro h; exact absurd hm h
      · rw [hw_supp t m hm, mul_zero]
        symm
        apply Finset.sum_eq_zero
        intro b hb
        have : m ≠ b := fun e => hm (e ▸ hb)
        simp [Pi.single_apply, this]
    have : ((toL2ᵢ (def002 L 1)).toHomeomorph ∘ w1) = fun t => ∑ n ∈ F,
        lp.single (E := fun _ : ℤ => ℂ) 2 n ((Real.sqrt ((def002 L 1).w n) : ℂ) * w t n) := by
      funext t; exact hsum t
    rw [this]
    refine continuous_finset_sum _ fun n _ => ?_
    exact (lp.isometry_single (E := fun _ : ℤ => ℂ) (p := 2) n).continuous.comp
      (continuous_const.mul (hwc n))
  have hu1 : ∀ t, H02.toL2 (by norm_num : (0 : ℝ) ≤ 1) (e.symm (w1 t)) = u t := by
    intro t
    have h1 := he (e.symm (w1 t))
    rw [Homeomorph.apply_symm_apply] at h1
    have h2 : toK (by norm_num : (0 : ℝ) ≤ 1) (w1 t) = w t := by
      apply lp.ext; funext n
      rw [toK_apply]; rfl
    rw [h2] at h1
    have h3 := congrArg (chartInv hΦ) h1
    rw [chartInv_left] at h3
    exact h3.symm
  have hcont : Continuous fun t => m21 (g2 (hmem t)) := by
    have hfun : (fun t => m21 (g2 (hmem t))) = fun t =>
        h02EquivH04 L (by norm_num : (0 : ℝ) ≤ 1)
          (fourierHs (one_le_def002 L (by norm_num : (0 : ℝ) ≤ 1)) (e.symm (w1 t))) := by
      funext t
      apply WSeq.ext
      funext n
      rw [m21_val]
      show fourierL2 L (u t) n = fourierL2 L (e.symm (w1 t)).val n
      rw [← hu1 t]; rfl
    rw [hfun]
    exact (h02EquivH04 L (by norm_num : (0 : ℝ) ≤ 1)).continuous.comp
      ((fourierHs (one_le_def002 L (by norm_num : (0 : ℝ) ≤ 1))).continuous.comp
        (e.symm.continuous.comp hw1c))
  -- differentiability in `L²`
  have hwd : ∀ t, HasDerivAt w (∑ n ∈ F, lp.single (E := fun _ : ℤ => ℂ) 2 n
      (-Complex.I * ((lam a n : ℝ) : ℂ) * w t n)) t :=
    fun t => hasDerivAt_rotFreq (lam a) F z hz t
  have hΨd : ∀ x : K, DifferentiableAt ℝ (chartInv hΦ) x := fun x =>
    (Classical.choose_spec hΦ.exists_inverse).2.2 x
  have hud : ∀ t, HasDerivAt u (physField κ (u t)) t := by
    intro t
    have h2 := (hΨd (w t)).hasFDerivAt.comp_hasDerivAt t (hwd t)
    have h3 := hlam F (w t) (hw_supp t)
    rw [hw_act t] at h3
    exact h2.congr_deriv h3
  have hgd : ∀ t, HasDerivAt (fun t => ι2 2 (g2 (hmem t)))
      (Gder (by norm_num : (1 : ℝ) ≤ 2) κ (g2 (hmem t))) t := by
    intro t
    set T := toL2ᵢ (f04W L (2 - 2)) with hT
    have h3 := ((fourierL2 L).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      t (hud t)
    have h4 := ((T.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt
      t h3
    have hfun : (fun s => ι2 2 (g2 (hmem s))) = fun s => T.symm (fourierL2 L (u s)) := by
      funext s
      rw [LinearIsometryEquiv.eq_symm_apply]
      apply lp.ext; funext n
      rw [hT, toL2ᵢ_apply_zero]
      rfl
    rw [hfun]
    refine h4.congr_deriv ?_
    show T.symm (fourierL2 L (physField κ (u t))) = _
    rw [fourier_physField (hmem t), hT, LinearIsometryEquiv.symm_apply_apply]
  have hflow := regular_eq_flow hκ.le hcont hgd t
  rw [emb_m21_g2, emb_m21_g2] at hflow
  have hu0 : u 0 = chartInv hΦ z := by
    simp only [hu, hw, rotFreq_zero]
  unfold chartFlow
  show Φ (flowMap hκ.le (chartInv hΦ z) t) = rotFreq (lam a) t z
  rw [← hu0, ← hflow, hΦu]

/-- **Finite-support commutation** from the finite-action field identity and `Reg015Input`. -/
theorem finiteCommutation_of_fieldRotation (hκ : 0 < κ) (hR : Reg015Input L κ hκ)
    (hΦ : IsStronglySymplectic Φ) (hcΦ : Continuous Φ) (hcΨ : Continuous (chartInv hΦ))
    (hmod : ∀ (u : L2T L) (n : ℤ), ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n)
    (hFR : FieldRotation hΦ κ) : FiniteCommutation hΦ hκ.le := by
  obtain ⟨lam, hlam⟩ := hFR
  rintro t θ z ⟨F, hF⟩
  have hF' : ∀ n, n ∉ F → rotE θ z n = 0 := by
    intro n hn; rw [rotE_apply, hF n hn, mul_zero]
  rw [chartFlow_eq_rotFreq hκ hR hΦ hcΦ hcΨ hmod hlam F (rotE θ z) hF' t,
    chartFlow_eq_rotFreq hκ hR hΦ hcΦ hcΨ hmod hlam F z hF t]
  have hact : act (rotE θ z) = act z := by
    funext n
    simp only [act, rotE_apply, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [hact]
  apply lp.ext; funext n
  simp only [rotFreq_apply, rotE_apply]
  ring

end Main

#print axioms chartFlow_eq_rotFreq
#print axioms finiteCommutation_of_fieldRotation

end QuantumNLS.REF88Finite
