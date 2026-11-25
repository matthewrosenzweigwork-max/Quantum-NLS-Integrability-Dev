import NlsGge.Hierarchy.ALTransferDefs38
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Batch 38, E07-6a: the AL Poisson structure and Liouville's theorem
(paper/v2.tex l.1971-1977, l.2051).

Real coordinates: the phase space is `ZMod L → ℂ`, viewed as a real normed space, derivatives are
`fderiv ℝ`, and the coordinate directions are `alPx38 j = e_j` (real part of `α_j`) and
`alPy38 j = i e_j` (imaginary part).  Wirtinger derivatives of a real `H`:
`∂H/∂α_j = (H_x - i H_y)/2`, `∂H/∂ᾱ_j = (H_x + i H_y)/2`.

CONVENTION (differs by a factor 2 from the task text, per the spec "{α_j, ᾱ_k} = i(1-|α_j|²)δ_jk"):
 bracket   `{F,H} = Σ_j i(1-|α_j|²)(F_α H_ᾱ - F_ᾱ H_α)`,
 vector field `X_H(α)_j = {α_j, H} = i(1-|α_j|²) ∂H/∂ᾱ_j`.
With the constant `2i` one would get `{α_j, ᾱ_k} = 2i(1-|α_j|²)δ_jk`; that is the same flow run
at twice the speed.  Liouville and the chain rule do not depend on this constant. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open scoped BigOperators

variable {L : ℕ} [NeZero L]

/-- The open polydisk `𝔻^L`. -/
def alDisk38 (L : ℕ) : Set (ZMod L → ℂ) := {α | IsALField38 α}

/-- Direction of `Re α_j`. -/
def alPx38 (j : ZMod L) : ZMod L → ℂ := Pi.single j (1 : ℂ)
/-- Direction of `Im α_j`. -/
def alPy38 (j : ZMod L) : ZMod L → ℂ := Pi.single j Complex.I

/-- `∂H/∂α_j = (H_x - i H_y)/2`. -/
def alWd38 (H : (ZMod L → ℂ) → ℝ) (α : ZMod L → ℂ) (j : ZMod L) : ℂ :=
  (1 / 2 : ℂ) * (((fderiv ℝ H α (alPx38 j) : ℝ) : ℂ) - Complex.I * ((fderiv ℝ H α (alPy38 j) : ℝ) : ℂ))

/-- `∂H/∂ᾱ_j = (H_x + i H_y)/2`. -/
def alWdb38 (H : (ZMod L → ℂ) → ℝ) (α : ZMod L → ℂ) (j : ZMod L) : ℂ :=
  (1 / 2 : ℂ) * (((fderiv ℝ H α (alPx38 j) : ℝ) : ℂ) + Complex.I * ((fderiv ℝ H α (alPy38 j) : ℝ) : ℂ))

/-- AL Hamiltonian vector field `X_H(α)_j = i(1-|α_j|²) ∂H/∂ᾱ_j`. -/
def alX38 (H : (ZMod L → ℂ) → ℝ) (α : ZMod L → ℂ) : ZMod L → ℂ :=
  fun j => Complex.I * ((1 - ‖α j‖ ^ 2 : ℝ) : ℂ) * alWdb38 H α j

/-- AL bracket `{F,H} = Σ_j i(1-|α_j|²)(F_α H_ᾱ - F_ᾱ H_α)` (real for real `F,H`; we take `re`). -/
def alBracket38 (F H : (ZMod L → ℂ) → ℝ) (α : ZMod L → ℂ) : ℝ :=
  (∑ j : ZMod L, Complex.I * ((1 - ‖α j‖ ^ 2 : ℝ) : ℂ) *
    (alWd38 F α j * alWdb38 H α j - alWdb38 F α j * alWd38 H α j)).re

/-- Liouville density `ρ = ∏_j (1-|α_j|²)⁻¹`. -/
def alRho38 (α : ZMod L → ℂ) : ℝ := ∏ j : ZMod L, (1 - ‖α j‖ ^ 2)⁻¹

/-- The weighted field `ρ X_H`. -/
def alRhoX38 (H : (ZMod L → ℂ) → ℝ) (α : ZMod L → ℂ) : ZMod L → ℂ :=
  fun j => (alRho38 α : ℂ) * alX38 H α j

/-- Real-coordinate divergence `Σ_j (∂_{x_j} Re V_j + ∂_{y_j} Im V_j)`. -/
def alDiv38 (V : (ZMod L → ℂ) → ZMod L → ℂ) (α : ZMod L → ℂ) : ℝ :=
  ∑ j : ZMod L, (fderiv ℝ (fun β => (V β j).re) α (alPx38 j) +
    fderiv ℝ (fun β => (V β j).im) α (alPy38 j))

lemma isOpen_alDisk38 : IsOpen (alDisk38 L) := by
  have : alDisk38 L = ⋂ j : ZMod L, {α : ZMod L → ℂ | ‖α j‖ < 1} := by
    ext α; simp [alDisk38, IsALField38]
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt (continuous_norm.comp (continuous_apply j)) continuous_const

/-- `ρ (1 - r_j)` without the `j`-th factor. -/
def alP38 (j : ZMod L) (α : ZMod L → ℂ) : ℝ :=
  ∏ k ∈ Finset.univ.erase j, (1 - ‖α k‖ ^ 2)⁻¹

lemma differentiableAt_alP38 (j : ZMod L) {α : ZMod L → ℂ} (hα : IsALField38 α) :
    DifferentiableAt ℝ (alP38 j) α := by
  have hk : ∀ k ∈ Finset.univ.erase j,
      DifferentiableAt ℝ (fun β : ZMod L → ℂ => (1 - ‖β k‖ ^ 2)⁻¹) α := fun k _ => by
    have h1 : DifferentiableAt ℝ (fun β : ZMod L → ℂ => 1 - ‖β k‖ ^ 2) α := by
      have : DifferentiableAt ℝ (fun z : ℂ => ‖z‖ ^ 2) (α k) :=
        ((contDiff_norm_sq ℝ : ContDiff ℝ 1 fun z : ℂ => ‖z‖ ^ 2).differentiable one_ne_zero) _
      have hp : DifferentiableAt ℝ (fun β : ZMod L → ℂ => β k) α := by fun_prop
      have hc : DifferentiableAt ℝ ((fun z : ℂ => ‖z‖ ^ 2) ∘ fun β : ZMod L → ℂ => β k) α :=
        this.comp α hp
      exact (differentiableAt_const _).sub hc
    refine h1.inv ?_
    have := hα k
    have h0 : ‖α k‖ ^ 2 < 1 := by nlinarith [norm_nonneg (α k)]
    linarith
  have hd := (HasFDerivAt.finsetProd (fun k hk' => (hk k hk').hasFDerivAt)).differentiableAt
  convert hd using 1
  funext β
  simp [alP38]

lemma fderiv_alP38_single (j : ZMod L) {α : ZMod L → ℂ} (hα : IsALField38 α) (c : ℂ) :
    fderiv ℝ (alP38 j) α (Pi.single j c) = 0 := by
  have hd := (differentiableAt_alP38 j hα).hasFDerivAt
  have hg : HasDerivAt (fun t : ℝ => α + t • (Pi.single j c : ZMod L → ℂ))
      (Pi.single j c) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single j c : ZMod L → ℂ)).const_add α
  have hd' : HasFDerivAt (alP38 j) (fderiv ℝ (alP38 j) α)
      (α + (0 : ℝ) • (Pi.single j c : ZMod L → ℂ)) := by simpa using hd
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) hg
  have hconst : (alP38 j ∘ fun t : ℝ => α + t • (Pi.single j c : ZMod L → ℂ)) =
      fun _ => alP38 j α := by
    funext t
    simp only [Function.comp]
    unfold alP38
    refine Finset.prod_congr rfl fun k hk => ?_
    have : k ≠ j := Finset.ne_of_mem_erase hk
    simp [this]
  rw [hconst] at h1
  exact (h1.unique (hasDerivAt_const _ _)).symm ▸ rfl

lemma alRho38_mul_eq (j : ZMod L) {α : ZMod L → ℂ} (hα : IsALField38 α) :
    alRho38 α * (1 - ‖α j‖ ^ 2) = alP38 j α := by
  have := hα j
  have h0 : 1 - ‖α j‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg (α j)]
  unfold alRho38 alP38
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  field_simp

/-- Directional derivative of `fderiv H` is the second derivative. -/
lemma hasFDerivAt_fderiv_apply38 {H : (ZMod L → ℂ) → ℝ} {α : ZMod L → ℂ}
    (h : DifferentiableAt ℝ (fderiv ℝ H) α) (v : ZMod L → ℂ) :
    HasFDerivAt (fun β => fderiv ℝ H β v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ H) α)) α :=
  (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp α h.hasFDerivAt

/-- (i) Liouville: `div(ρ X_H) = 0` pointwise on the open polydisk, for `H` of class `C²`. -/
theorem alLiouville38 {H : (ZMod L → ℂ) → ℝ} (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    {α : ZMod L → ℂ} (hα : IsALField38 α) : alDiv38 (alRhoX38 H) α = 0 := by
  have hU : alDisk38 L ∈ nhds α := isOpen_alDisk38.mem_nhds hα
  have hH2 : ContDiffAt ℝ 2 H α := hH.contDiffAt hU
  have hDiff : DifferentiableAt ℝ (fderiv ℝ H) α :=
    (hH2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsymm := hH2.isSymmSndFDerivAt (by simp)
  unfold alDiv38
  refine Finset.sum_eq_zero fun j _ => ?_
  -- pointwise formulas on the polydisk
  have hre : (fun β => (alRhoX38 H β j).re) =ᶠ[nhds α]
      fun β => -(1 / 2 : ℝ) * (alP38 j β * fderiv ℝ H β (alPy38 j)) := by
    filter_upwards [hU] with β hβ
    have hβ' : IsALField38 β := hβ
    have := alRho38_mul_eq j hβ'
    simp only [alRhoX38, alX38, alWdb38]
    rw [← this]
    have h1 : ((‖β j‖ : ℂ) ^ 2).re = ‖β j‖ ^ 2 := by
      rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
    have h2 : ((‖β j‖ : ℂ) ^ 2).im = 0 := by
      rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
    simp [Complex.mul_re, Complex.mul_im, h1, h2]
    ring
  have him : (fun β => (alRhoX38 H β j).im) =ᶠ[nhds α]
      fun β => (1 / 2 : ℝ) * (alP38 j β * fderiv ℝ H β (alPx38 j)) := by
    filter_upwards [hU] with β hβ
    have hβ' : IsALField38 β := hβ
    have := alRho38_mul_eq j hβ'
    simp only [alRhoX38, alX38, alWdb38]
    rw [← this]
    have h1 : ((‖β j‖ : ℂ) ^ 2).re = ‖β j‖ ^ 2 := by
      rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
    have h2 : ((‖β j‖ : ℂ) ^ 2).im = 0 := by
      rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
    simp [Complex.mul_re, Complex.mul_im, h1, h2]
    ring
  have hP := (differentiableAt_alP38 j hα).hasFDerivAt
  have e1 : HasFDerivAt (fun β => -(1 / 2 : ℝ) * (alP38 j β * fderiv ℝ H β (alPy38 j))) _ α :=
    ((hP.mul (hasFDerivAt_fderiv_apply38 hDiff (alPy38 j))).const_mul (-(1 / 2 : ℝ)))
  have e2 : HasFDerivAt (fun β => (1 / 2 : ℝ) * (alP38 j β * fderiv ℝ H β (alPx38 j))) _ α :=
    ((hP.mul (hasFDerivAt_fderiv_apply38 hDiff (alPx38 j))).const_mul ((1 / 2 : ℝ)))
  rw [hre.fderiv_eq, e1.fderiv, him.fderiv_eq, e2.fderiv]
  have hz : fderiv ℝ (alP38 j) α (alPx38 j) = 0 := fderiv_alP38_single j hα 1
  have hz' : fderiv ℝ (alP38 j) α (alPy38 j) = 0 := fderiv_alP38_single j hα Complex.I
  have hs := hsymm (alPx38 j) (alPy38 j)
  simp [hz, hz', hs]

/-- Chain rule in Wirtinger form: `dF(v) = Σ_j (F_α v_j + F_ᾱ conj v_j)` for real `F`. -/
lemma fderiv_eq_wirtinger38 (F : (ZMod L → ℂ) → ℝ) (α v : ZMod L → ℂ) :
    ((fderiv ℝ F α v : ℝ) : ℂ) =
      ∑ j : ZMod L, (alWd38 F α j * v j + alWdb38 F α j * (starRingEnd ℂ) (v j)) := by
  have hv : v = ∑ j : ZMod L, ((v j).re • alPx38 j + (v j).im • alPy38 j) := by
    funext k
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, alPx38, alPy38]
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    apply Complex.ext <;> simp
  conv_lhs => rw [hv]
  rw [map_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_add, map_smul, smul_eq_mul, alWd38, alWdb38]
  apply Complex.ext <;> simp <;> ring

omit [NeZero L] in
lemma alWdb38_conj (H : (ZMod L → ℂ) → ℝ) (α : ZMod L → ℂ) (j : ZMod L) :
    (starRingEnd ℂ) (alWdb38 H α j) = alWd38 H α j := by
  apply Complex.ext <;> simp [alWdb38, alWd38]

/-- (ii) `d/dt F(α(t)) = {F,H}(α(t))` along an integral curve of `X_H`, for `F` differentiable. -/
theorem alBracket_deriv38 {F H : (ZMod L → ℂ) → ℝ} {γ : ℝ → ZMod L → ℂ} {t : ℝ}
    (hF : DifferentiableAt ℝ F (γ t))
    (hγ : HasDerivAt γ (alX38 H (γ t)) t) :
    HasDerivAt (fun s => F (γ s)) (alBracket38 F H (γ t)) t := by
  have h := hF.hasFDerivAt.comp_hasDerivAt t hγ
  have h' : HasDerivAt (fun s => F (γ s)) (fderiv ℝ F (γ t) (alX38 H (γ t))) t := h
  have key := fderiv_eq_wirtinger38 F (γ t) (alX38 H (γ t))
  have : alBracket38 F H (γ t) = (((fderiv ℝ F (γ t) (alX38 H (γ t)) : ℝ) : ℂ)).re := by
    rw [key, alBracket38]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have hc : (starRingEnd ℂ) (alX38 H (γ t) j) =
        -(Complex.I * ((1 - ‖γ t j‖ ^ 2 : ℝ) : ℂ) * alWd38 H (γ t) j) := by
      simp only [alX38, map_mul, alWdb38_conj, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hc]
    simp only [alX38]
    ring
  rw [this, Complex.ofReal_re]
  exact h'

/-- (iii) `{H,H} = 0`. -/
theorem alBracket_self38 (H : (ZMod L → ℂ) → ℝ) (α : ZMod L → ℂ) : alBracket38 H H α = 0 := by
  simp only [alBracket38]
  have : ∀ j : ZMod L, Complex.I * ((1 - ‖α j‖ ^ 2 : ℝ) : ℂ) *
      (alWd38 H α j * alWdb38 H α j - alWdb38 H α j * alWd38 H α j) = 0 := fun j => by ring
  rw [Finset.sum_eq_zero (fun j _ => this j)]
  simp

/-- Energy conservation: along an integral curve of `X_H`, `H` has derivative zero. -/
theorem alEnergy_deriv38 {H : (ZMod L → ℂ) → ℝ} {γ : ℝ → ZMod L → ℂ} {t : ℝ}
    (hH : DifferentiableAt ℝ H (γ t)) (hγ : HasDerivAt γ (alX38 H (γ t)) t) :
    HasDerivAt (fun s => H (γ s)) 0 t := by
  simpa [alBracket_self38] using alBracket_deriv38 hH hγ

/-- `H` is constant along an integral curve of `X_H` that stays in the polydisk. -/
theorem alEnergy_const38 {H : (ZMod L → ℂ) → ℝ} {γ : ℝ → ZMod L → ℂ}
    (hH : ∀ t, DifferentiableAt ℝ H (γ t)) (hγ : ∀ t, HasDerivAt γ (alX38 H (γ t)) t)
    (s t : ℝ) : H (γ s) = H (γ t) := by
  have hd : ∀ u, HasDerivAt (fun r => H (γ r)) 0 u := fun u => alEnergy_deriv38 (hH u) (hγ u)
  exact is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) s t

#check @alLiouville38
#check @alBracket_deriv38
#check @alBracket_self38
#check @alEnergy_deriv38
#check @alEnergy_const38
#print axioms alLiouville38
#print axioms alBracket_deriv38
#print axioms alBracket_self38
#print axioms alEnergy_deriv38
#print axioms alEnergy_const38

end NlsGge.AblowitzLadik
end
