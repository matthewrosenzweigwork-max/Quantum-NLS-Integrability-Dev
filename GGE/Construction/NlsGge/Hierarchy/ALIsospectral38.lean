import NlsGge.Hierarchy.ALPoissonLiouville38
import NlsGge.Hierarchy.ALPositiveDecompositions38
import NlsGge.Hierarchy.ALC12Exact38
import NlsGge.Hierarchy.ALLaurent38
import NlsGge.Hierarchy.ALMoments38
import NlsGge.Analysis.EvenLogDisk38
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open scoped Matrix ComplexConjugate
open scoped Matrix.Norms.Frobenius

/-- Lax matrix entry `B_j(z)` with `u = α_j`, `v = α_{j-1}` (includes the rotation part `i σ₃`). -/
def alLax38 (u v z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-(Complex.I * z ^ 2) + Complex.I * ((u * conj v + conj u * v) / 2) + Complex.I,
      -(Complex.I * u * z) + Complex.I * v * z⁻¹;
     -(Complex.I * conj v * z) + Complex.I * conj u * z⁻¹,
      Complex.I * (z ^ 2)⁻¹ - Complex.I * ((u * conj v + conj u * v) / 2) - Complex.I]

/-- Explicit `H_d`-flow vector field `α_j' = 2iα_j - i(1-r_j)(α_{j+1}+α_{j-1})`. -/
def alXd38 {L : ℕ} (α : ZMod L → ℂ) : ZMod L → ℂ := fun j =>
  2 * Complex.I * α j - Complex.I * ((1 - ‖α j‖ ^ 2 : ℝ) : ℂ) * (α (j + 1) + α (j - 1))

lemma alLax_step38 (u v w z : ℂ) (hz : z ≠ 0) (s ν : ℂ)
    (hr : ((‖u‖ ^ 2 : ℝ) : ℂ) = u * conj u)
    (hν : ν = (conj u * (w + v) - u * (conj w + conj v)) / (2 * Complex.I)) :
    alLax38 w u z * (s • !![z, u; conj u, z⁻¹]) - (s • !![z, u; conj u, z⁻¹]) * alLax38 u v z =
      s • (!![0, 2 * Complex.I * u - Complex.I * ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) * (w + v);
              conj (2 * Complex.I * u - Complex.I * ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) * (w + v)), 0]
        + ν • !![z, u; conj u, z⁻¹]) := by
  have hr' : ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) = 1 - u * conj u := by push_cast at hr ⊢; rw [hr]
  rw [hr']
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alLax38, hν, map_sub, map_mul, map_add, map_ofNat] <;>
    field_simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring


lemma re_conj_mul_X38 (u v w : ℂ) :
    (conj u * (2 * Complex.I * u - Complex.I * ((1 - ‖u‖ ^ 2 : ℝ) : ℂ) * (w + v))).re =
      (1 - ‖u‖ ^ 2) * (conj u * (w + v)).im := by
  have h1 : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = 1 - ‖u‖ ^ 2 := ⟨_, rfl⟩
  rw [← hh]
  simp [Complex.mul_re, Complex.mul_im]
  rw [hh, h1]
  ring

lemma hasDerivAt_alTransfer38 {a : ℝ → ℂ} {t : ℝ} {v w z : ℂ} (hz : z ≠ 0) (ha : ‖a t‖ < 1)
    (hd : HasDerivAt a (2 * Complex.I * a t - Complex.I * ((1 - ‖a t‖ ^ 2 : ℝ) : ℂ) * (w + v)) t) :
    HasDerivAt (fun τ => alTransfer38 (a τ) z)
      (alLax38 w (a t) z * alTransfer38 (a t) z - alTransfer38 (a t) z * alLax38 (a t) v z) t := by
  set X : ℂ := 2 * Complex.I * a t - Complex.I * ((1 - ‖a t‖ ^ 2 : ℝ) : ℂ) * (w + v) with hX
  have hU : HasDerivAt (fun τ => (!![z, a τ; conj (a τ), z⁻¹] : Matrix (Fin 2) (Fin 2) ℂ))
      !![0, X; conj X, 0] t := by
    have e : (fun τ => (!![z, a τ; conj (a τ), z⁻¹] : Matrix (Fin 2) (Fin 2) ℂ)) =
        fun τ => (!![z, 0; 0, z⁻¹] : Matrix (Fin 2) (Fin 2) ℂ) + a τ • (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)
          + conj (a τ) • (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
      funext τ; ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [e]
    have h2 := ((hasDerivAt_const t (!![z, 0; 0, z⁻¹] : Matrix (Fin 2) (Fin 2) ℂ)).add
      (hd.smul_const (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ))).add
      (hd.star.smul_const (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ))
    refine h2.congr_deriv ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hr : ‖a t‖ ^ 2 < 1 := by nlinarith [norm_nonneg (a t)]
  have hpos : 0 < 1 - ‖a t‖ ^ 2 := by linarith
  have hn : HasDerivAt (fun τ => ‖a τ‖ ^ 2)
      (2 * (a t).re * X.re + 2 * (a t).im * X.im) t := by
    have e : (fun τ => ‖a τ‖ ^ 2) = fun τ => (a τ).re ^ 2 + (a τ).im ^ 2 := by
      funext τ; rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [e]
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
    have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hd
    have := (hre.pow 2).add (him.pow 2)
    refine this.congr_deriv ?_
    simp
  have h1 : HasDerivAt (fun τ => 1 - ‖a τ‖ ^ 2)
      (-(2 * (a t).re * X.re + 2 * (a t).im * X.im)) t := hn.const_sub 1
  have hg := h1.sqrt hpos.ne'
  have hsq : 0 < Real.sqrt (1 - ‖a t‖ ^ 2) := Real.sqrt_pos.mpr hpos
  have hs := hg.inv hsq.ne'
  have hsC := hs.ofReal_comp
  have hP : (a t).re * X.re + (a t).im * X.im = (1 - ‖a t‖ ^ 2) * (conj (a t) * (w + v)).im := by
    have := re_conj_mul_X38 (a t) v w
    rw [← hX] at this
    rw [← this]; simp [Complex.mul_re]
  set ν : ℂ := (conj (a t) * (w + v) - a t * (conj w + conj v)) / (2 * Complex.I) with hν
  have hνim : ν = (((conj (a t) * (w + v)).im : ℝ) : ℂ) := by
    rw [Complex.im_eq_sub_conj, hν]; simp
  have hsν : (((-(-(2 * (a t).re * X.re + 2 * (a t).im * X.im) /
      (2 * Real.sqrt (1 - ‖a t‖ ^ 2))) / Real.sqrt (1 - ‖a t‖ ^ 2) ^ 2 : ℝ)) : ℂ) =
      (Real.sqrt (1 - ‖a t‖ ^ 2) : ℂ)⁻¹ * ν := by
    rw [hνim]
    have e2 : (2 * (a t).re * X.re + 2 * (a t).im * X.im) =
        2 * ((1 - ‖a t‖ ^ 2) * (conj (a t) * (w + v)).im) := by rw [← hP]; ring
    have hg2 : Real.sqrt (1 - ‖a t‖ ^ 2) ^ 2 = 1 - ‖a t‖ ^ 2 := Real.sq_sqrt hpos.le
    rw [e2]
    generalize Real.sqrt (1 - ‖a t‖ ^ 2) = g at *
    have hg0 : g ≠ 0 := hsq.ne'
    rw [← hg2]
    push_cast
    field_simp
  have key := alLax_step38 (a t) v w z hz ((Real.sqrt (1 - ‖a t‖ ^ 2) : ℂ)⁻¹) ν
    (by rw [Complex.mul_conj']; push_cast; rfl) hν
  have hprod := hsC.smul hU
  unfold alTransfer38
  have hfun : (fun τ => (((Real.sqrt (1 - ‖a τ‖ ^ 2) : ℝ) : ℂ))⁻¹ •
      (!![z, a τ; star (a τ), z⁻¹] : Matrix (Fin 2) (Fin 2) ℂ)) =
      ((fun y => (((fun y => (Real.sqrt (1 - ‖a y‖ ^ 2))⁻¹) y : ℝ) : ℂ)) •
        fun τ => (!![z, a τ; conj (a τ), z⁻¹] : Matrix (Fin 2) (Fin 2) ℂ)) := by
    funext τ; simp [Complex.ofReal_inv]
  rw [hfun]
  refine hprod.congr_deriv ?_
  simp only [Complex.star_def]
  rw [← hX] at key
  rw [key, hsν, smul_add, smul_smul]
  simp only [Pi.inv_apply, Complex.ofReal_inv]

set_option linter.unusedSectionVars false

variable {L : ℕ} [NeZero L]

/-- `B_j(z)` along a lattice field. -/
def alLaxB38 (α : ZMod L → ℂ) (z : ℂ) (j : ZMod L) : Matrix (Fin 2) (Fin 2) ℂ :=
  alLax38 (α j) (α (j - 1)) z

lemma hasDerivAt_alPartial38 {γ : ℝ → ZMod L → ℂ} {t : ℝ} {z : ℂ} (hz : z ≠ 0)
    (hα : IsALField38 (γ t)) (hγ : HasDerivAt γ (alXd38 (γ t)) t) (k : ℕ) :
    HasDerivAt (fun τ => alPartial38 (γ τ) z k)
      (alLaxB38 (γ t) z (k : ZMod L) * alPartial38 (γ t) z k -
        alPartial38 (γ t) z k * alLaxB38 (γ t) z 0) t := by
  induction k with
  | zero =>
    refine (hasDerivAt_const t (1 : Matrix (Fin 2) (Fin 2) ℂ)).congr_deriv ?_
    simp [alPartial38]
  | succ k ih =>
    have hc : HasDerivAt (fun τ => γ τ (k : ZMod L)) (alXd38 (γ t) (k : ZMod L)) t :=
      (hasDerivAt_pi.1 hγ) _
    have hA := hasDerivAt_alTransfer38 (v := γ t ((k : ZMod L) - 1)) (w := γ t ((k : ZMod L) + 1))
      hz (hα _) hc
    have hm := hA.mul ih
    simp only [alPartial38]
    refine hm.congr_deriv ?_
    have e1 : alLax38 (γ t ((k : ZMod L) + 1)) (γ t (k : ZMod L)) z =
        alLaxB38 (γ t) z ((k + 1 : ℕ) : ZMod L) := by
      simp [alLaxB38]
    have e2 : alLax38 (γ t (k : ZMod L)) (γ t ((k : ZMod L) - 1)) z =
        alLaxB38 (γ t) z (k : ZMod L) := rfl
    rw [e1, e2]
    simp only [mul_sub, sub_mul, mul_assoc]
    abel

theorem hasDerivAt_trace_alMonodromy38 {γ : ℝ → ZMod L → ℂ} {t : ℝ} {z : ℂ} (hz : z ≠ 0)
    (hα : IsALField38 (γ t)) (hγ : HasDerivAt γ (alXd38 (γ t)) t) :
    HasDerivAt (fun τ => Matrix.trace (alMonodromy38 (γ τ) z)) 0 t := by
  have h := hasDerivAt_alPartial38 hz hα hγ L
  have hL : ((L : ℕ) : ZMod L) = 0 := ZMod.natCast_self L
  rw [hL] at h
  let T : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).restrictScalars ℝ)
  have hT := T.hasFDerivAt.comp_hasDerivAt t h
  have e : (fun τ => Matrix.trace (alMonodromy38 (γ τ) z)) =
      T ∘ (fun τ => alPartial38 (γ τ) z L) := by
    funext τ; simp [T, alMonodromy38]
  rw [e]
  refine hT.congr_deriv ?_
  have hTx : ∀ x, T x = Matrix.trace x := fun x => rfl
  refine (hTx _).trans ?_
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

open NlsGge.HierarchyRiccati.Core in
/-- Directional derivative of `H_d`. -/
def alHdDer38 (α v : ZMod L → ℂ) : ℝ :=
  ∑ k : ZMod L, 4 * ((α k).re * (v k).re + (α k).im * (v k).im) / (1 - ‖α k‖ ^ 2)
    - 2 * (∑ k : ZMod L, (v k * conj (α (k - 1)) + α k * conj (v (k - 1)))).re

lemma hasDerivAt_normSq38 {a : ℝ → ℂ} {X : ℂ} {t : ℝ} (hd : HasDerivAt a X t) :
    HasDerivAt (fun τ => ‖a τ‖ ^ 2) (2 * ((a t).re * X.re + (a t).im * X.im)) t := by
  have e : (fun τ => ‖a τ‖ ^ 2) = fun τ => (a τ).re ^ 2 + (a τ).im ^ 2 := by
    funext τ; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [e]
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hd
  have := (hre.pow 2).add (him.pow 2)
  refine this.congr_deriv ?_
  simp
  ring

open NlsGge.HierarchyRiccati.Core in
lemma hasDerivAt_alHd_line38 {α : ZMod L → ℂ} (hα : IsALField38 α) (v : ZMod L → ℂ) :
    HasDerivAt (fun τ : ℝ => alHd (α + τ • v)) (alHdDer38 α v) 0 := by
  have hk : ∀ k : ZMod L, HasDerivAt (fun τ : ℝ => (α + τ • v) k) (v k) 0 := fun k => by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (v k)).const_add (α k)
    simpa using this
  have hr : ∀ k : ZMod L, 0 < 1 - ‖α k‖ ^ 2 := fun k => by
    have := hα k; nlinarith [norm_nonneg (α k)]
  -- mass part
  have hM : HasDerivAt (fun τ : ℝ => alMd (α + τ • v))
      (∑ k : ZMod L, 2 * ((α k).re * (v k).re + (α k).im * (v k).im) / (1 - ‖α k‖ ^ 2)) 0 := by
    have hlog : ∀ k : ZMod L, HasDerivAt (fun τ : ℝ => -Real.log (1 - ‖(α + τ • v) k‖ ^ 2))
        (2 * ((α k).re * (v k).re + (α k).im * (v k).im) / (1 - ‖α k‖ ^ 2)) 0 := fun k => by
      have hn := hasDerivAt_normSq38 (hk k)
      have h1 := hn.const_sub 1
      have h2 := h1.log (by simp; exact (hr k).ne')
      have h3 := h2.neg
      refine h3.congr_deriv ?_
      simp
      ring
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => hlog k)
    convert this using 1
    funext τ
    simp [alMd, alR, Finset.sum_neg_distrib]
  -- C1 part
  have hC : HasDerivAt (fun τ : ℝ => alC1 (α + τ • v))
      (∑ k : ZMod L, (v k * conj (α (k - 1)) + α k * conj (v (k - 1)))) 0 := by
    have hterm : ∀ k : ZMod L, HasDerivAt (fun τ : ℝ => (α + τ • v) k * conj ((α + τ • v) (k - 1)))
        (v k * conj (α (k - 1)) + α k * conj (v (k - 1))) 0 := fun k => by
      have := (hk k).mul (hk (k - 1)).star
      refine this.congr_deriv ?_
      simp
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => hterm k)
    simpa [alC1] using this
  have hRe := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hC
  have := (hM.const_mul 2).sub (hRe.const_mul 2)
  refine this.congr_deriv ?_
  simp [alHdDer38, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

open NlsGge.HierarchyRiccati.Core in
lemma differentiableAt_alHd38 {α : ZMod L → ℂ} (hα : IsALField38 α) :
    DifferentiableAt ℝ alHd α := by
  have hr : ∀ k : ZMod L, 0 < 1 - ‖α k‖ ^ 2 := fun k => by
    have := hα k; nlinarith [norm_nonneg (α k)]
  have hnorm : ∀ k : ZMod L, DifferentiableAt ℝ (fun β : ZMod L → ℂ => 1 - ‖β k‖ ^ 2) α := fun k => by
    have h1 : DifferentiableAt ℝ (fun z : ℂ => ‖z‖ ^ 2) (α k) :=
      ((contDiff_norm_sq ℝ : ContDiff ℝ 1 fun z : ℂ => ‖z‖ ^ 2).differentiable one_ne_zero) _
    have hp : DifferentiableAt ℝ (fun β : ZMod L → ℂ => β k) α := by fun_prop
    have hc : DifferentiableAt ℝ ((fun z : ℂ => ‖z‖ ^ 2) ∘ fun β : ZMod L → ℂ => β k) α :=
      h1.comp α hp
    exact (differentiableAt_const _).sub hc
  have hM : DifferentiableAt ℝ alMd α := by
    have : alMd = fun β : ZMod L → ℂ => ∑ k : ZMod L, -Real.log (1 - ‖β k‖ ^ 2) := by
      funext β; simp [alMd, alR, Finset.sum_neg_distrib]
    rw [this]
    refine DifferentiableAt.fun_sum fun k _ => ?_
    exact ((hnorm k).log (hr k).ne').neg
  have hC : DifferentiableAt ℝ (fun β : ZMod L → ℂ => (alC1 β).re) α := by
    have hp : ∀ k : ZMod L, DifferentiableAt ℝ (fun β : ZMod L → ℂ => β k) α := fun k => by fun_prop
    have : DifferentiableAt ℝ alC1 α := by
      unfold alC1
      refine DifferentiableAt.fun_sum fun k _ => ?_
      exact (hp k).mul ((Complex.conjCLE.differentiableAt).comp α (hp (k - 1)))
    exact Complex.reCLM.differentiableAt.comp α this
  exact (hM.const_mul 2).sub (hC.const_mul 2)

open NlsGge.HierarchyRiccati.Core in
lemma fderiv_alHd38 {α : ZMod L → ℂ} (hα : IsALField38 α) (v : ZMod L → ℂ) :
    fderiv ℝ alHd α v = alHdDer38 α v := by
  have hd := (differentiableAt_alHd38 hα).hasFDerivAt
  have hg : HasDerivAt (fun t : ℝ => α + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add α
  have hd' : HasFDerivAt alHd (fderiv ℝ alHd α) (α + (0 : ℝ) • v) := by simpa using hd
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) hg
  exact h1.unique (hasDerivAt_alHd_line38 hα v)

lemma alHdDer_single38 (α : ZMod L → ℂ) (j : ZMod L) (c : ℂ) :
    alHdDer38 α (Pi.single j c) =
      4 * ((α j).re * c.re + (α j).im * c.im) / (1 - ‖α j‖ ^ 2)
        - 2 * (c * conj (α (j - 1)) + α (j + 1) * conj c).re := by
  unfold alHdDer38
  congr 1
  · rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk; simp [Pi.single_eq_of_ne hk]
    · simp
  · congr 2
    rw [Finset.sum_add_distrib, Finset.sum_eq_single j, Finset.sum_eq_single (j + 1)]
    · simp
    · intro k _ hk
      have : k - 1 ≠ j := fun h => hk (by rw [← h]; ring)
      simp [Pi.single_eq_of_ne this]
    · simp
    · intro k _ hk; simp [Pi.single_eq_of_ne hk]
    · simp

open NlsGge.HierarchyRiccati.Core in
lemma alWdb_alHd38 {α : ZMod L → ℂ} (hα : IsALField38 α) (j : ZMod L) :
    alWdb38 alHd α j = 2 * α j / ((1 - ‖α j‖ ^ 2 : ℝ) : ℂ) - (α (j + 1) + α (j - 1)) := by
  have hr : 0 < 1 - ‖α j‖ ^ 2 := by have := hα j; nlinarith [norm_nonneg (α j)]
  unfold alWdb38 alPx38 alPy38
  rw [fderiv_alHd38 hα, fderiv_alHd38 hα, alHdDer_single38, alHdDer_single38]
  have h1 : ‖α j‖ ^ 2 = (α j).re ^ 2 + (α j).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = 1 - ‖α j‖ ^ 2 := ⟨_, rfl⟩
  rw [← hh] at hr ⊢
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hh1 : h ≠ 0 := hr.ne'
  rw [← Complex.re_add_im (α j)]
  simp
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  · field_simp; ring
  · field_simp; ring

open NlsGge.HierarchyRiccati.Core in
/-- The AL Hamiltonian vector field of `H_d = 2M_d - 2 Re C₁` in explicit form. -/
theorem alX38_alHd {α : ZMod L → ℂ} (hα : IsALField38 α) : alX38 alHd α = alXd38 α := by
  funext j
  have hr : 0 < 1 - ‖α j‖ ^ 2 := by have := hα j; nlinarith [norm_nonneg (α j)]
  have hh0 : (((1 - ‖α j‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [alX38, alXd38, alWdb_alHd38 hα]
  field_simp

open Metric Filter Topology in
/-- Equal discriminants force equal exterior multipliers on the unit `ζ`-disk. -/
theorem alExteriorG38_eq_of_trace38 {α β : ZMod L → ℂ} (hα : IsALField38 α) (hβ : IsALField38 β)
    (h : ∀ z : ℂ, z ≠ 0 → Matrix.trace (alMonodromy38 α z) = Matrix.trace (alMonodromy38 β z)) :
    ∀ ζ ∈ ball (0 : ℂ) 1, alExteriorG38 α ζ = alExteriorG38 β ζ := by
  have hne : ∀ ζ ∈ ball (0 : ℂ) 1, ζ ≠ 0 → alExteriorG38 α ζ = alExteriorG38 β ζ := by
    intro ζ hζ h0
    obtain ⟨_, r1, n1⟩ := alExteriorG38_multiplier hα hζ h0
    obtain ⟨_, r2, n2⟩ := alExteriorG38_multiplier hβ hζ h0
    rw [← h ζ⁻¹ (inv_ne_zero h0)] at r2
    set W1 := (ζ ^ L)⁻¹ * alExteriorG38 α ζ with hW1
    set W2 := (ζ ^ L)⁻¹ * alExteriorG38 β ζ with hW2
    set t := Matrix.trace (alMonodromy38 α ζ⁻¹)
    have hfac : (W1 - W2) * (W1 + W2 - t) = 0 := by linear_combination r1 - r2
    have hW : W1 = W2 := by
      rcases mul_eq_zero.mp hfac with h1 | h1
      · exact sub_eq_zero.mp h1
      · exfalso
        have hprod : W1 * W2 = 1 := by
          have : W2 = t - W1 := by linear_combination h1
          rw [this]; linear_combination -r1
        have := congrArg norm hprod
        rw [norm_mul, norm_one] at this
        nlinarith [norm_nonneg W1, norm_nonneg W2]
    have hz : ζ ^ L ≠ 0 := pow_ne_zero _ h0
    have := congrArg (fun w => ζ ^ L * w) hW
    simp only [hW1, hW2] at this
    rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hz, one_mul, one_mul] at this
  intro ζ hζ
  by_cases h0 : ζ = 0
  · subst h0
    have c1 : ContinuousAt (alExteriorG38 α) 0 :=
      (alExteriorG38_analytic hα).continuousOn.continuousAt (isOpen_ball.mem_nhds hζ)
    have c2 : ContinuousAt (alExteriorG38 β) 0 :=
      (alExteriorG38_analytic hβ).continuousOn.continuousAt (isOpen_ball.mem_nhds hζ)
    have heq : alExteriorG38 α =ᶠ[𝓝[≠] (0 : ℂ)] alExteriorG38 β := by
      have : ∀ᶠ x in 𝓝 (0 : ℂ), x ∈ ball (0 : ℂ) 1 := isOpen_ball.mem_nhds hζ
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds this, self_mem_nhdsWithin] with x hx hx0
      exact hne x hx hx0
    exact tendsto_nhds_unique (c1.tendsto.mono_left nhdsWithin_le_nhds |>.congr' heq)
      (c2.tendsto.mono_left nhdsWithin_le_nhds)
  · exact hne ζ hζ h0

open Metric in
theorem alMass38_eq_of_trace38 {α β : ZMod L → ℂ} (hα : IsALField38 α) (hβ : IsALField38 β)
    (h : ∀ z : ℂ, z ≠ 0 → Matrix.trace (alMonodromy38 α z) = Matrix.trace (alMonodromy38 β z)) :
    alMass38 L α = alMass38 L β := by
  have hG := alExteriorG38_eq_of_trace38 hα hβ h 0 (mem_ball_self one_pos)
  rw [alExteriorG38_zero hα, alExteriorG38_zero hβ] at hG
  have := Real.exp_injective (Complex.ofReal_injective hG)
  linarith

open Metric in
theorem alC38_eq_of_trace38 {α β : ZMod L → ℂ} (hα : IsALField38 α) (hβ : IsALField38 β)
    (h : ∀ z : ℂ, z ≠ 0 → Matrix.trace (alMonodromy38 α z) = Matrix.trace (alMonodromy38 β z))
    (k : ℕ) : alC38 α k = alC38 β k := by
  have hG := alExteriorG38_eq_of_trace38 hα hβ h
  have hM := alMass38_eq_of_trace38 hα hβ h
  have sα := alLog38_spec hα
  have sβ := alLog38_spec hβ
  have heq : ∀ ζ ∈ ball (0 : ℂ) 1, alLog38 α ζ = alLog38 β ζ :=
    NlsGge.Analysis.log_unique_ball38 (alExteriorG38_analytic hα).differentiableOn
      (fun ζ hζ => alExteriorG38_ne_zero hα hζ) sα.1.differentiableOn sβ.1.differentiableOn
      sα.2.1 (fun ζ hζ => (sβ.2.1 ζ hζ).trans (hG ζ hζ).symm)
      (by rw [sα.2.2.1, sβ.2.2.1, hM])
  have hev : alLog38 α =ᶠ[nhds (0 : ℂ)] alLog38 β :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self one_pos)) heq
  unfold alC38
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    (hev.iteratedFDeriv ℂ (2 * k)).eq_of_nhds]

/-- Main conservation: `t(z)` is constant along `X_{H_d}`-integral curves in the polydisk. -/
theorem trace_alMonodromy_const38 {U : Set ℝ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {γ : ℝ → ZMod L → ℂ}
    (hγ : ∀ t ∈ U, IsALField38 (γ t) ∧
      HasDerivAt γ (alX38 NlsGge.HierarchyRiccati.Core.alHd (γ t)) t)
    {z : ℂ} (hz : z ≠ 0) {s t : ℝ} (hs : s ∈ U) (ht : t ∈ U) :
    Matrix.trace (alMonodromy38 (γ s) z) = Matrix.trace (alMonodromy38 (γ t) z) := by
  have hd : ∀ τ ∈ U, HasDerivAt (fun τ => Matrix.trace (alMonodromy38 (γ τ) z)) 0 τ := by
    intro τ hτ
    obtain ⟨hα, hγ'⟩ := hγ τ hτ
    rw [alX38_alHd hα] at hγ'
    exact hasDerivAt_trace_alMonodromy38 hz hα hγ'
  exact hU.is_const_of_deriv_eq_zero hUc
    (fun τ hτ => (hd τ hτ).differentiableAt.differentiableWithinAt)
    (fun τ hτ => (hd τ hτ).deriv) hs ht

theorem alMass_const38 {U : Set ℝ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {γ : ℝ → ZMod L → ℂ}
    (hγ : ∀ t ∈ U, IsALField38 (γ t) ∧
      HasDerivAt γ (alX38 NlsGge.HierarchyRiccati.Core.alHd (γ t)) t)
    {s t : ℝ} (hs : s ∈ U) (ht : t ∈ U) : alMass38 L (γ s) = alMass38 L (γ t) :=
  alMass38_eq_of_trace38 (hγ s hs).1 (hγ t ht).1 fun _ hz =>
    trace_alMonodromy_const38 hU hUc hγ hz hs ht

theorem alC_const38 {U : Set ℝ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {γ : ℝ → ZMod L → ℂ}
    (hγ : ∀ t ∈ U, IsALField38 (γ t) ∧
      HasDerivAt γ (alX38 NlsGge.HierarchyRiccati.Core.alHd (γ t)) t)
    {s t : ℝ} (hs : s ∈ U) (ht : t ∈ U) (k : ℕ) : alC38 (γ s) k = alC38 (γ t) k :=
  alC38_eq_of_trace38 (hγ s hs).1 (hγ t ht).1 (fun _ hz =>
    trace_alMonodromy_const38 hU hUc hγ hz hs ht) k

theorem alK_const38 {U : Set ℝ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {γ : ℝ → ZMod L → ℂ}
    (hγ : ∀ t ∈ U, IsALField38 (γ t) ∧
      HasDerivAt γ (alX38 NlsGge.HierarchyRiccati.Core.alHd (γ t)) t)
    {s t : ℝ} (hs : s ∈ U) (ht : t ∈ U) (j : ℕ) : alK38 (γ s) j = alK38 (γ t) j := by
  unfold alK38
  rw [alMass_const38 hU hUc hγ hs ht]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [alC_const38 hU hUc hγ hs ht k]

open NlsGge.HierarchyRiccati.Core in
theorem alHd_eq_alK38_one (hL : 3 ≤ L) {α : ZMod L → ℂ} (hα : IsALField38 α) :
    alHd α = alK38 α 1 := by
  rw [alK38_one, alC38_one38 hL hα]
  simp [alHd, alMd, alR, alMass38, alC1]

open NlsGge.HierarchyRiccati.Core in
theorem alKd_eq_alK38_two (hL : 3 ≤ L) {α : ZMod L → ℂ} (hα : IsALField38 α) :
    alKd α = alK38 α 2 := by
  simp only [alK38, alKd]
  rw [Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.sum_singleton,
    alC38_one38 hL hα, alC38_two38 hL hα]
  simp [alMd, alR, alMass38, alC1, alC2, Nat.choose]
  ring

open NlsGge.HierarchyRiccati.Core in
theorem alHd_const38 (hL : 3 ≤ L) {U : Set ℝ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {γ : ℝ → ZMod L → ℂ}
    (hγ : ∀ t ∈ U, IsALField38 (γ t) ∧ HasDerivAt γ (alX38 alHd (γ t)) t)
    {s t : ℝ} (hs : s ∈ U) (ht : t ∈ U) : alHd (γ s) = alHd (γ t) := by
  rw [alHd_eq_alK38_one hL (hγ s hs).1, alHd_eq_alK38_one hL (hγ t ht).1]
  exact alK_const38 hU hUc hγ hs ht 1

open NlsGge.HierarchyRiccati.Core in
theorem alKd_const38 (hL : 3 ≤ L) {U : Set ℝ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {γ : ℝ → ZMod L → ℂ}
    (hγ : ∀ t ∈ U, IsALField38 (γ t) ∧ HasDerivAt γ (alX38 alHd (γ t)) t)
    {s t : ℝ} (hs : s ∈ U) (ht : t ∈ U) : alKd (γ s) = alKd (γ t) := by
  rw [alKd_eq_alK38_two hL (hγ s hs).1, alKd_eq_alK38_two hL (hγ t ht).1]
  exact alK_const38 hU hUc hγ hs ht 2

/-! ### Bracket form -/

lemma differentiableAt_alTransfer38 (z : ℂ) {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableAt ℝ (fun x : ℂ => alTransfer38 x z) a := by
  have hpos : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hn : DifferentiableAt ℝ (fun x : ℂ => 1 - ‖x‖ ^ 2) a :=
    (differentiableAt_const _).sub
      ((contDiff_norm_sq ℝ : ContDiff ℝ 1 fun z : ℂ => ‖z‖ ^ 2).differentiable one_ne_zero _)
  have hs : DifferentiableAt ℝ (fun x : ℂ => (((Real.sqrt (1 - ‖x‖ ^ 2) : ℝ)) : ℂ)⁻¹) a := by
    have h1 := hn.sqrt hpos.ne'
    have h2 : DifferentiableAt ℝ (fun x : ℂ => (((Real.sqrt (1 - ‖x‖ ^ 2) : ℝ)) : ℂ)) a :=
      Complex.ofRealCLM.differentiableAt.comp a h1
    exact h2.inv (by exact_mod_cast (Real.sqrt_pos.mpr hpos).ne')
  have hm : DifferentiableAt ℝ (fun x : ℂ => (!![z, x; star x, z⁻¹] : Matrix (Fin 2) (Fin 2) ℂ)) a := by
    have e : (fun x : ℂ => (!![z, x; star x, z⁻¹] : Matrix (Fin 2) (Fin 2) ℂ)) =
        fun x => (!![z, 0; 0, z⁻¹] : Matrix (Fin 2) (Fin 2) ℂ) + x • (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)
          + star x • (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
      funext x; ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [e]
    exact ((differentiableAt_const _).add (differentiableAt_id.smul_const _)).add
      ((differentiableAt_id.star).smul_const _)
  exact hs.smul hm

lemma differentiableAt_alPartial38 (z : ℂ) {α : ZMod L → ℂ} (hα : IsALField38 α) (k : ℕ) :
    DifferentiableAt ℝ (fun β : ZMod L → ℂ => alPartial38 β z k) α := by
  induction k with
  | zero => simp [alPartial38]
  | succ k ih =>
    have hp : DifferentiableAt ℝ (fun β : ZMod L → ℂ => β (k : ZMod L)) α := by fun_prop
    have hA := (differentiableAt_alTransfer38 z (hα (k : ZMod L))).comp α hp
    exact hA.mul ih

lemma differentiableAt_trace_alMonodromy38 (z : ℂ) {α : ZMod L → ℂ} (hα : IsALField38 α) :
    DifferentiableAt ℝ (fun β : ZMod L → ℂ => Matrix.trace (alMonodromy38 β z)) α := by
  let T : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (Fin 2) ℂ ℂ).restrictScalars ℝ)
  have e : (fun β : ZMod L → ℂ => Matrix.trace (alMonodromy38 β z)) =
      T ∘ (fun β : ZMod L → ℂ => alPartial38 β z L) := by
    funext β; simp [T, alMonodromy38]
  rw [e]
  exact T.differentiableAt.comp α (differentiableAt_alPartial38 z hα L)

open NlsGge.HierarchyRiccati.Core in
/-- Isospectrality in bracket form: `{Re t(z), H_d} = 0` and `{Im t(z), H_d} = 0`
on the polydisk, `z ≠ 0`. -/
theorem alBracket_trace_alHd38 {α : ZMod L → ℂ} (hα : IsALField38 α) {z : ℂ} (hz : z ≠ 0) :
    alBracket38 (fun β => (Matrix.trace (alMonodromy38 β z)).re) alHd α = 0 ∧
    alBracket38 (fun β => (Matrix.trace (alMonodromy38 β z)).im) alHd α = 0 := by
  set γ : ℝ → ZMod L → ℂ := fun s => α + s • alX38 alHd α with hγdef
  have hγ0 : γ 0 = α := by simp [hγdef]
  have hγ : HasDerivAt γ (alX38 alHd (γ 0)) 0 := by
    rw [hγ0]
    have h0 := ((hasDerivAt_id (0 : ℝ)).smul_const (alX38 alHd α)).const_add α
    have h1 : HasDerivAt (fun s : ℝ => α + s • alX38 alHd α) ((1 : ℝ) • alX38 alHd α) 0 := h0
    exact h1.congr_deriv (one_smul _ _)
  have hγ' : HasDerivAt γ (alXd38 (γ 0)) 0 := by rw [hγ0, ← alX38_alHd hα]; rw [hγ0] at hγ; exact hγ
  have htr := hasDerivAt_trace_alMonodromy38 (γ := γ) (t := 0) hz (by rw [hγ0]; exact hα) hγ'
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) htr
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) htr
  have dre : DifferentiableAt ℝ (fun β : ZMod L → ℂ => (Matrix.trace (alMonodromy38 β z)).re) (γ 0) := by
    rw [hγ0]; exact Complex.reCLM.differentiableAt.comp α (differentiableAt_trace_alMonodromy38 z hα)
  have dim : DifferentiableAt ℝ (fun β : ZMod L → ℂ => (Matrix.trace (alMonodromy38 β z)).im) (γ 0) := by
    rw [hγ0]; exact Complex.imCLM.differentiableAt.comp α (differentiableAt_trace_alMonodromy38 z hα)
  have b1 := alBracket_deriv38 dre hγ
  have b2 := alBracket_deriv38 dim hγ
  rw [hγ0] at b1 b2
  have hre' : HasDerivAt (fun s => (Matrix.trace (alMonodromy38 (γ s) z)).re) 0 0 :=
    hre.congr_deriv (map_zero _)
  have him' : HasDerivAt (fun s => (Matrix.trace (alMonodromy38 (γ s) z)).im) 0 0 :=
    him.congr_deriv (map_zero _)
  exact ⟨b1.unique hre', b2.unique him'⟩

#check @alX38_alHd
#check @hasDerivAt_trace_alMonodromy38
#check @trace_alMonodromy_const38
#check @alBracket_trace_alHd38
#check @alMass_const38
#check @alC_const38
#check @alK_const38
#check @alHd_const38
#check @alKd_const38
#check @alExteriorG38_eq_of_trace38
#print axioms alX38_alHd
#print axioms hasDerivAt_trace_alMonodromy38
#print axioms trace_alMonodromy_const38
#print axioms alBracket_trace_alHd38
#print axioms alMass_const38
#print axioms alC_const38
#print axioms alK_const38
#print axioms alHd_const38
#print axioms alKd_const38
#print axioms alExteriorG38_eq_of_trace38

end NlsGge.AblowitzLadik
end
