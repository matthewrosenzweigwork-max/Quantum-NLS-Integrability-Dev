import NlsGge.Spectral.MatrixNormalFormUniformBox38V1
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.SpectralFoundations

/-! # UB-B2: generic dissipative normal form (pure analysis)

`Λ = diag(0, μ)` with `Re μ ≤ 0`, `expΛ τ = diag(1, exp(μ τ))`.  Norm: `rowSumNorm2`
(maximal row sum), conventions as in `MatrixNormalFormUniformBox38V1`. -/

/-- `Λ = diag(0, μ)`. -/
def dnfLam (μ : ℂ) : Mat2 := !![0, 0; 0, μ]

/-- `expΛ τ = diag(1, exp(μ τ))`. -/
def dnfExp (μ : ℂ) (τ : ℝ) : Mat2 := !![1, 0; 0, Complex.exp (μ * τ)]

theorem dnfExp_zero (μ : ℂ) : dnfExp μ 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dnfExp]

theorem dnfExp_comm (μ : ℂ) (τ : ℝ) : dnfExp μ τ * dnfLam μ = dnfLam μ * dnfExp μ τ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dnfExp, dnfLam, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem rowSumNorm2_dnfExp_le (μ : ℂ) (hμ : μ.re ≤ 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    rowSumNorm2 (dnfExp μ τ) ≤ 1 := by
  have h : ‖Complex.exp (μ * τ)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.2
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  rw [rowSumNorm2_le_iff]
  intro i
  fin_cases i <;> simp [dnfExp, h]

/-! ## Entrywise matrix derivatives -/

/-- Entrywise derivative of a matrix path at a point. -/
def MatHasDerivAt (F : ℝ → Mat2) (F' : Mat2) (s : ℝ) : Prop :=
  ∀ i j : Fin 2, HasDerivAt (fun r => F r i j) (F' i j) s

theorem MatHasDerivAt.mul {P Q : ℝ → Mat2} {P' Q' : Mat2} {s : ℝ}
    (hP : MatHasDerivAt P P' s) (hQ : MatHasDerivAt Q Q' s) :
    MatHasDerivAt (fun r => P r * Q r) (P' * Q s + P s * Q') s := by
  intro i j
  have key := ((hP i 0).mul (hQ 0 j)).add ((hP i 1).mul (hQ 1 j))
  have e : (fun r => (P r * Q r) i j) = fun r => P r i 0 * Q r 0 j + P r i 1 * Q r 1 j := by
    funext r
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
  rw [e]
  refine key.congr_deriv ?_
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem MatHasDerivAt.unique {F : ℝ → Mat2} {F1 F2 : Mat2} {s : ℝ}
    (h1 : MatHasDerivAt F F1 s) (h2 : MatHasDerivAt F F2 s) : F1 = F2 := by
  ext i j
  exact (h1 i j).unique (h2 i j)

theorem MatHasDerivAt.const (C : Mat2) (s : ℝ) : MatHasDerivAt (fun _ => C) 0 s := by
  intro i j
  simpa using hasDerivAt_const s (C i j)

theorem MatHasDerivAt.congr_of_eventuallyEq {F G : ℝ → Mat2} {F' : Mat2} {s : ℝ}
    (h : MatHasDerivAt F F' s) (hev : G =ᶠ[nhds s] F) : MatHasDerivAt G F' s := by
  intro i j
  exact (h i j).congr_of_eventuallyEq (hev.mono fun r hr => by
    show G r i j = F r i j
    rw [hr])

/-! ## Scalar absolute-continuity helpers -/

theorem dnf_ac_of_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) :
    AbsolutelyContinuousOnInterval f 0 1 := by
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (s := Set.uIcc (0:ℝ) 1)
    one_ne_zero (convex_uIcc 0 1) isCompact_uIcc
  exact hK.absolutelyContinuousOnInterval

theorem dnf_ac_mul {f g : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hg : AbsolutelyContinuousOnInterval g 0 1) :
    AbsolutelyContinuousOnInterval (fun s => f s * g s) 0 1 := by
  simpa only [Pi.smul_apply, smul_eq_mul] using! hf.smul hg

theorem dnf_ac_add {f g : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hg : AbsolutelyContinuousOnInterval g 0 1) :
    AbsolutelyContinuousOnInterval (fun s => f s + g s) 0 1 :=
  hf.add hg

theorem dnf_ac_sub {f g : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hg : AbsolutelyContinuousOnInterval g 0 1) :
    AbsolutelyContinuousOnInterval (fun s => f s - g s) 0 1 :=
  hf.sub hg

theorem dnf_ac_neg {f : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f 0 1) :
    AbsolutelyContinuousOnInterval (fun s => -f s) 0 1 :=
  hf.neg

theorem dnf_dist_inv_le {x y : ℂ} {c : ℝ} (hc : 0 < c) (hx : c ≤ ‖x‖) (hy : c ≤ ‖y‖) :
    dist x⁻¹ y⁻¹ ≤ c⁻¹ ^ 2 * dist x y := by
  have hx0 : x ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hc hx)
  have hy0 : y ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hc hy)
  rw [dist_eq_norm, dist_eq_norm]
  have e : x⁻¹ - y⁻¹ = (y - x) * (x⁻¹ * y⁻¹) := by
    field_simp
  rw [e, norm_mul, norm_mul, norm_inv, norm_inv, norm_sub_rev]
  have h : ‖x‖⁻¹ * ‖y‖⁻¹ ≤ c⁻¹ ^ 2 := by
    rw [sq]
    exact mul_le_mul (inv_anti₀ hc hx) (inv_anti₀ hc hy) (by positivity) (by positivity)
  have hn := norm_nonneg (x - y)
  nlinarith

/-- Reciprocal of an absolutely continuous complex function bounded away from zero. -/
theorem dnf_ac_inv {f : ℝ → ℂ} {c : ℝ} (hc : 0 < c) (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hlow : ∀ x ∈ Set.uIcc (0:ℝ) 1, c ≤ ‖f x‖) :
    AbsolutelyContinuousOnInterval (fun x => (f x)⁻¹) 0 1 := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  apply squeeze_zero' ?_ ?_ (by simpa using hf.const_mul (c⁻¹ ^ 2))
  · exact Filter.Eventually.of_forall <| fun _ ↦ Finset.sum_nonneg (fun i hi ↦ dist_nonneg)
  rw [eventually_inf_principal]
  filter_upwards with E hE
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  simp only [AbsolutelyContinuousOnInterval.disjWithin, Set.mem_ofPred_eq] at hE
  exact dnf_dist_inv_le hc (hlow _ (hE.1 i hi).1) (hlow _ (hE.1 i hi).2)

/-! ## The explicit inverse `(1 + B)⁻¹` -/

/-- `det (1 + B r)`. -/
def dnfDet (B : ℝ → Mat2) (r : ℝ) : ℂ :=
  (1 + B r 0 0) * (1 + B r 1 1) - B r 0 1 * B r 1 0

/-- Adjugate formula for `(1 + B r)⁻¹`. -/
def dnfR (B : ℝ → Mat2) (r : ℝ) : Mat2 :=
  !![(dnfDet B r)⁻¹ * (1 + B r 1 1), -((dnfDet B r)⁻¹ * B r 0 1);
     -((dnfDet B r)⁻¹ * B r 1 0), (dnfDet B r)⁻¹ * (1 + B r 0 0)]

theorem dnfR_mul_left (B : ℝ → Mat2) (r : ℝ) (hd : dnfDet B r ≠ 0) :
    dnfR B r * (1 + B r) = 1 := by
  have hk : (dnfDet B r)⁻¹ * dnfDet B r = 1 := inv_mul_cancel₀ hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [dnfR, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.one_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue] <;>
    generalize (dnfDet B r)⁻¹ = k at hk ⊢ <;> unfold dnfDet at hk <;> simp <;>
    first | ring1 | linear_combination hk

theorem dnfR_mul_right (B : ℝ → Mat2) (r : ℝ) (hd : dnfDet B r ≠ 0) :
    (1 + B r) * dnfR B r = 1 := by
  have hk : (dnfDet B r)⁻¹ * dnfDet B r = 1 := inv_mul_cancel₀ hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [dnfR, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.one_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue] <;>
    generalize (dnfDet B r)⁻¹ = k at hk ⊢ <;> unfold dnfDet at hk <;> simp <;>
    first | ring1 | linear_combination hk

theorem dnfDet_norm_ge (B : ℝ → Mat2) (r : ℝ) {β : ℝ} (hβ : β ≤ 1/4)
    (hB : rowSumNorm2 (B r) ≤ β) : 1/4 ≤ ‖dnfDet B r‖ := by
  have r0 := le_trans (rowSumNorm2_row_le (B r) 0) hB
  have r1 := le_trans (rowSumNorm2_row_le (B r) 1) hB
  have na := norm_nonneg (B r 0 0)
  have nb := norm_nonneg (B r 0 1)
  have nc := norm_nonneg (B r 1 0)
  have ne := norm_nonneg (B r 1 1)
  have ha : 1 - ‖B r 0 0‖ ≤ ‖1 + B r 0 0‖ := by
    have := norm_sub_le (1 + B r 0 0) (B r 0 0)
    simp only [add_sub_cancel_right, norm_one] at this
    linarith
  have he : 1 - ‖B r 1 1‖ ≤ ‖1 + B r 1 1‖ := by
    have := norm_sub_le (1 + B r 1 1) (B r 1 1)
    simp only [add_sub_cancel_right, norm_one] at this
    linarith
  have hprod : (1 - ‖B r 0 0‖) * (1 - ‖B r 1 1‖) ≤ ‖1 + B r 0 0‖ * ‖1 + B r 1 1‖ :=
    mul_le_mul ha he (by linarith) (norm_nonneg _)
  have h34 : (3/4 : ℝ) * (3/4) ≤ (1 - ‖B r 0 0‖) * (1 - ‖B r 1 1‖) :=
    mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  have hbc : ‖B r 0 1‖ * ‖B r 1 0‖ ≤ (1/4) * (1/4) :=
    mul_le_mul (by linarith) (by linarith) nc (by norm_num)
  have htri := norm_sub_norm_le ((1 + B r 0 0) * (1 + B r 1 1)) (B r 0 1 * B r 1 0)
  rw [norm_mul, norm_mul] at htri
  unfold dnfDet
  linarith

/-! ## Entrywise continuity / integrability helpers -/

theorem EntryCont.mul {P Q : ℝ → Mat2} (hP : EntryCont P) (hQ : EntryCont Q) :
    EntryCont (fun s => P s * Q s) := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hP i 0).mul (hQ 0 j)).add ((hP i 1).mul (hQ 1 j))

theorem EntryII.sub {P Q : ℝ → Mat2} (hP : EntryII P) (hQ : EntryII Q) :
    EntryII (fun s => P s - Q s) := by
  intro i j
  simpa only [Matrix.sub_apply] using (hP i j).sub (hQ i j)

theorem dnf_ae_ne (a : ℝ) : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ a := by
  have := measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton (a := a))
  filter_upwards [this] with s hs
  simpa using hs

/-! ## The propagator `expΛ (t - r)` as a function of `r` -/

theorem dnfExp_shift_hasDeriv (μ : ℂ) (t s : ℝ) :
    MatHasDerivAt (fun r => dnfExp μ (t - r)) (-(dnfLam μ * dnfExp μ (t - s))) s := by
  have h11 : HasDerivAt (fun r : ℝ => Complex.exp (μ * ((t - r : ℝ) : ℂ)))
      (-(μ * Complex.exp (μ * ((t - s : ℝ) : ℂ)))) s := by
    have h1 : HasDerivAt (fun r : ℝ => ((t - r : ℝ) : ℂ)) ((-1 : ℝ) : ℂ) s :=
      ((hasDerivAt_id s).const_sub t).ofReal_comp
    have h2 := (h1.const_mul μ).cexp
    convert h2 using 1
    push_cast
    ring
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [dnfExp, dnfLam] using hasDerivAt_const s (1:ℂ)
  · simpa [dnfExp, dnfLam, Matrix.mul_apply] using hasDerivAt_const s (0:ℂ)
  · simpa [dnfExp, dnfLam, Matrix.mul_apply] using hasDerivAt_const s (0:ℂ)
  · have e : (fun r => dnfExp μ (t - r) 1 1)
        = fun r : ℝ => Complex.exp (μ * ((t - r : ℝ) : ℂ)) := by
      funext r
      simp [dnfExp]
    show HasDerivAt (fun r => dnfExp μ (t - r) 1 1) _ s
    rw [e]
    convert h11 using 1
    simp [dnfExp, dnfLam]

theorem dnfExp_shift_ac (μ : ℂ) (t : ℝ) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun r => dnfExp μ (t - r) i j) 0 1 := by
  apply dnf_ac_of_contDiff
  have hof : ContDiff ℝ 1 (fun r : ℝ => (r : ℂ)) := Complex.ofRealCLM.contDiff
  fin_cases i <;> fin_cases j <;> simp [dnfExp] <;> fun_prop

/-! ## Main theorem -/

/-- **UB-B2: dissipative normal-form estimate.**  Norm `rowSumNorm2` (maximal row sum).
`Λ = diag(0, μ)` with `Re μ ≤ 0`, `expΛ τ = diag(1, exp(μ τ))`.
Hypotheses: `Φ, B` entrywise absolutely continuous on `[0,1]`; a.e. on `[0,1]`,
`Φ' = (Λ + V) Φ` and `B' = W` (entrywise `HasDerivAt`); `V, W` entrywise interval integrable;
`Φ 0 = 1`; a.e. on `[0,1]`, `Λ B - B Λ + V = 0`; `‖B t‖ ≤ β` on `[0,1]`;
`∫⁻_{[0,1]} ofReal ‖V B - W‖ ≤ ofReal η`; `β ≤ 1/4`, `0 ≤ η ≤ 1/8`.
Conclusion: for every `t ∈ [0,1]`, `‖Φ t - expΛ t‖ ≤ (8/3) (β + η)` and `‖Φ t‖ ≤ 2`. -/
theorem dissipativeNormalForm_bound
    (μ : ℂ) (Φ B V W : ℝ → Mat2) (β η : ℝ)
    (hμ : μ.re ≤ 0)
    (hΦac : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun s => Φ s i j) 0 1)
    (hBac : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun s => B s i j) 0 1)
    (hV : ∀ i j : Fin 2, IntervalIntegrable (fun s => V s i j) volume 0 1)
    (hW : ∀ i j : Fin 2, IntervalIntegrable (fun s => W s i j) volume 0 1)
    (hΦder : ∀ᵐ s ∂volume, s ∈ Set.Icc (0:ℝ) 1 →
      ∀ i j : Fin 2, HasDerivAt (fun r => Φ r i j) (((dnfLam μ + V s) * Φ s) i j) s)
    (hBder : ∀ᵐ s ∂volume, s ∈ Set.Icc (0:ℝ) 1 →
      ∀ i j : Fin 2, HasDerivAt (fun r => B r i j) (W s i j) s)
    (hΦ0 : Φ 0 = 1)
    (hcomm : ∀ᵐ s ∂volume, s ∈ Set.Icc (0:ℝ) 1 →
      dnfLam μ * B s - B s * dnfLam μ + V s = 0)
    (hB : ∀ t ∈ Set.Icc (0:ℝ) 1, rowSumNorm2 (B t) ≤ β)
    (hη : ∫⁻ s in Set.Icc (0:ℝ) 1,
        ENNReal.ofReal (rowSumNorm2 (V s * B s - W s)) ≤ ENNReal.ofReal η)
    (hβ : β ≤ 1/4) (hη0 : 0 ≤ η) (hη1 : η ≤ 1/8) :
    ∀ t ∈ Set.Icc (0:ℝ) 1,
      rowSumNorm2 (Φ t - dnfExp μ t) ≤ 8/3 * (β + η) ∧ rowSumNorm2 (Φ t) ≤ 2 := by
  have huI : Set.uIcc (0:ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have h0I : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hβ0 : 0 ≤ β := le_trans (rowSumNorm2_nonneg _) (hB 0 h0I)
  set A : ℝ → Mat2 := fun r => 1 + B r with hAdef
  set R : ℝ → Mat2 := fun r => dnfR B r with hRdef
  set Ψ : ℝ → Mat2 := fun r => R r * Φ r with hΨdef
  -- determinant and inverse
  have hdet : ∀ r ∈ Set.Icc (0:ℝ) 1, 1/4 ≤ ‖dnfDet B r‖ :=
    fun r hr => dnfDet_norm_ge B r hβ (hB r hr)
  have hdet0 : ∀ r ∈ Set.Icc (0:ℝ) 1, dnfDet B r ≠ 0 := by
    intro r hr h
    have := hdet r hr
    rw [h, norm_zero] at this
    norm_num at this
  have hRA : ∀ r ∈ Set.Icc (0:ℝ) 1, R r * A r = 1 :=
    fun r hr => dnfR_mul_left B r (hdet0 r hr)
  have hAR : ∀ r ∈ Set.Icc (0:ℝ) 1, A r * R r = 1 :=
    fun r hr => dnfR_mul_right B r (hdet0 r hr)
  have hRB : ∀ r ∈ Set.Icc (0:ℝ) 1, R r * B r = 1 - R r := by
    intro r hr
    have := hRA r hr
    simp only [hAdef, mul_add, mul_one] at this
    rw [← this]
    abel
  have hRn : ∀ r ∈ Set.Icc (0:ℝ) 1, rowSumNorm2 (R r) ≤ 4/3 := by
    intro r hr
    have e : R r = 1 - R r * B r := by rw [hRB r hr]; abel
    have hm := le_trans (rowSumNorm2_mul_le (R r) (B r))
      (mul_le_mul_of_nonneg_left (hB r hr) (rowSumNorm2_nonneg (R r)))
    have h1 : rowSumNorm2 (R r) ≤ 1 + rowSumNorm2 (R r) * β := by
      have := rowSumNorm2_sub_le 1 (R r * B r)
      rw [← e, rowSumNorm2_one] at this
      linarith
    have := rowSumNorm2_nonneg (R r)
    nlinarith
  -- absolute continuity / continuity
  have c1 : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1:ℂ)) 0 1 :=
    dnf_ac_of_contDiff contDiff_const
  have hdetac : AbsolutelyContinuousOnInterval (fun r => dnfDet B r) 0 1 := by
    unfold dnfDet
    exact dnf_ac_sub (dnf_ac_mul (dnf_ac_add c1 (hBac 0 0)) (dnf_ac_add c1 (hBac 1 1)))
      (dnf_ac_mul (hBac 0 1) (hBac 1 0))
  have hinvac := dnf_ac_inv (by norm_num : (0:ℝ) < 1/4) hdetac (by rw [huI]; exact hdet)
  have hRac : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun s => R s i j) 0 1 := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [hRdef, dnfR] using dnf_ac_mul hinvac (dnf_ac_add c1 (hBac 1 1))
    · simpa [hRdef, dnfR] using dnf_ac_neg (dnf_ac_mul hinvac (hBac 0 1))
    · simpa [hRdef, dnfR] using dnf_ac_neg (dnf_ac_mul hinvac (hBac 1 0))
    · simpa [hRdef, dnfR] using dnf_ac_mul hinvac (dnf_ac_add c1 (hBac 0 0))
  have hΨac : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun s => Ψ s i j) 0 1 :=
    absolutelyContinuous_mat2_mul_entry hRac hΦac
  have hRc : EntryCont R := fun i j => (hRac i j).continuousOn
  have hBc : EntryCont B := fun i j => (hBac i j).continuousOn
  have hΨc : EntryCont Ψ := fun i j => (hΨac i j).continuousOn
  have hVBW : EntryII (fun s => V s * B s - W s) := (EntryII.mul_cont hV hBc).sub hW
  -- the interaction-picture derivative of Ψ
  have hΨder : ∀ᵐ s ∂volume, s ∈ Set.Icc (0:ℝ) 1 →
      MatHasDerivAt Ψ (dnfLam μ * Ψ s + R s * (V s * B s - W s) * Ψ s) s := by
    filter_upwards [hΦder, hBder, hcomm, dnf_ae_ne 0, dnf_ae_ne 1]
      with s hΦs hBs hcs hs0 hs1 hmem
    have hsI : s ∈ Set.Ioo (0:ℝ) 1 :=
      ⟨lt_of_le_of_ne hmem.1 (Ne.symm hs0), lt_of_le_of_ne hmem.2 hs1⟩
    have hb := hBs hmem
    have hφ : MatHasDerivAt Φ ((dnfLam μ + V s) * Φ s) s := hΦs hmem
    have hc := hcs hmem
    have hB00 : DifferentiableAt ℝ (fun r => B r 0 0) s := (hb 0 0).differentiableAt
    have hB01 : DifferentiableAt ℝ (fun r => B r 0 1) s := (hb 0 1).differentiableAt
    have hB10 : DifferentiableAt ℝ (fun r => B r 1 0) s := (hb 1 0).differentiableAt
    have hB11 : DifferentiableAt ℝ (fun r => B r 1 1) s := (hb 1 1).differentiableAt
    have hdD : DifferentiableAt ℝ (fun r => dnfDet B r) s := by
      unfold dnfDet
      fun_prop
    have hiD : DifferentiableAt ℝ (fun r => (dnfDet B r)⁻¹) s := hdD.inv (hdet0 s hmem)
    have hRd : ∀ i j : Fin 2, DifferentiableAt ℝ (fun r => R r i j) s := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp only [hRdef, dnfR] <;> simp <;> fun_prop
    set R' : Mat2 := Matrix.of fun i j => deriv (fun r => R r i j) s with hR'def
    have hR : MatHasDerivAt R R' s := fun i j => by
      simpa [hR'def] using (hRd i j).hasDerivAt
    have hA : MatHasDerivAt A (W s) s := by
      intro i j
      simpa [hAdef] using (hb i j).const_add ((1:Mat2) i j)
    have hRA' : R' * A s + R s * W s = 0 := by
      have h1 := hR.mul hA
      have hev : (fun r => R r * A r) =ᶠ[nhds s] fun _ => (1:Mat2) := by
        filter_upwards [Ioo_mem_nhds hsI.1 hsI.2] with r hr
        exact hRA r ⟨hr.1.le, hr.2.le⟩
      have h2 := (MatHasDerivAt.const (1:Mat2) s).congr_of_eventuallyEq hev
      exact h1.unique h2
    have hR'eq : R' = -(R s * W s * R s) := by
      calc R' = R' * (A s * R s) := by rw [hAR s hmem, mul_one]
        _ = (R' * A s + R s * W s) * R s - R s * W s * R s := by noncomm_ring
        _ = -(R s * W s * R s) := by rw [hRA', zero_mul, zero_sub]
    have key1 : (dnfLam μ + V s) * A s = A s * dnfLam μ + V s * B s := by
      have e : dnfLam μ * B s + V s = B s * dnfLam μ := by
        rw [← sub_eq_zero, ← hc]
        abel
      simp only [hAdef, mul_add, add_mul, mul_one, one_mul]
      rw [← e]
      abel
    have key2 : R s * (dnfLam μ + V s) = dnfLam μ * R s + R s * (V s * B s) * R s := by
      calc R s * (dnfLam μ + V s) = R s * ((dnfLam μ + V s) * (A s * R s)) := by
            rw [hAR s hmem, mul_one]
        _ = R s * ((dnfLam μ + V s) * A s) * R s := by simp only [mul_assoc]
        _ = R s * (A s * dnfLam μ + V s * B s) * R s := by rw [key1]
        _ = (R s * A s) * dnfLam μ * R s + R s * (V s * B s) * R s := by noncomm_ring
        _ = _ := by rw [hRA s hmem, one_mul]
    have h3 := hR.mul hφ
    have hval : R' * Φ s + R s * ((dnfLam μ + V s) * Φ s)
        = dnfLam μ * Ψ s + R s * (V s * B s - W s) * Ψ s := by
      rw [hR'eq, ← mul_assoc (R s), key2]
      simp only [hΨdef]
      noncomm_ring
    rw [← hval]
    exact h3
  -- the majorant
  set h : ℝ → ℝ := fun s => rowSumNorm2 (V s * B s - W s) with hhdef
  have hhi : IntervalIntegrable h volume 0 1 := EntryII.rowSumNorm2 hVBW
  have hhnn : ∀ s, 0 ≤ h s := fun s => rowSumNorm2_nonneg _
  have hint : ∫ s in (0:ℝ)..1, h s ≤ η := integral_le_of_lintegral_le hhi hhnn hη0 hη
  -- supremum of ‖Ψ‖ on [0,1]
  have hΨcont : ContinuousOn (fun s => rowSumNorm2 (Ψ s)) (Set.Icc (0:ℝ) 1) := by
    unfold rowSumNorm2
    have hc : ∀ i j : Fin 2, ContinuousOn (fun s => ‖Ψ s i j‖) (Set.Icc (0:ℝ) 1) :=
      fun i j => by rw [← huI]; exact (hΨc i j).norm
    exact ContinuousOn.sup ((hc 0 0).add (hc 0 1)) ((hc 1 0).add (hc 1 1))
  obtain ⟨t0, ht0, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.2 (zero_le_one : (0:ℝ) ≤ 1)) hΨcont
  set Mx : ℝ := rowSumNorm2 (Ψ t0) with hMxdef
  have hMxnn : 0 ≤ Mx := rowSumNorm2_nonneg _
  have hMx : ∀ t ∈ Set.Icc (0:ℝ) 1, rowSumNorm2 (Ψ t) ≤ Mx := fun t ht => hmax ht
  -- Duhamel estimate
  have hduh : ∀ t ∈ Set.Icc (0:ℝ) 1,
      rowSumNorm2 (Ψ t - dnfExp μ t * Ψ 0) ≤ η * (4/3 * Mx) := by
    intro t ht
    have hEac := dnfExp_shift_ac μ t
    have hEc : EntryCont (fun r => dnfExp μ (t - r)) := fun i j => (hEac i j).continuousOn
    have hgac := absolutelyContinuous_mat2_mul_entry hEac hΨac
    have hGII : EntryII (fun r => dnfExp μ (t - r) * R r * (V r * B r - W r) * Ψ r) :=
      ((hEc.mul hRc).mul_II hVBW).mul_cont hΨc
    have hgder : ∀ᵐ s ∂volume, s ∈ Set.Icc (0:ℝ) 1 → ∀ i j : Fin 2,
        HasDerivAt (fun r => (dnfExp μ (t - r) * Ψ r) i j)
          ((dnfExp μ (t - s) * R s * (V s * B s - W s) * Ψ s) i j) s := by
      filter_upwards [hΨder] with s hs hmem
      have h1 := (dnfExp_shift_hasDeriv μ t s).mul (hs hmem)
      have hv : -(dnfLam μ * dnfExp μ (t - s)) * Ψ s
          + dnfExp μ (t - s) * (dnfLam μ * Ψ s + R s * (V s * B s - W s) * Ψ s)
          = dnfExp μ (t - s) * R s * (V s * B s - W s) * Ψ s := by
        rw [mul_add, ← mul_assoc (dnfExp μ (t - s)) (dnfLam μ), dnfExp_comm]
        noncomm_ring
      rw [hv] at h1
      exact h1
    have hftc := mat2_entry_eq_initial_add_integral hgac hGII hgder t ht
    have heq : Ψ t - dnfExp μ t * Ψ 0
        = matIntegral (fun r => dnfExp μ (t - r) * R r * (V r * B r - W r) * Ψ r) t := by
      ext i j
      have := hftc i j
      simp only [sub_self, dnfExp_zero, one_mul, sub_zero] at this
      simp only [Matrix.sub_apply, matIntegral, Matrix.of_apply]
      rw [this]
      ring
    have hsub : Set.uIcc (0:ℝ) t ⊆ Set.uIcc 0 1 :=
      Set.uIcc_subset_uIcc Set.left_mem_uIcc (by rw [huI]; exact ht)
    have hct : IntervalIntegrable (fun s => h s * (4/3 * Mx)) volume 0 t :=
      (hhi.mono_set hsub).mul_const _
    have h1 := rowSumNorm2_matIntegral_le hGII ht hct (by
      intro s hs
      have hs1 : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs.1, le_trans hs.2 ht.2⟩
      have e1 := rowSumNorm2_dnfExp_le μ hμ (sub_nonneg.2 hs.2)
      have m1 := rowSumNorm2_mul_le (dnfExp μ (t - s)) (R s)
      have m2 := rowSumNorm2_mul_le (dnfExp μ (t - s) * R s) (V s * B s - W s)
      have m3 := rowSumNorm2_mul_le (dnfExp μ (t - s) * R s * (V s * B s - W s)) (Ψ s)
      have r1 := hRn s hs1
      have p1 := hMx s hs1
      have a0 : rowSumNorm2 (dnfExp μ (t - s)) * rowSumNorm2 (R s) ≤ 1 * (4/3) :=
        mul_le_mul e1 r1 (rowSumNorm2_nonneg _) zero_le_one
      have a1 : rowSumNorm2 (dnfExp μ (t - s) * R s) ≤ 4/3 := by linarith
      have a2 : rowSumNorm2 (dnfExp μ (t - s) * R s * (V s * B s - W s)) ≤ 4/3 * h s :=
        le_trans m2 (mul_le_mul_of_nonneg_right a1 (hhnn s))
      have a3 : rowSumNorm2 (dnfExp μ (t - s) * R s * (V s * B s - W s) * Ψ s)
          ≤ 4/3 * h s * Mx :=
        le_trans m3 (mul_le_mul a2 p1 (rowSumNorm2_nonneg _) (mul_nonneg (by norm_num) (hhnn s)))
      calc _ ≤ 4/3 * h s * Mx := a3
        _ = h s * (4/3 * Mx) := by ring)
    have h2 : ∫ s in (0:ℝ)..t, h s * (4/3 * Mx) = (∫ s in (0:ℝ)..t, h s) * (4/3 * Mx) :=
      intervalIntegral.integral_mul_const _ _
    have h3 : ∫ s in (0:ℝ)..t, h s ≤ ∫ s in (0:ℝ)..1, h s :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 (ae_of_all _ hhnn) hhi
    rw [h2] at h1
    rw [heq]
    have h4 : (∫ s in (0:ℝ)..t, h s) * (4/3 * Mx) ≤ η * (4/3 * Mx) :=
      mul_le_mul_of_nonneg_right (le_trans h3 hint) (by positivity)
    linarith
  -- bound on Ψ 0 and on Mx
  have hΨ0 : Ψ 0 = R 0 := by simp only [hΨdef, hΦ0, mul_one]
  have hEΨ0 : ∀ t ∈ Set.Icc (0:ℝ) 1, rowSumNorm2 (dnfExp μ t * Ψ 0) ≤ 4/3 := by
    intro t ht
    have e1 := rowSumNorm2_dnfExp_le μ hμ ht.1
    have m := rowSumNorm2_mul_le (dnfExp μ t) (Ψ 0)
    have a0 : rowSumNorm2 (dnfExp μ t) * rowSumNorm2 (Ψ 0) ≤ 1 * (4/3) := by
      rw [hΨ0]
      exact mul_le_mul e1 (hRn 0 h0I) (rowSumNorm2_nonneg _) zero_le_one
    linarith
  have hMxb : Mx ≤ 8/5 := by
    have e : Ψ t0 = (Ψ t0 - dnfExp μ t0 * Ψ 0) + dnfExp μ t0 * Ψ 0 := by abel
    have h1 := rowSumNorm2_add_le (Ψ t0 - dnfExp μ t0 * Ψ 0) (dnfExp μ t0 * Ψ 0)
    rw [← e] at h1
    have h2 := hduh t0 ht0
    have h3 := hEΨ0 t0 ht0
    have h4 : η * Mx ≤ 1/8 * Mx := mul_le_mul_of_nonneg_right hη1 hMxnn
    have : Mx ≤ η * (4/3 * Mx) + 4/3 := by rw [hMxdef]; linarith
    nlinarith
  -- final estimates
  have hR0B0 : R 0 * B 0 = 1 - R 0 := hRB 0 h0I
  intro t ht
  have hΦt : Φ t = A t * Ψ t := by
    simp only [hΨdef]
    rw [← mul_assoc, hAR t ht, one_mul]
  have hAn : rowSumNorm2 (A t) ≤ 1 + β := by
    have := rowSumNorm2_add_le (1 : Mat2) (B t)
    rw [rowSumNorm2_one] at this
    simp only [hAdef]
    linarith [hB t ht]
  have hAnn := rowSumNorm2_nonneg (A t)
  have hid : Φ t - dnfExp μ t = A t * (Ψ t - dnfExp μ t * Ψ 0) + B t * (dnfExp μ t * Ψ 0)
      - dnfExp μ t * (R 0 * B 0) := by
    rw [hR0B0, hΨ0]
    conv_lhs => rw [hΦt]
    simp only [hAdef]
    noncomm_ring
  have n2 : rowSumNorm2 (A t * (Ψ t - dnfExp μ t * Ψ 0)) ≤ (1 + β) * (η * (4/3 * Mx)) :=
    le_trans (rowSumNorm2_mul_le _ _)
      (mul_le_mul hAn (hduh t ht) (rowSumNorm2_nonneg _) (by linarith))
  have n3 : rowSumNorm2 (B t * (dnfExp μ t * Ψ 0)) ≤ β * (4/3) :=
    le_trans (rowSumNorm2_mul_le _ _)
      (mul_le_mul (hB t ht) (hEΨ0 t ht) (rowSumNorm2_nonneg _) hβ0)
  have n4 : rowSumNorm2 (dnfExp μ t * (R 0 * B 0)) ≤ 1 * ((4/3) * β) := by
    refine le_trans (rowSumNorm2_mul_le _ _)
      (mul_le_mul (rowSumNorm2_dnfExp_le μ hμ ht.1) ?_ (rowSumNorm2_nonneg _) zero_le_one)
    exact le_trans (rowSumNorm2_mul_le _ _)
      (mul_le_mul (hRn 0 h0I) (hB 0 h0I) (rowSumNorm2_nonneg _) (by norm_num))
  have n5 : (1 + β) * (η * (4/3 * Mx)) ≤ (5/4) * (η * (4/3 * (8/5))) := by
    have : η * (4/3 * Mx) ≤ η * (4/3 * (8/5)) :=
      mul_le_mul_of_nonneg_left (by linarith) hη0
    exact mul_le_mul (by linarith) this (mul_nonneg hη0 (by linarith)) (by norm_num)
  constructor
  · rw [hid]
    have s1 := rowSumNorm2_sub_le (A t * (Ψ t - dnfExp μ t * Ψ 0) + B t * (dnfExp μ t * Ψ 0))
      (dnfExp μ t * (R 0 * B 0))
    have s2 := rowSumNorm2_add_le (A t * (Ψ t - dnfExp μ t * Ψ 0))
      (B t * (dnfExp μ t * Ψ 0))
    linarith
  · rw [hΦt]
    have := le_trans (rowSumNorm2_mul_le (A t) (Ψ t))
      (mul_le_mul hAn (hMx t ht) (rowSumNorm2_nonneg _) (by linarith))
    nlinarith

end NlsGge.SpectralFoundations
end
