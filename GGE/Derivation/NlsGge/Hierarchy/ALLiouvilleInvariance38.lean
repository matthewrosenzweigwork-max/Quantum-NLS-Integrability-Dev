import NlsGge.Hierarchy.ALGlobalFlow38
import NlsGge.Analysis.ODEFlowDeriv38
import Mathlib

/-! Batch 38, E07-6c-ii/iii: invariance of the Ablowitz-Ladik Liouville measure
`∏ d²α_j / (1 - |α_j|²)` under the flow of `X_H` (paper/v2.tex l.1971-1977), for `H` of class `C²`
on the polydisk with `{M_d, H} = 0`.

Sections: (1) flow basics and the Lipschitz bound; (2) differentiability in the initial point;
(3) trace = real-coordinate divergence and Jacobi's formula at the identity; (4) the Jacobian
identity `ρ(φ_t x) det Dφ_t(x) = ρ(x)`; (5) change of variables and invariance. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

variable {L : ℕ} [NeZero L]

section Basics

variable {H : (ZMod L → ℂ) → ℝ}

omit [NeZero L] in
lemma alFlow_of_not_mem38 (H : (ZMod L → ℂ) → ℝ) (t : ℝ) {α : ZMod L → ℂ}
    (hα : α ∉ alDisk38 L) : alFlow38 H t α = α := by
  classical
  unfold alFlow38
  rw [dite_eq_right_iff]
  rintro ⟨γ, h0, hγ⟩
  exact absurd (h0 ▸ (hγ 0).1) hα

lemma alFlow_zero38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    (α : ZMod L → ℂ) : alFlow38 H 0 α = α := by
  by_cases h : α ∈ alDisk38 L
  · exact (alFlow_spec38 hH hcons h).1
  · exact alFlow_of_not_mem38 H 0 h

lemma alFlow_mem38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {α : ZMod L → ℂ} (hα : α ∈ alDisk38 L) (t : ℝ) : alFlow38 H t α ∈ alDisk38 L :=
  (alFlow_spec38 hH hcons hα).2 t |>.1

lemma alFlow_mass38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {α : ZMod L → ℂ} (hα : α ∈ alDisk38 L) (t : ℝ) :
    alMass38 L (alFlow38 H t α) = alMass38 L α := by
  have hsp := (alFlow_spec38 hH hcons hα)
  have hI : ∀ s ∈ Ioo (-(|t| + 1)) (|t| + 1), IsALField38 (alFlow38 H s α) ∧
      HasDerivAt (fun u => alFlow38 H u α) (alX38 H (alFlow38 H s α)) s := fun s _ => hsp.2 s
  have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) :=
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have h0 : (0 : ℝ) ∈ Ioo (-(|t| + 1)) (|t| + 1) := ⟨by linarith [abs_nonneg t], by linarith [abs_nonneg t]⟩
  have := alMass_const_Ioo38 hcons hI ht h0
  rw [this, hsp.1]

lemma alFlow_hasDerivAt38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {α : ZMod L → ℂ} (hα : α ∈ alDisk38 L) (t : ℝ) :
    HasDerivAt (fun s => alFlow38 H s α) (alX38 H (alFlow38 H t α)) t :=
  ((alFlow_spec38 hH hcons hα).2 t).2

lemma alX'_continuousOn38 (hH : ContDiffOn ℝ 2 H (alDisk38 L)) :
    ContinuousOn (fderiv ℝ (alX38 H)) (alDisk38 L) := fun x hx =>
  (ContDiffAt.fderiv_right (alX38_contDiffAt38 hH hx) (m := 0) (by norm_num)).continuousAt.continuousWithinAt

lemma alX_hasFDerivAt38 (hH : ContDiffOn ℝ 2 H (alDisk38 L)) {x : ZMod L → ℂ}
    (hx : x ∈ alDisk38 L) : HasFDerivAt (alX38 H) (fderiv ℝ (alX38 H) x) x :=
  ((alX38_contDiffAt38 hH hx).differentiableAt one_ne_zero).hasFDerivAt

omit [NeZero L] in
lemma convex_box38 (c : ℝ) : Convex ℝ {α : ZMod L → ℂ | ∀ j, ‖α j‖ ≤ c} := by
  have : {α : ZMod L → ℂ | ∀ j, ‖α j‖ ≤ c} = Set.pi univ fun _ => closedBall (0 : ℂ) c := by
    ext α; simp [Set.pi, mem_closedBall, dist_zero_right]
  rw [this]
  exact convex_pi fun _ _ => convex_closedBall _ _

/-- Lipschitz bound for the flow on a small open neighbourhood of any point of the disk. -/
theorem alFlow_lipschitz38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {x₀ : ZMod L → ℂ} (hx₀ : x₀ ∈ alDisk38 L) (T : ℝ) :
    ∃ V : Set (ZMod L → ℂ), IsOpen V ∧ x₀ ∈ V ∧ V ⊆ alDisk38 L ∧
      ∃ C : ℝ, ∀ t ∈ Icc 0 T, ∀ x ∈ V, ∀ y ∈ V,
        ‖alFlow38 H t y - alFlow38 H t x‖ ≤ C * ‖y - x‖ := by
  set m := alMass38 L x₀ with hm
  have hMc : ContinuousOn (alMass38 L) (alDisk38 L) := fun x hx =>
    (alMass_continuousAt38 hx).continuousWithinAt
  refine ⟨alDisk38 L ∩ (alMass38 L) ⁻¹' Iio (m + 1), hMc.isOpen_inter_preimage isOpen_alDisk38
    isOpen_Iio, ⟨hx₀, by simp [hm]⟩, inter_subset_left, ?_⟩
  set q : ℝ := 1 - Real.exp (-(m + 1)) with hq
  set c : ℝ := Real.sqrt q with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc1 : c < 1 := by
    rw [hc, Real.sqrt_lt' one_pos]
    have := Real.exp_pos (-(m + 1))
    rw [hq]; nlinarith
  set B : Set (ZMod L → ℂ) := {α | ∀ j, ‖α j‖ ≤ c} with hB
  have hBdisk : B ⊆ alDisk38 L := fun α hα j => lt_of_le_of_lt (hα j) hc1
  have hBc : IsCompact B := isCompact_box38 c
  have horb : ∀ x ∈ alDisk38 L ∩ (alMass38 L) ⁻¹' Iio (m + 1), ∀ t, alFlow38 H t x ∈ B := by
    intro x hx t j
    have hd := alFlow_mem38 hH hcons hx.1 t
    have h1 := alNormSq_le_mass38 hd j
    rw [alFlow_mass38 hH hcons hx.1 t] at h1
    have h2 : alMass38 L x < m + 1 := hx.2
    have h3 : Real.exp (-(m + 1)) ≤ Real.exp (-alMass38 L x) := Real.exp_le_exp.mpr (by linarith)
    have h4 : ‖alFlow38 H t x j‖ ^ 2 ≤ q := by rw [hq]; linarith
    have := Real.abs_le_sqrt h4
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  obtain ⟨C0, hC0⟩ := hBc.exists_bound_of_continuousOn ((alX'_continuousOn38 hH).mono hBdisk)
  set K : ℝ≥0 := (max C0 0).toNNReal with hK
  have hLip : LipschitzOnWith K (alX38 H) B := by
    refine Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (f' := fderiv ℝ (alX38 H))
      (fun x hx => (alX_hasFDerivAt38 hH (hBdisk hx)).hasFDerivWithinAt) (fun x hx => ?_)
      (convex_box38 c)
    rw [← NNReal.coe_le_coe, coe_nnnorm, hK, Real.coe_toNNReal _ (le_max_right _ _)]
    exact (hC0 x hx).trans (le_max_left _ _)
  refine ⟨Real.exp (K * T), fun t ht x hx y hy => ?_⟩
  have hder : ∀ z ∈ alDisk38 L ∩ (alMass38 L) ⁻¹' Iio (m + 1), ∀ s ∈ Ico 0 T,
      HasDerivWithinAt (fun u => alFlow38 H u z) ((fun _ => alX38 H) s (alFlow38 H s z)) (Ici s) s :=
    fun z hz s _ => (alFlow_hasDerivAt38 hH hcons hz.1 s).hasDerivWithinAt
  have hcont : ∀ z ∈ alDisk38 L ∩ (alMass38 L) ⁻¹' Iio (m + 1),
      ContinuousOn (fun u => alFlow38 H u z) (Icc 0 T) := fun z hz u _ =>
    (alFlow_hasDerivAt38 hH hcons hz.1 u).continuousAt.continuousWithinAt
  have key := dist_le_of_trajectories_ODE_of_mem (v := fun _ => alX38 H) (s := fun _ => B)
    (K := K) (a := 0) (b := T) (f := fun u => alFlow38 H u y) (g := fun u => alFlow38 H u x)
    (δ := dist y x) (fun _ _ => hLip) (hcont y hy) (hder y hy) (fun s _ => horb y hy s)
    (hcont x hx) (hder x hx) (fun s _ => horb x hx s)
    (by rw [alFlow_zero38 hH hcons, alFlow_zero38 hH hcons])
  have := key t ht
  rw [dist_eq_norm, dist_eq_norm, sub_zero] at this
  refine this.trans ?_
  have hKT : (K : ℝ) * t ≤ K * T := mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg
  rw [mul_comm]
  gcongr

/-- The variational data of the flow at `x ∈ disk`, on `[0,T]`. -/
theorem alFlow_variational38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {x : ZMod L → ℂ} (hx : x ∈ alDisk38 L) {T : ℝ} (hT : 0 ≤ T) :
    ∃ D : ℝ → (ZMod L → ℂ) →L[ℝ] (ZMod L → ℂ), D 0 = 1 ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt D ((fderiv ℝ (alX38 H) (alFlow38 H t x)).comp (D t))
        (Icc 0 T) t) ∧ ∀ t ∈ Icc 0 T, HasFDerivAt (alFlow38 H t) (D t) x := by
  obtain ⟨V, hVo, hxV, hVd, C, hC⟩ := alFlow_lipschitz38 hH hcons hx T
  exact NlsGge.ODEFlowDeriv38.flow_hasFDerivAt_on38 (X := alX38 H) (X' := fderiv ℝ (alX38 H)) (U := alDisk38 L) (V := V)
    (φ := alFlow38 H) (T := T) isOpen_alDisk38 (fun z hz => alX_hasFDerivAt38 hH hz)
    (alX'_continuousOn38 hH) hVo hT (fun y _ => alFlow_zero38 hH hcons y)
    (fun y hy t _ => (alFlow_hasDerivAt38 hH hcons (hVd hy) t).hasDerivWithinAt)
    (fun y hy t _ => alFlow_mem38 hH hcons (hVd hy) t)
    ⟨C, hC⟩ x hxV

/-- Differentiability of `φ_t` in the initial point for `t ≥ 0`. -/
theorem alFlow_hasFDerivAt38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {x : ZMod L → ℂ} (hx : x ∈ alDisk38 L) {t : ℝ} (ht : 0 ≤ t) :
    HasFDerivAt (alFlow38 H t) (fderiv ℝ (alFlow38 H t) x) x := by
  obtain ⟨D, -, -, hD⟩ := alFlow_variational38 hH hcons hx ht
  exact (hD t ⟨ht, le_rfl⟩).differentiableAt.hasFDerivAt

/-- The derivative `h ↦ Dφ_h(x)` has right derivative `X'(x)` at `h = 0`. -/
theorem alFlow_fderiv_rightDeriv38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {x : ZMod L → ℂ} (hx : x ∈ alDisk38 L) :
    HasDerivWithinAt (fun h => fderiv ℝ (alFlow38 H h) x) (fderiv ℝ (alX38 H) x) (Ici 0) 0 ∧
      fderiv ℝ (alFlow38 H 0) x = 1 := by
  obtain ⟨D, hD0, hD, hF⟩ := alFlow_variational38 hH hcons hx (zero_le_one' ℝ)
  have hEq : ∀ t ∈ Icc (0 : ℝ) 1, fderiv ℝ (alFlow38 H t) x = D t := fun t ht => (hF t ht).fderiv
  have h0 := hD 0 ⟨le_rfl, zero_le_one⟩
  rw [alFlow_zero38 hH hcons, hD0, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id] at h0
  have h1 : HasDerivWithinAt (fun h => fderiv ℝ (alFlow38 H h) x) (fderiv ℝ (alX38 H) x)
      (Icc 0 1) 0 := h0.congr (fun t ht => hEq t ht) (hEq 0 ⟨le_rfl, zero_le_one⟩)
  exact ⟨h1.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE zero_lt_one),
    (hEq 0 ⟨le_rfl, zero_le_one⟩).trans hD0⟩

end Basics

section Det
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma differentiable_det38 : Differentiable ℝ (fun f : E →L[ℝ] E => f.det) := by
  classical
  let b := Module.finBasis ℝ E
  have hent : ∀ i j, Differentiable ℝ (fun f : E →L[ℝ] E => b.coord i (f (b j))) := fun i j => by
    have hc : Continuous (b.coord i) := LinearMap.continuous_of_finiteDimensional _
    exact ((LinearMap.toContinuousLinearMap (b.coord i)).differentiable).comp
      ((ContinuousLinearMap.apply ℝ E (b j)).differentiable)
  have : (fun f : E →L[ℝ] E => f.det) = fun f => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, b.coord (σ i) (f (b i)) := by
    funext f
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [LinearMap.toMatrix_apply, Units.smul_def]
  rw [this]
  intro f
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  refine (differentiableAt_const _).mul ?_
  have hd := (HasFDerivAt.finsetProd (u := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
    (g := fun i (f : E →L[ℝ] E) => b.coord (σ i) (f (b i)))
    (fun i _ => (hent (σ i) i f).hasFDerivAt)).differentiableAt
  convert hd using 1


/-- Derivative of `det` at the identity is the trace. -/
lemma hasFDerivAt_det_one38 :
    ∃ d : (E →L[ℝ] E) →L[ℝ] ℝ, HasFDerivAt (fun f : E →L[ℝ] E => f.det) d 1 ∧
      ∀ M : E →L[ℝ] E, d M = LinearMap.trace ℝ E (M : E →ₗ[ℝ] E) := by
  classical
  refine ⟨fderiv ℝ (fun f : E →L[ℝ] E => f.det) 1, (differentiable_det38 1).hasFDerivAt, fun M => ?_⟩
  have hd := (differentiable_det38 (E := E) 1).hasFDerivAt
  have hline : HasDerivAt (fun r : ℝ => (1 : E →L[ℝ] E) + r • M) M 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const M).const_add (1 : E →L[ℝ] E)
  have h1 : HasDerivAt (fun r : ℝ => ((1 : E →L[ℝ] E) + r • M).det)
      (fderiv ℝ (fun f : E →L[ℝ] E => f.det) 1 M) 0 := by
    have hd' : HasFDerivAt (fun f : E →L[ℝ] E => f.det) (fderiv ℝ (fun f : E →L[ℝ] E => f.det) 1)
        ((1 : E →L[ℝ] E) + (0 : ℝ) • M) := by simpa using hd
    exact hd'.comp_hasDerivAt (0 : ℝ) hline
  let b := Module.finBasis ℝ E
  set A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    LinearMap.toMatrix b b (M : E →ₗ[ℝ] E) with hA
  have hdet : ∀ r : ℝ, ((1 : E →L[ℝ] E) + r • M).det = Matrix.det (1 + r • A) := fun r => by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b]
    congr 1
    simp [hA, map_add, map_smul]
  set P := (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C)).divX.divX with hP
  have h2 : HasDerivAt (fun r : ℝ => ((1 : E →L[ℝ] E) + r • M).det) (Matrix.trace A) 0 := by
    have e : (fun r : ℝ => ((1 : E →L[ℝ] E) + r • M).det) =
        fun r => 1 + Matrix.trace A * r + P.eval r * r ^ 2 := by
      funext r
      rw [hdet, Matrix.det_one_add_smul]
    rw [e]
    have hp := (Polynomial.hasDerivAt P 0).mul ((hasDerivAt_pow 2 (0 : ℝ)))
    have hl : HasDerivAt (fun r : ℝ => 1 + Matrix.trace A * r) (Matrix.trace A) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (Matrix.trace A)).const_add (1 : ℝ)
    have h3 := hl.add hp
    simp only [mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Nat.cast_ofNat] at h3
    convert h3 using 1
    simp
  rw [h1.unique h2, hA, LinearMap.trace_eq_matrix_trace ℝ b]

end Det

section Trace

lemma trace_eq_sum38 (f : (ZMod L → ℂ) →L[ℝ] (ZMod L → ℂ)) :
    LinearMap.trace ℝ (ZMod L → ℂ) (f : (ZMod L → ℂ) →ₗ[ℝ] (ZMod L → ℂ)) =
      ∑ j : ZMod L, ((f (alPx38 j) j).re + (f (alPy38 j) j).im) := by
  classical
  let b := Pi.basis (fun _ : ZMod L => Complex.basisOneI)
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.diag, LinearMap.toMatrix_apply, Fin.sum_univ_two, b, alPx38, alPy38, Pi.basis_apply,
    Complex.coe_basisOneI_repr]

lemma fderiv_re_apply38 {X : (ZMod L → ℂ) → ZMod L → ℂ} {y : ZMod L → ℂ}
    (hX : DifferentiableAt ℝ X y) (j : ZMod L) (v : ZMod L → ℂ) :
    fderiv ℝ (fun β => (X β j).re) y v = (fderiv ℝ X y v j).re := by
  have h := ((Complex.reCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ZMod L => ℂ) j)).hasFDerivAt.comp y hX.hasFDerivAt)
  have h' : (fun β => (X β j).re) = ⇑(Complex.reCLM.comp (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : ZMod L => ℂ) j)) ∘ X := rfl
  rw [h', h.fderiv]
  simp

lemma fderiv_im_apply38 {X : (ZMod L → ℂ) → ZMod L → ℂ} {y : ZMod L → ℂ}
    (hX : DifferentiableAt ℝ X y) (j : ZMod L) (v : ZMod L → ℂ) :
    fderiv ℝ (fun β => (X β j).im) y v = (fderiv ℝ X y v j).im := by
  have h := ((Complex.imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ZMod L => ℂ) j)).hasFDerivAt.comp y hX.hasFDerivAt)
  have h' : (fun β => (X β j).im) = ⇑(Complex.imCLM.comp (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : ZMod L => ℂ) j)) ∘ X := rfl
  rw [h', h.fderiv]
  simp

/-- The trace of the derivative is the real-coordinate divergence. -/
lemma trace_fderiv_eq_div38 {X : (ZMod L → ℂ) → ZMod L → ℂ} {y : ZMod L → ℂ}
    (hX : DifferentiableAt ℝ X y) :
    LinearMap.trace ℝ (ZMod L → ℂ) (fderiv ℝ X y : (ZMod L → ℂ) →ₗ[ℝ] (ZMod L → ℂ)) = alDiv38 X y := by
  classical
  rw [trace_eq_sum38, alDiv38]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_re_apply38 hX, fderiv_im_apply38 hX]

lemma decomp38 (v : ZMod L → ℂ) :
    v = ∑ j : ZMod L, ((v j).re • alPx38 j + (v j).im • alPy38 j) := by
  funext k
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, alPx38, alPy38]
  rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  apply Complex.ext <;> simp

/-- Product rule for the divergence with a real density. -/
lemma div_rho_mul38 {X : (ZMod L → ℂ) → ZMod L → ℂ} {r : (ZMod L → ℂ) → ℝ} {y : ZMod L → ℂ}
    (hX : DifferentiableAt ℝ X y) (hr : DifferentiableAt ℝ r y) :
    alDiv38 (fun β j => (r β : ℂ) * X β j) y = r y * alDiv38 X y + fderiv ℝ r y (X y) := by
  have hre : ∀ j, DifferentiableAt ℝ (fun β => (X β j).re) y := fun j =>
    (Complex.reCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ZMod L => ℂ) j)).differentiableAt.comp y hX
  have him : ∀ j, DifferentiableAt ℝ (fun β => (X β j).im) y := fun j =>
    (Complex.imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ZMod L => ℂ) j)).differentiableAt.comp y hX
  have e1 : ∀ j v, fderiv ℝ (fun β => ((r β : ℂ) * X β j).re) y v =
      r y * (fderiv ℝ X y v j).re + (X y j).re * fderiv ℝ r y v := fun j v => by
    have : (fun β => ((r β : ℂ) * X β j).re) = fun β => r β * (X β j).re := by
      funext β; simp
    rw [this, (hr.hasFDerivAt.fun_mul (hre j).hasFDerivAt).fderiv]
    simp [fderiv_re_apply38 hX]
  have e2 : ∀ j v, fderiv ℝ (fun β => ((r β : ℂ) * X β j).im) y v =
      r y * (fderiv ℝ X y v j).im + (X y j).im * fderiv ℝ r y v := fun j v => by
    have : (fun β => ((r β : ℂ) * X β j).im) = fun β => r β * (X β j).im := by
      funext β; simp
    rw [this, (hr.hasFDerivAt.fun_mul (him j).hasFDerivAt).fderiv]
    simp [fderiv_im_apply38 hX]
  have hdec : fderiv ℝ r y (X y) = ∑ j : ZMod L, ((X y j).re * fderiv ℝ r y (alPx38 j) +
      (X y j).im * fderiv ℝ r y (alPy38 j)) := by
    conv_lhs => rw [decomp38 (X y)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [map_add, map_smul]
  unfold alDiv38
  simp only [e1, e2, fderiv_re_apply38 hX, fderiv_im_apply38 hX]
  rw [hdec, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma differentiableAt_alRho38 {α : ZMod L → ℂ} (hα : IsALField38 α) :
    DifferentiableAt ℝ alRho38 α := by
  have h1 : DifferentiableAt ℝ (fun β : ZMod L → ℂ => (1 - ‖β 0‖ ^ 2)⁻¹) α := by
    have h2 : DifferentiableAt ℝ (fun β : ZMod L → ℂ => 1 - ‖β 0‖ ^ 2) α := by
      have : DifferentiableAt ℝ (fun z : ℂ => ‖z‖ ^ 2) (α 0) :=
        ((contDiff_norm_sq ℝ : ContDiff ℝ 1 fun z : ℂ => ‖z‖ ^ 2).differentiable one_ne_zero) _
      have hp : DifferentiableAt ℝ (fun β : ZMod L → ℂ => β 0) α := by fun_prop
      have hc : DifferentiableAt ℝ ((fun z : ℂ => ‖z‖ ^ 2) ∘ fun β : ZMod L → ℂ => β 0) α :=
        this.comp α hp
      exact (differentiableAt_const _).sub hc
    refine h2.inv ?_
    have := hα 0
    nlinarith [norm_nonneg (α 0)]
  have := h1.mul (differentiableAt_alP38 (0 : ZMod L) hα)
  convert this using 1
  funext β
  simp only [alRho38, Pi.mul_apply, alP38]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : ZMod L))]

end Trace

section Jacobian

variable {H : (ZMod L → ℂ) → ℝ}

omit [NeZero L] in
lemma det_one38 : (1 : (ZMod L → ℂ) →L[ℝ] (ZMod L → ℂ)).det = 1 := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_one]
  exact map_one _

omit [NeZero L] in
lemma det_comp38 (A B : (ZMod L → ℂ) →L[ℝ] (ZMod L → ℂ)) : (A.comp B).det = A.det * B.det := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.det, ContinuousLinearMap.det,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]

lemma alFlow_fderiv_continuousOn38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {x : ZMod L → ℂ} (hx : x ∈ alDisk38 L) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => fderiv ℝ (alFlow38 H t) x) (Icc 0 T) := by
  obtain ⟨D, -, hD, hF⟩ := alFlow_variational38 hH hcons hx hT
  have hc : ContinuousOn D (Icc 0 T) := fun t ht => (hD t ht).continuousWithinAt
  exact hc.congr fun t ht => (hF t ht).fderiv

/-- The Jacobian density `ρ(φ_h y) det Dφ_h(y)` has right derivative `0` at `h = 0`
(Jacobi's formula plus Liouville's `div(ρ X_H) = 0`). -/
theorem alJacobi_rate38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {y : ZMod L → ℂ} (hy : y ∈ alDisk38 L) :
    HasDerivWithinAt
      (fun h => alRho38 (alFlow38 H h y) * (fderiv ℝ (alFlow38 H h) y).det) 0 (Ici 0) 0 := by
  obtain ⟨hD, hD0⟩ := alFlow_fderiv_rightDeriv38 hH hcons hy
  obtain ⟨d, hd, hdtr⟩ := hasFDerivAt_det_one38 (E := ZMod L → ℂ)
  have hdet : HasDerivWithinAt (fun h => (fderiv ℝ (alFlow38 H h) y).det)
      (LinearMap.trace ℝ (ZMod L → ℂ) (fderiv ℝ (alX38 H) y : (ZMod L → ℂ) →ₗ[ℝ] (ZMod L → ℂ)))
      (Ici 0) 0 := by
    have hd' : HasFDerivAt (fun f : (ZMod L → ℂ) →L[ℝ] (ZMod L → ℂ) => f.det) d
        (fderiv ℝ (alFlow38 H 0) y) := by rw [hD0]; exact hd
    exact (hd'.comp_hasDerivWithinAt (0 : ℝ) hD).congr_deriv (hdtr _)
  have hρ : HasDerivAt (fun h => alRho38 (alFlow38 H h y)) (fderiv ℝ alRho38 y (alX38 H y)) 0 := by
    have h1 : HasFDerivAt alRho38 (fderiv ℝ alRho38 y) (alFlow38 H 0 y) := by
      rw [alFlow_zero38 hH hcons]; exact (differentiableAt_alRho38 hy).hasFDerivAt
    have h2 := alFlow_hasDerivAt38 hH hcons hy 0
    rw [alFlow_zero38 hH hcons] at h2
    exact h1.comp_hasDerivAt (0 : ℝ) h2
  refine (hρ.hasDerivWithinAt.mul hdet).congr_deriv ?_
  have hXd : DifferentiableAt ℝ (alX38 H) y :=
    (alX38_contDiffAt38 hH hy).differentiableAt one_ne_zero
  have hl := alLiouville38 hH hy
  have hp : alDiv38 (alRhoX38 H) y =
      alRho38 y * alDiv38 (alX38 H) y + fderiv ℝ alRho38 y (alX38 H y) :=
    div_rho_mul38 (X := alX38 H) (r := alRho38) hXd (differentiableAt_alRho38 hy)
  rw [trace_fderiv_eq_div38 hXd, alFlow_zero38 hH hcons, hD0]
  rw [det_one38]
  linarith

lemma alFlow_fderiv_add38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {x : ZMod L → ℂ} (hx : x ∈ alDisk38 L) {h t : ℝ} (hh : 0 ≤ h) (ht : 0 ≤ t) :
    fderiv ℝ (alFlow38 H (h + t)) x =
      (fderiv ℝ (alFlow38 H h) (alFlow38 H t x)).comp (fderiv ℝ (alFlow38 H t) x) := by
  have h1 := alFlow_hasFDerivAt38 hH hcons hx ht
  have h2 := alFlow_hasFDerivAt38 hH hcons (alFlow_mem38 hH hcons hx t) hh
  have h3 := h2.comp x h1
  have heq : alFlow38 H (h + t) =ᶠ[𝓝 x] alFlow38 H h ∘ alFlow38 H t := by
    filter_upwards [isOpen_alDisk38.mem_nhds hx] with z hz
    exact alFlow_add38 hH hcons hz h t
  exact (h3.congr_of_eventuallyEq heq).fderiv

theorem alJacobian_deriv38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {x : ZMod L → ℂ} (hx : x ∈ alDisk38 L) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt
      (fun s => alRho38 (alFlow38 H s x) * (fderiv ℝ (alFlow38 H s) x).det) 0 (Ici t) t := by
  set y := alFlow38 H t x with hy
  have hyd : y ∈ alDisk38 L := alFlow_mem38 hH hcons hx t
  set c := (fderiv ℝ (alFlow38 H t) x).det with hc
  set J : ℝ → ℝ := fun s => alRho38 (alFlow38 H s x) * (fderiv ℝ (alFlow38 H s) x).det with hJ
  set G : ℝ → ℝ := fun h => (alRho38 (alFlow38 H h y) * (fderiv ℝ (alFlow38 H h) y).det) * c
    with hG
  have hG0 : HasDerivWithinAt G 0 (Ici 0) 0 := by
    simpa using (alJacobi_rate38 hH hcons hyd).mul_const c
  have hJG : ∀ h : ℝ, 0 ≤ h → J (h + t) = G h := fun h hh => by
    simp only [hJ, hG]
    rw [alFlow_add38 hH hcons hx h t, alFlow_fderiv_add38 hH hcons hx hh ht]
    rw [← hy, det_comp38, ← hc]
    ring
  have hshift : HasDerivWithinAt (fun s : ℝ => s - t) 1 (Ici t) t :=
    (hasDerivWithinAt_id t _).sub_const t
  have hmaps : MapsTo (fun s : ℝ => s - t) (Ici t) (Ici 0) := fun s hs => by show (0 : ℝ) ≤ s - t; exact sub_nonneg.2 hs
  have hG' : HasDerivWithinAt G 0 (Ici 0) ((fun s : ℝ => s - t) t) := by simpa using hG0
  have := HasDerivWithinAt.comp (h₂ := G) (h := fun s : ℝ => s - t) t hG' hshift hmaps
  refine (this.congr_deriv (by simp)).congr (fun s hs => ?_) ?_
  · have := hJG (s - t) (sub_nonneg.2 hs)
    simpa using this
  · have := hJG 0 le_rfl
    simpa using this

theorem alJacobian38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {x : ZMod L → ℂ} (hx : x ∈ alDisk38 L) {t : ℝ} (ht : 0 ≤ t) :
    alRho38 (alFlow38 H t x) * (fderiv ℝ (alFlow38 H t) x).det = alRho38 x := by
  have hcont : ContinuousOn
      (fun s => alRho38 (alFlow38 H s x) * (fderiv ℝ (alFlow38 H s) x).det) (Icc 0 t) := by
    refine ContinuousOn.mul (fun s _ => ?_) ?_
    · exact (ContinuousAt.comp (g := alRho38) (f := fun s => alFlow38 H s x)
        (differentiableAt_alRho38 (alFlow_mem38 hH hcons hx s)).continuousAt
        (alFlow_hasDerivAt38 hH hcons hx s).continuousAt).continuousWithinAt
    · exact (differentiable_det38.continuous).comp_continuousOn
        (alFlow_fderiv_continuousOn38 hH hcons hx ht)
  have := constant_of_has_deriv_right_zero hcont
    (fun s hs => alJacobian_deriv38 hH hcons hx hs.1) t ⟨ht, le_rfl⟩
  rw [this]
  simp only [alFlow_zero38 hH hcons, (alFlow_fderiv_rightDeriv38 hH hcons hx).2,
    det_one38, mul_one]

end Jacobian

section Invariance

variable {H : (ZMod L → ℂ) → ℝ}

/-- The (unnormalised) AL Liouville measure `∏ d²α_j / (1 - |α_j|²)` on the open polydisk:
`volume` on `ZMod L → ℂ` is the product of `Complex.volume` (`d Re d Im`), restricted to the disk
and weighted by `ρ = ∏ (1 - |α_j|²)⁻¹`. -/
def alLiouvilleMeasure38 (L : ℕ) [NeZero L] : Measure (ZMod L → ℂ) :=
  (volume.restrict (alDisk38 L)).withDensity (fun α => ENNReal.ofReal (alRho38 α))

lemma measurableSet_alDisk38 : MeasurableSet (alDisk38 L) := isOpen_alDisk38.measurableSet

lemma alRho38_pos {α : ZMod L → ℂ} (hα : α ∈ alDisk38 L) : 0 < alRho38 α := by
  refine Finset.prod_pos fun j _ => inv_pos.mpr ?_
  have := hα j
  nlinarith [norm_nonneg (α j)]

lemma alLiouville_apply38 {A : Set (ZMod L → ℂ)} (hA : MeasurableSet A) :
    alLiouvilleMeasure38 L A =
      ∫⁻ y in alDisk38 L, A.indicator (fun y => ENNReal.ofReal (alRho38 y)) y := by
  rw [alLiouvilleMeasure38, withDensity_apply _ hA, ← lintegral_indicator hA]

lemma alLiouville_apply_inter38 {B : Set (ZMod L → ℂ)} (hB : MeasurableSet B) :
    alLiouvilleMeasure38 L B = alLiouvilleMeasure38 L (B ∩ alDisk38 L) := by
  rw [alLiouville_apply38 hB, alLiouville_apply38 (hB.inter measurableSet_alDisk38)]
  refine setLIntegral_congr_fun measurableSet_alDisk38 fun y hy => ?_
  by_cases hyB : y ∈ B <;> simp [Set.indicator, hyB, hy]

lemma alFlow_inv38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {x : ZMod L → ℂ} (hx : x ∈ alDisk38 L) (s : ℝ) :
    alFlow38 H (-s) (alFlow38 H s x) = x := by
  rw [← alFlow_add38 hH hcons hx, neg_add_cancel, alFlow_zero38 hH hcons]

lemma alFlow_injOn38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0) (s : ℝ) :
    InjOn (alFlow38 H s) (alDisk38 L) := fun x hx y hy h => by
  rw [← alFlow_inv38 hH hcons hx s, ← alFlow_inv38 hH hcons hy s, h]

lemma alFlow_image38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0) (s : ℝ) :
    alFlow38 H s '' alDisk38 L = alDisk38 L := by
  refine Subset.antisymm (by rintro _ ⟨x, hx, rfl⟩; exact alFlow_mem38 hH hcons hx s) fun β hβ => ?_
  refine ⟨alFlow38 H (-s) β, alFlow_mem38 hH hcons hβ _, ?_⟩
  have := alFlow_inv38 hH hcons hβ (-s)
  rwa [neg_neg] at this

lemma alFlow_continuousOn38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {t : ℝ} (ht : 0 ≤ t) : ContinuousOn (alFlow38 H t) (alDisk38 L) := fun x hx =>
  (alFlow_hasFDerivAt38 hH hcons hx ht).continuousAt.continuousWithinAt

lemma alFlow_measurable_nonneg38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {t : ℝ} (ht : 0 ≤ t) : Measurable (alFlow38 H t) := by
  classical
  have : alFlow38 H t = (alDisk38 L).piecewise (alFlow38 H t) id := by
    funext x
    by_cases hx : x ∈ alDisk38 L
    · simp [hx]
    · simp [hx, alFlow_of_not_mem38 H t hx]
  rw [this]
  exact ContinuousOn.measurable_piecewise (alFlow_continuousOn38 hH hcons ht) continuousOn_id
    measurableSet_alDisk38

/-- Invariance for `t ≥ 0`, on preimages: change of variables with the Jacobian identity. -/
theorem alLiouville_preimage_nonneg38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {t : ℝ} (ht : 0 ≤ t) {A : Set (ZMod L → ℂ)} (hA : MeasurableSet A) :
    alLiouvilleMeasure38 L (alFlow38 H t ⁻¹' A) = alLiouvilleMeasure38 L A := by
  have hmeas := alFlow_measurable_nonneg38 hH hcons ht
  have hpre : MeasurableSet (alFlow38 H t ⁻¹' A) := hmeas hA
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure (ZMod L → ℂ))
    (s := alDisk38 L) (f := alFlow38 H t) (f' := fun x => fderiv ℝ (alFlow38 H t) x)
    measurableSet_alDisk38
    (fun x hx => (alFlow_hasFDerivAt38 hH hcons hx ht).hasFDerivWithinAt)
    (alFlow_injOn38 hH hcons t) (A.indicator (fun y => ENNReal.ofReal (alRho38 y)))
  rw [alFlow_image38 hH hcons, ← alLiouville_apply38 hA] at hcv
  rw [hcv, alLiouville_apply38 hpre]
  refine setLIntegral_congr_fun measurableSet_alDisk38 fun x hx => ?_
  have hJ := alJacobian38 hH hcons hx ht
  have hρ := alRho38_pos (alFlow_mem38 hH hcons hx t)
  have hρx := alRho38_pos hx
  have hdet : 0 < (fderiv ℝ (alFlow38 H t) x).det := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hρ.le hneg]
  by_cases hφ : alFlow38 H t x ∈ A
  · have hx' : x ∈ alFlow38 H t ⁻¹' A := hφ
    rw [Set.indicator_of_mem hφ, Set.indicator_of_mem hx', ← ENNReal.ofReal_mul (abs_nonneg _),
      abs_of_pos hdet, mul_comm, hJ]
  · have hx' : x ∉ alFlow38 H t ⁻¹' A := hφ
    rw [Set.indicator_of_notMem hφ, Set.indicator_of_notMem hx', mul_zero]

/-- Preimage of a measurable set under `φ_{-t}`, `t ≥ 0`, as a Lusin-Souslin image. -/
lemma alFlow_preimage_neg38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {t : ℝ} {A : Set (ZMod L → ℂ)} :
    alFlow38 H (-t) ⁻¹' A =
      alFlow38 H t '' (A ∩ alDisk38 L) ∪ (A \ alDisk38 L) := by
  ext x
  by_cases hx : x ∈ alDisk38 L
  · constructor
    · intro h
      left
      refine ⟨alFlow38 H (-t) x, ⟨h, alFlow_mem38 hH hcons hx _⟩, ?_⟩
      have := alFlow_inv38 hH hcons hx (-t)
      rwa [neg_neg] at this
    · rintro (⟨z, ⟨hzA, hz⟩, rfl⟩ | ⟨_, hxn⟩)
      · show alFlow38 H (-t) (alFlow38 H t z) ∈ A
        rw [alFlow_inv38 hH hcons hz t]; exact hzA
      · exact absurd hx hxn
  · constructor
    · intro h
      right
      refine ⟨?_, hx⟩
      have : alFlow38 H (-t) x = x := alFlow_of_not_mem38 H _ hx
      rwa [mem_preimage, this] at h
    · rintro (⟨z, ⟨hzA, hz⟩, rfl⟩ | ⟨hxA, _⟩)
      · exact absurd (alFlow_mem38 hH hcons hz t) hx
      · show alFlow38 H (-t) x ∈ A
        rw [alFlow_of_not_mem38 H _ hx]; exact hxA

/-- Negative times: measurability and invariance on preimages (Lusin-Souslin for the image
`φ_t(A ∩ 𝔻^L)` and the `t ≥ 0` statement). -/
theorem alLiouville_preimage_neg38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {t : ℝ} (ht : 0 ≤ t) {A : Set (ZMod L → ℂ)} (hA : MeasurableSet A) :
    MeasurableSet (alFlow38 H (-t) ⁻¹' A) ∧
      alLiouvilleMeasure38 L (alFlow38 H (-t) ⁻¹' A) = alLiouvilleMeasure38 L A := by
  have hB : MeasurableSet (alFlow38 H t '' (A ∩ alDisk38 L)) :=
    MeasurableSet.image_of_continuousOn_injOn (hA.inter measurableSet_alDisk38)
      ((alFlow_continuousOn38 hH hcons ht).mono inter_subset_right)
      ((alFlow_injOn38 hH hcons t).mono inter_subset_right)
  have hpre := alFlow_preimage_neg38 hH hcons (t := t) (A := A)
  have hm : MeasurableSet (alFlow38 H (-t) ⁻¹' A) := by
    rw [hpre]; exact hB.union (hA.diff measurableSet_alDisk38)
  refine ⟨hm, ?_⟩
  have hBd : alFlow38 H t '' (A ∩ alDisk38 L) ⊆ alDisk38 L := by
    rintro _ ⟨z, hz, rfl⟩; exact alFlow_mem38 hH hcons hz.2 t
  have hinter : alFlow38 H (-t) ⁻¹' A ∩ alDisk38 L = alFlow38 H t '' (A ∩ alDisk38 L) := by
    rw [hpre]
    ext x
    constructor
    · rintro ⟨h | h, hx⟩
      · exact h
      · exact absurd hx h.2
    · intro h; exact ⟨Or.inl h, hBd h⟩
  have hmeas := alFlow_measurable_nonneg38 hH hcons ht
  have hpreB : alFlow38 H t ⁻¹' (alFlow38 H t '' (A ∩ alDisk38 L)) ∩ alDisk38 L =
      A ∩ alDisk38 L := by
    ext x
    constructor
    · rintro ⟨⟨z, hz, hzx⟩, hx⟩
      have : z = x := alFlow_injOn38 hH hcons t hz.2 hx hzx
      exact ⟨this ▸ hz.1, hx⟩
    · rintro ⟨hxA, hx⟩
      exact ⟨⟨x, ⟨hxA, hx⟩, rfl⟩, hx⟩
  rw [alLiouville_apply_inter38 hm, hinter,
    ← alLiouville_preimage_nonneg38 hH hcons ht hB,
    alLiouville_apply_inter38 (hmeas hB), hpreB, ← alLiouville_apply_inter38 hA]

/-- Full flow-invariance of the Liouville measure on preimages, all `s ∈ ℝ`. -/
theorem alLiouville_preimage38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0) (s : ℝ) :
    Measurable (alFlow38 H s) ∧ ∀ A : Set (ZMod L → ℂ), MeasurableSet A →
      alLiouvilleMeasure38 L (alFlow38 H s ⁻¹' A) = alLiouvilleMeasure38 L A := by
  rcases le_total 0 s with hs | hs
  · exact ⟨alFlow_measurable_nonneg38 hH hcons hs, fun A hA =>
      alLiouville_preimage_nonneg38 hH hcons hs hA⟩
  · obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ s = -t := ⟨-s, by linarith, by ring⟩
    exact ⟨fun A hA => (alLiouville_preimage_neg38 hH hcons ht hA).1,
      fun A hA => (alLiouville_preimage_neg38 hH hcons ht hA).2⟩

/-- **Invariance of the AL Liouville measure** `∏ d²α_j/(1-|α_j|²)` under the flow of `X_H`, for
every `C²` Hamiltonian `H` on the polydisk with `{M_d, H} = 0`, and every time `s ∈ ℝ`. -/
theorem alLiouville_invariant38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0) (s : ℝ) :
    (alLiouvilleMeasure38 L).map (alFlow38 H s) = alLiouvilleMeasure38 L := by
  obtain ⟨hm, hA⟩ := alLiouville_preimage38 hH hcons s
  refine Measure.ext fun A hA' => ?_
  rw [Measure.map_apply hm hA', hA A hA']

/-- Integral form: `∫⁻ f ∘ φ_s dμ = ∫⁻ f dμ`. -/
theorem alLiouville_lintegral_flow38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0) (s : ℝ)
    {f : (ZMod L → ℂ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ α, f (alFlow38 H s α) ∂(alLiouvilleMeasure38 L) = ∫⁻ α, f α ∂(alLiouvilleMeasure38 L) := by
  have hm := (alLiouville_preimage38 hH hcons s).1
  rw [← lintegral_map hf hm, alLiouville_invariant38 hH hcons s]

/-- Instance-ready form: the Liouville measure restricted to any measurable flow-invariant subset
`S` of the polydisk (in particular a mass sublevel) is invariant. -/
theorem alLiouville_restrict_invariant38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0)
    {S : Set (ZMod L → ℂ)} (hS : MeasurableSet S)
    (hinv : ∀ α ∈ alDisk38 L, ∀ s : ℝ, alFlow38 H s α ∈ S ↔ α ∈ S) (s : ℝ) :
    ((alLiouvilleMeasure38 L).restrict S).map (alFlow38 H s) =
      (alLiouvilleMeasure38 L).restrict S := by
  obtain ⟨hm, hA⟩ := alLiouville_preimage38 hH hcons s
  refine Measure.ext fun A hA' => ?_
  rw [Measure.map_apply hm hA', Measure.restrict_apply (hm hA'), Measure.restrict_apply hA']
  have h1 : alFlow38 H s ⁻¹' A ∩ S ∩ alDisk38 L = alFlow38 H s ⁻¹' (A ∩ S) ∩ alDisk38 L := by
    ext x
    constructor
    · rintro ⟨⟨hxA, hxS⟩, hx⟩
      exact ⟨⟨hxA, (hinv x hx s).2 hxS⟩, hx⟩
    · rintro ⟨⟨hxA, hxS⟩, hx⟩
      exact ⟨⟨hxA, (hinv x hx s).1 hxS⟩, hx⟩
  rw [alLiouville_apply_inter38 ((hm hA').inter hS), h1, ← alLiouville_apply_inter38 (hm (hA'.inter hS)),
    hA _ (hA'.inter hS)]

lemma measurable_alMass38 : Measurable (alMass38 L) := by
  unfold alMass38
  fun_prop

/-- The mass sublevel `{M_d ≤ m} ∩ 𝔻^L`. -/
def alMassSublevel38 (L : ℕ) [NeZero L] (m : ℝ) : Set (ZMod L → ℂ) :=
  alDisk38 L ∩ {α | alMass38 L α ≤ m}

/-- Corollary used downstream: the Liouville measure restricted to a mass sublevel is invariant
under the flow of every `C²` Hamiltonian with `{M_d, H} = 0`. -/
theorem alLiouville_massSublevel_invariant38 (hH : ContDiffOn ℝ 2 H (alDisk38 L))
    (hcons : ∀ α : ZMod L → ℂ, IsALField38 α → alBracket38 (alMass38 L) H α = 0) (m s : ℝ) :
    ((alLiouvilleMeasure38 L).restrict (alMassSublevel38 L m)).map (alFlow38 H s) =
      (alLiouvilleMeasure38 L).restrict (alMassSublevel38 L m) := by
  refine alLiouville_restrict_invariant38 hH hcons
    (measurableSet_alDisk38.inter (measurableSet_le measurable_alMass38 measurable_const))
    (fun α hα s => ?_) s
  simp only [mem_inter_iff, mem_setOf_eq, alFlow_mem38 hH hcons hα s,
    alFlow_mass38 hH hcons hα s, hα, true_and]

end Invariance

#check @alFlow_lipschitz38
#check @alFlow_variational38
#check @alFlow_hasFDerivAt38
#check @alFlow_fderiv_rightDeriv38
#check @hasFDerivAt_det_one38
#check @trace_fderiv_eq_div38
#check @div_rho_mul38
#check @alJacobi_rate38
#check @alJacobian38
#check @alLiouville_preimage_nonneg38
#check @alLiouville_preimage_neg38
#check @alLiouville_preimage38
#check @alLiouville_invariant38
#check @alLiouville_lintegral_flow38
#check @alLiouville_restrict_invariant38
#check @alLiouville_massSublevel_invariant38
#print axioms alFlow_lipschitz38
#print axioms alFlow_variational38
#print axioms alFlow_hasFDerivAt38
#print axioms alFlow_fderiv_rightDeriv38
#print axioms hasFDerivAt_det_one38
#print axioms trace_fderiv_eq_div38
#print axioms div_rho_mul38
#print axioms alJacobi_rate38
#print axioms alJacobian38
#print axioms alLiouville_preimage_nonneg38
#print axioms alLiouville_preimage_neg38
#print axioms alLiouville_preimage38
#print axioms alLiouville_invariant38
#print axioms alLiouville_lintegral_flow38
#print axioms alLiouville_restrict_invariant38
#print axioms alLiouville_massSublevel_invariant38

end NlsGge.AblowitzLadik
end
