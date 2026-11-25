import Mathlib
import NlsGge.Birkhoff.F01Determinant38c
import NlsGge.ThirdConsultation.Narrative.G03

   
                                               
                                                                           
                                                                        
                                                                             
                                                                            
  

set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Birkhoff NlsGge.Sobolev38

namespace NlsGge.ThirdConsultation.Narrative

/-- Cauchy--Schwarz for three already convergent real series. -/
theorem g03i_hasSum_cauchy {ι : Type*} {f g : ι → ℝ} {a b c : ℝ}
    (hf : HasSum (fun i => f i ^ 2) a)
    (hg : HasSum (fun i => g i ^ 2) b)
    (hfg : HasSum (fun i => f i * g i) c) :
    c ≤ Real.sqrt a * Real.sqrt b := by
  have hbound (S : Finset ι) :
      ∑ i ∈ S, f i * g i ≤ Real.sqrt a * Real.sqrt b := by
    refine (Real.sum_mul_le_sqrt_mul_sqrt S f g).trans ?_
    apply mul_le_mul
    · exact Real.sqrt_le_sqrt (sum_le_hasSum S (fun _ _ => sq_nonneg _) hf)
    · exact Real.sqrt_le_sqrt (sum_le_hasSum S (fun _ _ => sq_nonneg _) hg)
    · exact Real.sqrt_nonneg _
    · exact Real.sqrt_nonneg _
  rw [← hfg.tsum_eq]
  exact hfg.summable.tsum_le_of_sum_le hbound

/-- The genuine single-vector h0/h1/h2 interpolation inequality.
This does not interpolate the input norm of an arbitrary operator. -/
theorem g03i_vector_interpolation (z : H2_38) :
    ‖i21_38 z‖ ^ 2 ≤ ‖i20_38 z‖ * ‖z‖ := by
  let f : ℤ → ℝ := fun n => ‖carrierCoe38 (((1 + 1 : ℕ)) : ℝ) z n‖
  let g : ℤ → ℝ := fun n => (1 + (n : ℝ) ^ 2) * f n
  have hf : HasSum (fun n => f n ^ 2) (‖i20_38 z‖ ^ 2) := by
    have h := carrier_hasSum_norm_sq_zero38 (i20_38 z)
    simpa only [f, carrierCoe38_i20] using h
  have hg : HasSum (fun n => g n ^ 2) (‖z‖ ^ 2) := by
    have h := carrier_hasSum_norm_sq38 (((1 + 1 : ℕ)) : ℝ) z
    refine h.congr_fun (fun n => ?_)
    rw [sobolevModeWeight_natCast_F01_38]
    dsimp only [g, f]
    ring
  have hfg : HasSum (fun n => f n * g n) (‖i21_38 z‖ ^ 2) := by
    have h := carrier_hasSum_norm_sq38 ((1 : ℕ) : ℝ) (i21_38 z)
    refine h.congr_fun (fun n => ?_)
    rw [carrierCoe38_i21, sobolevModeWeight_natCast_F01_38]
    dsimp only [f, g]
    ring
  have h := g03i_hasSum_cauchy hf hg hfg
  simpa only [Real.sqrt_sq (norm_nonneg (i20_38 z)), Real.sqrt_sq (norm_nonneg z)] using h

/-- The source h1 inclusion has dense image in the SAME completed h0 space. -/
theorem g03i_denseRange_i10 : DenseRange i10_38 := by
  have hle : Submodule.span ℝ (Set.range (fun p => bas0_38 p)) ≤
      LinearMap.range i10_38.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact ⟨xi38 p, i10_xi38 p⟩
  have hspan := bas0_38.dense_span
  change (Submodule.span ℝ (Set.range (fun p => bas0_38 p))).topologicalClosure = ⊤ at hspan
  have hdense : Dense (Submodule.span ℝ (Set.range (fun p => bas0_38 p)) : Set H0_38) := by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, hspan]
    rfl
  change Dense (Set.range i10_38)
  exact hdense.mono (fun x hx => hle hx)

/-- A uniform inverse estimate for h1 -> h0 is false, so the h1 input factor
left by single-vector Cauchy--Schwarz cannot be removed by inclusion alone. -/
theorem g03i_no_bound_inverse_i10 :
    ¬ ∃ C : ℝ, ∀ ξ : H1_38, ‖ξ‖ ≤ C * ‖i10_38 ξ‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  let p : ℤ × Fin 2 := ((n : ℤ), 0)
  have h := hC (xi38 p)
  simp only [i10_xi38, bas0_38.orthonormal.norm_eq_one, mul_one] at h
  have hC0 : 0 ≤ C := (norm_nonneg (xi38 p)).trans h
  have hsq : ‖xi38 p‖ ^ 2 ≤ C ^ 2 :=
    (sq_le_sq₀ (norm_nonneg (xi38 p)) hC0).mpr h
  rw [norm_xi38_sq] at hsq
  have hsq' : 1 + (n : ℝ) ^ 2 ≤ C ^ 2 := by
    simpa only [rho38, p, Int.cast_natCast] using hsq
  have hn2 : C ^ 2 < (n : ℝ) ^ 2 :=
    (sq_lt_sq₀ hC0 (Nat.cast_nonneg n)).mpr hn
  linarith only [hsq', hn2]

end NlsGge.ThirdConsultation.Narrative


/-! Finite real-matrix Hilbert-scale interpolation through scalar Hadamard.
The four preceding compiled support declarations are preserved verbatim.
The actual infinite-dimensional Birkhoff lift is assembled after these helpers. -/
namespace NlsGge.ThirdConsultation.Narrative

open Set
open Complex.HadamardThreeLines

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Complexification of a real finite matrix preserves its squared l2 bound. -/
theorem g03i_complexify_sq_bound (T : ι → κ → ℝ) (a : ℝ)
    (hT : ∀ u : κ → ℝ,
      (∑ i, (∑ j, T i j * u j)^2) ≤ a^2 * ∑ j, (u j)^2)
    (u : κ → ℂ) :
    (∑ i, ‖∑ j, (T i j : ℂ) * u j‖^2) ≤ a^2 * ∑ j, ‖u j‖^2 := by
  have hr := hT (fun j => (u j).re)
  have hi := hT (fun j => (u j).im)
  have hre (i : ι) : (∑ j, (T i j : ℂ) * u j).re = ∑ j, T i j * (u j).re := by
    have h := map_sum Complex.reCLM (fun j : κ => (T i j : ℂ) * u j) Finset.univ
    simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using h
  have him (i : ι) : (∑ j, (T i j : ℂ) * u j).im = ∑ j, T i j * (u j).im := by
    have h := map_sum Complex.imCLM (fun j : κ => (T i j : ℂ) * u j) Finset.univ
    simpa only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] using h
  have hleft : (∑ i, ‖∑ j, (T i j : ℂ) * u j‖^2) =
      (∑ i, (∑ j, T i j * (u j).re)^2) +
        ∑ i, (∑ j, T i j * (u j).im)^2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  have hright : a^2 * (∑ j, ‖u j‖^2) =
      a^2 * (∑ j, (u j).re^2) + a^2 * ∑ j, (u j).im^2 := by
    have hn : (∑ j, ‖u j‖^2) = ∑ j, ((u j).re^2 + (u j).im^2) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [hn, Finset.sum_add_distrib, mul_add]
  rw [hleft, hright]
  exact add_le_add hr hi

/-- Complex bilinear testing of a genuine real finite matrix. -/
def g03i_matrixBilinear (T : ι → κ → ℝ) (x : κ → ℂ) (y : ι → ℂ) : ℂ :=
  ∑ i, (∑ j, (T i j : ℂ) * x j) * y i

theorem g03i_complex_bilinear_bound (T : ι → κ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hT : ∀ u : κ → ℝ,
      (∑ i, (∑ j, T i j * u j)^2) ≤ a^2 * ∑ j, (u j)^2)
    (x : κ → ℂ) (y : ι → ℂ) :
    ‖g03i_matrixBilinear T x y‖ ≤
      a * Real.sqrt (∑ j, ‖x j‖^2) * Real.sqrt (∑ i, ‖y i‖^2) := by
  have hs := Real.sqrt_le_sqrt (g03i_complexify_sq_bound T a hT x)
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha] at hs
  calc
    ‖g03i_matrixBilinear T x y‖ ≤ ∑ i, ‖(∑ j, (T i j : ℂ) * x j) * y i‖ :=
      norm_sum_le _ _
    _ = ∑ i, ‖∑ j, (T i j : ℂ) * x j‖ * ‖y i‖ := by simp only [norm_mul]
    _ ≤ Real.sqrt (∑ i, ‖∑ j, (T i j : ℂ) * x j‖^2) *
        Real.sqrt (∑ i, ‖y i‖^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ ≤ a * Real.sqrt (∑ j, ‖x j‖^2) * Real.sqrt (∑ i, ‖y i‖^2) :=
      mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)

/-- An entire exponential with real affine exponent. -/
def g03i_expLine (a b : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((a : ℂ) + (b : ℂ) * z)

theorem g03i_expLine_differentiable (a b : ℝ) : Differentiable ℂ (g03i_expLine a b) := by
  unfold g03i_expLine
  exact ((differentiable_const (a : ℂ)).add
    ((differentiable_const (b : ℂ)).mul differentiable_id)).cexp

theorem g03i_expLine_norm (a b : ℝ) (z : ℂ) :
    ‖g03i_expLine a b z‖ = Real.exp (a + b * z.re) := by
  simp only [g03i_expLine, Complex.norm_exp, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem g03i_expLine_strip_bound (a b : ℝ) (z : ℂ) (hz : 0 ≤ z.re ∧ z.re ≤ 1) :
    ‖g03i_expLine a b z‖ ≤ Real.exp (|a| + |b|) := by
  rw [g03i_expLine_norm]
  apply Real.exp_le_exp.mpr
  calc
    a + b * z.re ≤ |a| + |b| * z.re :=
      add_le_add (le_abs_self a) (mul_le_mul_of_nonneg_right (le_abs_self b) hz.1)
    _ ≤ |a| + |b| :=
      add_le_add (le_refl |a|) (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left hz.2 (abs_nonneg b)))

theorem g03i_expLine_factor (a b t : ℝ) (z : ℂ) :
    g03i_expLine a b z = (Real.exp (a + b*t) : ℂ) *
      Complex.exp ((b : ℂ) * (z - (t : ℂ))) := by
  rw [g03i_expLine, Complex.ofReal_exp, ← Complex.exp_add]
  apply congrArg Complex.exp
  push_cast
  ring

/-- Imaginary exponential factors are norm-preserving on a vertical boundary. -/
theorem g03i_phase_norm {t : ℝ} {z : ℂ} (hz : z.re = t) (b : ℝ) (w : ℂ) :
    ‖Complex.exp ((b : ℂ) * (z - (t : ℂ))) * w‖ = ‖w‖ := by
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    hz, sub_self, mul_zero, zero_mul, sub_zero, Real.exp_zero, one_mul]

/-- The real matrix on a horizontal real parameter of the scale pencil. -/
def g03i_matrixAt (r : ι → ℝ) (s : κ → ℝ) (M : ι → κ → ℝ) (t : ℝ) : ι → κ → ℝ :=
  fun i j => Real.exp ((3*t - 1)*r i + (2 - 3*t)*s j) * M i j

/-- Scalarized finite exponential family for the source endpoint pair. -/
def g03i_expBilinear (r : ι → ℝ) (s : κ → ℝ) (M : ι → κ → ℝ)
    (x : κ → ℂ) (y : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ i, ∑ j, ((M i j : ℂ) * x j * y i) *
    g03i_expLine (-r i + 2*s j) (3*r i - 3*s j) z

theorem g03i_expBilinear_differentiable (r : ι → ℝ) (s : κ → ℝ) (M : ι → κ → ℝ)
    (x : κ → ℂ) (y : ι → ℂ) : Differentiable ℂ (g03i_expBilinear r s M x y) := by
  unfold g03i_expBilinear
  apply Differentiable.fun_sum
  intro i _
  apply Differentiable.fun_sum
  intro j _
  exact (g03i_expLine_differentiable _ _).const_mul _

theorem g03i_expBilinear_bdd (r : ι → ℝ) (s : κ → ℝ) (M : ι → κ → ℝ)
    (x : κ → ℂ) (y : ι → ℂ) :
    BddAbove ((norm ∘ g03i_expBilinear r s M x y) '' verticalClosedStrip 0 1) := by
  classical
  refine ⟨∑ i, ∑ j, ‖(M i j : ℂ) * x j * y i‖ *
    Real.exp (|-r i + 2*s j| + |3*r i - 3*s j|), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz' : 0 ≤ z.re ∧ z.re ≤ 1 := hz
  change ‖g03i_expBilinear r s M x y z‖ ≤ _
  unfold g03i_expBilinear
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (g03i_expLine_strip_bound _ _ z hz') (norm_nonneg _)

/-- Factoring the finite pencil on either boundary changes only the test vectors by phases. -/
theorem g03i_expBilinear_factor (r : ι → ℝ) (s : κ → ℝ) (M : ι → κ → ℝ)
    (x : κ → ℂ) (y : ι → ℂ) (t : ℝ) (z : ℂ) :
    g03i_expBilinear r s M x y z =
      g03i_matrixBilinear (g03i_matrixAt r s M t)
        (fun j => Complex.exp (((-3*s j : ℝ) : ℂ) * (z - (t : ℂ))) * x j)
        (fun i => Complex.exp (((3*r i : ℝ) : ℂ) * (z - (t : ℂ))) * y i) := by
  unfold g03i_expBilinear g03i_matrixBilinear
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [g03i_expLine_factor _ _ t z]
  dsimp only [g03i_matrixAt]
  rw [Complex.ofReal_mul]
  have he : (-r i + 2*s j) + (3*r i - 3*s j)*t =
      (3*t - 1)*r i + (2 - 3*t)*s j := by ring
  rw [he]
  have hp : Complex.exp (((3*r i - 3*s j : ℝ) : ℂ) * (z - (t : ℂ))) =
      Complex.exp (((3*r i : ℝ) : ℂ) * (z - (t : ℂ))) *
        Complex.exp (((-3*s j : ℝ) : ℂ) * (z - (t : ℂ))) := by
    rw [← Complex.exp_add]
    apply congrArg Complex.exp
    push_cast
    ring
  rw [hp]
  ring

theorem g03i_expBilinear_real (r : ι → ℝ) (s : κ → ℝ) (M : ι → κ → ℝ)
    (x : κ → ℂ) (y : ι → ℂ) (t : ℝ) :
    g03i_expBilinear r s M x y (t : ℂ) =
      g03i_matrixBilinear (g03i_matrixAt r s M t) x y := by
  rw [g03i_expBilinear_factor r s M x y t]
  simp only [sub_self, mul_zero, Complex.exp_zero, one_mul]

theorem g03i_matrixAt_theta (r : ι → ℝ) (s : κ → ℝ) (M : ι → κ → ℝ) :
    g03i_matrixAt r s M (2/3 : ℝ) = fun i j => Real.exp (r i) * M i j := by
  funext i j
  unfold g03i_matrixAt
  have he : (3*(2/3 : ℝ) - 1)*r i + (2 - 3*(2/3 : ℝ))*s j = r i := by ring
  rw [he]

/-- Every boundary bound here is derived from a real matrix endpoint bound. -/
theorem g03i_expBilinear_line_bound (r : ι → ℝ) (s : κ → ℝ) (M : ι → κ → ℝ)
    (x : κ → ℂ) (y : ι → ℂ) (t a : ℝ) (ha : 0 ≤ a)
    (hT : ∀ u : κ → ℝ,
      (∑ i, (∑ j, g03i_matrixAt r s M t i j * u j)^2) ≤ a^2 * ∑ j, (u j)^2)
    (z : ℂ) (hz : z.re = t) :
    ‖g03i_expBilinear r s M x y z‖ ≤
      a * Real.sqrt (∑ j, ‖x j‖^2) * Real.sqrt (∑ i, ‖y i‖^2) := by
  rw [g03i_expBilinear_factor r s M x y t z]
  have h := g03i_complex_bilinear_bound (g03i_matrixAt r s M t) a ha hT
    (fun j => Complex.exp (((-3*s j : ℝ) : ℂ) * (z - (t : ℂ))) * x j)
    (fun i => Complex.exp (((3*r i : ℝ) : ℂ) * (z - (t : ℂ))) * y i)
  simpa only [g03i_phase_norm hz] using h

/-- Equal-bound scalar three-lines specialization, including the zero-bound case. -/
theorem g03i_hadamard_constant_bound (f : ℂ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hd : DiffContOnCl ℂ f (verticalStrip 0 1))
    (hB : BddAbove ((norm ∘ f) '' verticalClosedStrip 0 1))
    (h0 : ∀ z : ℂ, z.re = 0 → ‖f z‖ ≤ K)
    (h1 : ∀ z : ℂ, z.re = 1 → ‖f z‖ ≤ K) :
    ‖f ((2/3 : ℝ) : ℂ)‖ ≤ K := by
  have hz : (((2/3 : ℝ) : ℂ)) ∈ verticalClosedStrip 0 1 := by
    norm_num [verticalClosedStrip]
  have h := norm_le_interp_of_mem_verticalClosedStrip₀₁' f hz hd hB
    (fun z hz => h0 z hz) (fun z hz => h1 z hz)
  have hp : K ^ (1 - (2/3 : ℝ)) * K ^ (2/3 : ℝ) = K := by
    rcases eq_or_lt_of_le hK with hzero | hpos
    · subst K
      norm_num [Real.zero_rpow]
    · rw [← Real.rpow_add hpos, sub_add_cancel, Real.rpow_one]
  simpa only [Complex.ofReal_re, hp] using h

/-- Uniform finite real-matrix Hilbert-scale bilinear interpolation.
The only estimates assumed are the two real endpoint operator bounds. -/
theorem g03i_finite_exp_bilinear_interpolation
    (r : ι → ℝ) (s : κ → ℝ) (M : ι → κ → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h0 : ∀ u : κ → ℝ,
      (∑ i, (∑ j, g03i_matrixAt r s M 0 i j * u j)^2) ≤ a^2 * ∑ j, (u j)^2)
    (h1 : ∀ u : κ → ℝ,
      (∑ i, (∑ j, g03i_matrixAt r s M 1 i j * u j)^2) ≤ b^2 * ∑ j, (u j)^2)
    (x : κ → ℂ) (y : ι → ℂ) :
    ‖g03i_matrixBilinear (fun i j => Real.exp (r i) * M i j) x y‖ ≤
      (a+b) * Real.sqrt (∑ j, ‖x j‖^2) * Real.sqrt (∑ i, ‖y i‖^2) := by
  let K : ℝ := (a+b) * Real.sqrt (∑ j, ‖x j‖^2) * Real.sqrt (∑ i, ‖y i‖^2)
  have hK : 0 ≤ K :=
    mul_nonneg (mul_nonneg (add_nonneg ha hb) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hb0 : ∀ z : ℂ, z.re = 0 → ‖g03i_expBilinear r s M x y z‖ ≤ K := by
    intro z hz
    refine (g03i_expBilinear_line_bound r s M x y 0 a ha h0 z hz).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hb) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have hb1 : ∀ z : ℂ, z.re = 1 → ‖g03i_expBilinear r s M x y z‖ ≤ K := by
    intro z hz
    refine (g03i_expBilinear_line_bound r s M x y 1 b hb h1 z hz).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ha) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have h := g03i_hadamard_constant_bound (g03i_expBilinear r s M x y) K hK
    (g03i_expBilinear_differentiable r s M x y).diffContOnCl
    (g03i_expBilinear_bdd r s M x y) hb0 hb1
  rw [g03i_expBilinear_real, g03i_matrixAt_theta] at h
  exact h

end NlsGge.ThirdConsultation.Narrative


/-! Actual Sobolev application of the compiled finite three-lines estimate. -/
namespace NlsGge.ThirdConsultation.Narrative

abbrev G03Mode := ℤ × Fin 2

def g03i_logWeight (p : G03Mode) : ℝ := Real.log (japaneseBracket p.1)

theorem g03i_sqrtWeight_exp (r : ℝ) (p : G03Mode) :
    Real.sqrt (sobolevModeWeight r p.1) = Real.exp (r * g03i_logWeight p) := by
  have hw : sobolevModeWeight r p.1 = Real.exp (r * g03i_logWeight p) ^ 2 := by
    unfold sobolevModeWeight
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_def_of_pos (japaneseBracket_pos p.1), pow_two, ← Real.exp_add]
    congr 1
    unfold g03i_logWeight
    ring
  rw [hw, Real.sqrt_sq (Real.exp_pos _).le]

/-- The same unnormalized smooth real Fourier mode at every Sobolev exponent. -/
def g03i_mode (r : ℝ) (p : G03Mode) : SobolevCarrier38 r :=
  Real.exp (r * g03i_logWeight p) • g03Basis r p

theorem g03i_mode_coe (r : ℝ) (p : G03Mode) (n : ℤ) :
    carrierCoe38 r (g03i_mode r p) n =
      if n = p.1 then Complex.orthonormalBasisOneI p.2 else 0 := by
  classical
  rw [g03i_mode, g03Coe_smul, g03Basis_coe]
  by_cases hn : n = p.1
  · subst n
    rw [if_pos rfl, g03i_sqrtWeight_exp r p]
    have he : (Real.exp (r * g03i_logWeight p) : ℂ) ≠ 0 := by
      exact_mod_cast Real.exp_ne_zero (r * g03i_logWeight p)
    field_simp [he] <;> ring
  · simp only [if_neg hn, zero_div, mul_zero]

theorem g03i_mode_incl {r s : ℝ} (hrs : r ≤ s) (p : G03Mode) :
    carrierIncl38 hrs (g03i_mode s p) = g03i_mode r p := by
  apply carrierExt38
  funext n
  rw [carrierCoe38_incl38, g03i_mode_coe, g03i_mode_coe]

theorem g03i_mode_zero (p : G03Mode) :
    g03i_mode ((0 : ℕ) : ℝ) p = g03Basis ((0 : ℕ) : ℝ) p := by
  simp only [g03i_mode, Nat.cast_zero, zero_mul, Real.exp_zero, one_smul]

theorem g03i_mode_cancel (r : ℝ) (p : G03Mode) :
    Real.exp (-(r * g03i_logWeight p)) • g03i_mode r p = g03Basis r p := by
  rw [g03i_mode, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

/-- Equality of raw Fourier coefficients gives the precise normalized-basis change. -/
theorem g03i_inner_of_coe (r s : ℝ) (x : SobolevCarrier38 r)
    (y : SobolevCarrier38 s) (h : carrierCoe38 r x = carrierCoe38 s y) (p : G03Mode) :
    inner ℝ (g03Basis r p) x = Real.exp ((r-s) * g03i_logWeight p) *
      inner ℝ (g03Basis s p) y := by
  rw [g03Basis_inner, g03Basis_inner, h, g03i_sqrtWeight_exp r p, g03i_sqrtWeight_exp s p,
    ← mul_assoc, ← Real.exp_add]
  have he : (r-s)*g03i_logWeight p + s*g03i_logWeight p = r*g03i_logWeight p := by ring
  rw [he]

/-- Real h0 matrix of the same operator, in both real directions at every integer mode. -/
def g03i_operatorMatrix (A : H0_38 →L[ℝ] H0_38) (p q : G03Mode) : ℝ :=
  inner ℝ (g03Basis ((0 : ℕ) : ℝ) p) (A (g03i_mode ((0 : ℕ) : ℝ) q))

theorem g03i_endpoint_entry (A : H0_38 →L[ℝ] H0_38) (r s : ℝ)
    (K : SobolevCarrier38 r →L[ℝ] SobolevCarrier38 s)
    (hK : ∀ q : G03Mode, carrierCoe38 s (K (g03i_mode r q)) =
      carrierCoe38 ((0 : ℕ) : ℝ) (A (g03i_mode ((0 : ℕ) : ℝ) q))) (p q : G03Mode) :
    inner ℝ (g03Basis s p) (K (g03Basis r q)) =
      Real.exp (s*g03i_logWeight p-r*g03i_logWeight q) * g03i_operatorMatrix A p q := by
  have hm : Real.exp (r*g03i_logWeight q) *
      inner ℝ (g03Basis s p) (K (g03Basis r q)) =
      Real.exp (s*g03i_logWeight p) * g03i_operatorMatrix A p q := by
    have h := g03i_inner_of_coe s ((0 : ℕ) : ℝ)
      (K (g03i_mode r q)) (A (g03i_mode ((0 : ℕ) : ℝ) q)) (hK q) p
    have he : (s-((0 : ℕ) : ℝ))*g03i_logWeight p = s*g03i_logWeight p := by norm_num
    rw [he] at h
    simpa only [g03i_mode, map_smul, real_inner_smul_right, g03i_operatorMatrix] using h
  calc
    inner ℝ (g03Basis s p) (K (g03Basis r q)) =
        Real.exp (-(r*g03i_logWeight q)) * (Real.exp (r*g03i_logWeight q) *
          inner ℝ (g03Basis s p) (K (g03Basis r q))) := by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ = Real.exp (-(r*g03i_logWeight q)) *
        (Real.exp (s*g03i_logWeight p) * g03i_operatorMatrix A p q) := by rw [hm]
    _ = _ := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      ring

/-- The positive smoothing endpoint has the same raw Fourier action on smooth modes. -/
theorem g03i_positive_mode_coe (A : H0_38 →L[ℝ] H0_38) (D : H1_38 →L[ℝ] H2_38)
    (hD : ∀ ξ : H1_38, A (i10_38 ξ) = i20_38 (D ξ)) (q : G03Mode) :
    carrierCoe38 (((1+1 : ℕ)) : ℝ) (D (g03i_mode ((1 : ℕ) : ℝ) q)) =
      carrierCoe38 ((0 : ℕ) : ℝ) (A (g03i_mode ((0 : ℕ) : ℝ) q)) := by
  have hi : i10_38 (g03i_mode ((1 : ℕ) : ℝ) q) = g03i_mode ((0 : ℕ) : ℝ) q :=
    g03i_mode_incl _ q
  have h := hD (g03i_mode ((1 : ℕ) : ℝ) q)
  rw [hi] at h
  funext n
  have hc := congrArg (fun z : H0_38 => carrierCoe38 ((0 : ℕ) : ℝ) z n) h
  simpa only [carrierCoe38_i20] using hc.symm

/-- The landed dual operator supplies the negative endpoint on those SAME modes. -/
theorem g03i_negative_mode_coe (A : H0_38 →L[ℝ] H0_38) (E : H1_38 →L[ℝ] H2_38)
    (hE : ∀ ξ : H1_38, ContinuousLinearMap.adjoint A (i10_38 ξ) = i20_38 (E ξ))
    (q : G03Mode) :
    carrierCoe38 (-((1 : ℕ) : ℝ))
      (g03Dualize ((1 : ℕ) : ℝ) (((1+1 : ℕ)) : ℝ) E
        (g03i_mode (-(((1+1 : ℕ)) : ℝ)) q)) =
      carrierCoe38 ((0 : ℕ) : ℝ) (A (g03i_mode ((0 : ℕ) : ℝ) q)) := by
  have h := g03Dualize_compatible A E hE (g03i_mode ((0 : ℕ) : ℝ) q)
  rw [g03i_mode_incl] at h
  funext n
  have hc := congrArg (fun z : SobolevCarrier38 (-((1 : ℕ) : ℝ)) =>
    carrierCoe38 (-((1 : ℕ) : ℝ)) z n) h
  simpa only [carrierCoe38_incl38] using hc

section FiniteCoordinates

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem g03i_norm_synthesis (r : ℝ) (f : κ → G03Mode) (hf : Function.Injective f)
    (u : κ → ℝ) :
    ‖∑ j, u j • g03Basis r (f j)‖^2 = ∑ j, (u j)^2 := by
  have ho := (g03Basis r).orthonormal.comp f hf
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp only [real_inner_smul_left]
  apply Finset.sum_congr rfl
  intro j _
  have hcoeff : inner ℝ (g03Basis r (f j)) (∑ i, u i • g03Basis r (f i)) = u j := by
    simpa only [Function.comp_apply] using ho.inner_right_fintype u j
  rw [hcoeff, pow_two]

theorem g03i_matrix_endpoint_bound (r s : ℝ)
    (K : SobolevCarrier38 r →L[ℝ] SobolevCarrier38 s)
    (e : ι → G03Mode) (f : κ → G03Mode)
    (he : Function.Injective e) (hf : Function.Injective f) (u : κ → ℝ) :
    (∑ i, (∑ j, inner ℝ (g03Basis s (e i)) (K (g03Basis r (f j))) * u j)^2) ≤
      ‖K‖^2 * ∑ j, (u j)^2 := by
  let v : SobolevCarrier38 r := ∑ j, u j • g03Basis r (f j)
  have hB := ((g03Basis s).orthonormal.comp e he).sum_inner_products_le
    (s := Finset.univ) (K v)
  have hn := (sq_le_sq₀ (norm_nonneg (K v))
    (mul_nonneg (norm_nonneg K) (norm_nonneg v))).mpr (K.le_opNorm v)
  have hN : ‖v‖^2 = ∑ j, (u j)^2 := g03i_norm_synthesis r f hf u
  rw [mul_pow, hN] at hn
  have hc (i : ι) : inner ℝ (g03Basis s (e i)) (K v) =
      ∑ j, inner ℝ (g03Basis s (e i)) (K (g03Basis r (f j))) * u j := by
    simp only [v, map_sum, map_smul, inner_sum, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hB' : (∑ i, (∑ j, inner ℝ (g03Basis s (e i))
      (K (g03Basis r (f j))) * u j)^2) ≤ ‖K v‖^2 := by
    simpa only [Function.comp_apply, hc, Real.norm_eq_abs, sq_abs] using hB
  exact hB'.trans hn

/-- Both matrix endpoint bounds are uniform in the two independently chosen truncations. -/
theorem g03i_actual_matrix_endpoints (A : H0_38 →L[ℝ] H0_38)
    (D E : H1_38 →L[ℝ] H2_38)
    (hD : ∀ ξ : H1_38, A (i10_38 ξ) = i20_38 (D ξ))
    (hE : ∀ ξ : H1_38, ContinuousLinearMap.adjoint A (i10_38 ξ) = i20_38 (E ξ))
    (e : ι → G03Mode) (f : κ → G03Mode)
    (he : Function.Injective e) (hf : Function.Injective f) :
    (∀ u : κ → ℝ,
      (∑ i, (∑ j, g03i_matrixAt (g03i_logWeight ∘ e) (g03i_logWeight ∘ f)
        (fun i j => g03i_operatorMatrix A (e i) (f j)) 0 i j * u j)^2) ≤
        ‖E‖^2 * ∑ j, (u j)^2) ∧
    (∀ u : κ → ℝ,
      (∑ i, (∑ j, g03i_matrixAt (g03i_logWeight ∘ e) (g03i_logWeight ∘ f)
        (fun i j => g03i_operatorMatrix A (e i) (f j)) 1 i j * u j)^2) ≤
        ‖D‖^2 * ∑ j, (u j)^2) := by
  let K := g03Dualize ((1 : ℕ) : ℝ) (((1+1 : ℕ)) : ℝ) E
  have hneg (i : ι) (j : κ) :
      g03i_matrixAt (g03i_logWeight ∘ e) (g03i_logWeight ∘ f)
          (fun i j => g03i_operatorMatrix A (e i) (f j)) 0 i j =
        inner ℝ (g03Basis (-((1 : ℕ) : ℝ)) (e i))
          (K (g03Basis (-(((1+1 : ℕ)) : ℝ)) (f j))) := by
    rw [g03i_endpoint_entry A _ _ K (g03i_negative_mode_coe A E hE)]
    dsimp only [g03i_matrixAt, Function.comp_apply]
    congr 1
    congr 1
    norm_num
    <;> ring
  have hpos (i : ι) (j : κ) :
      g03i_matrixAt (g03i_logWeight ∘ e) (g03i_logWeight ∘ f)
          (fun i j => g03i_operatorMatrix A (e i) (f j)) 1 i j =
        inner ℝ (g03Basis (((1+1 : ℕ)) : ℝ) (e i))
          (D (g03Basis ((1 : ℕ) : ℝ) (f j))) := by
    rw [g03i_endpoint_entry A _ _ D (g03i_positive_mode_coe A D hD)]
    dsimp only [g03i_matrixAt, Function.comp_apply]
    congr 1
    congr 1
    norm_num
    <;> ring
  constructor
  · intro u
    simp only [hneg]
    refine (g03i_matrix_endpoint_bound _ _ K e f he hf u).trans ?_
    apply mul_le_mul_of_nonneg_right
    · exact (sq_le_sq₀ (norm_nonneg K) (norm_nonneg E)).mpr (g03Dualize_norm_le _ _ E)
    · exact Finset.sum_nonneg (fun j _ => sq_nonneg (u j))
  · intro u
    simpa only [hpos] using g03i_matrix_endpoint_bound _ _ D e f he hf u

/-- Real l2 consequence of the already compiled complex bilinear interpolation. -/
theorem g03i_finite_exp_square_bound
    (r : ι → ℝ) (s : κ → ℝ) (M : ι → κ → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h0 : ∀ u : κ → ℝ,
      (∑ i, (∑ j, g03i_matrixAt r s M 0 i j * u j)^2) ≤ a^2 * ∑ j, (u j)^2)
    (h1 : ∀ u : κ → ℝ,
      (∑ i, (∑ j, g03i_matrixAt r s M 1 i j * u j)^2) ≤ b^2 * ∑ j, (u j)^2)
    (u : κ → ℝ) :
    (∑ i, (∑ j, Real.exp (r i) * M i j * u j)^2) ≤ (a+b)^2 * ∑ j, (u j)^2 := by
  let v : ι → ℝ := fun i => ∑ j, Real.exp (r i) * M i j * u j
  let U : ℝ := ∑ j, (u j)^2
  let V : ℝ := ∑ i, (v i)^2
  have hU : 0 ≤ U := Finset.sum_nonneg (fun j _ => sq_nonneg (u j))
  have hV : 0 ≤ V := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  have h := g03i_finite_exp_bilinear_interpolation r s M a b ha hb h0 h1
    (fun j => (u j : ℂ)) (fun i => (v i : ℂ))
  have hbil : g03i_matrixBilinear (fun i j => Real.exp (r i) * M i j)
      (fun j => (u j : ℂ)) (fun i => (v i : ℂ)) = (V : ℂ) := by
    have hv (i : ι) : (∑ j, (Real.exp (r i) * M i j : ℂ) * (u j : ℂ)) = (v i : ℂ) := by
      dsimp only [v]
      push_cast <;> rfl
    simp only [Complex.ofReal_exp] at hv
    dsimp only [g03i_matrixBilinear, V]
    push_cast <;> simp only [pow_two, hv]
  rw [hbil, Complex.norm_real, Real.norm_of_nonneg hV] at h
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  change V ≤ (a+b)*Real.sqrt U*Real.sqrt V at h
  have hroot : Real.sqrt V ≤ (a+b)*Real.sqrt U := by
    by_cases hz : Real.sqrt V = 0
    · rw [hz]
      exact mul_nonneg (add_nonneg ha hb) (Real.sqrt_nonneg U)
    · have hp := lt_of_le_of_ne (Real.sqrt_nonneg V) (Ne.symm hz)
      apply (mul_le_mul_iff_of_pos_right hp).mp
      change Real.sqrt V * Real.sqrt V ≤ ((a+b)*Real.sqrt U)*Real.sqrt V
      rw [← pow_two, Real.sq_sqrt hV]
      exact h
  calc
    V = (Real.sqrt V)^2 := (Real.sq_sqrt hV).symm
    _ ≤ ((a+b)*Real.sqrt U)^2 := (sq_le_sq₀ (Real.sqrt_nonneg V)
      (mul_nonneg (add_nonneg ha hb) (Real.sqrt_nonneg U))).mpr hroot
    _ = (a+b)^2 * U := by rw [mul_pow, Real.sq_sqrt hU]

end FiniteCoordinates

/-- The interpolated output coefficients of the SAME smooth mode. -/
theorem g03i_smooth_output_entry (A : H0_38 →L[ℝ] H0_38) (D : H1_38 →L[ℝ] H2_38)
    (hD : ∀ ξ : H1_38, A (i10_38 ξ) = i20_38 (D ξ)) (p q : G03Mode) :
    inner ℝ (g03Basis ((1 : ℕ) : ℝ) p) (i21_38 (D (g03i_mode ((1 : ℕ) : ℝ) q))) =
      Real.exp (g03i_logWeight p) * g03i_operatorMatrix A p q := by
  have hc : carrierCoe38 ((1 : ℕ) : ℝ) (i21_38 (D (g03i_mode ((1 : ℕ) : ℝ) q))) =
      carrierCoe38 ((0 : ℕ) : ℝ) (A (g03i_mode ((0 : ℕ) : ℝ) q)) := by
    funext n
    rw [carrierCoe38_i21]
    exact congrFun (g03i_positive_mode_coe A D hD q) n
  have h := g03i_inner_of_coe ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ)
    (i21_38 (D (g03i_mode ((1 : ℕ) : ℝ) q)))
    (A (g03i_mode ((0 : ℕ) : ℝ) q)) hc p
  have he : (((1 : ℕ) : ℝ)-((0 : ℕ) : ℝ))*g03i_logWeight p = g03i_logWeight p := by norm_num
  rw [he] at h
  exact h

/-- Supremum over arbitrary finite output mode sets, for a finite smooth input. -/
theorem g03i_finite_input_bound (A : H0_38 →L[ℝ] H0_38) (D E : H1_38 →L[ℝ] H2_38)
    (hD : ∀ ξ : H1_38, A (i10_38 ξ) = i20_38 (D ξ))
    (hE : ∀ ξ : H1_38, ContinuousLinearMap.adjoint A (i10_38 ξ) = i20_38 (E ξ))
    (Q : Finset G03Mode) (u : Q → ℝ) :
    ‖i21_38 (D (∑ j : Q, u j • g03i_mode ((1 : ℕ) : ℝ) j.val))‖ ≤
      (‖D‖+‖E‖) * ‖i10_38 (∑ j : Q, u j • g03i_mode ((1 : ℕ) : ℝ) j.val)‖ := by
  let ξ : H1_38 := ∑ j : Q, u j • g03i_mode ((1 : ℕ) : ℝ) j.val
  let y : H1_38 := i21_38 (D ξ)
  have hn : ‖i10_38 ξ‖^2 = ∑ j : Q, (u j)^2 := by
    have he : i10_38 ξ = ∑ j : Q, u j • g03Basis ((0 : ℕ) : ℝ) j.val := by
      dsimp only [ξ]
      simp only [map_sum, map_smul, show ∀ p, i10_38 (g03i_mode ((1 : ℕ) : ℝ) p) =
        g03i_mode ((0 : ℕ) : ℝ) p from fun p => g03i_mode_incl _ p, g03i_mode_zero]
    rw [he]
    exact g03i_norm_synthesis _ (fun j : Q => j.val) Subtype.val_injective u
  have hcoeff (p : G03Mode) : inner ℝ (g03Basis ((1 : ℕ) : ℝ) p) y =
      ∑ j : Q, Real.exp (g03i_logWeight p) * g03i_operatorMatrix A p j.val * u j := by
    simp only [y, ξ, map_sum, map_smul, inner_sum, real_inner_smul_right,
      g03i_smooth_output_entry A D hD]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hs := hasSum_inner_sq38 (g03Basis ((1 : ℕ) : ℝ)) y
  have hsq : ‖y‖^2 ≤ (‖D‖+‖E‖)^2 * ∑ j : Q, (u j)^2 := by
    rw [← hs.tsum_eq]
    apply hs.summable.tsum_le_of_sum_le
    intro R
    have hend := g03i_actual_matrix_endpoints A D E hD hE
      (fun i : R => i.val) (fun j : Q => j.val) Subtype.val_injective Subtype.val_injective
    have h := g03i_finite_exp_square_bound
      (fun i : R => g03i_logWeight i.val) (fun j : Q => g03i_logWeight j.val)
      (fun i j => g03i_operatorMatrix A i.val j.val)
      ‖E‖ ‖D‖ (norm_nonneg E) (norm_nonneg D) hend.1 hend.2 u
    rw [add_comm ‖E‖ ‖D‖] at h
    have hsub : (∑ i : R, (inner ℝ (g03Basis ((1 : ℕ) : ℝ) i.val) y)^2) ≤
        (‖D‖+‖E‖)^2 * ∑ j : Q, (u j)^2 := by
      simpa only [← hcoeff] using h
    rw [Finset.sum_coe_sort R
      (fun p => (inner ℝ (g03Basis ((1 : ℕ) : ℝ) p) y)^2)] at hsub
    exact hsub
  have hsq' : ‖y‖^2 ≤ ((‖D‖+‖E‖)*‖i10_38 ξ‖)^2 := by
    rwa [mul_pow, hn]
  exact (sq_le_sq₀ (norm_nonneg y)
    (mul_nonneg (add_nonneg (norm_nonneg D) (norm_nonneg E)) (norm_nonneg (i10_38 ξ)))).mp hsq'

/-- Hilbert-scale interpolation on the full dense h1 input, with constant one.
No extra assumption is placed on the source operator or its Fourier matrix. -/
theorem g03i_dense_input_bound (A : H0_38 →L[ℝ] H0_38) (D E : H1_38 →L[ℝ] H2_38)
    (hD : ∀ ξ : H1_38, A (i10_38 ξ) = i20_38 (D ξ))
    (hE : ∀ ξ : H1_38, ContinuousLinearMap.adjoint A (i10_38 ξ) = i20_38 (E ξ))
    (ξ : H1_38) : ‖i21_38 (D ξ)‖ ≤ (‖D‖+‖E‖) * ‖i10_38 ξ‖ := by
  have hclosed : IsClosed {v : H1_38 |
      ‖i21_38 (D v)‖ ≤ (‖D‖+‖E‖) * ‖i10_38 v‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  apply hclosed.mem_of_tendsto ((g03Basis ((1 : ℕ) : ℝ)).hasSum_repr ξ)
  apply Filter.Eventually.of_forall
  intro Q
  change ‖i21_38 (D (∑ p ∈ Q,
      (g03Basis ((1 : ℕ) : ℝ)).repr ξ p • g03Basis ((1 : ℕ) : ℝ) p))‖ ≤
    (‖D‖+‖E‖) * ‖i10_38 (∑ p ∈ Q,
      (g03Basis ((1 : ℕ) : ℝ)).repr ξ p • g03Basis ((1 : ℕ) : ℝ) p)‖
  let u : Q → ℝ := fun j => (g03Basis ((1 : ℕ) : ℝ)).repr ξ j.val *
    Real.exp (-(((1 : ℕ) : ℝ)*g03i_logWeight j.val))
  have he : (∑ j : Q, u j • g03i_mode ((1 : ℕ) : ℝ) j.val) =
      ∑ p ∈ Q, (g03Basis ((1 : ℕ) : ℝ)).repr ξ p • g03Basis ((1 : ℕ) : ℝ) p := by
    rw [← Finset.sum_coe_sort Q
      (fun p => (g03Basis ((1 : ℕ) : ℝ)).repr ξ p • g03Basis ((1 : ℕ) : ℝ) p)]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [u]
    rw [mul_smul, g03i_mode_cancel]
  simpa only [he] using g03i_finite_input_bound A D E hD hE Q u

theorem g03i_dense_input_interpolation :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : H0_38 →L[ℝ] H0_38) (D E : H1_38 →L[ℝ] H2_38),
      (∀ ξ : H1_38, A (i10_38 ξ) = i20_38 (D ξ)) →
      (∀ ξ : H1_38, ContinuousLinearMap.adjoint A (i10_38 ξ) = i20_38 (E ξ)) →
      ∀ ξ : H1_38, ‖i21_38 (D ξ)‖ ≤ C*(‖D‖+‖E‖)*‖i10_38 ξ‖ := by
  refine ⟨1, one_pos, ?_⟩
  intro A D E hD hE ξ
  simpa only [one_mul] using g03i_dense_input_bound A D E hD hE ξ

/-- Canonical extension from h1 to the SAME completed h0 input space.
Its extension characterization is used only after the interpolation bound is proved. -/
def g03i_lift (D : H1_38 →L[ℝ] H2_38) : H0_38 →L[ℝ] H1_38 :=
  (i21_38.comp D).toLinearMap.extendOfNorm i10_38.toLinearMap

theorem g03i_lift_on_h1 (A : H0_38 →L[ℝ] H0_38) (D E : H1_38 →L[ℝ] H2_38)
    (hD : ∀ ξ : H1_38, A (i10_38 ξ) = i20_38 (D ξ))
    (hE : ∀ ξ : H1_38, ContinuousLinearMap.adjoint A (i10_38 ξ) = i20_38 (E ξ))
    (ξ : H1_38) : g03i_lift D (i10_38 ξ) = i21_38 (D ξ) :=
  LinearMap.extendOfNorm_eq g03i_denseRange_i10
    ⟨‖D‖+‖E‖, g03i_dense_input_bound A D E hD hE⟩ ξ

theorem g03i_lift_norm (A : H0_38 →L[ℝ] H0_38) (D E : H1_38 →L[ℝ] H2_38)
    (hD : ∀ ξ : H1_38, A (i10_38 ξ) = i20_38 (D ξ))
    (hE : ∀ ξ : H1_38, ContinuousLinearMap.adjoint A (i10_38 ξ) = i20_38 (E ξ)) :
    ‖g03i_lift D‖ ≤ ‖D‖+‖E‖ :=
  LinearMap.opNorm_extendOfNorm_le g03i_denseRange_i10
    (add_nonneg (norm_nonneg D) (norm_nonneg E)) (g03i_dense_input_bound A D E hD hE)

theorem g03i_lift_compatible (A : H0_38 →L[ℝ] H0_38) (D E : H1_38 →L[ℝ] H2_38)
    (hD : ∀ ξ : H1_38, A (i10_38 ξ) = i20_38 (D ξ))
    (hE : ∀ ξ : H1_38, ContinuousLinearMap.adjoint A (i10_38 ξ) = i20_38 (E ξ))
    (h : H0_38) : i10_38 (g03i_lift D h) = A h := by
  refine g03i_denseRange_i10.induction_on
    (p := fun z : H0_38 => i10_38 (g03i_lift D z) = A z) h ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro ξ
    rw [g03i_lift_on_h1 A D E hD hE, i10_38_i21_38, ← hD]

/-- The same interpolation estimate applied to operator differences. -/
theorem g03i_lift_difference_bound
    (A A' : H0_38 →L[ℝ] H0_38) (D E D' E' : H1_38 →L[ℝ] H2_38)
    (hD : ∀ ξ : H1_38, A (i10_38 ξ) = i20_38 (D ξ))
    (hE : ∀ ξ : H1_38, ContinuousLinearMap.adjoint A (i10_38 ξ) = i20_38 (E ξ))
    (hD' : ∀ ξ : H1_38, A' (i10_38 ξ) = i20_38 (D' ξ))
    (hE' : ∀ ξ : H1_38, ContinuousLinearMap.adjoint A' (i10_38 ξ) = i20_38 (E' ξ)) :
    ‖g03i_lift D - g03i_lift D'‖ ≤ ‖D-D'‖+‖E-E'‖ := by
  have hd : ∀ ξ : H1_38, (A-A') (i10_38 ξ) = i20_38 ((D-D') ξ) := by
    intro ξ
    simp only [ContinuousLinearMap.sub_apply, hD, hD', map_sub]
  have he : ∀ ξ : H1_38, ContinuousLinearMap.adjoint (A-A') (i10_38 ξ) =
      i20_38 ((E-E') ξ) := by
    intro ξ
    simp only [map_sub, ContinuousLinearMap.sub_apply, hE, hE']
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro h
  refine g03i_denseRange_i10.induction_on
    (p := fun z : H0_38 => ‖(g03i_lift D - g03i_lift D') z‖ ≤
      (‖D-D'‖+‖E-E'‖) * ‖z‖) h ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro ξ
    simp only [ContinuousLinearMap.sub_apply, g03i_lift_on_h1 A D E hD hE,
      g03i_lift_on_h1 A' D' E' hD' hE']
    have hs := g03i_dense_input_bound (A-A') (D-D') (E-E') hd he ξ
    simpa only [ContinuousLinearMap.sub_apply, map_sub] using hs

/-- Actual h0-to-h1 extension of B(x), using the already constructed source smoothing map. -/
def g03i_actualLift (x : H1_38) : H0_38 →L[ℝ] H1_38 :=
  g03i_lift (PDE.actualBirkhoffInput38.Dfwd PDE.actualOneSmoothingInput38 x)

theorem g03i_actualLift_on_h1 (x ξ : H1_38) :
    g03i_actualLift x (i10_38 ξ) =
      i21_38 (PDE.actualBirkhoffInput38.Dfwd PDE.actualOneSmoothingInput38 x ξ) :=
  g03i_lift_on_h1 _ _ _ (PDE.actualBirkhoffInput38.Bop_incl PDE.actualOneSmoothingInput38 x)
    (PDE.actualBirkhoffInput38.Bop_adjoint_incl PDE.actualOneSmoothingInput38 x) ξ

theorem g03i_actualLift_compatible (x : H1_38) (h : H0_38) :
    i10_38 (g03i_actualLift x h) = PDE.actualBirkhoffInput38.Bop (i10_38 x) h :=
  g03i_lift_compatible _ _ _ (PDE.actualBirkhoffInput38.Bop_incl PDE.actualOneSmoothingInput38 x)
    (PDE.actualBirkhoffInput38.Bop_adjoint_incl PDE.actualOneSmoothingInput38 x) h

/-- Agreement with the landed negative extension on the entire common h0 domain. -/
theorem g03i_actualLift_dual_compatible (x : H1_38) (h : H0_38) :
    g03ActualDualExtension x
      (carrierIncl38 (by norm_num : (-(((1+1 : ℕ)) : ℝ)) ≤ ((0 : ℕ) : ℝ)) h) =
      carrierIncl38 (by norm_num : (-((1 : ℕ) : ℝ)) ≤ ((1 : ℕ) : ℝ))
        (g03i_actualLift x h) := by
  rw [g03ActualDualExtension_compatible]
  apply carrierExt38
  funext n
  rw [carrierCoe38_incl38, carrierCoe38_incl38]
  have hc := congrArg (fun z : H0_38 => carrierCoe38 ((0 : ℕ) : ℝ) z n)
    (g03i_actualLift_compatible x h)
  simpa only [carrierCoe38_i10] using hc.symm

theorem g03i_actualLift_norm (x : H1_38) :
    ‖g03i_actualLift x‖ ≤
      ‖PDE.actualBirkhoffInput38.Dfwd PDE.actualOneSmoothingInput38 x‖ +
      ‖PDE.actualBirkhoffInput38.Dadj PDE.actualOneSmoothingInput38 x‖ :=
  g03i_lift_norm _ _ _ (PDE.actualBirkhoffInput38.Bop_incl PDE.actualOneSmoothingInput38 x)
    (PDE.actualBirkhoffInput38.Bop_adjoint_incl PDE.actualOneSmoothingInput38 x)

theorem g03i_actualLift_difference_bound (x y : H1_38) :
    ‖g03i_actualLift x - g03i_actualLift y‖ ≤
      ‖PDE.actualBirkhoffInput38.Dfwd PDE.actualOneSmoothingInput38 x -
        PDE.actualBirkhoffInput38.Dfwd PDE.actualOneSmoothingInput38 y‖ +
      ‖PDE.actualBirkhoffInput38.Dadj PDE.actualOneSmoothingInput38 x -
        PDE.actualBirkhoffInput38.Dadj PDE.actualOneSmoothingInput38 y‖ :=
  g03i_lift_difference_bound _ _ _ _ _ _
    (PDE.actualBirkhoffInput38.Bop_incl PDE.actualOneSmoothingInput38 x)
    (PDE.actualBirkhoffInput38.Bop_adjoint_incl PDE.actualOneSmoothingInput38 x)
    (PDE.actualBirkhoffInput38.Bop_incl PDE.actualOneSmoothingInput38 y)
    (PDE.actualBirkhoffInput38.Bop_adjoint_incl PDE.actualOneSmoothingInput38 y)

theorem continuous_g03i_actualLift : Continuous g03i_actualLift := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hD : Filter.Tendsto (fun y =>
      ‖PDE.actualBirkhoffInput38.Dfwd PDE.actualOneSmoothingInput38 y -
        PDE.actualBirkhoffInput38.Dfwd PDE.actualOneSmoothingInput38 x‖) (nhds x) (nhds 0) := by
    simpa using (((PDE.actualBirkhoffInput38.continuous_Dfwd
      PDE.actualOneSmoothingInput38).tendsto x).sub_const
      (PDE.actualBirkhoffInput38.Dfwd PDE.actualOneSmoothingInput38 x)).norm
  have hE : Filter.Tendsto (fun y =>
      ‖PDE.actualBirkhoffInput38.Dadj PDE.actualOneSmoothingInput38 y -
        PDE.actualBirkhoffInput38.Dadj PDE.actualOneSmoothingInput38 x‖) (nhds x) (nhds 0) := by
    simpa using (((PDE.actualBirkhoffInput38.continuous_Dadj
      PDE.actualOneSmoothingInput38).tendsto x).sub_const
      (PDE.actualBirkhoffInput38.Dadj PDE.actualOneSmoothingInput38 x)).norm
  have hb : Filter.Tendsto (fun y =>
      ‖PDE.actualBirkhoffInput38.Dfwd PDE.actualOneSmoothingInput38 y -
        PDE.actualBirkhoffInput38.Dfwd PDE.actualOneSmoothingInput38 x‖ +
      ‖PDE.actualBirkhoffInput38.Dadj PDE.actualOneSmoothingInput38 y -
        PDE.actualBirkhoffInput38.Dadj PDE.actualOneSmoothingInput38 x‖) (nhds x) (nhds 0) := by
    simpa only [add_zero] using hD.add hE
  exact squeeze_zero (fun _ => norm_nonneg _) (fun y => g03i_actualLift_difference_bound y x) hb

/-- G03 interpolation: a continuous h1-base-point family of genuine h0-to-h1 operators,
whose inclusion is the SAME actual Birkhoff perturbation on the entire h0 domain. -/
theorem grouped_f01_interpolation_gain :
    ∃ G : H1_38 → (H0_38 →L[ℝ] H1_38), Continuous G ∧
      (∀ (x : H1_38) (h : H0_38),
        i10_38 (G x h) = PDE.actualBirkhoffInput38.Bop (i10_38 x) h) ∧
      (∀ (x ξ : H1_38), G x (i10_38 ξ) =
        i21_38 (PDE.actualBirkhoffInput38.Dfwd PDE.actualOneSmoothingInput38 x ξ)) :=
  ⟨g03i_actualLift, continuous_g03i_actualLift,
    g03i_actualLift_compatible, g03i_actualLift_on_h1⟩

/-- The exact G03 gain head proposed in GROUPED_LEDGER01, with no new hypotheses. -/
theorem grouped_f01_gain :
    ∃ G : H1_38 → (H0_38 →L[ℝ] H1_38), Continuous G ∧
      ∀ (x : H1_38) (h : H0_38),
        i10_38 (G x h) = PDE.actualBirkhoffInput38.Bop (i10_38 x) h :=
  ⟨g03i_actualLift, continuous_g03i_actualLift, g03i_actualLift_compatible⟩

end NlsGge.ThirdConsultation.Narrative
