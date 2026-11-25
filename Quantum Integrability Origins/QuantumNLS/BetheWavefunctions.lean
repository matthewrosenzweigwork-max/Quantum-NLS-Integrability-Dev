import QuantumNLS.BetheSmooth
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.GroupTheory.Perm.Fin

/-!
Finite coordinate Bethe wavefunctions, a constituent of U5.
Report pin: 3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f.
Frozen BetheSmooth: fcd5511e378acd7ffb005714680901797a84169d17d7692dae2bcb165fc86911.
Source: foundations/periodic_basis.tex:24--41, 206--226, 267--286.

The printed decreasing labels and roots are used literally: I_i = n_i +
(N-1)/2-i. Reversing the increasing convention never negates a rapidity.
The sum below is the unnormalized formula on L>x_0>...>x_(N-1)>0.
No periodic extension, L2 eigenvector, basis, completeness or U5 unitary is
assumed or asserted. The contact calculation is a two-particle constituent.
The physical coupling is c (potential 2c delta), including c=kappa/N.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace QuantumNLS.BetheWavefunctions
open BetheAdmission BetheSmooth

/-- The source's decreasing open coordinate chamber. -/
def chamber (N : ℕ) (L : ℝ) : Set (Fin N → ℝ) :=
  {x | StrictAnti x ∧ ∀ i, 0 < x i ∧ x i < L}

/-- Each literal scattering coefficient factor, totalized by field division.
Physical roots have distinct entries, proved below. -/
def factor (c a b : ℝ) : ℂ := 1 - Complex.I * (c : ℂ) / ((a - b : ℝ) : ℂ)

theorem factor_re (c a b : ℝ) : (factor c a b).re = 1 := by
  simp [factor, div_eq_mul_inv, Complex.mul_re, Complex.mul_im]

theorem factor_ne_zero (c a b : ℝ) : factor c a b ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [factor_re] at this

/-- The source coefficient C_c(q), with each unordered pair once. -/
def coefficient {N : ℕ} (c : ℝ) (q : Fin N → ℝ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), factor c (q i) (q j)

theorem coefficient_ne_zero {N : ℕ} (c : ℝ) (q : Fin N → ℝ) :
    coefficient c q ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact factor_ne_zero c (q i) (q j)

/-- Plane waves use real rapidities, with the source positive i exponent. -/
def planeWave {N : ℕ} (q x : Fin N → ℝ) : ℂ :=
  Complex.exp (Complex.I * ((∑ i, q i * x i : ℝ) : ℂ))

theorem planeWave_norm {N : ℕ} (q x : Fin N → ℝ) : ‖planeWave q x‖ = 1 := by
  simp [planeWave, Complex.norm_exp, Complex.mul_re]

/-- The finite coordinate ansatz. The permutations enumerate every assignment
of rapidities to positions once; inverse versus direct permutation has the
same full sum. This formula is defined on real coordinates before extension. -/
def coordinateAnsatz {N : ℕ} (c : ℝ) (q x : Fin N → ℝ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin N), coefficient c (q ∘ σ) * planeWave (q ∘ σ) x

/-- Actual wavefunction formula from roots constructed by Yang--Yang
minimization. It agrees with the source formula on `chamber N L`. -/
def wavefunction {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (x : Fin N → ℝ) : ℂ :=
  coordinateAnsatz c (sourceRoots L n c) x

theorem wavefunction_chamber_formula {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (x : Fin N → ℝ) :
    wavefunction L c n x = ∑ σ : Equiv.Perm (Fin N),
      (∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        (1 - Complex.I * (c : ℂ) /
          ((sourceRoots L n c (σ i) - sourceRoots L n c (σ j) : ℝ) : ℂ))) *
      Complex.exp (Complex.I * ((∑ i, sourceRoots L n c (σ i) * x i : ℝ) : ℂ)) := rfl

/-- The finite expression is smooth in coordinates even before a chamber
restriction. This does not assert smoothness of a symmetric extension. -/
theorem coordinateAnsatz_contDiff {N : ℕ} (c : ℝ) (q : Fin N → ℝ) :
    ContDiff ℝ ∞ (coordinateAnsatz c q) := by
  unfold coordinateAnsatz
  apply ContDiff.sum
  intro σ _
  have hd : ContDiff ℝ ∞ (fun x : Fin N → ℝ => ∑ i, q (σ i) * x i) := by fun_prop
  exact contDiff_const.mul (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hd)).cexp

/-- In the one-particle sector the coefficient is exactly one. -/
theorem coordinateAnsatz_one (c : ℝ) (q x : Fin 1 → ℝ) :
    coordinateAnsatz c q x = Complex.exp (Complex.I * ((q 0 * x 0 : ℝ) : ℂ)) := by
  simp [coordinateAnsatz, coefficient, planeWave, Finset.prod_filter]

/-- Elementary physical normalization with ordinary Lebesgue measure: the
one-particle formula has norm squared 1/L after division by sqrt L. -/
theorem wavefunction_one_normalized {L : ℝ} (hL : 0 < L) (c : ℝ)
    (n : Fin 1 → ℤ) :
    (∫ x in (0 : ℝ)..L,
      ‖((Real.sqrt L : ℂ)⁻¹) * wavefunction L c n (fun _ => x)‖ ^ 2) = 1 := by
  have hi (x : ℝ) :
      ‖((Real.sqrt L : ℂ)⁻¹) * wavefunction L c n (fun _ => x)‖ ^ 2 = L⁻¹ := by
    simp only [wavefunction, coordinateAnsatz_one, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg L),
      Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_self,
      Real.exp_zero, mul_one, inv_pow, Real.sq_sqrt hL.le]
  simp only [hi, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  exact mul_inv_cancel₀ hL.ne'

/-- The actual on-shell tuple has no coefficient poles. -/
theorem sourceRoots_difference_ne_zero {N : ℕ} {L c : ℝ} (hL : 0 < L)
    (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (σ : Equiv.Perm (Fin N)) {i j : Fin N} (hij : i ≠ j) :
    sourceRoots L n c (σ i) - sourceRoots L n c (σ j) ≠ 0 := by
  exact sub_ne_zero.mpr (fun h => hij (σ.injective
    ((sourceRoots_strictAnti hL hc hn).injective h)))

/-- Distinct permutation assignments really have distinct frequency vectors. -/
theorem permuted_roots_injective {N : ℕ} {L c : ℝ} (hL : 0 < L)
    (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n) :
    Function.Injective (fun σ : Equiv.Perm (Fin N) => sourceRoots L n c ∘ σ) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  exact (sourceRoots_strictAnti hL hc hn).injective (congrFun h i)

/-- Opposite pair factors add to two. No normalization has been inserted. -/
theorem factor_add_reverse (c a b : ℝ) : factor c a b + factor c b a = 2 := by
  have h : ((b - a : ℝ) : ℂ) = -((a - b : ℝ) : ℂ) := by push_cast; ring
  simp only [factor, h, div_neg]
  ring

/-- The exact local coefficient identity fixing the sign and the factor c
in the collision condition. It is valid for any spectator multiplier. -/
theorem factor_contact (c a b : ℝ) (hab : a ≠ b) :
    Complex.I * ((a - b : ℝ) : ℂ) * (factor c a b - factor c b a) =
      (c : ℂ) * (factor c a b + factor c b a) := by
  have hd : ((a - b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hab)
  have h : ((b - a : ℝ) : ℂ) = -((a - b : ℝ) : ℂ) := by push_cast; ring
  simp only [factor, h, div_neg]
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Two waves paired at a collision, with their literal source coefficients. -/
def pairWave (c a b x y : ℝ) : ℂ :=
  factor c a b * Complex.exp (Complex.I * ((a * x + b * y : ℝ) : ℂ)) +
  factor c b a * Complex.exp (Complex.I * ((b * x + a * y : ℝ) : ℂ))

theorem coefficient_two (c : ℝ) (q : Fin 2 → ℝ) :
    coefficient c q = factor c (q 0) (q 1) := by
  simp [coefficient, Fin.prod_univ_two, Finset.prod_filter]

/-- The local calculation is the full ansatz in the two-particle sector. -/
theorem coordinateAnsatz_two (c : ℝ) (q x : Fin 2 → ℝ) :
    coordinateAnsatz c q x = pairWave c (q 0) (q 1) (x 0) (x 1) := by
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  have he : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  simp [coordinateAnsatz, hu, Finset.sum_pair he, coefficient_two, planeWave,
    Fin.sum_univ_two, pairWave]

theorem pairWave_diagonal (c a b t : ℝ) :
    pairWave c a b t t = 2 * Complex.exp (Complex.I * (((a + b) * t : ℝ) : ℂ)) := by
  have h₁ : a * t + b * t = (a + b) * t := by ring
  have h₂ : b * t + a * t = (a + b) * t := by ring
  rw [pairWave, h₁, h₂, ← add_mul, factor_add_reverse]

theorem coordinateAnsatz_two_nonzero (c : ℝ) (q : Fin 2 → ℝ) (t : ℝ) :
    coordinateAnsatz c q (fun _ => t) ≠ 0 := by
  rw [coordinateAnsatz_two, pairWave_diagonal]
  exact mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)

/-- Along the actual relative-coordinate line (x,y)=(t+r,t-r), the
derivative at r=0 is exactly c times the boundary value. This is
(partial_x-partial_y)psi=c psi; using (t+r/2,t-r/2) gives c/2. -/
theorem pairWave_contact_hasDerivAt (c a b t : ℝ) (hab : a ≠ b) :
    HasDerivAt (fun r : ℝ => pairWave c a b (t + r) (t - r))
      ((c : ℂ) * pairWave c a b t t) 0 := by
  have hp (u v : ℝ) : HasDerivAt
      (fun r : ℝ => Complex.exp (Complex.I * ((u * (t + r) + v * (t - r) : ℝ) : ℂ)))
      (Complex.I * ((u - v : ℝ) : ℂ) *
        Complex.exp (Complex.I * (((u + v) * t : ℝ) : ℂ))) 0 := by
    have hd : HasDerivAt (fun r : ℝ => u * (t + r) + v * (t - r)) (u - v) 0 := by
      convert! (((hasDerivAt_id (0 : ℝ)).const_add t).const_mul u).add
        (((hasDerivAt_const (0 : ℝ) t).sub (hasDerivAt_id (0 : ℝ))).const_mul v) using 1
      ring
    have hdc : HasDerivAt (fun r : ℝ => ((u * (t + r) + v * (t - r) : ℝ) : ℂ))
        ((u - v : ℝ) : ℂ) 0 := by
      simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
        Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hd
    convert (hdc.const_mul Complex.I).cexp using 1
    simp
    ring
  convert ((hp a b).const_mul (factor c a b)).add
    ((hp b a).const_mul (factor c b a)) using 1
  · rfl
  · have h : ((b - a : ℝ) : ℂ) = -((a - b : ℝ) : ℂ) := by push_cast; ring
    rw [pairWave_diagonal]
    have he : (b + a) * t = (a + b) * t := by ring
    rw [he, h]
    have hc := factor_contact c a b hab
    rw [factor_add_reverse] at hc
    linear_combination -Complex.exp (Complex.I * (((a + b) * t : ℝ) : ℂ)) * hc

/-- The contact identity specializes to the wavefunction built from the
proved roots, with no eigenfunction or boundary axiom supplied by the caller. -/
theorem wavefunction_two_contact {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin 2 → ℤ} (hn : Antitone n) (t : ℝ) :
    HasDerivAt (fun r : ℝ => wavefunction L c n ![t + r, t - r])
      ((c : ℂ) * wavefunction L c n ![t, t]) 0 := by
  simp only [wavefunction, coordinateAnsatz_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact pairWave_contact_hasDerivAt c _ _ t
    ((sourceRoots_strictAnti hL hc hn) (by decide : (0 : Fin 2) < 1)).ne'

end QuantumNLS.BetheWavefunctions

#print axioms QuantumNLS.BetheWavefunctions.chamber
#print axioms QuantumNLS.BetheWavefunctions.factor
#print axioms QuantumNLS.BetheWavefunctions.factor_re
#print axioms QuantumNLS.BetheWavefunctions.factor_ne_zero
#print axioms QuantumNLS.BetheWavefunctions.coefficient
#print axioms QuantumNLS.BetheWavefunctions.coefficient_ne_zero
#print axioms QuantumNLS.BetheWavefunctions.planeWave
#print axioms QuantumNLS.BetheWavefunctions.planeWave_norm
#print axioms QuantumNLS.BetheWavefunctions.coordinateAnsatz
#print axioms QuantumNLS.BetheWavefunctions.wavefunction
#print axioms QuantumNLS.BetheWavefunctions.wavefunction_chamber_formula
#print axioms QuantumNLS.BetheWavefunctions.coordinateAnsatz_contDiff
#print axioms QuantumNLS.BetheWavefunctions.coordinateAnsatz_one
#print axioms QuantumNLS.BetheWavefunctions.wavefunction_one_normalized
#print axioms QuantumNLS.BetheWavefunctions.sourceRoots_difference_ne_zero
#print axioms QuantumNLS.BetheWavefunctions.permuted_roots_injective
#print axioms QuantumNLS.BetheWavefunctions.factor_add_reverse
#print axioms QuantumNLS.BetheWavefunctions.factor_contact
#print axioms QuantumNLS.BetheWavefunctions.pairWave
#print axioms QuantumNLS.BetheWavefunctions.coefficient_two
#print axioms QuantumNLS.BetheWavefunctions.coordinateAnsatz_two
#print axioms QuantumNLS.BetheWavefunctions.pairWave_diagonal
#print axioms QuantumNLS.BetheWavefunctions.coordinateAnsatz_two_nonzero
#print axioms QuantumNLS.BetheWavefunctions.pairWave_contact_hasDerivAt
#print axioms QuantumNLS.BetheWavefunctions.wavefunction_two_contact
