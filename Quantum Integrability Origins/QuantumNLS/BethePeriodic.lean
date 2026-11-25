import QuantumNLS.BetheContact
import QuantumNLS.BetheConvexity
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
Periodic outer-face identities for the literal finite coordinate Bethe ansatz.
Source: foundations/periodic_basis.tex:231--246, positive i exponent and
decreasing labels I_i = n_i + (N-1)/2-i. Frozen contact input: 533c6df6.
This module does not construct a periodic H1 extension or an operator-domain
eigenvector, and makes no normalization, completeness, or U5 claim.
-/

noncomputable section
open scoped BigOperators

namespace QuantumNLS.BethePeriodic
open BetheAdmission BetheSmooth BetheWavefunctions BetheContact

/-- The source's oriented scattering ratio. -/
def scattering (c d : ℝ) : ℂ :=
  ((d : ℂ) + Complex.I * (c : ℂ)) / ((d : ℂ) - Complex.I * (c : ℂ))

theorem scattering_eq_exp {c : ℝ} (hc : c ≠ 0) (d : ℝ) :
    scattering c d = -Complex.exp (-2 * Complex.I * (Real.arctan (d / c) : ℂ)) := by
  have hplus : 1 + (d / c : ℝ) * Complex.I ≠ (0 : ℂ) := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hminus : 1 - (d / c : ℝ) * Complex.I ≠ (0 : ℂ) := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have he : -2 * Complex.I * (Real.arctan (d / c) : ℂ) =
      -Complex.log ((1 + (d / c : ℝ) * Complex.I) /
        (1 - (d / c : ℝ) * Complex.I)) := by
    rw [Complex.ofReal_arctan, Complex.arctan]
    ring_nf
    simp [Complex.I_sq]
  rw [he, Complex.exp_neg, Complex.exp_log (div_ne_zero hplus hminus), inv_div]
  unfold scattering
  push_cast
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hd : (d : ℂ) - Complex.I * (c : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hc this
  have hn : (d : ℂ) * Complex.I + (c : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hc this
  field_simp [hc', hn]
  ring_nf
  simp only [Complex.I_sq]
  field_simp [hn]
  ring_nf
  simp [Complex.I_sq]

/-- Exponentiating the literal half-integer source labels supplies the
parity factor; integer labels do not change it. -/
theorem sourceNumbers_exp {N : ℕ} (n : Fin (N+1) → ℤ) (i : Fin (N+1)) :
    Complex.exp (Complex.I * ((2 * Real.pi * sourceNumbers n i : ℝ) : ℂ)) =
      (-1 : ℂ)^N := by
  have he : Complex.I * ((2 * Real.pi * sourceNumbers n i : ℝ) : ℂ) =
      ((n i - (i.val : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) +
        (N : ℂ) * (Real.pi * Complex.I) := by
    simp only [sourceNumbers]
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    Complex.exp_nat_mul, Complex.exp_pi_mul_I, one_mul]

theorem coefficient_cons {N : ℕ} (c a : ℝ) (q : Fin N → ℝ) :
    coefficient c (Fin.cons a q) =
      (∏ j, factor c a (q j)) * coefficient c q := by
  classical
  simp only [coefficient, Finset.prod_filter]
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.prod_univ_succ, Fin.cons_succ,
    lt_self_iff_false, Fin.succ_pos, Fin.succ_lt_succ_iff,
    not_lt_zero, ite_false, ite_true, one_mul]

theorem coefficient_snoc {N : ℕ} (c a : ℝ) (q : Fin N → ℝ) :
    coefficient c (Fin.snoc q a) =
      coefficient c q * (∏ j, factor c (q j) a) := by
  classical
  simp only [coefficient, Finset.prod_filter]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_last, Fin.prod_univ_castSucc, Fin.snoc_castSucc,
    Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_last, not_lt_of_ge (Fin.le_last _),
    ite_false, ite_true, mul_one, Finset.prod_mul_distrib,
    Finset.prod_const_one]

/-- The exponential equations are derived from the logarithmic equations,
including the N scattering minus signs and half-integer label parity. -/
theorem exponential_of_logarithmic {N : ℕ} {L c : ℝ} (hc : 0 < c)
    (n : Fin (N+1) → ℤ) (q : Fin (N+1) → ℝ)
    (hq : logMap L c q = fun i => 2 * Real.pi * sourceNumbers n i)
    (i : Fin (N+1)) :
    Complex.exp (Complex.I * ((L * q i : ℝ) : ℂ)) =
      ∏ j ∈ Finset.univ.erase i, scattering c (q i - q j) := by
  classical
  have he : L * q i = 2 * Real.pi * sourceNumbers n i -
      2 * ∑ j ∈ Finset.univ.erase i, Real.arctan ((q i - q j) / c) := by
    have h := congrFun hq i
    rw [logMap_erase] at h
    linarith
  rw [he]
  have hex : Complex.I * ((2 * Real.pi * sourceNumbers n i -
      2 * ∑ j ∈ Finset.univ.erase i, Real.arctan ((q i - q j) / c) : ℝ) : ℂ) =
      Complex.I * ((2 * Real.pi * sourceNumbers n i : ℝ) : ℂ) +
        ∑ j ∈ Finset.univ.erase i,
          -2 * Complex.I * (Real.arctan ((q i - q j) / c) : ℂ) := by
    push_cast
    rw [← Finset.mul_sum]
    ring
  rw [hex, Complex.exp_add, sourceNumbers_exp, Complex.exp_sum]
  simp_rw [scattering_eq_exp hc.ne']
  rw [Finset.prod_neg]
  simp

/-- The actual roots supplied by the proved Yang--Yang construction satisfy
the source exponential Bethe equations; no exponential premise is supplied. -/
theorem sourceRoots_exponential {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (i : Fin (N+1)) :
    Complex.exp (Complex.I * ((L * sourceRoots L n c i : ℝ) : ℂ)) =
      ∏ j ∈ Finset.univ.erase i,
        scattering c (sourceRoots L n c i - sourceRoots L n c j) :=
  exponential_of_logarithmic hc n _ ((BetheConvexity.source_roots_spec hL hn).2 c hc).1 i

/-- Equation `basis:eq:bethe` with the source's numerator, denominator,
and positive i exponent written out literally. -/
theorem sourceRoots_exponential_printed {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (i : Fin (N+1)) :
    Complex.exp (Complex.I * ((L * sourceRoots L n c i : ℝ) : ℂ)) =
      ∏ j ∈ Finset.univ.erase i,
        (((sourceRoots L n c i - sourceRoots L n c j : ℝ) : ℂ) + Complex.I * (c : ℂ)) /
          (((sourceRoots L n c i - sourceRoots L n c j : ℝ) : ℂ) - Complex.I * (c : ℂ)) :=
  sourceRoots_exponential hL hc hn i

theorem factor_reverse {c a b : ℝ} (hc : c ≠ 0) (hab : a ≠ b) :
    factor c b a = factor c a b * scattering c (a - b) := by
  have hd : ((a - b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hab)
  have hs : ((a - b : ℝ) : ℂ) - Complex.I * (c : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hc this
  have hr : ((b - a : ℝ) : ℂ) = -((a - b : ℝ) : ℂ) := by push_cast; ring
  unfold factor scattering
  rw [hr]
  field_simp
  ring

/-- Moving the first rapidity to the last place changes the literal pair
product by exactly the source's product of oriented scattering ratios. -/
theorem coefficient_rotate {N : ℕ} {c : ℝ} (hc : c ≠ 0)
    (q : Fin (N+1) → ℝ) (hq : Function.Injective q) :
    coefficient c (q ∘ finRotate (N+1)) = coefficient c q *
      ∏ j : Fin N, scattering c (q 0 - q j.succ) := by
  have hcons := coefficient_cons c (q 0) (Fin.tail q)
  rw [Fin.cons_self_tail] at hcons
  have hrot : q ∘ finRotate (N+1) = Fin.snoc (Fin.tail q) (q 0) := by
    rw [Fin.snoc_eq_cons_rotate, Fin.cons_self_tail]
    rfl
  rw [hrot, coefficient_snoc, hcons]
  have hf (j : Fin N) : factor c (Fin.tail q j) (q 0) =
      factor c (q 0) (Fin.tail q j) * scattering c (q 0 - q j.succ) := by
    exact factor_reverse hc (fun h => Fin.succ_ne_zero j (hq h).symm)
  simp_rw [hf]
  rw [Finset.prod_mul_distrib]
  ring

theorem coefficient_rotate_ratio {N : ℕ} {c : ℝ} (hc : c ≠ 0)
    (q : Fin (N+1) → ℝ) (hq : Function.Injective q) :
    coefficient c (q ∘ finRotate (N+1)) / coefficient c q =
      ∏ j : Fin N, scattering c (q 0 - q j.succ) := by
  rw [coefficient_rotate hc q hq]
  exact mul_div_cancel_left₀ _ (coefficient_ne_zero c q)

/-- Reindexing the scattering product by a permutation removes precisely
the label placed first, rather than a rank chosen by a sign convention. -/
theorem scattering_product_permute {N : ℕ} (c : ℝ) (q : Fin (N+1) → ℝ)
    (σ : Equiv.Perm (Fin (N+1))) :
    (∏ j : Fin N, scattering c (q (σ 0) - q (σ j.succ))) =
      ∏ k ∈ Finset.univ.erase (σ 0), scattering c (q (σ 0) - q k) := by
  classical
  refine Finset.prod_bij (fun j _ => σ j.succ) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro j _
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact fun h => Fin.succ_ne_zero j (σ.injective h)
  · intro a _ b _ h
    exact Fin.succ_injective _ (σ.injective h)
  · intro k hk
    have hz : σ.symm k ≠ 0 := by
      intro h
      have := congrArg σ h
      simp only [Equiv.apply_symm_apply] at this
      exact (Finset.mem_erase.mp hk).1 this
    obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero hz
    exact ⟨j, Finset.mem_univ _, by simp [← hj]⟩

/-- Cyclic reindexing of assignments is a proved bijection. The rotation
acts on positions, and never changes the sign of a rapidity. -/
def rotatePermutation {N : ℕ} (σ : Equiv.Perm (Fin (N+1))) :
    Equiv.Perm (Fin (N+1)) := (finRotate (N+1)).trans σ

theorem rotatePermutation_bijective (N : ℕ) :
    Function.Bijective (rotatePermutation (N := N)) := by
  constructor
  · intro σ τ h
    apply Equiv.ext
    intro i
    have := congrArg (fun ρ : Equiv.Perm (Fin (N+1)) => ρ ((finRotate (N+1)).symm i)) h
    simpa [rotatePermutation] using this
  · intro τ
    refine ⟨(finRotate (N+1)).symm.trans τ, ?_⟩
    ext i
    simp [rotatePermutation]

theorem sourceRoots_coefficient_rotate {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (σ : Equiv.Perm (Fin (N+1))) :
    coefficient c (sourceRoots L n c ∘ rotatePermutation σ) =
      coefficient c (sourceRoots L n c ∘ σ) *
        Complex.exp (Complex.I * ((L * sourceRoots L n c (σ 0) : ℝ) : ℂ)) := by
  have hq := (sourceRoots_strictAnti hL hc hn).injective
  change coefficient c ((sourceRoots L n c ∘ σ) ∘ finRotate (N+1)) = _
  rw [coefficient_rotate hc.ne' _ (hq.comp σ.injective)]
  rw [sourceRoots_exponential hL hc hn, ← scattering_product_permute]
  rfl

theorem planeWave_cons {N : ℕ} (q : Fin (N+1) → ℝ) (x : Fin N → ℝ) (t : ℝ) :
    planeWave q (Fin.cons t x) =
      Complex.exp (Complex.I * ((q 0 * t : ℝ) : ℂ)) * planeWave (Fin.tail q) x := by
  simp only [planeWave, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]

theorem planeWave_snoc_rotate {N : ℕ} (q : Fin (N+1) → ℝ) (x : Fin N → ℝ) (t : ℝ) :
    planeWave (q ∘ finRotate (N+1)) (Fin.snoc x t) = planeWave q (Fin.cons t x) := by
  have hx : Fin.snoc x t = Fin.cons t x ∘ finRotate (N+1) := Fin.snoc_eq_cons_rotate x t
  unfold planeWave
  rw [hx]
  congr 2
  exact congrArg Complex.ofReal ((finRotate (N+1)).bijective.sum_comp
    (fun i => q i * (Fin.cons t x : Fin (N+1) → ℝ) i))

/-- Termwise outer-face matching includes an arbitrary real displacement
t of the crossing coordinate; t=0 is the pair of source boundary faces. -/
theorem sourceRoots_term_periodic {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (σ : Equiv.Perm (Fin (N+1)))
    (x : Fin N → ℝ) (t : ℝ) :
    coefficient c (sourceRoots L n c ∘ σ) *
        planeWave (sourceRoots L n c ∘ σ) (Fin.cons (L+t) x) =
      coefficient c (sourceRoots L n c ∘ rotatePermutation σ) *
        planeWave (sourceRoots L n c ∘ rotatePermutation σ) (Fin.snoc x t) := by
  rw [sourceRoots_coefficient_rotate hL hc hn]
  change _ = _ * planeWave ((sourceRoots L n c ∘ σ) ∘ finRotate (N+1)) _
  rw [planeWave_snoc_rotate, planeWave_cons, planeWave_cons]
  have he : Complex.I * ((sourceRoots L n c (σ 0) * (L+t) : ℝ) : ℂ) =
      Complex.I * ((L * sourceRoots L n c (σ 0) : ℝ) : ℂ) +
        Complex.I * ((sourceRoots L n c (σ 0) * t : ℝ) : ℂ) := by push_cast; ring
  simp only [Function.comp_apply] at *
  rw [he, Complex.exp_add]
  ring

/-- Actual finite-sum periodic matching, by the cyclic bijection of all
rapidity assignments. No periodicity premise is assumed. -/
theorem wavefunction_periodic_faces {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (x : Fin N → ℝ) (t : ℝ) :
    wavefunction L c n (Fin.cons (L+t) x) = wavefunction L c n (Fin.snoc x t) := by
  classical
  unfold wavefunction coordinateAnsatz
  simp_rw [sourceRoots_term_periodic hL hc hn]
  exact (rotatePermutation_bijective N).sum_comp
    (fun σ : Equiv.Perm (Fin (N+1)) => coefficient c (sourceRoots L n c ∘ σ) *
      planeWave (sourceRoots L n c ∘ σ) (Fin.snoc x t))

theorem wavefunction_outer_faces {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (x : Fin N → ℝ) :
    wavefunction L c n (Fin.cons L x) = wavefunction L c n (Fin.snoc x 0) := by
  simpa using wavefunction_periodic_faces hL hc hn x 0

/-- Directional frequency identity for the actual real coordinate line. -/
theorem frequency_line {N : ℕ} (q x v : Fin N → ℝ) (r : ℝ) :
    (∑ i, q i * (x i + r * v i)) =
      (∑ i, q i * x i) + r * ∑ i, q i * v i := by
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  simp_rw [show ∀ i, q i * (r * v i) = r * (q i * v i) from fun i => by ring]
  rw [Finset.mul_sum]

theorem planeWave_line_hasDerivAt {N : ℕ} (q x v : Fin N → ℝ) :
    HasDerivAt (fun r : ℝ => planeWave q (fun i => x i + r * v i))
      (Complex.I * ((∑ i, q i * v i : ℝ) : ℂ) * planeWave q x) 0 := by
  have hd : HasDerivAt (fun r : ℝ => (∑ i, q i * x i) + r * ∑ i, q i * v i)
      (∑ i, q i * v i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (∑ i, q i * v i)).const_add
      (∑ i, q i * x i)
  have hdc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hd
  simpa [planeWave, frequency_line, Function.comp_def, mul_comm] using
    (hdc.const_mul Complex.I).cexp

/-- The finite ansatz derivative is proved by differentiating every actual
exponential and its finite sum. -/
theorem coordinateAnsatz_line_hasDerivAt {N : ℕ} (c : ℝ) (q x v : Fin N → ℝ) :
    HasDerivAt (fun r : ℝ => coordinateAnsatz c q (fun i => x i + r * v i))
      (∑ σ : Equiv.Perm (Fin N), coefficient c (q ∘ σ) *
        (Complex.I * ((∑ i, q (σ i) * v i : ℝ) : ℂ) * planeWave (q ∘ σ) x)) 0 := by
  classical
  exact HasDerivAt.fun_sum (u := Finset.univ)
    (fun σ _ => (planeWave_line_hasDerivAt (q ∘ σ) x v).const_mul
      (coefficient c (q ∘ σ)))

/-- All first directional derivatives match at the outer faces under the
same cyclic coordinate identification. The common value is the literal
finite derivative sum, and w/v allow both normal and tangential directions. -/
theorem wavefunction_faces_hasDerivAt {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (x v : Fin N → ℝ) (w : ℝ) :
    let D := ∑ σ : Equiv.Perm (Fin (N+1)),
      coefficient c (sourceRoots L n c ∘ σ) *
        (Complex.I * ((∑ i, sourceRoots L n c (σ i) *
          (Fin.cons w v : Fin (N+1) → ℝ) i : ℝ) : ℂ) *
          planeWave (sourceRoots L n c ∘ σ) (Fin.cons L x))
    HasDerivAt (fun r : ℝ => wavefunction L c n
      (Fin.cons (L+r*w) (fun j => x j + r * v j))) D 0 ∧
    HasDerivAt (fun r : ℝ => wavefunction L c n
      (Fin.snoc (fun j => x j + r * v j) (r*w))) D 0 := by
  dsimp only
  have he (r : ℝ) : (fun i => (Fin.cons L x : Fin (N+1) → ℝ) i +
      r * (Fin.cons w v : Fin (N+1) → ℝ) i) =
      Fin.cons (L+r*w) (fun j => x j + r * v j) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hu := coordinateAnsatz_line_hasDerivAt c (sourceRoots L n c)
    (Fin.cons L x) (Fin.cons w v)
  simp_rw [he] at hu
  change HasDerivAt _ _ _ ∧ HasDerivAt _ _ _
  constructor
  · exact hu
  · have hf : (fun r : ℝ => wavefunction L c n
        (Fin.snoc (fun j => x j + r * v j) (r*w))) =
        (fun r : ℝ => wavefunction L c n
          (Fin.cons (L+r*w) (fun j => x j + r * v j))) := by
      funext r
      exact (wavefunction_periodic_faces hL hc hn _ _).symm
    rw [hf]
    exact hu

end QuantumNLS.BethePeriodic

#print axioms QuantumNLS.BethePeriodic.scattering
#print axioms QuantumNLS.BethePeriodic.scattering_eq_exp
#print axioms QuantumNLS.BethePeriodic.sourceNumbers_exp
#print axioms QuantumNLS.BethePeriodic.coefficient_cons
#print axioms QuantumNLS.BethePeriodic.coefficient_snoc
#print axioms QuantumNLS.BethePeriodic.exponential_of_logarithmic
#print axioms QuantumNLS.BethePeriodic.sourceRoots_exponential
#print axioms QuantumNLS.BethePeriodic.sourceRoots_exponential_printed
#print axioms QuantumNLS.BethePeriodic.factor_reverse
#print axioms QuantumNLS.BethePeriodic.coefficient_rotate
#print axioms QuantumNLS.BethePeriodic.coefficient_rotate_ratio
#print axioms QuantumNLS.BethePeriodic.scattering_product_permute
#print axioms QuantumNLS.BethePeriodic.rotatePermutation
#print axioms QuantumNLS.BethePeriodic.rotatePermutation_bijective
#print axioms QuantumNLS.BethePeriodic.sourceRoots_coefficient_rotate
#print axioms QuantumNLS.BethePeriodic.planeWave_cons
#print axioms QuantumNLS.BethePeriodic.planeWave_snoc_rotate
#print axioms QuantumNLS.BethePeriodic.sourceRoots_term_periodic
#print axioms QuantumNLS.BethePeriodic.wavefunction_periodic_faces
#print axioms QuantumNLS.BethePeriodic.wavefunction_outer_faces
#print axioms QuantumNLS.BethePeriodic.frequency_line
#print axioms QuantumNLS.BethePeriodic.planeWave_line_hasDerivAt
#print axioms QuantumNLS.BethePeriodic.coordinateAnsatz_line_hasDerivAt
#print axioms QuantumNLS.BethePeriodic.wavefunction_faces_hasDerivAt
