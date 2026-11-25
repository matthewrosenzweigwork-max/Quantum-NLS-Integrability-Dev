import QuantumNLS.Ext006PhysicalNormBridge

/-! All-degree tensor algebra for the physical pair exponential.
No norm/trace identity or commutator is taken as a hypothesis. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 350000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006PairPowerWick
open TensorCarrier PhysicalTensor IntrinsicContact BetheCoefficientTransform
open Ext006PhysicalExponentialTerms Ext006PhysicalNormBridge.CreationFormula

section TensorAlgebra
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Unsymmetrized completed tensor concatenation. -/
def concat {k m : ℕ} (x : HilbertTensorPower ℂ E k) (y : HilbertTensorPower ℂ E m) :
    HilbertTensorPower ℂ E (k+m) := (splitIsometry k m).symm (htmul x y)

lemma concat_continuous {k m : ℕ} : Continuous
    (fun p : HilbertTensorPower ℂ E k × HilbertTensorPower ℂ E m => concat p.1 p.2) :=
  (splitIsometry k m).symm.continuous.comp (htmulB (A := HilbertTensorPower ℂ E k)
    (F := HilbertTensorPower ℂ E m)).continuous₂

lemma concat_smul_left {k m : ℕ} (c : ℂ) (x : HilbertTensorPower ℂ E k)
    (y : HilbertTensorPower ℂ E m) : concat (c • x) y = c • concat x y := by
  simp only [concat, htmul_smul_left, map_smul]

lemma concat_smul_right {k m : ℕ} (c : ℂ) (x : HilbertTensorPower ℂ E k)
    (y : HilbertTensorPower ℂ E m) : concat x (c • y) = c • concat x y := by
  simp only [concat, htmul_smul_right, map_smul]

lemma concat_add_left {k m : ℕ} (x x' : HilbertTensorPower ℂ E k)
    (y : HilbertTensorPower ℂ E m) : concat (x+x') y = concat x y + concat x' y := by
  simp only [concat, htmul_add_left, map_add]

lemma concat_add_right {k m : ℕ} (x : HilbertTensorPower ℂ E k)
    (y y' : HilbertTensorPower ℂ E m) : concat x (y+y') = concat x y + concat x y' := by
  simp only [concat, htmul_add_right, map_add]

lemma concat_ptprod {k m : ℕ} (f : Fin k → E) (g : Fin m → E) :
    concat ((ptprod f : AlgTensorPower ℂ E k) : HilbertTensorPower ℂ E k)
      ((ptprod g : AlgTensorPower ℂ E m) : HilbertTensorPower ℂ E m) =
        ((ptprod (Fin.append f g) : AlgTensorPower ℂ E (k+m)) :
          HilbertTensorPower ℂ E (k+m)) := by
  rw [concat, ← splitIsometry_ptprod_append, LinearIsometryEquiv.symm_apply_apply]

/-- Concatenation as a bounded linear map in its second argument. -/
def concatLeftMap {k m : ℕ} (x : HilbertTensorPower ℂ E k) :
    HilbertTensorPower ℂ E m →L[ℂ] HilbertTensorPower ℂ E (k+m) :=
  (splitIsometry k m).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L htmulR x

lemma concatLeftMap_apply {k m : ℕ} (x : HilbertTensorPower ℂ E k)
    (y : HilbertTensorPower ℂ E m) : concatLeftMap x y = concat x y := rfl

/-- Concatenation as a bounded linear map in its first argument. -/
def concatRightMap {k m : ℕ} (y : HilbertTensorPower ℂ E m) :
    HilbertTensorPower ℂ E k →L[ℂ] HilbertTensorPower ℂ E (k+m) :=
  (splitIsometry k m).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (htcommIsometry ℂ (HilbertTensorPower ℂ E m)
      (HilbertTensorPower ℂ E k)).toContinuousLinearMap ∘L htmulR y

lemma concatRightMap_apply {k m : ℕ} (x : HilbertTensorPower ℂ E k)
    (y : HilbertTensorPower ℂ E m) : concatRightMap y x = concat x y := by
  simp only [concatRightMap, ContinuousLinearMap.comp_apply, htmulR_apply,
    LinearIsometry.coe_toContinuousLinearMap, htcommIsometry_htmul, concat]
  rfl

/-- Extend a permutation by the identity on the first block. -/
def rightPerm (k : ℕ) {m : ℕ} (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (k+m)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr (Equiv.refl (Fin k)) σ).trans finSumFinEquiv)

lemma concat_perm_right {k m : ℕ} (σ : Equiv.Perm (Fin m))
    (x : HilbertTensorPower ℂ E k) (y : HilbertTensorPower ℂ E m) :
    concat x (permHilbertIsometry σ y) = permHilbertIsometry (rightPerm k σ) (concat x y) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    have hc1 := (concatRightMap (E := E) (k := k) (m := m)
      (permHilbertIsometry σ y)).continuous
    have hc2 := (permHilbertIsometry (𝕜 := ℂ) (E := E) (rightPerm k σ)).continuous.comp
      (concatRightMap (E := E) (k := k) (m := m) y).continuous
    simpa only [Function.comp_apply, concatRightMap_apply] using isClosed_eq hc1 hc2
  | ih a =>
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod c f =>
      simp only [UniformSpace.Completion.coe_smul, concat_smul_left, map_smul]
      congr 1
      induction y using UniformSpace.Completion.induction_on with
      | hp =>
        let x : HilbertTensorPower ℂ E k := ((ptprod f : AlgTensorPower ℂ E k) : _)
        have hc1 := (concatLeftMap (E := E) (k := k) (m := m) x).continuous.comp
          (permHilbertIsometry (𝕜 := ℂ) (E := E) σ).continuous
        have hc2 := (permHilbertIsometry (𝕜 := ℂ) (E := E) (rightPerm k σ)).continuous.comp
          (concatLeftMap (E := E) (k := k) (m := m) x).continuous
        simpa only [Function.comp_apply, concatLeftMap_apply] using isClosed_eq hc1 hc2
      | ih a =>
        induction a using AlgTensorPower.induction_on with
        | smul_ptprod d g =>
          simp only [UniformSpace.Completion.coe_smul, map_smul, concat_smul_right,
            permHilbertIsometry_coe, permLinearEquiv_ptprod, concat_ptprod]
          have he : Fin.append f (fun i => g (σ.symm i)) =
              (fun i => Fin.append f g ((rightPerm k σ).symm i)) := by
            funext i
            refine Fin.addCases (fun j => ?_) (fun j => ?_) i
            · simp [rightPerm]
            · simp [rightPerm]
          exact congrArg (fun h : Fin (k+m) → E => d •
            ((ptprod h : AlgTensorPower ℂ E (k+m)) : HilbertTensorPower ℂ E (k+m))) he
        | add a b ha hb =>
          simp only [UniformSpace.Completion.coe_add, map_add, concat_add_right, ha, hb]
    | add a b ha hb =>
      simp only [UniformSpace.Completion.coe_add, concat_add_left, map_add, ha, hb]

lemma symProj_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : HilbertTensorPower ℂ E n) :
    symProj ℂ E n (permHilbertIsometry σ x) = symProj ℂ E n x := by
  have h := congrArg (fun A : HilbertTensorPower ℂ E n →L[ℂ] _ => A x)
    (groupAverage_mul_rep (permRep ℂ E n) σ)
  exact h

/-- Inner symmetrization can be removed before the final symmetrization.
This holds for arbitrary completed tensors and arbitrary block sizes. -/
theorem symProj_concat_symProj_right {k m : ℕ} (x : HilbertTensorPower ℂ E k)
    (y : HilbertTensorPower ℂ E m) :
    symProj ℂ E (k+m) (concat x (symProj ℂ E m y)) =
      symProj ℂ E (k+m) (concat x y) := by
  classical
  let C : HilbertTensorPower ℂ E m →L[ℂ] HilbertTensorPower ℂ E (k+m) :=
    (splitIsometry k m).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L htmulR x
  change symProj ℂ E (k+m) (C (symProj ℂ E m y)) = _
  rw [symProj_eq_factorial_average (𝕜 := ℂ) (E := E) m]
  simp only [smul_apply, sum_apply, map_smul, map_sum]
  have hs : ∀ σ : Equiv.Perm (Fin m),
      symProj ℂ E (k+m) (C ((permRep ℂ E m σ : _ →L[ℂ] _) y)) =
        symProj ℂ E (k+m) (concat x y) := by
    intro σ
    change symProj ℂ E (k+m) (concat x (permHilbertIsometry σ y)) = _
    rw [concat_perm_right, symProj_perm]
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero m),
    one_smul]

lemma inner_htpow_concat {k m : ℕ} (u : E) (x : HilbertTensorPower ℂ E k)
    (y : HilbertTensorPower ℂ E m) :
    inner ℂ (htpow (k+m) u) (concat x y) =
      inner ℂ (htpow k u) x * inner ℂ (htpow m u) y := by
  have hf : (fun _ : Fin (k+m) => u) =
      Fin.append (fun _ : Fin k => u) (fun _ : Fin m => u) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
  have hs : splitIsometry k m (htpow (k+m) u : HilbertTensorPower ℂ E (k+m)) =
      htmul (htpow k u) (htpow m u) := by
    change splitIsometry k m ((ptprod (fun _ : Fin (k+m) => u) : AlgTensorPower ℂ E (k+m)) : HilbertTensorPower ℂ E (k+m)) = _
    rw [hf, splitIsometry_ptprod_append]
    rfl
  have h := (splitIsometry (𝕜 := ℂ) (E := E) k m).inner_map_map
    (htpow (k+m) u) (concat x y)
  rw [hs, concat, LinearIsometryEquiv.apply_symm_apply, inner_htmul] at h
  exact h.symm

end TensorAlgebra

section PhysicalPowers
variable {L : ℝ} [Fact (0 < L)]

lemma coe_sectorCast {n m : ℕ} (h : n = m) (x : HN L n) :
    (sectorCast h x : HilbertTensorPower ℂ (L2T L) m) =
      castHTP h (x : HilbertTensorPower ℂ (L2T L) n) := by
  subst m
  rfl

lemma symProj_cast {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {n m : ℕ} (h : n = m) (x : HilbertTensorPower ℂ E n) :
    castHTP h (symProj ℂ E n x) = symProj ℂ E m (castHTP h x) := by
  subst m
  rfl

/-- The unsymmetrized n-fold power of the actual physical pair tensor. -/
def rawPower (b : HN L 2) : (n : ℕ) → HilbertTensorPower ℂ (L2T L) (2*n)
  | 0 => (Ext006ZeroVacuum.sectorVacuum L : HilbertTensorPower ℂ (L2T L) 0)
  | n+1 => castHTP (by omega : 2+2*n = 2*(n+1))
      (concat (b : HilbertTensorPower ℂ (L2T L) 2) (rawPower b n))

lemma sqrt_factorial_step (n : ℕ) :
    Real.sqrt ((((2*n : ℕ) : ℝ)+1)*(((2*n : ℕ) : ℝ)+2)) *
      Real.sqrt ((2*n).factorial : ℝ) = Real.sqrt ((2*(n+1)).factorial : ℝ) := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  have he : 2*(n+1) = (2*n+1)+1 := by omega
  rw [he, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  ring

/-- All creation powers, by induction: no intermediate projection remains. -/
theorem power_eq_sym_rawPower (b : HN L 2) (n : ℕ) :
    (power b n : HilbertTensorPower ℂ (L2T L) (2*n)) =
      (Real.sqrt ((2*n).factorial : ℝ) : ℂ) •
        symProj ℂ (L2T L) (2*n) (rawPower b n) := by
  induction n with
  | zero =>
    change (Ext006ZeroVacuum.sectorVacuum L : HilbertTensorPower ℂ (L2T L) 0) = _
    simp only [rawPower, Nat.mul_zero, Nat.factorial_zero, Nat.cast_one, Real.sqrt_one,
      Complex.ofReal_one, one_smul, symProj_zero, ContinuousLinearMap.id_apply]
  | succ n ih =>
    change (sectorCast (by omega : 2+2*n = 2*(n+1))
      (Ext005PairSector.creation b (2*n) (power b n)) :
        HilbertTensorPower ℂ (L2T L) (2*(n+1))) = _
    rw [coe_sectorCast, creation_eq_projection]
    change castHTP _ ((Real.sqrt ((((2*n : ℕ) : ℝ)+1)*(((2*n : ℕ) : ℝ)+2)) : ℂ) •
      (physSector L (2+2*n)).starProjection
        (concat (b : HilbertTensorPower ℂ (L2T L) 2)
          (power b n : HilbertTensorPower ℂ (L2T L) (2*n)))) = _
    rw [← symProj_eq_starProjection, ih, concat_smul_right]
    simp only [map_smul]
    rw [symProj_concat_symProj_right, smul_smul, ← Complex.ofReal_mul,
      sqrt_factorial_step, symProj_cast]
    rfl

/-- The exponential coefficient multiplying the single final symmetrization. -/
def amplitude (n : ℕ) : ℂ :=
  ((-1/2 : ℂ)^n / (n.factorial : ℂ)) * (Real.sqrt ((2*n).factorial : ℝ) : ℂ)

/-- Exact all-degree physical term formula, with sign and factorial. -/
theorem term_eq_sym_rawPower (b : HN L 2) (n : ℕ) :
    (term b n : HilbertTensorPower ℂ (L2T L) (2*n)) =
      amplitude n • symProj ℂ (L2T L) (2*n) (rawPower b n) := by
  rw [term_eq_power]
  change ((-1/2 : ℂ)^n / (n.factorial : ℂ)) •
    (power b n : HilbertTensorPower ℂ (L2T L) (2*n)) = _
  rw [power_eq_sym_rawPower, smul_smul]
  rfl

lemma amplitude_norm_sq (n : ℕ) :
    ‖amplitude n‖^2 = ((2*n).factorial : ℝ) / (4^n * (n.factorial : ℝ)^2) := by
  have hf : 0 ≤ ((2*n).factorial : ℝ) := by positivity
  have hn : 0 ≤ (n.factorial : ℝ) := by positivity
  rw [amplitude, norm_mul, norm_div, norm_pow, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt hf]
  have hhalf : ‖(-1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
  rw [hhalf, div_pow, ← pow_mul, mul_comm n 2, pow_mul]
  rw [show (1/2 : ℝ)^2 = (4 : ℝ)⁻¹ by norm_num, inv_pow]
  ring

/-- Exact all-degree physical norm reduced to one symmetric projection. -/
theorem term_norm_sq_projection (b : HN L 2) (n : ℕ) :
    ‖term b n‖^2 = ((2*n).factorial : ℝ) / (4^n * (n.factorial : ℝ)^2) *
      ‖symProj ℂ (L2T L) (2*n) (rawPower b n)‖^2 := by
  have he := term_eq_sym_rawPower b n
  have hnorm := congrArg (fun x : HilbertTensorPower ℂ (L2T L) (2*n) => ‖x‖^2) he
  simpa only [Submodule.norm_coe, norm_smul, mul_pow, amplitude_norm_sq] using hnorm

end PhysicalPowers

section CoherentCoefficients
variable {L : ℝ} [Fact (0 < L)]

lemma inner_htpow_symProj (n : ℕ) (u : L2T L)
    (x : HilbertTensorPower ℂ (L2T L) n) :
    inner ℂ (htpow n u) (symProj ℂ (L2T L) n x) = inner ℂ (htpow n u) x := by
  rw [symProj_eq_starProjection]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (⟨htpow n u, htpow_mem_symSector n u⟩ : physSector L n) x

lemma inner_htpow_rawPower (b : HN L 2) (u : L2T L) (n : ℕ) :
    inner ℂ (htpow (2*n) u) (rawPower b n) =
      (inner ℂ (htpow 2 u) (b : HilbertTensorPower ℂ (L2T L) 2))^n := by
  induction n with
  | zero =>
    change inner ℂ (htpow 0 u) (htpow 0 (0 : L2T L)) = _
    rw [inner_htpow]
    simp
  | succ n ih =>
    let h : 2+2*n = 2*(n+1) := by omega
    have hc := (castHTP (𝕜 := ℂ) (E := L2T L) h).inner_map_map
      (htpow (2+2*n) u) (concat (b : HilbertTensorPower ℂ (L2T L) 2) (rawPower b n))
    rw [castHTP_htpow, inner_htpow_concat, ih] at hc
    change inner ℂ (htpow (2*(n+1)) u)
      (castHTP h (concat (b : HilbertTensorPower ℂ (L2T L) 2) (rawPower b n))) = _
    exact hc.trans (by rw [pow_succ]; ring)

/-- The generating polynomial of every actual physical exponential term.
This computes all degrees by one induction, for every completed pair tensor. -/
theorem inner_htpow_term (b : HN L 2) (u : L2T L) (n : ℕ) :
    inner ℂ (htpow (2*n) u) (term b n : HilbertTensorPower ℂ (L2T L) (2*n)) =
      amplitude n * (inner ℂ (htpow 2 u) (b : HilbertTensorPower ℂ (L2T L) 2))^n := by
  rw [term_eq_sym_rawPower, inner_smul_right, inner_htpow_symProj, inner_htpow_rawPower]

end CoherentCoefficients

section WickReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma symProj_norm_sq (n : ℕ) (x : HilbertTensorPower ℂ E n) :
    ‖symProj ℂ E n x‖^2 = (inner ℂ x (symProj ℂ E n x)).re := by
  rw [symProj_eq_starProjection]
  have h := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
    ((SymSector ℂ E n).orthogonalProjectionOnto x) x
  change inner ℂ ((SymSector ℂ E n).starProjection x)
      ((SymSector ℂ E n).starProjection x) =
    inner ℂ x ((SymSector ℂ E n).starProjection x) at h
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) ((SymSector ℂ E n).starProjection x)).trans
    (congrArg Complex.re h)

/-- A finite, exact Wick permutation sum for any completed tensor. -/
theorem symProj_norm_sq_permutations (n : ℕ) (x : HilbertTensorPower ℂ E n) :
    ‖symProj ℂ E n x‖^2 = ((n.factorial : ℝ)⁻¹) *
      (∑ σ : Equiv.Perm (Fin n), inner ℂ x (permHilbertIsometry σ x)).re := by
  classical
  rw [symProj_norm_sq, symProj_eq_factorial_average]
  simp only [smul_apply, sum_apply, inner_smul_right, inner_sum, permRep_apply]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

variable {L : ℝ} [Fact (0 < L)]

/-- The full physical norm in every degree, as a finite Wick contraction sum.
Regrouping the permutations by contraction cycles into the trace-exponential
coefficient is still required; this theorem does not assume that equality. -/
theorem term_norm_sq_wick_sum (b : HN L 2) (n : ℕ) :
    ‖term b n‖^2 = (4^n * (n.factorial : ℝ)^2)⁻¹ *
      (∑ σ : Equiv.Perm (Fin (2*n)),
        inner ℂ (rawPower b n) (permHilbertIsometry σ (rawPower b n))).re := by
  rw [term_norm_sq_projection, symProj_norm_sq_permutations]
  have hf : ((2*n).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*n)
  field_simp

end WickReduction

end QuantumNLS.Ext006PairPowerWick
end

#print axioms QuantumNLS.Ext006PairPowerWick.concat
#print axioms QuantumNLS.Ext006PairPowerWick.concat_continuous
#print axioms QuantumNLS.Ext006PairPowerWick.concat_smul_left
#print axioms QuantumNLS.Ext006PairPowerWick.concat_smul_right
#print axioms QuantumNLS.Ext006PairPowerWick.concat_add_left
#print axioms QuantumNLS.Ext006PairPowerWick.concat_add_right
#print axioms QuantumNLS.Ext006PairPowerWick.concat_ptprod
#print axioms QuantumNLS.Ext006PairPowerWick.concatLeftMap
#print axioms QuantumNLS.Ext006PairPowerWick.concatLeftMap_apply
#print axioms QuantumNLS.Ext006PairPowerWick.concatRightMap
#print axioms QuantumNLS.Ext006PairPowerWick.concatRightMap_apply
#print axioms QuantumNLS.Ext006PairPowerWick.rightPerm
#print axioms QuantumNLS.Ext006PairPowerWick.concat_perm_right
#print axioms QuantumNLS.Ext006PairPowerWick.symProj_perm
#print axioms QuantumNLS.Ext006PairPowerWick.symProj_concat_symProj_right
#print axioms QuantumNLS.Ext006PairPowerWick.inner_htpow_concat
#print axioms QuantumNLS.Ext006PairPowerWick.coe_sectorCast
#print axioms QuantumNLS.Ext006PairPowerWick.symProj_cast
#print axioms QuantumNLS.Ext006PairPowerWick.rawPower
#print axioms QuantumNLS.Ext006PairPowerWick.sqrt_factorial_step
#print axioms QuantumNLS.Ext006PairPowerWick.power_eq_sym_rawPower
#print axioms QuantumNLS.Ext006PairPowerWick.amplitude
#print axioms QuantumNLS.Ext006PairPowerWick.term_eq_sym_rawPower
#print axioms QuantumNLS.Ext006PairPowerWick.amplitude_norm_sq
#print axioms QuantumNLS.Ext006PairPowerWick.term_norm_sq_projection
#print axioms QuantumNLS.Ext006PairPowerWick.inner_htpow_symProj
#print axioms QuantumNLS.Ext006PairPowerWick.inner_htpow_rawPower
#print axioms QuantumNLS.Ext006PairPowerWick.inner_htpow_term
#print axioms QuantumNLS.Ext006PairPowerWick.symProj_norm_sq
#print axioms QuantumNLS.Ext006PairPowerWick.symProj_norm_sq_permutations
#print axioms QuantumNLS.Ext006PairPowerWick.term_norm_sq_wick_sum

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006PairPowerWick." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
