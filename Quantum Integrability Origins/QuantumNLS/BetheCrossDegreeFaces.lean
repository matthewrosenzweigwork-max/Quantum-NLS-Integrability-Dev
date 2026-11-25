import QuantumNLS.BetheInternalFaces

/-! Ordinary interval evaluation and neighboring-degree cancellation on the
literal source wave. Local face identities retain c^m/q! from the proved
arbitrary-degree placement normalization. Global face enumeration and the
transfer eigenrelation remain separate obligations. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace QuantumNLS.BetheCrossDegreeFaces
open BetheWavefunctions BetheInternalFaces BetheExtension

/-- One moving coordinate, retaining every other rapidity-coordinate product. -/
theorem planeWave_update {N : ℕ} (q x : Fin N → ℝ) (a : Fin N) (t : ℝ) :
    planeWave q (Function.update x a t) =
      Complex.exp (Complex.I * ((∑ i ∈ Finset.univ.erase a, q i*x i : ℝ) : ℂ)) *
        Complex.exp (Complex.I * (q a : ℂ) * t) := by
  classical
  have he : (∑ i : Fin N, q i*Function.update x a t i) =
      (∑ i ∈ Finset.univ.erase a, q i*x i) + q a*t := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [planeWave,he,Complex.ofReal_add,mul_add,Complex.exp_add]
  simp only [Complex.ofReal_mul,mul_assoc]

theorem integral_planeWave_update {N : ℕ} (q x : Fin N → ℝ) (a : Fin N)
    (z : ℂ) (hz : z ≠ (q a : ℂ)) (u lo hi : ℝ) :
    (∫ t in lo..hi, Complex.exp (Complex.I*z*(u-t)) *
      planeWave q (Function.update x a t)) =
      Complex.exp (Complex.I*z*(u-hi)) * planeWave q (Function.update x a hi) /
          frequency z (q a) -
        Complex.exp (Complex.I*z*(u-lo)) * planeWave q (Function.update x a lo) /
          frequency z (q a) := by
  have he (t : ℝ) : Complex.exp (Complex.I*z*(u-t)) *
      planeWave q (Function.update x a t) =
      (Complex.exp (Complex.I*z*u) *
        Complex.exp (Complex.I * ((∑ i ∈ Finset.univ.erase a, q i*x i : ℝ) : ℂ))) *
          Complex.exp (frequency z (q a)*t) := by
    rw [planeWave_update]
    simp only [← Complex.exp_add]
    congr 1
    simp only [frequency]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,integral_exp_mul_complex (frequency_ne_zero hz)]
  ring

/-- Evaluate one further ordinary Lebesgue integral of the finite chamber
sum. The same formula works with any previously integrated set S. -/
theorem integral_primitive_update {N : ℕ} (c : ℝ) (q x : Fin N → ℝ)
    (a : Fin N) (z : ℂ) (hz : ∀ i, z ≠ (q i : ℂ))
    (S : Finset (Fin N)) (ha : a ∉ S) (u lo hi : ℝ) :
    (∫ t in lo..hi, Complex.exp (Complex.I*z*(u-t)) *
      primitive c q (Function.update x a t) z S) =
      Complex.exp (Complex.I*z*(u-hi)) * primitive c q (Function.update x a hi) z (insert a S) -
        Complex.exp (Complex.I*z*(u-lo)) * primitive c q (Function.update x a lo) z (insert a S) := by
  classical
  have hint (σ : Equiv.Perm (Fin N)) : IntervalIntegrable
      (fun t => coefficient c (q ∘ σ) * denominator z (q ∘ σ) S *
        (Complex.exp (Complex.I*z*(u-t)) * planeWave (q ∘ σ) (Function.update x a t)))
      volume lo hi := by
    apply Continuous.intervalIntegrable
    simp_rw [planeWave_update]
    fun_prop
  have he (t : ℝ) : Complex.exp (Complex.I*z*(u-t)) *
      primitive c q (Function.update x a t) z S =
      ∑ σ : Equiv.Perm (Fin N), coefficient c (q ∘ σ) * denominator z (q ∘ σ) S *
        (Complex.exp (Complex.I*z*(u-t)) * planeWave (q ∘ σ) (Function.update x a t)) := by
    simp only [primitive,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum (fun σ _ => hint σ)]
  simp only [intervalIntegral.integral_const_mul]
  have hiEval (σ : Equiv.Perm (Fin N)) :=
    integral_planeWave_update (q ∘ σ) x a z (hz (σ a)) u lo hi
  simp_rw [hiEval]
  simp only [primitive,denominator,Finset.prod_insert ha,Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  ring

/-- End tuples in the same closed chamber keep the entire moving segment
in that chamber, including its internal collision endpoints. -/
theorem antitone_update_between {N : ℕ} (x : Fin N → ℝ) (a : Fin N)
    {lo hi t : ℝ} (hlo : Antitone (Function.update x a lo))
    (hhi : Antitone (Function.update x a hi)) (ht : t ∈ Icc lo hi) :
    Antitone (Function.update x a t) := by
  classical
  intro i j hij
  by_cases hia : i = a
  · subst i
    by_cases hja : j = a
    · subst j; exact le_rfl
    have h := hlo hij
    simp only [Function.update_self,Function.update_of_ne hja] at h ⊢
    exact h.trans ht.1
  · by_cases hja : j = a
    · subst j
      have h := hhi hij
      simp only [Function.update_self,Function.update_of_ne hia] at h ⊢
      exact ht.2.trans h
    · simpa only [Function.update_of_ne hia,Function.update_of_ne hja] using hlo hij

/-- Actual symmetric source wave, on any moving-coordinate subinterval
whose endpoints lie in a common closed chamber. All N-1 spectators remain
arbitrary subject to these explicit geometric inequalities. -/
theorem integral_source_segment {N : ℕ} {L c : ℝ}
    (x : Fin N → ℝ) (a : Fin N) (n : Fin N → ℤ) (z : ℂ)
    (hz : ∀ i, z ≠ (BetheSmooth.sourceRoots L n c i : ℂ))
    (u lo hi : ℝ) (hlh : lo ≤ hi)
    (hlo : Antitone (Function.update x a lo))
    (hhi : Antitone (Function.update x a hi)) :
    (∫ t in lo..hi, Complex.exp (Complex.I*z*(u-t)) *
      symmetricExtension L c n (Function.update x a t)) =
      Complex.exp (Complex.I*z*(u-hi)) *
          primitive c (BetheSmooth.sourceRoots L n c) (Function.update x a hi) z {a} -
        Complex.exp (Complex.I*z*(u-lo)) *
          primitive c (BetheSmooth.sourceRoots L n c) (Function.update x a lo) z {a} := by
  have he : (∫ t in lo..hi, Complex.exp (Complex.I*z*(u-t)) *
      symmetricExtension L c n (Function.update x a t)) =
      ∫ t in lo..hi, Complex.exp (Complex.I*z*(u-t)) *
        primitive c (BetheSmooth.sourceRoots L n c) (Function.update x a t) z ∅ := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [primitive_empty,symmetricExtension_eq L c n
      (antitone_update_between x a hlo hhi (by simpa [uIcc_of_le hlh] using ht))]
    rfl
  rw [he]
  exact integral_primitive_update c _ x a z hz ∅ (Finset.notMem_empty a) u lo hi

/-- Local neighboring-degree scalar cancellation. The lower-degree
coefficient is (q+1)c^m/(q+1)! and the higher coefficient is c^(m+1)/q!.
The geometric enumeration yielding the q+1 factor is not asserted here. -/
theorem source_neighboring_degree_face {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (x : Fin N → ℝ) (z : ℂ)
    (hz : ∀ i, z ≠ (BetheSmooth.sourceRoots L n c i : ℂ))
    (S : Finset (Fin N)) {a b : Fin N} (hadj : b.val = a.val+1)
    (ha : a ∉ S) (hb : b ∉ S) (hx : x a = x b) (m q : ℕ) :
    (((q+1 : ℕ) : ℂ) * (c : ℂ)^m * ((q+1).factorial : ℂ)⁻¹) *
      (primitive c (BetheSmooth.sourceRoots L n c) x z (insert b S) -
        primitive c (BetheSmooth.sourceRoots L n c) x z (insert a S)) -
      ((c : ℂ)^(m+1) * (q.factorial : ℂ)⁻¹) *
        primitive c (BetheSmooth.sourceRoots L n c) x z (insert a (insert b S)) = 0 := by
  rw [source_primitive_internal_face hL hc hn x z hz S hadj ha hb hx,
    Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_inv_rev,pow_succ]
  have hq : (q : ℂ)+1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero q)
  field_simp [hq]
  ring

end QuantumNLS.BetheCrossDegreeFaces

#print axioms QuantumNLS.BetheCrossDegreeFaces.planeWave_update
#print axioms QuantumNLS.BetheCrossDegreeFaces.integral_planeWave_update
#print axioms QuantumNLS.BetheCrossDegreeFaces.integral_primitive_update
#print axioms QuantumNLS.BetheCrossDegreeFaces.antitone_update_between
#print axioms QuantumNLS.BetheCrossDegreeFaces.integral_source_segment
#print axioms QuantumNLS.BetheCrossDegreeFaces.source_neighboring_degree_face
