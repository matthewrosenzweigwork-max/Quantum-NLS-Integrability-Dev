import Mathlib

                                                                               
                                                                                                          
                                                                                          
                                                                                        
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.M.M037Interp

open MeasureTheory

/-- For x ≥ 0, the real power x^(n/(2m)) is the n-th power of x^(1/(2m)). -/
theorem rpow_nat_div_two_mul (x : ℝ) (hx : 0 ≤ x) (m n : ℕ) :
    x ^ ((n : ℝ) / (2 * (m : ℝ))) = (x ^ ((1 : ℝ) / (2 * (m : ℝ)))) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

/-- Product over a multiset of constant-times-monomial factors. -/
theorem multiset_prod_const_pow_mul {ι : Type*} (t : Multiset ι) (K α β : ℝ) (a c : ι → ℕ) :
    (t.map fun v => K * (α ^ a v * β ^ c v)).prod =
      K ^ Multiset.card t * α ^ (t.map a).sum * β ^ (t.map c).sum := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, Multiset.sum_cons, ih,
      pow_succ, pow_add]
    ring

/-- Two multiset sums whose termwise sums are the constant `c` add up to `c` times the cardinality. -/
theorem multiset_sum_add_eq_const {ι : Type*} (t : Multiset ι) (f g : ι → ℕ) (c : ℕ)
    (h : ∀ v ∈ t, f v + g v = c) :
    (t.map f).sum + (t.map g).sum = c * Multiset.card t := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    have hv : f v + g v = c := h v (Multiset.mem_cons_self v t)
    have ih' := ih (fun w hw => h w (Multiset.mem_cons_of_mem hw))
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    rw [mul_add, mul_one]
    linarith

/-- Termwise affine sum over a multiset. -/
theorem multiset_sum_two_mul_add_one {ι : Type*} (t : Multiset ι) (h : ι → ℕ) :
    (t.map fun v => 2 * h v + 1).sum = 2 * (t.map h).sum + Multiset.card t := by
  induction t using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    ring

/-- The product over the multiset of a finitely supported exponent vector is the finsupp product. -/
@[to_additive]
theorem toMultiset_map_prod {ι M : Type*} [CommMonoid M] [DecidableEq ι] (q : ι →₀ ℕ) (g : ι → M) :
    (q.toMultiset.map g).prod = q.prod fun v e => g v ^ e := by
  induction q using Finsupp.induction with
  | zero => simp
  | single_add a n f ha hn ih =>
    rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.prod_add, ih,
      Finsupp.toMultiset_single, Multiset.map_nsmul, Multiset.prod_nsmul, Multiset.map_singleton,
      Multiset.prod_singleton,
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun v e => g v ^ e) (pow_zero (g a))]

/-- The norm of a product over a multiset of complex numbers is the product of the norms. -/
theorem norm_multiset_map_prod {ι : Type*} (s : Multiset ι) (g : ι → ℂ) :
    ‖(s.map g).prod‖ = (s.map fun v => ‖g v‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons v s ih => simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul, ih]

end NlsGge.ThirdConsultation.M.M037Interp
