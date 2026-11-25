import NlsGge.Hierarchy.RiccatiLocalChargeReal38
import NlsGge.Hierarchy.RiccatiSmoothJetDerivativeAfterProductPrerequisite
import NlsGge.Hierarchy.RiccatiAttachedRecursionCore
import NlsGge.Hierarchy.RiccatiRecurrenceBidegreeInductionThird
import NlsGge.Hierarchy.RiccatiQ4IteratedDerivStarPrerequisiteThird
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Hierarchy.PlaneCoverIdentification38
import NlsGge.Sobolev.SourceWeighted
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot
open scoped ContDiff BigOperators NNReal

/-! ### Part 1: the real-line representative of a finite plane field -/

/-- The real-line field is `NlsGge.Pilot.planeReal` (no new definition). Smoothness is
`planeReal_smooth38` (`ContDiff ℝ ∞`, in `PlaneCoverIdentification38`), periodicity is
`planeReal_periodic`, and the a.e. identification with the doubled cover is
`planeReal_cover_ae38`. Explicit formula: -/
theorem planeReal_apply_exp38 (N : ℕ) (z : FourierPlane N) (x : ℝ) :
    planeReal N z x =
      ∑ i : Fin (2 * N + 1), z i *
        Complex.exp (2 * Real.pi * Complex.I * (modeIndex N i : ℂ) * (x : ℂ)) := by
  unfold planeReal planeField
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fourier_coe_apply]
  simp

/-! ### Part 2: the coefficient `l1` size of formal jet polynomials -/

/-- Sum of the absolute values of the coefficients. -/
def l1Poly38 (P : Poly) : ℤ := ∑ m ∈ P.support, |P.coeff m|

theorem l1Poly38_nonneg (P : Poly) : 0 ≤ l1Poly38 P :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem l1Poly38_eq_sum (P : Poly) (s : Finset (Jet →₀ ℕ)) (h : P.support ⊆ s) :
    l1Poly38 P = ∑ m ∈ s, |P.coeff m| := by
  unfold l1Poly38
  refine Finset.sum_subset h fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.mp hm]
  simp

theorem l1Poly38_add (P Q : Poly) : l1Poly38 (P + Q) ≤ l1Poly38 P + l1Poly38 Q := by
  classical
  rw [l1Poly38_eq_sum (P + Q) (P.support ∪ Q.support) (MvPolynomial.support_add),
    l1Poly38_eq_sum P (P.support ∪ Q.support) Finset.subset_union_left,
    l1Poly38_eq_sum Q (P.support ∪ Q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun m _ => by
    simpa using abs_add_le (P.coeff m) (Q.coeff m)

theorem l1Poly38_zero : l1Poly38 0 = 0 := by simp [l1Poly38]

theorem l1Poly38_sum_le {ι : Type*} (s : Finset ι) (f : ι → Poly) :
    l1Poly38 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1Poly38 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1Poly38_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (l1Poly38_add _ _).trans (by linarith)

theorem l1Poly38_monomial (s : Jet →₀ ℕ) (a : ℤ) :
    l1Poly38 (MvPolynomial.monomial s a) = |a| := by
  classical
  by_cases ha : a = 0
  · simp [ha, l1Poly38]
  · unfold l1Poly38
    rw [MvPolynomial.support_monomial]
    simp [ha]

theorem l1Poly38_mul (P Q : Poly) : l1Poly38 (P * Q) ≤ l1Poly38 P * l1Poly38 Q := by
  classical
  conv_lhs => rw [P.as_sum, Q.as_sum]
  rw [Finset.sum_mul_sum]
  refine (l1Poly38_sum_le _ _).trans ?_
  unfold l1Poly38
  rw [Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  refine (l1Poly38_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun b _ => ?_
  rw [MvPolynomial.monomial_mul_monomial, l1Poly38_monomial, abs_mul]


theorem l1Poly38_X (v : Jet) : l1Poly38 (MvPolynomial.X v : Poly) = 1 := by
  have : (MvPolynomial.X v : Poly) = MvPolynomial.monomial (Finsupp.single v 1) 1 := rfl
  rw [this, l1Poly38_monomial]; simp

theorem l1Poly38_C (a : ℤ) : l1Poly38 (MvPolynomial.C a : Poly) = |a| := by
  rw [MvPolynomial.C_apply, l1Poly38_monomial]

/-- Total field degree of an exponent vector. -/
def degJ38 (m : Jet →₀ ℕ) : ℕ := m.sum fun _ e => e

theorem l1Poly38_spatialD_monomial (s : Jet →₀ ℕ) (a : ℤ) :
    l1Poly38 (spatialD (MvPolynomial.monomial s a)) ≤ |a| * (degJ38 s : ℤ) := by
  have h : spatialD (MvPolynomial.monomial s a) =
      MvPolynomial.C a * s.sum fun i k =>
        MvPolynomial.monomial (s - Finsupp.single i 1) (k : ℤ) *
          (MvPolynomial.X (i.1, i.2 + 1) : Poly) := by
    change MvPolynomial.mkDerivation ℤ
      (fun w : Jet => (MvPolynomial.X (w.1, w.2 + 1) : Poly)) (MvPolynomial.monomial s a) = _
    rw [MvPolynomial.mkDerivation_monomial, MvPolynomial.smul_eq_C_mul]
    simp only [smul_eq_mul]
  rw [h]
  refine (l1Poly38_mul _ _).trans ?_
  rw [l1Poly38_C]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
  unfold Finsupp.sum
  refine (l1Poly38_sum_le _ _).trans ?_
  unfold degJ38 Finsupp.sum
  push_cast
  refine Finset.sum_le_sum fun i _ => ?_
  refine (l1Poly38_mul _ _).trans ?_
  rw [l1Poly38_monomial, l1Poly38_X]
  simp

theorem l1Poly38_spatialD_le (P : Poly) (d : ℕ) (hd : ∀ m ∈ P.support, degJ38 m ≤ d) :
    l1Poly38 (spatialD P) ≤ d * l1Poly38 P := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine (l1Poly38_sum_le _ _).trans ?_
  unfold l1Poly38
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  refine (l1Poly38_spatialD_monomial _ _).trans ?_
  have := hd m hm
  have h2 : (degJ38 m : ℤ) ≤ d := by exact_mod_cast this
  nlinarith [abs_nonneg (P.coeff m)]

theorem degJ38_le_weight (m : Jet →₀ ℕ) :
    degJ38 m ≤ riccatiJetWeightHomAfterComponents m := by
  unfold degJ38 riccatiJetWeightHomAfterComponents
  simp only [AddMonoidHom.coe_mk]
  unfold Finsupp.sum
  exact Finset.sum_le_sum fun v _ => Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

theorem gauge_le_degJ38 (m : Jet →₀ ℕ) :
    riccatiJetGaugeHomAfterComponents m ≤ (degJ38 m : ℤ) := by
  unfold degJ38 riccatiJetGaugeHomAfterComponents
  simp only [AddMonoidHom.coe_mk]
  unfold Finsupp.sum
  push_cast
  refine Finset.sum_le_sum fun v _ => ?_
  split_ifs <;> omega

theorem weight_eq_deg_add38 (m : Jet →₀ ℕ) :
    riccatiJetWeightHomAfterComponents m =
      degJ38 m + m.sum fun v e => e * v.2 := by
  unfold degJ38 riccatiJetWeightHomAfterComponents
  simp only [AddMonoidHom.coe_mk]
  unfold Finsupp.sum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- Support facts of `p k`: weight `k`, at least one and at most `k` field factors. -/
theorem p_support_facts38 (k : ℕ) (hk : 1 ≤ k) (m : Jet →₀ ℕ) (hm : m ∈ (p k).support) :
    riccatiJetWeightHomAfterComponents m = k ∧ 1 ≤ degJ38 m ∧ degJ38 m ≤ k := by
  have h := riccati_p_has_bidegree_after_components k hk m hm
  have hw : riccatiJetWeightHomAfterComponents m = k := congrArg Prod.fst h
  have hg : riccatiJetGaugeHomAfterComponents m = 1 := congrArg Prod.snd h
  refine ⟨hw, ?_, hw ▸ degJ38_le_weight m⟩
  have := gauge_le_degJ38 m
  omega


/-- The paper's recursion `L_{k+1} ≤ k L_k + Σ L_{k-l} L_l`, here for `k = n+1`. -/
theorem l1Poly38_p_succ (n : ℕ) :
    l1Poly38 (p (n + 2)) ≤ (n + 1) * l1Poly38 (p (n + 1)) +
      ∑ l ∈ Finset.Icc 1 n, l1Poly38 (p (n + 1 - l)) * l1Poly38 (p l) := by
  rw [p_recurrence]
  refine (l1Poly38_add _ _).trans ?_
  have h1 : l1Poly38 (spatialD (p (n + 1))) ≤ (n + 1 : ℕ) * l1Poly38 (p (n + 1)) :=
    l1Poly38_spatialD_le _ _ fun m hm => (p_support_facts38 (n + 1) (by omega) m hm).2.2
  have h2 : l1Poly38 (MvPolynomial.X (false, 0) *
      (Finset.Icc 1 n).attach.sum fun l => p (n + 1 - l.1) * p l.1) ≤
      ∑ l ∈ Finset.Icc 1 n, l1Poly38 (p (n + 1 - l)) * l1Poly38 (p l) := by
    refine (l1Poly38_mul _ _).trans ?_
    rw [l1Poly38_X, one_mul]
    refine (l1Poly38_sum_le _ _).trans ?_
    rw [← Finset.sum_attach (Finset.Icc 1 n)
      (fun l => l1Poly38 (p (n + 1 - l)) * l1Poly38 (p l))]
    exact Finset.sum_le_sum fun l _ => l1Poly38_mul _ _
  push_cast at h1
  linarith

theorem l1Poly38_p_le_aux (n : ℕ) : l1Poly38 (p (n + 1)) ≤ 4 ^ n * (n.factorial : ℤ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
        have h : l1Poly38 (-(MvPolynomial.X (true, 0) : Poly)) = l1Poly38 (MvPolynomial.X (true, 0)) := by
          simp [l1Poly38]
        rw [p_one, h, l1Poly38_X]; simp
    | succ n =>
        have hrec := l1Poly38_p_succ n
        have hn := ih n (Nat.lt_succ_self n)
        have hsum : ∑ l ∈ Finset.Icc 1 n, l1Poly38 (p (n + 1 - l)) * l1Poly38 (p l) ≤
            if n = 0 then 0 else 4 ^ (n - 1) * ((n : ℤ) * (n - 1).factorial) := by
          rcases Nat.eq_zero_or_pos n with h0 | hpos
          · subst h0; simp
          · rw [if_neg (by omega : ¬ n = 0)]
            have hterm : ∀ l ∈ Finset.Icc 1 n,
                l1Poly38 (p (n + 1 - l)) * l1Poly38 (p l) ≤
                  4 ^ (n - 1) * ((n - 1).factorial : ℤ) := by
              intro l hl
              obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.mp hl
              have a1 := ih (n - l) (by omega)
              have a2 := ih (l - 1) (by omega)
              have e1 : n - l + 1 = n + 1 - l := by omega
              have e2 : l - 1 + 1 = l := by omega
              rw [e1] at a1
              rw [e2] at a2
              have hf : (n - l).factorial * (l - 1).factorial ≤ (n - 1).factorial := by
                have := Nat.factorial_mul_factorial_dvd_factorial_add (n - l) (l - 1)
                have e3 : n - l + (l - 1) = n - 1 := by omega
                rw [e3] at this
                exact Nat.le_of_dvd (Nat.factorial_pos _) this
              have hf' : ((n - l).factorial : ℤ) * (l - 1).factorial ≤ (n - 1).factorial := by
                exact_mod_cast hf
              have hp : (4 : ℤ) ^ (n - l) * 4 ^ (l - 1) = 4 ^ (n - 1) := by
                rw [← pow_add]; congr 1; omega
              have b1 := l1Poly38_nonneg (p (n + 1 - l))
              have b2 := l1Poly38_nonneg (p l)
              calc l1Poly38 (p (n + 1 - l)) * l1Poly38 (p l)
                  ≤ (4 ^ (n - l) * ((n - l).factorial : ℤ)) *
                      (4 ^ (l - 1) * ((l - 1).factorial : ℤ)) :=
                    mul_le_mul a1 a2 b2 (by positivity)
                _ = (4 ^ (n - l) * 4 ^ (l - 1)) *
                      (((n - l).factorial : ℤ) * (l - 1).factorial) := by ring
                _ ≤ 4 ^ (n - 1) * ((n - 1).factorial : ℤ) := by
                    rw [hp]; exact mul_le_mul_of_nonneg_left hf' (by positivity)
            refine (Finset.sum_le_sum hterm).trans ?_
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
            simp only [Nat.add_sub_cancel]
            push_cast; ring_nf; exact le_rfl
        have hfac : ((n + 1).factorial : ℤ) = (n + 1) * n.factorial := by
          rw [Nat.factorial_succ]; push_cast; ring
        have hpos : (0 : ℤ) < 4 ^ n * n.factorial := by positivity
        rcases Nat.eq_zero_or_pos n with h0 | hp
        · subst h0
          simp at hsum hrec hn ⊢
          linarith
        · rw [if_neg (by omega : ¬ n = 0)] at hsum
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          simp only [Nat.add_sub_cancel] at hsum
          have hf2 : (((m + 1).factorial : ℕ) : ℤ) = (m + 1) * m.factorial := by
            rw [Nat.factorial_succ]; push_cast; ring
          have h4 : (4 : ℤ) ^ (m + 1) = 4 * 4 ^ m := by ring
          rw [hfac] at ⊢
          rw [hf2] at hn hpos ⊢
          rw [h4] at hn hpos
          have h4m : (0 : ℤ) < 4 ^ m * m.factorial := by positivity
          have : (4:ℤ) ^ (m + 1 + 1) = 4 * (4 * 4 ^ m) := by ring
          rw [this]
          have hrec' : l1Poly38 (p (m + 1 + 1 + 1)) ≤ ((((m + 1 : ℕ) : ℤ)) + 1) * l1Poly38 (p (m + 1 + 1)) +
              ∑ l ∈ Finset.Icc 1 (m + 1), l1Poly38 (p (m + 1 + 1 - l)) * l1Poly38 (p l) := hrec
          push_cast at hrec' hsum ⊢
          nlinarith [h4m, sq_nonneg (m : ℤ), (Nat.cast_nonneg m : (0:ℤ) ≤ m)]

/-- `W01.01`: the Riccati coefficient-count bound `L_k ≤ 4^(k-1) (k-1)!`. -/
theorem riccati_p_abs_coeff_sum_le38 (k : ℕ) (hk : 1 ≤ k) :
    ∑ m ∈ (p k).support, |(p k).coeff m| ≤ 4 ^ (k - 1) * ((k - 1).factorial : ℤ) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have := l1Poly38_p_le_aux n
  unfold l1Poly38 at this
  simpa using this


/-! ### Part 3: pointwise bounds -/

theorem norm_polynomialEvaluation_le38 (v : Jet → ℂ) (P : Poly) (B : ℝ)
    (hB : ∀ m ∈ P.support, ∏ i ∈ m.support, ‖v i‖ ^ (m i) ≤ B) :
    ‖polynomialEvaluation v P‖ ≤ (l1Poly38 P : ℝ) * B := by
  have h : polynomialEvaluation v P = ∑ m ∈ P.support,
      ((P.coeff m : ℤ) : ℂ) * ∏ i ∈ m.support, v i ^ (m i) := by
    unfold polynomialEvaluation
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
    simp
  rw [h]
  refine (norm_sum_le _ _).trans ?_
  unfold l1Poly38
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun m hm => ?_
  rw [norm_mul, norm_prod]
  simp only [norm_pow, Complex.norm_intCast]
  exact mul_le_mul_of_nonneg_left (hB m hm) (abs_nonneg _) |>.trans_eq' rfl

theorem monomial_norm_bound38 (v : Jet → ℂ) (A R K : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hK : 1 ≤ K) (hAK : A ≤ K) (hRK : R ≤ K)
    (hv : ∀ i : Jet, ‖v i‖ ≤ A * R ^ i.2) (k : ℕ) (m : Jet →₀ ℕ)
    (hw : riccatiJetWeightHomAfterComponents m = k) (hd : 1 ≤ degJ38 m) :
    ∏ i ∈ m.support, ‖v i‖ ^ (m i) ≤ A * K ^ (k - 1) := by
  have hK0 : 0 ≤ K := by linarith
  have h1 : ∏ i ∈ m.support, ‖v i‖ ^ (m i) ≤ ∏ i ∈ m.support, (A * R ^ i.2) ^ (m i) :=
    Finset.prod_le_prod₀ (fun i _ => pow_nonneg (norm_nonneg _) _)
      (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hv i) _)
  have h2 : ∏ i ∈ m.support, (A * R ^ i.2) ^ (m i) =
      A ^ degJ38 m * R ^ (m.sum fun v e => e * v.2) := by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← pow_mul]
    unfold degJ38 Finsupp.sum
    congr 2
    exact Finset.sum_congr rfl fun i _ => by ring
  have hwe := weight_eq_deg_add38 m
  set d := degJ38 m
  set e := m.sum fun v e => e * v.2
  have hk : k - 1 = (d - 1) + e := by omega
  have h3 : A ^ d ≤ A * K ^ (d - 1) := by
    obtain ⟨d', hd'⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    rw [hd', pow_succ, Nat.add_sub_cancel, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA hAK _) hA
  calc ∏ i ∈ m.support, ‖v i‖ ^ (m i) ≤ A ^ d * R ^ e := h1.trans_eq h2
    _ ≤ (A * K ^ (d - 1)) * K ^ e :=
        mul_le_mul h3 (pow_le_pow_left₀ hR hRK _) (by positivity) (by positivity)
    _ = A * K ^ (k - 1) := by rw [hk, pow_add]; ring

theorem norm_eval_p_le38 (v : Jet → ℂ) (A R K : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hK : 1 ≤ K) (hAK : A ≤ K) (hRK : R ≤ K)
    (hv : ∀ i : Jet, ‖v i‖ ≤ A * R ^ i.2) (k : ℕ) (hk : 1 ≤ k) :
    ‖polynomialEvaluation v (p k)‖ ≤
      (4 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) * (A * K ^ (k - 1)) := by
  refine (norm_polynomialEvaluation_le38 v (p k) (A * K ^ (k - 1)) fun m hm => ?_).trans ?_
  · obtain ⟨h1, h2, _⟩ := p_support_facts38 k hk m hm
    exact monomial_norm_bound38 v A R K hA hR hK hAK hRK hv k m h1 h2
  · have := riccati_p_abs_coeff_sum_le38 k hk
    have h' : (l1Poly38 (p k) : ℝ) ≤ 4 ^ (k - 1) * ((k - 1).factorial : ℝ) := by
      unfold l1Poly38; exact_mod_cast this
    exact mul_le_mul_of_nonneg_right h' (by positivity)

theorem norm_fourier_eq_one38 (n : ℤ) (x : PhysicalCircle) : ‖fourier n x‖ = 1 := by
  simp [fourier_apply]

theorem norm_planeReal_le38 (N : ℕ) (z : FourierPlane N) (x : ℝ) :
    ‖planeReal N z x‖ ≤ ∑ i, ‖z i‖ := by
  unfold planeReal planeField
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_fourier_eq_one38, mul_one]

theorem norm_derivativePlane_le38 (N : ℕ) (w : FourierPlane N) (i : Fin (2 * N + 1)) :
    ‖derivativePlane N w i‖ ≤ ‖w i‖ * (2 * Real.pi * N) := by
  unfold derivativePlane
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hb := modeIndex_bounds N i
  have : |(modeIndex N i : ℝ)| ≤ N := by
    rw [abs_le]; constructor <;> exact_mod_cast (by omega : _)
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
    Complex.norm_intCast, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
  nlinarith [Real.pi_pos]

theorem norm_iterate_derivativePlane38 (N : ℕ) (z : FourierPlane N) (a : ℕ)
    (i : Fin (2 * N + 1)) :
    ‖(derivativePlane N)^[a] z i‖ ≤ ‖z i‖ * (2 * Real.pi * N) ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Function.iterate_succ_apply']
      calc _ ≤ ‖(derivativePlane N)^[a] z i‖ * (2 * Real.pi * N) :=
            norm_derivativePlane_le38 N _ i
        _ ≤ ‖z i‖ * (2 * Real.pi * N) ^ a * (2 * Real.pi * N) :=
            mul_le_mul_of_nonneg_right ih (by positivity)
        _ = _ := by ring


theorem norm_riccatiJetFunction_planeReal_le38 (N : ℕ) (z : FourierPlane N) (v : Jet) (x : ℝ) :
    ‖riccatiJetFunction (planeReal N z) v x‖ ≤ (∑ i, ‖z i‖) * (2 * Real.pi * N) ^ v.2 := by
  have key : ∀ w : FourierPlane N, ‖planeReal N w x‖ ≤ ∑ i, ‖w i‖ := fun w =>
    norm_planeReal_le38 N w x
  have hsum : ∑ i, ‖(derivativePlane N)^[v.2] z i‖ ≤ (∑ i, ‖z i‖) * (2 * Real.pi * N) ^ v.2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => norm_iterate_derivativePlane38 N z v.2 i
  obtain ⟨b, a⟩ := v
  cases b
  · simp only [riccatiJetFunction, Bool.false_eq_true, if_false]
    rw [iteratedDeriv_planeReal]
    exact (key _).trans hsum
  · simp only [riccatiJetFunction, if_true]
    rw [iteratedDeriv_star_prerequisite, iteratedDeriv_planeReal, norm_star]
    exact (key _).trans hsum

/-- The real local charge `Re ∫₀¹ (-1)^{j+1} u p_{2j+1}` of a field `u : ℝ → ℂ`. -/
def localCharge38 (u : ℝ → ℂ) (j : ℕ) : ℝ :=
  (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (formalChargeIntegrand j)).re

/-- `W01.02/.03` for all `j` (including `j = 0`). -/
theorem localCharge38_plane_bound_all (N j : ℕ) (z : FourierPlane N) :
    |localCharge38 (planeReal N z) j| ≤
      (∑ i, ‖z i‖) ^ 2 * 4 ^ (2 * j) * ((2 * j).factorial : ℝ) *
        (max 1 (max (2 * Real.pi * N) (∑ i, ‖z i‖))) ^ (2 * j) := by
  set A := ∑ i, ‖z i‖ with hAdef
  set R := 2 * Real.pi * (N : ℝ) with hRdef
  set K := max 1 (max R A) with hKdef
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hR : 0 ≤ R := by positivity
  have hK : 1 ≤ K := le_max_left _ _
  have hAK : A ≤ K := (le_max_right R A).trans (le_max_right 1 (max R A))
  have hRK : R ≤ K := (le_max_left R A).trans (le_max_right 1 (max R A))
  have hv : ∀ i : Jet, ‖riccatiJetFunction (planeReal N z) i 0‖ ≤ A * R ^ i.2 :=
    fun i => norm_riccatiJetFunction_planeReal_le38 N z i 0
  unfold localCharge38
  refine (Complex.abs_re_le_norm _).trans ?_
  have hpt : ∀ x : ℝ, ‖riccatiJetEvaluation (planeReal N z) x (formalChargeIntegrand j)‖ ≤
      A ^ 2 * 4 ^ (2 * j) * ((2 * j).factorial : ℝ) * K ^ (2 * j) := by
    intro x
    have hvx : ∀ i : Jet, ‖riccatiJetFunction (planeReal N z) i x‖ ≤ A * R ^ i.2 :=
      fun i => norm_riccatiJetFunction_planeReal_le38 N z i x
    have hp := norm_eval_p_le38 (fun i => riccatiJetFunction (planeReal N z) i x) A R K hA hR hK
      hAK hRK hvx (2 * j + 1) (by omega)
    have hu := hvx (false, 0)
    simp only [pow_zero, mul_one] at hu
    have heq : riccatiJetEvaluation (planeReal N z) x (formalChargeIntegrand j) =
        ((((-1 : ℤ) ^ (j + 1) : ℤ)) : ℂ) * riccatiJetFunction (planeReal N z) (false, 0) x *
          polynomialEvaluation (fun i => riccatiJetFunction (planeReal N z) i x) (p (2 * j + 1)) := by
      unfold riccatiJetEvaluation formalChargeIntegrand
      simp
    rw [heq, norm_mul, norm_mul]
    simp only [Complex.norm_intCast, Int.cast_pow, Int.cast_neg, Int.cast_one, norm_pow,
      norm_neg, norm_one, one_pow, one_mul]
    simp only [Nat.add_sub_cancel] at hp
    calc _ ≤ A * ((4 : ℝ) ^ (2 * j) * ((2 * j).factorial : ℝ) * (A * K ^ (2 * j))) :=
          mul_le_mul hu hp (norm_nonneg _) hA
      _ = _ := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun x => riccatiJetEvaluation (planeReal N z) x (formalChargeIntegrand j))
    (C := A ^ 2 * 4 ^ (2 * j) * ((2 * j).factorial : ℝ) * K ^ (2 * j)) (fun x _ => hpt x)
  simpa using this

/-- `W01.03`: `|Q_{2j}| ≤ A² 4^{2j} (2j)! K^{2j}` for `j ≥ 1`. -/
theorem localCharge38_plane_bound (N j : ℕ) (_hj : 1 ≤ j) (z : FourierPlane N) :
    |localCharge38 (planeReal N z) j| ≤
      (∑ i, ‖z i‖) ^ 2 * 4 ^ (2 * j) * ((2 * j).factorial : ℝ) *
        (max 1 (max (2 * Real.pi * N) (∑ i, ‖z i‖))) ^ (2 * j) :=
  localCharge38_plane_bound_all N j z


/-! ### Part 4: the complete energy and its summable majorant -/

/-- The complete energy `E_W = Σ_j (c_j/(j!)^4) Q_{2j}` on the finite plane
(`W(r) = Σ c_j r^{2j}/(j!)^4`, so `E_W = (2/π)∫ W(2λ) v` termwise; see STATUS). -/
def fullEnergy38 {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) (z : FourierPlane N) : ℝ :=
  ∑' j : ℕ, c.val j / ((j.factorial : ℝ)) ^ 4 * localCharge38 (planeReal N z) j

theorem factorial_two_mul_le38 (j : ℕ) :
    ((2 * j).factorial : ℝ) ≤ 4 ^ j * ((j.factorial : ℝ)) ^ 2 := by
  have h1 : (2 * j).choose j * (j.factorial * j.factorial) = (2 * j).factorial := by
    have := Nat.add_choose_mul_factorial_mul_factorial j j
    rw [two_mul]
    rw [← this]
    ring
  have h2 : (2 * j).choose j ≤ 4 ^ j := by
    have := Nat.choose_le_two_pow (2 * j) j
    calc _ ≤ 2 ^ (2 * j) := this
      _ = 4 ^ j := by rw [pow_mul]; norm_num
  have h3 : (2 * j).factorial ≤ 4 ^ j * (j.factorial) ^ 2 := by
    rw [← h1]
    calc _ ≤ 4 ^ j * (j.factorial * j.factorial) := Nat.mul_le_mul_right _ h2
      _ = _ := by ring
  exact_mod_cast h3


theorem term_abs_le38 (cj up A K Q : ℝ) (j : ℕ) (hc0 : 0 ≤ cj) (hc : cj ≤ up) (hK : 0 ≤ K)
    (hQ : |Q| ≤ A ^ 2 * 4 ^ (2 * j) * ((2 * j).factorial : ℝ) * K ^ (2 * j)) :
    |cj / ((j.factorial : ℝ)) ^ 4 * Q| ≤ up * A ^ 2 * ((8 * K) ^ j / (j.factorial : ℝ)) ^ 2 := by
  have hF : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hF4 : (0 : ℝ) < (j.factorial : ℝ) ^ 4 := by positivity
  have hfac := factorial_two_mul_le38 j
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ cj / (j.factorial : ℝ) ^ 4)]
  have hup : 0 ≤ up := hc0.trans hc
  calc cj / (j.factorial : ℝ) ^ 4 * |Q|
      ≤ (up / (j.factorial : ℝ) ^ 4) * (A ^ 2 * 4 ^ (2 * j) * ((2 * j).factorial : ℝ) * K ^ (2 * j)) :=
        mul_le_mul (div_le_div_of_nonneg_right hc hF4.le) hQ (abs_nonneg _) (by positivity)
    _ ≤ (up / (j.factorial : ℝ) ^ 4) *
          (A ^ 2 * 4 ^ (2 * j) * (4 ^ j * (j.factorial : ℝ) ^ 2) * K ^ (2 * j)) := by gcongr
    _ = up * A ^ 2 * ((8 * K) ^ j / (j.factorial : ℝ)) ^ 2 := by
        have e1 : ((4 : ℝ) ^ (2 * j)) * 4 ^ j = 64 ^ j := by
          rw [← pow_add, show 2 * j + j = 3 * j by ring, pow_mul]; norm_num
        have e2 : (((8 : ℝ) * K) ^ j) ^ 2 = 64 ^ j * K ^ (2 * j) := by
          rw [← pow_mul, mul_comm j 2, mul_pow, pow_mul, pow_mul]; norm_num
        rw [div_pow, e2]
        have e3 : up / (j.factorial : ℝ) ^ 4 *
            (A ^ 2 * 4 ^ (2 * j) * (4 ^ j * (j.factorial : ℝ) ^ 2) * K ^ (2 * j)) =
            up * A ^ 2 * (((4 : ℝ) ^ (2 * j) * 4 ^ j) * K ^ (2 * j)) *
              ((j.factorial : ℝ) ^ 2 / (j.factorial : ℝ) ^ 4) := by ring
        rw [e3, e1]
        field_simp


/-- `A(z) = Σ_i ‖z_i‖`. -/
def planeAmp38 {N : ℕ} (z : FourierPlane N) : ℝ := ∑ i, ‖z i‖

/-- `K(z) = max {1, 2πN, A}`. -/
def planeK38 (N : ℕ) (z : FourierPlane N) : ℝ :=
  max 1 (max (2 * Real.pi * N) (planeAmp38 z))

theorem planeAmp38_nonneg {N : ℕ} (z : FourierPlane N) : 0 ≤ planeAmp38 z :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem one_le_planeK38 (N : ℕ) (z : FourierPlane N) : 1 ≤ planeK38 N z := le_max_left _ _

theorem sq_le_exp_mul38 (x : ℝ) (hx : 0 ≤ x) (j : ℕ) :
    (x ^ j / (j.factorial : ℝ)) ^ 2 ≤ Real.exp x * (x ^ j / (j.factorial : ℝ)) := by
  rw [sq, mul_comm]
  exact mul_le_mul_of_nonneg_right (NlsGge.Weights.expSeries_term_le x hx j) (by positivity)

theorem fullEnergy_term_le_majorant38 {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ)
    (z : FourierPlane N) (j : ℕ) (A' K' : ℝ) (hA : planeAmp38 z ≤ A') (hK : planeK38 N z ≤ K') :
    |c.val j / ((j.factorial : ℝ)) ^ 4 * localCharge38 (planeReal N z) j| ≤
      up * A' ^ 2 * Real.exp (8 * K') * ((8 * K') ^ j / (j.factorial : ℝ)) := by
  have hK0 : 0 ≤ planeK38 N z := (zero_le_one).trans (one_le_planeK38 N z)
  have hK'0 : 0 ≤ K' := hK0.trans hK
  have hc := c.property.2.2 j
  have hlo := c.property.1
  have hup : 0 ≤ up := hlo.le.trans (hc.1.trans hc.2)
  have hQ := localCharge38_plane_bound_all N j z
  have h1 := term_abs_le38 (c.val j) up (planeAmp38 z) (planeK38 N z) _ j (hlo.le.trans hc.1) hc.2
    hK0 hQ
  have hA0 := planeAmp38_nonneg z
  have ha : (8 * planeK38 N z) ^ j / (j.factorial : ℝ) ≤ (8 * K') ^ j / (j.factorial : ℝ) := by
    gcongr
  have ha0 : 0 ≤ (8 * planeK38 N z) ^ j / (j.factorial : ℝ) := by positivity
  calc _ ≤ up * planeAmp38 z ^ 2 * ((8 * planeK38 N z) ^ j / (j.factorial : ℝ)) ^ 2 := h1
    _ ≤ up * A' ^ 2 * ((8 * K') ^ j / (j.factorial : ℝ)) ^ 2 := by gcongr
    _ ≤ up * A' ^ 2 * (Real.exp (8 * K') * ((8 * K') ^ j / (j.factorial : ℝ))) := by
        gcongr; exact sq_le_exp_mul38 _ (by positivity) j
    _ = _ := by ring

theorem summable_majorant38 (up A' K' : ℝ) :
    Summable fun j : ℕ => up * A' ^ 2 * Real.exp (8 * K') * ((8 * K') ^ j / (j.factorial : ℝ)) :=
  (NlsGge.Weights.expSeries_hasSum (8 * K')).summable.mul_left _

theorem tsum_majorant38 (up A' K' : ℝ) :
    ∑' j : ℕ, up * A' ^ 2 * Real.exp (8 * K') * ((8 * K') ^ j / (j.factorial : ℝ)) =
      up * A' ^ 2 * Real.exp (16 * K') := by
  rw [tsum_mul_left, (NlsGge.Weights.expSeries_hasSum (8 * K')).tsum_eq, mul_assoc,
    ← Real.exp_add]
  ring_nf

/-- Summability of the complete energy series, with the majorant of `W01.04`. -/
theorem fullEnergy38_summable {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ)
    (z : FourierPlane N) :
    Summable fun j : ℕ => c.val j / ((j.factorial : ℝ)) ^ 4 * localCharge38 (planeReal N z) j :=
  Summable.of_norm_bounded (summable_majorant38 up (planeAmp38 z) (planeK38 N z)) fun j => by
    rw [Real.norm_eq_abs]
    exact fullEnergy_term_le_majorant38 c N z j _ _ le_rfl le_rfl

/-- Paper's `C:eq:fullupper`, in the form `E_W ≤ c₊ A² e^{16 K}`. -/
theorem fullEnergy38_le {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) (z : FourierPlane N) :
    fullEnergy38 c N z ≤ up * planeAmp38 z ^ 2 * Real.exp (16 * planeK38 N z) := by
  unfold fullEnergy38
  rw [← tsum_majorant38 up (planeAmp38 z) (planeK38 N z)]
  refine (Summable.tsum_le_tsum (f := fun j : ℕ => c.val j / ((j.factorial : ℝ)) ^ 4 *
    localCharge38 (planeReal N z) j) (fun j => ?_) (fullEnergy38_summable c N z)
    (summable_majorant38 _ _ _))
  exact (le_abs_self _).trans (fullEnergy_term_le_majorant38 c N z j _ _ le_rfl le_rfl)

/-- The intermediate form `E_W ≤ c₊ A² Σ_j (8K)^{2j}/(j!)²`. -/
theorem fullEnergy38_le_sq {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) (z : FourierPlane N) :
    Summable (fun j : ℕ => (8 * planeK38 N z) ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) ∧
    fullEnergy38 c N z ≤ up * planeAmp38 z ^ 2 *
      ∑' j : ℕ, (8 * planeK38 N z) ^ (2 * j) / ((j.factorial : ℝ)) ^ 2 := by
  have hK0 : 0 ≤ planeK38 N z := (zero_le_one).trans (one_le_planeK38 N z)
  have heq : ∀ j : ℕ, (8 * planeK38 N z) ^ (2 * j) / ((j.factorial : ℝ)) ^ 2 =
      ((8 * planeK38 N z) ^ j / (j.factorial : ℝ)) ^ 2 := fun j => by
    rw [div_pow, ← pow_mul, mul_comm j 2]
  have hsum : Summable (fun j : ℕ => (8 * planeK38 N z) ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
      ((NlsGge.Weights.expSeries_hasSum (8 * planeK38 N z)).summable.mul_left
        (Real.exp (8 * planeK38 N z)))
    rw [heq]; exact sq_le_exp_mul38 _ (by positivity) j
  refine ⟨hsum, ?_⟩
  unfold fullEnergy38
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun j => ?_) (fullEnergy38_summable c N z) (hsum.mul_left _)
  have hc := c.property.2.2 j
  have hlo := c.property.1
  have := term_abs_le38 (c.val j) up (planeAmp38 z) (planeK38 N z) _ j (hlo.le.trans hc.1) hc.2
    hK0 (localCharge38_plane_bound_all N j z)
  rw [heq]
  exact (le_abs_self _).trans this


/-! ### Part 5: continuity -/

theorem iterate_derivativePlane_apply38 (N : ℕ) (z : FourierPlane N) (a : ℕ)
    (i : Fin (2 * N + 1)) :
    (derivativePlane N)^[a] z i = z i * (2 * Real.pi * Complex.I * (modeIndex N i : ℂ)) ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Function.iterate_succ_apply', pow_succ]
      have h2 : derivativePlane N ((derivativePlane N)^[a] z) i =
          (derivativePlane N)^[a] z i * (2 * Real.pi * Complex.I * (modeIndex N i : ℂ)) := rfl
      rw [h2, ih]; ring

theorem continuous_planeReal_uncurry38 (N : ℕ) (a : ℕ) :
    Continuous (fun p : FourierPlane N × ℝ => planeReal N ((derivativePlane N)^[a] p.1) p.2) := by
  have : (fun p : FourierPlane N × ℝ => planeReal N ((derivativePlane N)^[a] p.1) p.2) =
      fun p => ∑ i : Fin (2 * N + 1), (p.1 i * (2 * Real.pi * Complex.I * (modeIndex N i : ℂ)) ^ a) *
        Complex.exp (2 * Real.pi * Complex.I * (modeIndex N i : ℂ) * (p.2 : ℂ)) := by
    funext p
    rw [planeReal_apply_exp38]
    exact Finset.sum_congr rfl fun i _ => by rw [iterate_derivativePlane_apply38]
  rw [this]
  fun_prop

theorem riccatiJetFunction_planeReal_eq38 (N : ℕ) (z : FourierPlane N) (v : Jet) (x : ℝ) :
    riccatiJetFunction (planeReal N z) v x =
      if v.1 then star (planeReal N ((derivativePlane N)^[v.2] z) x)
      else planeReal N ((derivativePlane N)^[v.2] z) x := by
  obtain ⟨b, a⟩ := v
  cases b
  · simp only [riccatiJetFunction, Bool.false_eq_true, if_false]
    rw [iteratedDeriv_planeReal]
  · simp only [riccatiJetFunction, if_true]
    rw [iteratedDeriv_star_prerequisite, iteratedDeriv_planeReal]

theorem continuous_jet_uncurry38 (N : ℕ) (v : Jet) :
    Continuous (fun p : FourierPlane N × ℝ => riccatiJetFunction (planeReal N p.1) v p.2) := by
  have : (fun p : FourierPlane N × ℝ => riccatiJetFunction (planeReal N p.1) v p.2) =
      fun p => if v.1 then star (planeReal N ((derivativePlane N)^[v.2] p.1) p.2)
        else planeReal N ((derivativePlane N)^[v.2] p.1) p.2 := by
    funext p; exact riccatiJetFunction_planeReal_eq38 N p.1 v p.2
  rw [this]
  have h := continuous_planeReal_uncurry38 N v.2
  split_ifs
  · exact h.star
  · exact h

theorem continuous_polynomialEvaluation38 {Y : Type*} [TopologicalSpace Y] (v : Y → Jet → ℂ)
    (hv : ∀ i, Continuous fun y => v y i) (P : Poly) :
    Continuous fun y => polynomialEvaluation (v y) P := by
  have h : (fun y => polynomialEvaluation (v y) P) = fun y => ∑ m ∈ P.support,
      ((P.coeff m : ℤ) : ℂ) * ∏ i ∈ m.support, v y i ^ (m i) := by
    funext y
    unfold polynomialEvaluation
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
    simp
  rw [h]
  refine continuous_finset_sum _ fun m _ => continuous_const.mul ?_
  exact continuous_finset_prod _ fun i _ => (hv i).pow _

theorem continuous_localCharge38 (N j : ℕ) :
    Continuous fun z : FourierPlane N => localCharge38 (planeReal N z) j := by
  unfold localCharge38
  refine Complex.continuous_re.comp ?_
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (z : FourierPlane N) (x : ℝ) =>
      riccatiJetEvaluation (planeReal N z) x (formalChargeIntegrand j)) ?_ 0 1
  exact continuous_polynomialEvaluation38 (fun (p : FourierPlane N × ℝ) (i : Jet) => riccatiJetFunction (planeReal N p.1) i p.2)
    (fun i => continuous_jet_uncurry38 N i) _


/-- Local-uniform majorant data on the sup-norm ball of radius `1` about `z₀`. -/
theorem planeAmp38_le_of_ball {N : ℕ} (z₀ z : FourierPlane N) (hz : z ∈ Metric.ball z₀ 1) :
    planeAmp38 z ≤ (2 * N + 1) * (‖z₀‖ + 1) := by
  have hn : ‖z‖ ≤ ‖z₀‖ + 1 := by
    have h2 : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
    have := norm_sub_norm_le z z₀
    linarith [norm_sub_rev z z₀]
  unfold planeAmp38
  calc ∑ i, ‖z i‖ ≤ ∑ _i : Fin (2 * N + 1), (‖z₀‖ + 1) :=
        Finset.sum_le_sum fun i _ => (norm_le_pi_norm z i).trans hn
    _ = (2 * N + 1) * (‖z₀‖ + 1) := by simp; ring

theorem planeK38_mono (N : ℕ) (z : FourierPlane N) (A' : ℝ) (h : planeAmp38 z ≤ A') :
    planeK38 N z ≤ max 1 (max (2 * Real.pi * N) A') := by
  unfold planeK38
  exact max_le_max le_rfl (max_le_max le_rfl h)

theorem continuous_fullEnergy38 {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) :
    Continuous fun z : FourierPlane N => fullEnergy38 c N z := by
  rw [continuous_iff_continuousAt]
  intro z₀
  set A' : ℝ := (2 * N + 1) * (‖z₀‖ + 1)
  set K' : ℝ := max 1 (max (2 * Real.pi * N) A')
  have hon : ContinuousOn (fun z : FourierPlane N => fullEnergy38 c N z) (Metric.ball z₀ 1) := by
    unfold fullEnergy38
    refine continuousOn_tsum (u := fun j : ℕ =>
        up * A' ^ 2 * Real.exp (8 * K') * ((8 * K') ^ j / (j.factorial : ℝ)))
      (fun j => ?_) (summable_majorant38 up A' K') (fun j z hz => ?_)
    · exact (continuous_const.mul (continuous_localCharge38 N j)).continuousOn
    · rw [Real.norm_eq_abs]
      exact fullEnergy_term_le_majorant38 c N z j A' K' (planeAmp38_le_of_ball z₀ z hz)
        (planeK38_mono N z A' (planeAmp38_le_of_ball z₀ z hz))
  exact hon.continuousAt (Metric.ball_mem_nhds z₀ one_pos)


/-! ### Part 6: auxiliary lower bound (W01.07), in the nonnegative-extended form -/

theorem energy_le_one_on_small38 (N : ℕ) (hN : 1 ≤ N) (c : BoundedCoefficients 1 2)
    (z : FourierPlane N) (hz : planeAmp38 z ≤ Real.exp (-(20 * Real.pi * (N + 1)))) :
    fullEnergy38 c N z ≤ 1 := by
  have hAN : Real.exp (-(20 * Real.pi * (N + 1))) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := Real.pi_pos; have : (0:ℝ) ≤ N := Nat.cast_nonneg N; nlinarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h2piN : 1 ≤ 2 * Real.pi * N := by nlinarith [Real.pi_gt_three]
  have hK : planeK38 N z ≤ 2 * Real.pi * N := by
    unfold planeK38
    refine max_le h2piN (max_le le_rfl (hz.trans (hAN.trans h2piN)))
  have hA0 := planeAmp38_nonneg z
  have h1 := fullEnergy38_le c N z
  have hexp : Real.exp (16 * planeK38 N z) ≤ Real.exp (32 * Real.pi * N) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hA2 : planeAmp38 z ^ 2 ≤ Real.exp (-(20 * Real.pi * (N + 1))) ^ 2 :=
    pow_le_pow_left₀ hA0 hz 2
  have hprod : Real.exp (-(20 * Real.pi * (N + 1))) ^ 2 * Real.exp (32 * Real.pi * N) ≤
      Real.exp (-1) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
    push_cast
    nlinarith [Real.pi_gt_three]
  have he : (2 : ℝ) * Real.exp (-1) ≤ 1 := by
    have h2 := Real.add_one_le_exp (1 : ℝ)
    have hp := Real.exp_pos 1
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hp]
    linarith
  have hmul : planeAmp38 z ^ 2 * Real.exp (16 * planeK38 N z) ≤
      Real.exp (-(20 * Real.pi * (N + 1))) ^ 2 * Real.exp (32 * Real.pi * N) :=
    mul_le_mul hA2 hexp (Real.exp_pos _).le (by positivity)
  calc fullEnergy38 c N z ≤ 2 * planeAmp38 z ^ 2 * Real.exp (16 * planeK38 N z) := h1
    _ = 2 * (planeAmp38 z ^ 2 * Real.exp (16 * planeK38 N z)) := by ring
    _ ≤ 2 * Real.exp (-1) := by nlinarith
    _ ≤ 1 := he


theorem small_polydisk_volume_lower38 (N : ℕ) (hN : 1 ≤ N) :
    Real.exp (-(40 * Real.pi * (N + 1) * (2 * N + 1) + 2 * (2 * (N : ℝ) + 1) ^ 2)) ≤
      ((Real.pi * (Real.exp (-(20 * Real.pi * (N + 1))) / (2 * N + 1)) ^ 2) ^ (2 * N + 1) : ℝ) := by
  set d : ℝ := 2 * N + 1 with hd
  have hd1 : 1 ≤ d := by have : (0:ℝ) ≤ N := Nat.cast_nonneg N; linarith
  set AN := Real.exp (-(20 * Real.pi * (N + 1))) with hAN
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hdn : ((2 * N + 1 : ℕ) : ℝ) = d := by rw [hd]; push_cast; ring
  have hd0 : 0 < d := by linarith
  have hy : 0 ≤ (AN / d) ^ 2 := by positivity
  have e1 : (1 : ℝ) ≤ Real.pi ^ (2 * N + 1) := one_le_pow₀ hpi
  have h1 : ((AN / d) ^ 2) ^ (2 * N + 1) ≤ (Real.pi * (AN / d) ^ 2) ^ (2 * N + 1) := by
    rw [mul_pow]; nlinarith [pow_nonneg hy (2 * N + 1)]
  refine le_trans ?_ h1
  have e2 : ((AN / d) ^ 2) ^ (2 * N + 1) = AN ^ (2 * (2 * N + 1)) / d ^ (2 * (2 * N + 1)) := by
    rw [← pow_mul, div_pow]
  have e3 : AN ^ (2 * (2 * N + 1)) =
      Real.exp (-(40 * Real.pi * (N + 1) * d)) := by
    rw [hAN, ← Real.exp_nat_mul]; congr 1; push_cast; rw [hd]; ring
  have e4 : d ^ (2 * (2 * N + 1)) ≤ Real.exp (2 * d ^ 2) := by
    have : d ≤ Real.exp d := by linarith [Real.add_one_le_exp d]
    calc d ^ (2 * (2 * N + 1)) ≤ (Real.exp d) ^ (2 * (2 * N + 1)) :=
          pow_le_pow_left₀ hd0.le this _
      _ = Real.exp (2 * d ^ 2) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; rw [hd]; ring
  rw [e2, e3, neg_add', Real.exp_sub]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (pow_pos hd0 _) e4


theorem planeVolume_polydisk38 (N : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    planeVolume N (Set.pi Set.univ fun _ : Fin (2 * N + 1) => Metric.closedBall (0 : ℂ) r) =
      ENNReal.ofReal ((Real.pi * r ^ 2) ^ (2 * N + 1)) := by
  unfold planeVolume
  rw [MeasureTheory.Measure.pi_pi]
  simp only [Complex.volume_closedBall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hpi : ((NNReal.pi : NNReal) : ENNReal) = ENNReal.ofReal Real.pi := by
    rw [ENNReal.ofReal, ← NNReal.coe_real_pi, Real.toNNReal_coe]
  rw [hpi, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul Real.pi_pos.le,
    ENNReal.ofReal_pow hr, mul_comm]

/-- `W01.07` (auxiliary lower bound, nonnegative-extended form): for `1 ≤ c_j ≤ 2`, `N ≥ 1`,
`∫⁻ e^{-E_W} ≥ e^{-C N²}` with an absolute `C`. Only the upper majorant is used; integrability
of `e^{-E_W}` (which needs the spectral lower bound `E_W ≥ β₀ Q₀`) is not claimed here. -/
theorem partition_lower38 :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ c : BoundedCoefficients 1 2,
      ENNReal.ofReal (Real.exp (-(C * (N : ℝ) ^ 2))) ≤
        ∫⁻ z, ENNReal.ofReal (Real.exp (-fullEnergy38 c N z)) ∂(planeVolume N) := by
  refine ⟨1 + 240 * Real.pi + 18, by positivity, fun N hN c => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set d : ℝ := 2 * N + 1 with hd
  have hd0 : 0 < d := by linarith
  set AN := Real.exp (-(20 * Real.pi * (N + 1))) with hAN
  set r : ℝ := AN / d with hr
  have hr0 : 0 ≤ r := by positivity
  set S : Set (FourierPlane N) :=
    Set.pi Set.univ fun _ : Fin (2 * N + 1) => Metric.closedBall (0 : ℂ) r with hS
  have hSm : MeasurableSet S := MeasurableSet.univ_pi fun _ => measurableSet_closedBall
  have hbound : ∀ z ∈ S, ENNReal.ofReal (Real.exp (-1)) ≤
      ENNReal.ofReal (Real.exp (-fullEnergy38 c N z)) := by
    intro z hz
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have hA : planeAmp38 z ≤ AN := by
      unfold planeAmp38
      calc ∑ i, ‖z i‖ ≤ ∑ _i : Fin (2 * N + 1), r := Finset.sum_le_sum fun i _ => by
            simpa using hz i (Set.mem_univ i)
        _ = AN := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hr]
            push_cast
            field_simp
            rw [hd]; ring
    have := energy_le_one_on_small38 N hN c z hA
    linarith
  have hlow := small_polydisk_volume_lower38 N hN
  calc ENNReal.ofReal (Real.exp (-((1 + 240 * Real.pi + 18) * (N : ℝ) ^ 2)))
      ≤ ENNReal.ofReal (Real.exp (-1)) * planeVolume N S := by
        rw [planeVolume_polydisk38 N r hr0, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        have h2 : Real.exp (-1) * Real.exp (-(40 * Real.pi * (N + 1) * (2 * N + 1) +
            2 * (2 * (N : ℝ) + 1) ^ 2)) ≤ Real.exp (-1) * (Real.pi * r ^ 2) ^ (2 * N + 1) :=
          mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le
        refine le_trans ?_ h2
        rw [← Real.exp_add, Real.exp_le_exp]
        have hp := Real.pi_pos
        have h3 : 0 ≤ Real.pi * ((4 * (N : ℝ) + 1) * ((N : ℝ) - 1)) :=
          mul_nonneg hp.le (mul_nonneg (by linarith) (by linarith))
        have h4 : 0 ≤ (11 * (N : ℝ) + 3) * ((N : ℝ) - 1) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith [h3, h4]
    _ = ∫⁻ _z in S, ENNReal.ofReal (Real.exp (-1)) ∂(planeVolume N) := by
        rw [MeasureTheory.setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ z in S, ENNReal.ofReal (Real.exp (-fullEnergy38 c N z)) ∂(planeVolume N) :=
        MeasureTheory.setLIntegral_mono' hSm hbound
    _ ≤ _ := MeasureTheory.setLIntegral_le_lintegral _ _

end NlsGge.HierarchyRiccati.Core
