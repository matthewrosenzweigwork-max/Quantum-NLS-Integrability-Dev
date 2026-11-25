import NlsGge.Weights.PoissonMoments
import NlsGge.Weights.StirlingBounds
/-! Concrete uniform Poisson estimates for source W02. Exact targets independently
reviewed before implementation; actual sums and Stirling bounds are prerequisites. -/
set_option autoImplicit false
noncomputable section
namespace NlsGge.Weights

lemma poissonTerm_le_one (t : ℝ) (ht : 0 ≤ t) (j : ℕ) : poissonTerm t j ≤ 1 := by
  have h := (poissonTerm_hasSum t ht).summable.le_tsum j
    (fun k hk => poissonTerm_nonneg t ht k)
  simpa only [(poissonTerm_hasSum t ht).tsum_eq] using h

lemma poissonTerm_fourth_summable (t : ℝ) (ht : 0 ≤ t) :
    Summable (fun j : ℕ => (poissonTerm t j)^4) := by
  apply (poissonTerm_hasSum t ht).summable.of_nonneg_of_le
    (fun j => pow_nonneg (poissonTerm_nonneg t ht j) 4)
  intro j
  have hp : (poissonTerm t j)^3 ≤ 1 := by
    simpa using pow_le_pow_left₀ (poissonTerm_nonneg t ht j) (poissonTerm_le_one t ht j) 3
  calc
    (poissonTerm t j)^4 = (poissonTerm t j)^3 * poissonTerm t j := pow_succ _ _
    _ ≤ 1 * poissonTerm t j := mul_le_mul_of_nonneg_right hp (poissonTerm_nonneg t ht j)
    _ = poissonTerm t j := one_mul _

lemma poisson_entropy_le_square (t x : ℝ) (ht : 0 < t) (hx : 0 < x) :
    x * Real.log (x/t) - (x-t) ≤ (x-t)^2/t := by
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hx ht)) hx.le
  calc
    x * Real.log (x/t) - (x-t) ≤ x * (x/t-1) - (x-t) := sub_le_sub_right hlog _
    _ = (x-t)^2/t := by field_simp

lemma poisson_central_geometry (t x : ℝ) (ht : 4 ≤ t)
    (hwindow : |x-t| ≤ Real.sqrt t) :
    t/2 ≤ x ∧ x ≤ 2*t ∧ (x-t)^2 ≤ t := by
  have ht0 : 0 ≤ t := by linarith
  have hsquare := Real.sq_sqrt ht0
  have hsqrt : Real.sqrt t ≤ t/2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht)]
  have hx := abs_le.mp hwindow
  have hdiff := pow_le_pow_left₀ (abs_nonneg (x-t)) hwindow 2
  rw [sq_abs] at hdiff
  exact ⟨by linarith, by linarith, by nlinarith⟩

lemma poisson_floor_geometry (t : ℝ) (ht : 1 ≤ t) :
    1 ≤ Nat.floor t ∧ t/2 ≤ (Nat.floor t : ℝ) := by
  have hn : 1 ≤ Nat.floor t := (Nat.one_le_floor_iff t).mpr ht
  refine ⟨hn, ?_⟩
  have hnr : (1 : ℝ) ≤ (Nat.floor t : ℝ) := by exact_mod_cast hn
  by_cases ht2 : t ≤ 2
  · linarith
  · have hfloor := Nat.lt_floor_add_one t
    linarith

lemma poissonTerm_le_at_floor (t : ℝ) (ht : 1 ≤ t) (j : ℕ) :
    poissonTerm t j ≤ poissonTerm t (Nat.floor t) := by
  have ht0 : 0 ≤ t := by linarith
  have hinc : MonotoneOn (poissonTerm t) (Set.Iic (Nat.floor t)) := by
    apply monotoneOn_of_le_succ Set.ordConnected_Iic
    intro k hkmax hk hk1
    have hkc : ((k+1 : ℕ) : ℝ) ≤ (Nat.floor t : ℝ) := by exact_mod_cast hk1
    have hkt : ((k+1 : ℕ) : ℝ) ≤ t := hkc.trans (Nat.floor_le ht0)
    apply (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < ((k+1 : ℕ) : ℝ))).mp
    calc
      ((k+1 : ℕ) : ℝ) * poissonTerm t k ≤ t * poissonTerm t k :=
        mul_le_mul_of_nonneg_right hkt (poissonTerm_nonneg t ht0 k)
      _ = ((k+1 : ℕ) : ℝ) * poissonTerm t (k+1) :=
        (poissonTerm_first_shift t k).symm
  have hdec : AntitoneOn (poissonTerm t) (Set.Ici (Nat.floor t)) := by
    apply antitoneOn_nat_Ici_of_succ_le
    intro k hk
    have hkc : (Nat.floor t : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkt : t ≤ ((k+1 : ℕ) : ℝ) := by
      have hf := Nat.lt_floor_add_one t
      push_cast
      linarith
    apply (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℝ) < ((k+1 : ℕ) : ℝ))).mp
    rw [poissonTerm_first_shift]
    exact mul_le_mul_of_nonneg_right hkt (poissonTerm_nonneg t ht0 k)
  rcases le_total j (Nat.floor t) with hj | hj
  · exact hinc (by change j ≤ Nat.floor t; exact hj)
      (by change Nat.floor t ≤ Nat.floor t; exact le_rfl) hj
  · exact hdec (by change Nat.floor t ≤ Nat.floor t; exact le_rfl)
      (by change Nat.floor t ≤ j; exact hj) hj

lemma poisson_stirling_exponential_identity (t : ℝ) (ht : 0 < t)
    (j : ℕ) (hj : 1 ≤ j) :
    Real.exp ((j : ℝ)-t+(j : ℝ)*Real.log (t/(j : ℝ))) =
      Real.exp (-t)*t^j / (((j : ℝ)/Real.exp 1)^j) := by
  have hjp : 0 < (j : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj)
  have hE1 : Real.exp (j : ℝ) = (Real.exp 1)^j := by
    simpa using Real.exp_nat_mul (1 : ℝ) j
  have hE2 : Real.exp ((j : ℝ)*Real.log (t/(j : ℝ))) = (t/(j : ℝ))^j := by
    rw [Real.exp_nat_mul, Real.exp_log (div_pos ht hjp)]
  rw [show (j : ℝ)-t+(j : ℝ)*Real.log (t/(j : ℝ)) =
    (-t+(j : ℝ))+(j : ℝ)*Real.log (t/(j : ℝ)) by ring,
    Real.exp_add, Real.exp_add, hE1, hE2]
  rw [div_pow, div_pow]
  field_simp
  <;> ring

lemma poissonTerm_stirling_upper (t : ℝ) (ht : 0 < t) (j : ℕ) (hj : 1 ≤ j) :
    poissonTerm t j ≤
      Real.exp ((j : ℝ)-t+(j : ℝ)*Real.log (t/(j : ℝ))) / Real.sqrt (2*Real.pi*(j : ℝ)) := by
  have hjp : 0 < (j : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj)
  have hs := (factorial_stirling_bounds j hj).1
  rw [← Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ)*Real.pi)] at hs
  have hd : 0 < Real.sqrt (2*Real.pi*(j : ℝ)) * ((j : ℝ)/Real.exp 1)^j := by positivity
  rw [poisson_stirling_exponential_identity t ht j hj, poissonTerm]
  calc
    Real.exp (-t)*t^j / (Nat.factorial j : ℝ) ≤
      Real.exp (-t)*t^j / (Real.sqrt (2*Real.pi*(j : ℝ)) * ((j : ℝ)/Real.exp 1)^j) :=
        div_le_div_of_nonneg_left (by positivity) hd hs
    _ = _ := by field_simp

lemma poissonTerm_stirling_lower (t : ℝ) (ht : 0 < t) (j : ℕ) (hj : 1 ≤ j) :
    Real.exp ((j : ℝ)-t+(j : ℝ)*Real.log (t/(j : ℝ))) /
      (Real.exp 1 * Real.sqrt (j : ℝ)) ≤ poissonTerm t j := by
  have hjp : 0 < (j : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hj)
  have hs := (factorial_stirling_bounds j hj).2
  rw [poisson_stirling_exponential_identity t ht j hj, poissonTerm]
  calc
    (Real.exp (-t)*t^j / ((j : ℝ)/Real.exp 1)^j) / (Real.exp 1*Real.sqrt (j : ℝ)) =
      Real.exp (-t)*t^j / (Real.exp 1*Real.sqrt (j : ℝ)*((j : ℝ)/Real.exp 1)^j) := by
        field_simp
        <;> ring
    _ ≤ Real.exp (-t)*t^j / (Nat.factorial j : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hs

lemma poisson_uniform_upper : ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 1 ≤ t → ∀ j : ℕ, poissonTerm t j ≤ C * t^(-1/2 : ℝ) := by
  refine ⟨1, by norm_num, ?_⟩
  intro t ht j
  have ht0 : 0 < t := by linarith
  have hn := (poisson_floor_geometry t ht).1
  have hnr : 0 < (Nat.floor t : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos ht0 hnr)) hnr.le
  have hE : (Nat.floor t : ℝ)-t+(Nat.floor t : ℝ)*Real.log (t/(Nat.floor t : ℝ)) ≤ 0 := by
    have hc : (Nat.floor t : ℝ) * (t/(Nat.floor t : ℝ)-1) = t-(Nat.floor t : ℝ) := by
      field_simp
      <;> ring
    rw [hc] at hlog
    linarith
  have harg : t ≤ 2*Real.pi*(Nat.floor t : ℝ) := by
    calc
      t ≤ 2*(Nat.floor t : ℝ) := by linarith [(poisson_floor_geometry t ht).2]
      _ ≤ 2*Real.pi*(Nat.floor t : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) hnr.le
  have hroot : Real.sqrt t ≤ Real.sqrt (2*Real.pi*(Nat.floor t : ℝ)) := Real.sqrt_le_sqrt harg
  have hhalf : t^(-1/2 : ℝ) = 1/Real.sqrt t := by
    rw [show (-1/2 : ℝ) = -(1/2 : ℝ) by ring,
      Real.rpow_neg ht0.le, ← Real.sqrt_eq_rpow]
    rw [one_div]
  rw [one_mul, hhalf]
  calc
    poissonTerm t j ≤ poissonTerm t (Nat.floor t) := poissonTerm_le_at_floor t ht j
    _ ≤ Real.exp ((Nat.floor t : ℝ)-t+(Nat.floor t : ℝ)*Real.log (t/(Nat.floor t : ℝ))) /
        Real.sqrt (2*Real.pi*(Nat.floor t : ℝ)) := poissonTerm_stirling_upper t ht0 _ hn
    _ ≤ 1/Real.sqrt (2*Real.pi*(Nat.floor t : ℝ)) := by
      apply div_le_div₀ (by norm_num) _ (by positivity) le_rfl
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hE
    _ ≤ 1/Real.sqrt t := div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos_of_pos ht0) hroot

lemma poisson_uniform_central_lower : ∃ δ : ℝ, 0 < δ ∧
    ∀ t : ℝ, 4 ≤ t → ∀ j : ℕ, |(j : ℝ)-t| ≤ Real.sqrt t →
      δ * t^(-1/2 : ℝ) ≤ poissonTerm t j := by
  refine ⟨Real.exp (-2)/2, by positivity, ?_⟩
  intro t ht j hwindow
  have ht0 : 0 < t := by linarith
  have hgeom := poisson_central_geometry t (j : ℝ) ht hwindow
  have hjp : 0 < (j : ℝ) := by linarith [hgeom.1]
  have hj : 1 ≤ j := by exact_mod_cast (show (1 : ℝ) ≤ (j : ℝ) by linarith [hgeom.1])
  have hratio : ((j : ℝ)-t)^2/t ≤ 1 := (div_le_iff₀ ht0).2 (by simpa using hgeom.2.2)
  have hlog : Real.log (t/(j : ℝ)) = -Real.log ((j : ℝ)/t) := by
    rw [Real.log_div ht0.ne' hjp.ne', Real.log_div hjp.ne' ht0.ne']
    ring
  have hE : -1 ≤ (j : ℝ)-t+(j : ℝ)*Real.log (t/(j : ℝ)) := by
    rw [hlog]
    linarith [poisson_entropy_le_square t (j : ℝ) ht0 hjp]
  have hroot : Real.sqrt (j : ℝ) ≤ 2*Real.sqrt t := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith [Real.sq_sqrt ht0.le, hgeom.2.1]⟩
  have hhalf : t^(-1/2 : ℝ) = 1/Real.sqrt t := by
    rw [show (-1/2 : ℝ) = -(1/2 : ℝ) by ring,
      Real.rpow_neg ht0.le, ← Real.sqrt_eq_rpow]
    rw [one_div]
  have he : Real.exp (-2)*Real.exp 1 = Real.exp (-1) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
  calc
    (Real.exp (-2)/2)*t^(-1/2 : ℝ) = Real.exp (-2)/(2*Real.sqrt t) := by rw [hhalf]; ring
    _ ≤ Real.exp (-2)/Real.sqrt (j : ℝ) :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) (Real.sqrt_pos_of_pos hjp) hroot
    _ = Real.exp (-1)/(Real.exp 1*Real.sqrt (j : ℝ)) := by
      field_simp
      exact he
    _ ≤ Real.exp ((j : ℝ)-t+(j : ℝ)*Real.log (t/(j : ℝ))) /
        (Real.exp 1*Real.sqrt (j : ℝ)) := by
      exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hE) (by positivity)
    _ ≤ poissonTerm t j := poissonTerm_stirling_lower t ht0 j hj

lemma poisson_central_window_count (t : ℝ) (ht : 4 ≤ t) :
    Real.sqrt t ≤
      ((Finset.Icc (Nat.ceil (t-Real.sqrt t)) (Nat.floor (t+Real.sqrt t))).card : ℝ) := by
  have ht0 : 0 ≤ t := by linarith
  have hs : 2 ≤ Real.sqrt t := Real.le_sqrt_of_sq_le (by norm_num; exact ht)
  have hlo : 0 ≤ t-Real.sqrt t := by
    have hsq := Real.sq_sqrt ht0
    nlinarith
  have hc := Nat.ceil_lt_add_one hlo
  have hf := Nat.lt_floor_add_one (t+Real.sqrt t)
  have horder : Nat.ceil (t-Real.sqrt t) ≤ Nat.floor (t+Real.sqrt t) := by
    have hreal : (Nat.ceil (t-Real.sqrt t) : ℝ) ≤ (Nat.floor (t+Real.sqrt t) : ℝ) := by linarith
    exact_mod_cast hreal
  rw [Nat.card_Icc, Nat.cast_sub (by omega : Nat.ceil (t-Real.sqrt t) ≤ Nat.floor (t+Real.sqrt t)+1),
    Nat.cast_add, Nat.cast_one]
  linarith

end NlsGge.Weights
