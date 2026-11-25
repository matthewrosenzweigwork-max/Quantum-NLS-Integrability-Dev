import NlsGge.GK38.XiSqChiMajorant
import NlsGge.GK38.XiSqCenteredCandidate

set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

/-- A scalar estimate for the normalized two root factors, with genuine denominator bounds. -/
theorem a5RootRational_bounds38 (q : ℂ) (hql : (1/2:ℝ) ≤ ‖q‖)
    (hqu : ‖q‖ ≤ 2) (hplus : 1 ≤ ‖1+q‖) :
    ‖2/(q*(1+q))‖ ≤ 4 ∧
      ‖2/(q*(1+q))-1‖ ≤ 8*‖q-1‖ := by
  have hqn : q ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hql)
  have hpn : 1+q ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hplus)
  have hden : (1/2:ℝ) ≤ ‖q*(1+q)‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg q, norm_nonneg (1+q)]
  have hfrac : ‖2/(q*(1+q))‖ ≤ 4 := by
    rw [Complex.norm_div, show ‖(2:ℂ)‖ = (2:ℝ) by norm_num]
    apply (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden).trans
    norm_num
  refine ⟨hfrac, ?_⟩
  have he : 2/(q*(1+q))-1 = -(q-1)*(q+2)/(q*(1+q)) := by
    field_simp
    ring
  rw [he, Complex.norm_div, norm_mul, norm_neg]
  have hq2 : ‖q+2‖ ≤ 4 := (norm_add_le _ _).trans (by norm_num at *; linarith)
  calc
    _ ≤ (‖q-1‖*4)/‖q*(1+q)‖ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq2 (norm_nonneg _)) (norm_nonneg _)
    _ ≤ (‖q-1‖*4)/(1/2:ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = _ := by ring

/-- The perturbation of the critical-point linear factor, uniformly for bounded coefficients. -/
theorem a5LinearFactor_bounds38 (w s a : ℂ) (d M : ℝ)
    (hd : 0 < d) (hw : d ≤ ‖w‖) (hM : 0 ≤ M) (ha : ‖a‖ ≤ M) (hs : ‖s‖ ≤ 1) :
    ‖1+s*a/w‖ ≤ 1+M/d ∧ ‖(1+s*a/w)-1‖ ≤ (M/d)*‖s‖ := by
  have hsa : ‖s*a/w‖ ≤ (M/d)*‖s‖ := by
    rw [Complex.norm_div, norm_mul]
    calc
      _ ≤ (‖s‖*M)/‖w‖ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha (norm_nonneg _)) (norm_nonneg _)
      _ ≤ (‖s‖*M)/d := div_le_div_of_nonneg_left (by positivity) hd hw
      _ = _ := by ring
  have hMd : 0 ≤ M/d := div_nonneg hM hd.le
  refine ⟨?_, by simpa only [add_sub_cancel_left] using hsa⟩
  calc
    _ ≤ ‖(1:ℂ)‖+‖s*a/w‖ := norm_add_le _ _
    _ ≤ 1+(M/d)*‖s‖ := by simpa only [norm_one] using add_le_add le_rfl hsa
    _ ≤ _ := by nlinarith

/-- Error in a product, preserving the actual chi error instead of assuming chi near one. -/
theorem a5ThreeFactor_error38 (x A B : ℂ) (K L e : ℝ)
    (hA : ‖A‖ ≤ K) (hB : ‖B‖ ≤ L) (hAe : ‖A-1‖ ≤ e) :
    ‖x*A*B-1‖ ≤ K*L*‖x-1‖ + L*e + ‖B-1‖ := by
  have hK : 0 ≤ K := (norm_nonneg _).trans hA
  have hL : 0 ≤ L := (norm_nonneg _).trans hB
  have he : x*A*B-1 = (x-1)*A*B+(A-1)*B+(B-1) := by ring
  rw [he]
  calc
    _ ≤ ‖(x-1)*A*B‖+‖(A-1)*B‖+‖B-1‖ := norm_add₃_le
    _ ≤ (‖x-1‖*K)*L + e*L + ‖B-1‖ := by
      simp only [norm_mul]
      exact add_le_add (add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left hA (norm_nonneg _)) hB
          (norm_nonneg _) (by positivity))
        (mul_le_mul hAe hB (norm_nonneg _) ((norm_nonneg _).trans hAe))) le_rfl
    _ = _ := by ring


/-- Rational centered kernels are controlled by chi, root, critical/mean and mean/lattice errors. -/
theorem a5CenteredScalar_error38 (x w w₀ h q : ℂ) (d r : ℝ)
    (hd : 0 < d) (hr : 0 < r) (hw : d ≤ ‖w‖) (hw₀ : r ≤ ‖w₀‖)
    (hh : ‖h‖ ≤ 1) (hql : (1/2:ℝ) ≤ ‖q‖) (hqu : ‖q‖ ≤ 2)
    (hplus : 1 ≤ ‖1+q‖) :
    ‖(-(x/Complex.I)*(w+h)/(4*w^2*q*(1+q))) - (-1/(8*Complex.I*w₀))‖ ≤
      (1/(8*d)) * (4*(1+1/d)*‖x-1‖ + 8*(1+1/d)*‖q-1‖ + ‖h‖/d) +
        ‖w-w₀‖/(8*d*r) := by
  have hwn : w ≠ 0 := norm_pos_iff.mp (hd.trans_le hw)
  have hw₀n : w₀ ≠ 0 := norm_pos_iff.mp (hr.trans_le hw₀)
  have hqn : q ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hql)
  have hpn : 1+q ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hplus)
  let A : ℂ := 2/(q*(1+q))
  let B : ℂ := 1+h/w
  let J : ℂ := -1/(8*Complex.I*w)
  let J₀ : ℂ := -1/(8*Complex.I*w₀)
  have hA := a5RootRational_bounds38 q hql hqu hplus
  have hB := a5LinearFactor_bounds38 w h 1 d 1 hd hw (by norm_num) (by norm_num) hh
  have hBe : ‖B-1‖ ≤ ‖h‖/d := by simpa [B, div_eq_mul_inv, mul_comm] using hB.2
  have hBn : ‖B‖ ≤ 1+1/d := by simpa [B, mul_one] using hB.1
  have hT : ‖x*A*B-1‖ ≤ 4*(1+1/d)*‖x-1‖ + 8*(1+1/d)*‖q-1‖ + ‖h‖/d := by
    have he := a5ThreeFactor_error38 x A B 4 (1+1/d) (8*‖q-1‖) hA.1 hBn hA.2
    apply he.trans
    nlinarith
  have hJn : ‖J‖ ≤ 1/(8*d) := by
    dsimp [J]
    rw [Complex.norm_div]
    norm_num only [norm_neg, norm_one, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hJdiff : ‖J-J₀‖ ≤ ‖w-w₀‖/(8*d*r) := by
    have he : J-J₀ = (w-w₀)/(8*Complex.I*w*w₀) := by
      dsimp [J,J₀]
      field_simp
      ring
    rw [he, Complex.norm_div]
    norm_num only [norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
    nlinarith [norm_nonneg w, norm_nonneg w₀]
  have he : -(x/Complex.I)*(w+h)/(4*w^2*q*(1+q)) = J*(x*A*B) := by
    dsimp [J,A,B]
    field_simp
    ring
  change ‖(-(x/Complex.I)*(w+h)/(4*w^2*q*(1+q))) - J₀‖ ≤ _
  rw [he]
  have he' : J*(x*A*B)-J₀ = J*(x*A*B-1)+(J-J₀) := by ring
  rw [he']
  calc
    _ ≤ ‖J*(x*A*B-1)‖ + ‖J-J₀‖ := norm_add_le _ _
    _ = ‖J‖*‖x*A*B-1‖ + ‖J-J₀‖ := by rw [norm_mul]
    _ ≤ _ := add_le_add (mul_le_mul hJn hT (norm_nonneg _) (by positivity)) hJdiff

end
end NlsGge.GK38
