import NlsGge.GK38.Lib.InterpolationFormula

/-!
# L4b, part 7: the Hermite remainder identity

For a circle of radius `R` separating the roots `σ_m`, `|m| ≤ N`, from the others (`hin`, `hout`)
and `z` inside the circle, not a root:

`φ(z) - Σ_{|n|≤N} φ(σ_n) c_{N,n}(z) T_N(z)/T_N(σ_n) = ψ(z) · J_N(z)`,
`J_N(z) = (1/2πi) ∮_{|λ|=R} φ(λ)/(ψ(λ)(λ - z)) dλ`

(`hermite_remainder`; book Lemma F.4, residue theorem step).
-/

set_option autoImplicit false

open Filter Topology SummationFilter Metric Complex

namespace NlsGge.GK38.Lib

noncomputable section

/-- `J_R(z) = (2πi)⁻¹ ∮_{|λ|=R} φ(λ) / (ψ(λ) (λ - z)) dλ`. -/
def hermiteJ (φ : ℂ → ℂ) (σ : ℤ → ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * ∮ l in C((0 : ℂ), R), φ l / (psiProd σ l * (l - z))

theorem alg_integrand (ε a b c φ : ℂ) (hε : ε ≠ 0) :
    φ / a / (b * c) = ε * (φ / (ε * c * a * b)) := by
  simp only [div_eq_mul_inv, mul_inv]
  have := mul_inv_cancel₀ hε
  calc φ * a⁻¹ * (b⁻¹ * c⁻¹) = φ * a⁻¹ * (b⁻¹ * c⁻¹) * (ε * ε⁻¹) := by rw [this, mul_one]
    _ = _ := by ring

/-- **Hermite remainder formula** (the finite form of the residue sum of book Lemma F.4). -/
theorem hermite_remainder {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ) {σ : ℤ → ℂ}
    (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) (hinj : Function.Injective σ) (N : ℕ) {R : ℝ}
    (hR : 0 < R) (hin : ∀ m ∈ win N, ‖σ m‖ < R) (hout : ∀ m, m ∉ win N → R < ‖σ m‖)
    {z : ℂ} (hzR : ‖z‖ < R) (hz : ∀ m, σ m ≠ z) :
    φ z - ∑ n ∈ win N, φ (σ n) * (cFin σ N z n * (tailProd σ N z / tailProd σ N (σ n)))
      = psiProd σ z * hermiteJ φ σ R z := by
  classical
  set T := tailProd σ N with hT
  have hdisc : ∀ w : ℂ, ‖w‖ ≤ R → DifferentiableAt ℂ T w ∧ T w ≠ 0 :=
    fun w hw => tail_diff_ne hσ N hout hw
  set Φ : ℂ → ℂ := fun l => φ l / T l with hΦ
  have hΦd : DiffContOnCl ℂ Φ (ball (0 : ℂ) R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hR.ne']
    intro w hw
    have hw' : ‖w‖ ≤ R := by simpa using hw
    exact ((hφ w).div (hdisc w hw').1 (hdisc w hw').2).differentiableWithinAt
  set s : Finset ℂ := insert z ((win N).image σ) with hs
  have hs_ne : s.Nonempty := ⟨z, Finset.mem_insert_self _ _⟩
  have hs_in : ∀ a ∈ s, ‖a‖ < R := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hzR
    · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
      exact hin m hm
  have hCD := circle_divided_difference hR hΦd s hs_ne hs_in
  rw [hs, sum_nodes hinj (win N) z (fun m _ => hz m) Φ] at hCD
  -- constants
  set P : ℂ → ℂ := fun l => ∏ m ∈ win N, (l - σ m) with hP
  set ε : ℂ := ∏ m ∈ win N, (-1 / (piN m : ℂ)) with hεdef
  have hε : ε ≠ 0 := Finset.prod_ne_zero_iff.mpr fun m _ =>
    div_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (piN_ne_zero m))
  have hψ : ∀ w, psiProd σ w = ε * P w * T w := by
    intro w
    rw [psiProd_eq hσ N w, hεdef, hP, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun m _ => ?_
    unfold prodFactor
    ring
  -- the integrand on the circle
  have hint : Set.EqOn (fun l => Φ l / ∏ a ∈ s, (l - a))
      (fun l => ε * (φ l / (psiProd σ l * (l - z)))) (sphere (0 : ℂ) R) := by
    intro l _
    simp only [hs, prod_nodes hinj (win N) z (fun m _ => hz m) l, hψ l, hΦ]
    exact alg_integrand ε (T l) (l - z) (P l) (φ l) hε |>.trans (by ring_nf)
  have h2πi : (2 * Real.pi * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hJ : (2 * Real.pi * Complex.I) * hermiteJ φ σ R z
      = ∮ l in C((0 : ℂ), R), φ l / (psiProd σ l * (l - z)) := by
    unfold hermiteJ
    field_simp
  rw [circleIntegral.integral_congr hR.le hint, circleIntegral.integral_const_mul] at hCD
  have hεJ : ε * hermiteJ φ σ R z = Φ z / P z
      + ∑ n ∈ win N, Φ (σ n) / ((σ n - z) * ∏ m ∈ (win N).erase n, (σ n - σ m)) := by
    apply mul_left_cancel₀ h2πi
    calc (2 * Real.pi * Complex.I) * (ε * hermiteJ φ σ R z)
        = ε * ((2 * Real.pi * Complex.I) * hermiteJ φ σ R z) := by ring
      _ = ε * ∮ l in C((0 : ℂ), R), φ l / (psiProd σ l * (l - z)) := by rw [hJ]
      _ = _ := hCD
  have hPz : P z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun m _ => sub_ne_zero.mpr (hz m).symm
  have hTz : T z ≠ 0 := (hdisc z hzR.le).2
  have hTσ : ∀ n ∈ win N, T (σ n) ≠ 0 := fun n hn => (hdisc _ (hin n hn).le).2
  have h1 : P z * T z * (Φ z / P z) = φ z := by
    simp only [hΦ]
    field_simp
  have h2 : ∀ n ∈ win N, P z * T z * (Φ (σ n) / ((σ n - z) * ∏ m ∈ (win N).erase n, (σ n - σ m)))
      = -(φ (σ n) * (cFin σ N z n * (T z / T (σ n)))) := by
    intro n hn
    have := lagrange_coeff_eq (σ := σ) (win N) hn z (hz n)
    have e : P z * T z * (Φ (σ n) / ((σ n - z) * ∏ m ∈ (win N).erase n, (σ n - σ m)))
        = T z * Φ (σ n) * (P z / ((σ n - z) * ∏ m ∈ (win N).erase n, (σ n - σ m))) := by ring
    rw [e, hP, this]
    simp only [hΦ, cFin]
    have := hTσ n hn
    field_simp
  rw [hψ z]
  calc φ z - ∑ n ∈ win N, φ (σ n) * (cFin σ N z n * (T z / T (σ n)))
      = P z * T z * (Φ z / P z) + ∑ n ∈ win N,
          P z * T z * (Φ (σ n) / ((σ n - z) * ∏ m ∈ (win N).erase n, (σ n - σ m))) := by
        rw [h1, Finset.sum_congr rfl h2, Finset.sum_neg_distrib]; ring
    _ = P z * T z * (Φ z / P z + ∑ n ∈ win N,
          Φ (σ n) / ((σ n - z) * ∏ m ∈ (win N).erase n, (σ n - σ m))) := by
        rw [mul_add, Finset.mul_sum]
    _ = ε * P z * T z * hermiteJ φ σ R z := by rw [← hεJ]; ring

end

end NlsGge.GK38.Lib
