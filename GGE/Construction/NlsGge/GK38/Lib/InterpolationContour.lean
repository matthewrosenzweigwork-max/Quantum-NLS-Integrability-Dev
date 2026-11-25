import Mathlib

/-!
# L4b, part 4: the divided-difference identity on a circle

Source: the residue-theorem step of the proof of Grébert–Kappeler book Lemma F.4.  Mathlib has no
residue theorem for meromorphic functions, but for the rational weight `1/∏(z-a)` with finitely
many simple poles `a` inside the circle the residue computation is the Lagrange partial-fraction
identity plus Cauchy's integral formula:

`(1/2πi) ∮_{|z|=R} F(z)/∏_{a∈s}(z-a) dz = Σ_{a∈s} F(a)/∏_{b∈s∖{a}}(a-b)`

for `F` continuous on the closed disc and holomorphic inside (`circle_divided_difference`).
-/

set_option autoImplicit false

open Metric Complex

namespace NlsGge.GK38.Lib

noncomputable section

theorem circleIntegral_finset_sum' {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {c : ℂ} {R : ℝ}
    (h : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    ∮ z in C(c, R), ∑ i ∈ s, f i z = ∑ i ∈ s, ∮ z in C(c, R), f i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [circleIntegral]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [circleIntegral.integral_add (h a (Finset.mem_insert_self a s)) ?_]
    · rw [ih fun i hi => h i (Finset.mem_insert_of_mem hi)]
    · have := CircleIntegrable.sum s fun i hi => h i (Finset.mem_insert_of_mem hi)
      simpa [Finset.sum_fn] using this

/-- Lagrange partial fractions `1/∏(z-a) = Σ_a 1/((z-a) ∏_{b≠a}(a-b))`. -/
theorem partial_fractions (s : Finset ℂ) (hne : s.Nonempty) (z : ℂ) (hz : ∀ a ∈ s, z ≠ a) :
    (∏ a ∈ s, (z - a))⁻¹ = ∑ a ∈ s, ((∏ b ∈ s.erase a, (a - b)) * (z - a))⁻¹ := by
  classical
  have h1 := Lagrange.sum_basis (F := ℂ) (s := s) (v := id) (Set.injOn_id _) hne
  have h2 : ∑ a ∈ s, ∏ b ∈ s.erase a, (z - b) / (a - b) = 1 := by
    have := congrArg (Polynomial.eval z) h1
    simpa [Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_finsetSum, Polynomial.eval_prod,
      div_eq_inv_mul, mul_comm] using this
  have hP : (∏ a ∈ s, (z - a)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a ha => sub_ne_zero.mpr (hz a ha)
  calc (∏ a ∈ s, (z - a))⁻¹
      = (∑ a ∈ s, ∏ b ∈ s.erase a, (z - b) / (a - b)) * (∏ a ∈ s, (z - a))⁻¹ := by
        rw [h2, one_mul]
    _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a ha => ?_
        have hza : z - a ≠ 0 := sub_ne_zero.mpr (hz a ha)
        rw [Finset.prod_div_distrib, ← Finset.mul_prod_erase s (fun b => z - b) ha]
        have hq : ∏ b ∈ s.erase a, (z - b) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr fun b hb =>
            sub_ne_zero.mpr (hz b (Finset.mem_of_mem_erase hb))
        have hq2 : ∏ b ∈ s.erase a, (a - b) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr fun b hb =>
            sub_ne_zero.mpr (Finset.ne_of_mem_erase hb).symm
        field_simp

/-- **Divided differences by a contour integral.**  For finitely many nodes `a ∈ s` inside the
circle `|z| = R` and `F` continuous on the closed disc and holomorphic inside,
`∮ F/∏(z-a) = 2πi Σ_a F(a)/∏_{b≠a}(a-b)`. -/
theorem circle_divided_difference {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DiffContOnCl ℂ F (ball (0 : ℂ) R)) (s : Finset ℂ) (hne : s.Nonempty)
    (hs : ∀ a ∈ s, ‖a‖ < R) :
    (∮ z in C((0 : ℂ), R), F z / ∏ a ∈ s, (z - a))
      = (2 * Real.pi * Complex.I) * ∑ a ∈ s, F a / ∏ b ∈ s.erase a, (a - b) := by
  classical
  have hsph : ∀ z ∈ sphere (0 : ℂ) R, ∀ a ∈ s, z ≠ a := by
    intro z hz a ha h
    have := hs a ha
    rw [← h, mem_sphere_zero_iff_norm.mp hz] at this
    exact lt_irrefl _ this
  have hFc : ContinuousOn F (sphere (0 : ℂ) R) := by
    refine hF.continuousOn.mono ?_
    rw [closure_ball _ hR.ne']
    exact sphere_subset_closedBall
  have hK : ∀ a ∈ s, (∏ b ∈ s.erase a, (a - b)) ≠ 0 := fun a _ =>
    Finset.prod_ne_zero_iff.mpr fun b hb => sub_ne_zero.mpr (Finset.ne_of_mem_erase hb).symm
  have e : Set.EqOn (fun z => F z / ∏ a ∈ s, (z - a))
      (fun z => ∑ a ∈ s, (∏ b ∈ s.erase a, (a - b))⁻¹ • ((z - a)⁻¹ • F z)) (sphere (0 : ℂ) R) := by
    intro z hz
    have := partial_fractions s hne z (hsph z hz)
    simp only [smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm, this, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_inv]
    ring
  rw [circleIntegral.integral_congr hR.le e]
  have hint : ∀ a ∈ s, CircleIntegrable
      (fun z => (∏ b ∈ s.erase a, (a - b))⁻¹ • ((z - a)⁻¹ • F z)) 0 R := by
    intro a ha
    refine CircleIntegrable.const_smul (a := (∏ b ∈ s.erase a, (a - b))⁻¹) ?_
    refine ContinuousOn.circleIntegrable hR.le ?_
    have h1 : ContinuousOn (fun z : ℂ => (z - a)⁻¹) (sphere (0 : ℂ) R) :=
      ContinuousOn.inv₀ (by fun_prop) fun z hz => sub_ne_zero.mpr (hsph z hz a ha)
    simp only [smul_eq_mul]
    exact h1.mul hFc
  rw [circleIntegral_finset_sum' s _ hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [circleIntegral.integral_smul]
  have := hF.circleIntegral_sub_inv_smul (w := a) (mem_ball_zero_iff.mpr (hs a ha))
  rw [this]
  simp only [smul_eq_mul, div_eq_inv_mul]
  ring

end

end NlsGge.GK38.Lib
