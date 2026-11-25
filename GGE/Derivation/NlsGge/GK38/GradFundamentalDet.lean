import NlsGge.GK38.GradFundamentalDefs

/-! # K1: determinant one throughout the closed unit interval.
GK Chapter I, Proposition 3.1; the accepted F3 AC determinant proof is extended
by evaluating its constant determinant at arbitrary unit time.
-/
set_option autoImplicit false
open Filter Topology MeasureTheory
namespace NlsGge.GK38
noncomputable section

theorem det_primitive_eq_one_time38 {a b g00 g01 g10 g11 : ℝ → ℂ}
    (i00 : IntervalIntegrable g00 volume 0 1) (i01 : IntervalIntegrable g01 volume 0 1)
    (i10 : IntervalIntegrable g10 volume 0 1) (i11 : IntervalIntegrable g11 volume 0 1)
    (h00 : ∀ s ∈ Set.Icc (0 : ℝ) 1, g00 s = a s * ∫ r in (0 : ℝ)..s, g10 r)
    (h01 : ∀ s ∈ Set.Icc (0 : ℝ) 1, g01 s = a s * (1 + ∫ r in (0 : ℝ)..s, g11 r))
    (h10 : ∀ s ∈ Set.Icc (0 : ℝ) 1, g10 s = b s * (1 + ∫ r in (0 : ℝ)..s, g00 r))
    (h11 : ∀ s ∈ Set.Icc (0 : ℝ) 1, g11 s = b s * ∫ r in (0 : ℝ)..s, g01 r)
    (t : Set.Icc (0 : ℝ) 1) :
    (1 + ∫ r in (0 : ℝ)..(t : ℝ), g00 r) * (1 + ∫ r in (0 : ℝ)..(t : ℝ), g11 r) -
      (∫ r in (0 : ℝ)..(t : ℝ), g01 r) * (∫ r in (0 : ℝ)..(t : ℝ), g10 r) = 1 := by
  set q00 : ℝ → ℂ := fun s => 1 + ∫ r in (0 : ℝ)..s, g00 r with hq00
  set q11 : ℝ → ℂ := fun s => 1 + ∫ r in (0 : ℝ)..s, g11 r with hq11
  set q01 : ℝ → ℂ := fun s => ∫ r in (0 : ℝ)..s, g01 r with hq01
  set q10 : ℝ → ℂ := fun s => ∫ r in (0 : ℝ)..s, g10 r with hq10
  have h0 : (0 : ℝ) ∈ Set.uIcc 0 1 := Set.left_mem_uIcc
  have ac01 := ac_primitive38 i01 h0
  have ac10 := ac_primitive38 i10 h0
  have ac00 : AbsolutelyContinuousOnInterval q00 0 1 :=
    (absolutelyContinuousOnInterval_const38 1 0 1).add (ac_primitive38 i00 h0)
  have ac11 : AbsolutelyContinuousOnInterval q11 0 1 :=
    (absolutelyContinuousOnInterval_const38 1 0 1).add (ac_primitive38 i11 h0)
  set D : ℝ → ℂ := fun s => q00 s * q11 s - q01 s * q10 s with hD
  have acD : AbsolutelyContinuousOnInterval D 0 1 := (ac00.smul ac11).sub (ac01.smul ac10)
  have hderiv : ∀ᵐ x : ℝ, x ∈ Set.uIcc (0 : ℝ) 1 → HasDerivAt D 0 x := by
    filter_upwards [i00.ae_hasDerivAt_integral, i01.ae_hasDerivAt_integral,
      i10.ae_hasDerivAt_integral, i11.ae_hasDerivAt_integral] with x d00 d01 d10 d11 hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by rwa [Set.uIcc_of_le zero_le_one] at hx
    have e00 : HasDerivAt q00 (g00 x) x := (d00 hx 0 h0).const_add 1
    have e11 : HasDerivAt q11 (g11 x) x := (d11 hx 0 h0).const_add 1
    have e01 : HasDerivAt q01 (g01 x) x := d01 hx 0 h0
    have e10 : HasDerivAt q10 (g10 x) x := d10 hx 0 h0
    have := (e00.mul e11).sub (e01.mul e10)
    convert this using 1
    rw [h00 x hx', h01 x hx', h10 x hx', h11 x hx']
    ring
  obtain ⟨C, hC⟩ := acD.const_of_ae_hasDerivAt_zero hderiv
  have hD0 : D 0 = 1 := by simp [hD, hq00, hq11, hq01, hq10]
  have hD1 : D t = C := hC t (by simpa [Set.uIcc_of_le zero_le_one] using t.2)
  have hD0' : D 0 = C := hC 0 h0
  have hD1' : D t = 1 := hD1.trans (hD0'.symm.trans hD0)
  exact hD1'

theorem det_fundPair38 (φ : PotPair) (z : ℂ) (t : Set.Icc (0 : ℝ) 1) :
    (fundPair φ z t).det = 1 := by
  have key := det_primitive_eq_one_time38
    (a := fun s => freeE z (-s) 0 0 * (Complex.I * potRepFst38 φ s) * freeE z s 1 1)
    (b := fun s => freeE z (-s) 1 1 * (-(Complex.I * potRepSnd38 φ s)) * freeE z s 0 0)
    (intervalIntegrable_detKer38 φ z 0 0) (intervalIntegrable_detKer38 φ z 0 1)
    (intervalIntegrable_detKer38 φ z 1 0) (intervalIntegrable_detKer38 φ z 1 1)
    (fun s hs => by simpa using detKer38_zero_row φ z 0 hs)
    (fun s hs => by simpa using detKer38_zero_row φ z 1 hs)
    (fun s hs => by simpa using detKer38_one_row φ z 0 hs)
    (fun s hs => by simpa using detKer38_one_row φ z 1 hs) t
  have h1 := t.2
  have e : ∀ i j, fundPair φ z t i j = fundContP φ z t i j := fun i j => rfl
  rw [Matrix.det_fin_two, e, e, e, e, fundContP_entry_eq φ z h1, fundContP_entry_eq φ z h1,
    fundContP_entry_eq φ z h1, fundContP_entry_eq φ z h1]
  have h2 := freeE_diag_prod z t
  simp only [ite_true, show ¬ ((0 : Fin 2) = 1) from by decide, show ¬ ((1 : Fin 2) = 0) from by decide, ite_false]
  linear_combination (freeE z t 0 0 * freeE z t 1 1) * key + h2


end
end NlsGge.GK38
