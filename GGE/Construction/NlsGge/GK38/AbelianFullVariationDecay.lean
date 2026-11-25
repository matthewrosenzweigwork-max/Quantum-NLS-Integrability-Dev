import NlsGge.GK38.AbelianFullNumeratorVariation

/-! Actual little-o growth for the full variation. The unvaried omitted
numerator decays because its counting-circle distance tends to infinity. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38.P6FullNumeratorVariation
noncomputable section
open NlsGge.GK38.P4NumeratorVariation

theorem omittedNumerator_countingDecay (n : ℤ) (s : Lib.L2Seq) :
    countingDecay (p2FullNumerator38 n s) := by
  intro ε hε
  obtain ⟨C,hC,hprod⟩ := Lib.omitProd_circle_bound_dist ‖s‖
  let D : ℝ := 2*C/ε
  have hD : 0 < D := by dsimp [D];positivity
  let a : ℂ := (n : ℂ)*(Real.pi : ℂ)
  refine ⟨⌈(D+‖a‖)/Real.pi⌉₊,?_⟩
  intro m hm z hz
  have hm' : (⌈(D+‖a‖)/Real.pi⌉₊ : ℝ) ≤ m := by exact_mod_cast hm
  have hceil := Nat.le_ceil ((D+‖a‖)/Real.pi)
  have hrad : D+‖a‖ ≤ (m : ℝ)*Real.pi :=
    (div_le_iff₀ Real.pi_pos).mp (hceil.trans hm')
  have hbig : D ≤ ‖z-a‖ := by
    have h := norm_sub_norm_le z a
    rw [hz] at h
    linarith [Real.pi_pos]
  have hp : ‖p2FullNumerator38 n s z‖*‖z-a‖ ≤ 2*C*‖Complex.sin z‖ := by
    have h := mul_le_mul_of_nonneg_left (hprod s le_rfl n m z hz)
      (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [p2FullNumerator38,norm_mul,norm_neg,Complex.norm_ofNat,mul_assoc,a] using h
  have hsmall : ‖p2FullNumerator38 n s z‖*D ≤ 2*C*‖Complex.sin z‖ :=
    (mul_le_mul_of_nonneg_left hbig (norm_nonneg _)).trans hp
  calc
    _ ≤ (2*C*‖Complex.sin z‖)/D := (le_div_iff₀ hD).mpr hsmall
    _ = ε*‖Complex.sin z‖ := by dsimp [D];field_simp

theorem fullVariation_countingDecay (s h : Lib.L2Seq) :
    countingDecay (fullVariation s h) := by
  have h1 := countingDecay_const_mul (h 0) (omittedNumerator_countingDecay 0 s)
  have h2 := variation_full_weighted_countingDecay 0 s h
  have hsum := countingDecay_add h1 h2
  have hscale := countingDecay_const_mul ((Real.pi : ℂ)⁻¹) hsum
  have he : fullVariation s h =
      (fun z => (Real.pi : ℂ)⁻¹*(h 0*p2FullNumerator38 0 s z+
        p4NumeratorVariation38 0 s h z*(Lib.sigmaOf s 0-z))) := by
    funext z
    rw [fullVariation_factor 0]
    ring
  rw [he]
  exact hscale

end
end NlsGge.GK38.P6FullNumeratorVariation
