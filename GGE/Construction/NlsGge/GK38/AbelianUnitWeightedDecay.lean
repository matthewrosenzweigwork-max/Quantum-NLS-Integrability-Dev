import NlsGge.GK38.AbelianWeightedCircleBound

/-! Genuine finite-head decay: the extracted r-th product factor supplies an
additional distance tending to infinity on the counting circles. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38.P4NumeratorVariation
noncomputable section

theorem variation_unit_weighted_decay (n r : ℤ) (hrn : r ≠ n) (s : Lib.L2Seq) :
    ∀ ε > 0, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ z : ℂ,
      ‖z‖=m*Real.pi+Real.pi/2 →
      ‖p4NumeratorVariation38 n s (lp.single 2 r (1 : ℂ)) z‖*
        ‖Lib.sigmaOf s n-z‖ ≤ ε*‖Complex.sin z‖ := by
  intro ε hε
  obtain ⟨C,hC,hprod⟩ := Lib.omitProd_circle_bound_dist ‖s‖
  obtain ⟨B,hB,hratio⟩ := sigma_counting_norm_ratio n s
  let D : ℝ := 2*C*B/ε
  have hD : 0 < D := by dsimp [D];positivity
  refine ⟨⌈(D+‖Lib.sigmaOf s r‖)/Real.pi⌉₊,?_⟩
  intro m hm z hz
  have hm' : (⌈(D+‖Lib.sigmaOf s r‖)/Real.pi⌉₊ : ℝ) ≤ m := by exact_mod_cast hm
  have hceil := Nat.le_ceil ((D+‖Lib.sigmaOf s r‖)/Real.pi)
  have hrad : D+‖Lib.sigmaOf s r‖ ≤ (m : ℝ)*Real.pi :=
    (div_le_iff₀ Real.pi_pos).mp (hceil.trans hm')
  have hbig : D ≤ ‖Lib.sigmaOf s r-z‖ := by
    have h := norm_sub_norm_le z (Lib.sigmaOf s r)
    rw [hz,norm_sub_rev] at h
    linarith [Real.pi_pos]
  have heq : p2FullNumerator38 n s z = (Lib.sigmaOf s r-z)*
      p4NumeratorVariation38 n s (lp.single 2 r (1 : ℂ)) z := by
    rw [variation_unit_column n r hrn]
    exact P3JacobianColumns.numerator_factor n r hrn s z
  have hp : ‖p2FullNumerator38 n s z‖*‖z-(n : ℂ)*(Real.pi : ℂ)‖ ≤
      2*C*‖Complex.sin z‖ := by
    have h := mul_le_mul_of_nonneg_left (hprod s le_rfl n m z hz) (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [p2FullNumerator38,norm_mul,norm_neg,Complex.norm_ofNat,mul_assoc] using h
  have hnorm := congrArg norm heq
  rw [norm_mul] at hnorm
  have hweighted : (‖p4NumeratorVariation38 n s (lp.single 2 r (1 : ℂ)) z‖*
      ‖Lib.sigmaOf s n-z‖)*D ≤ (2*C*B)*‖Complex.sin z‖ := by
    calc
      _ ≤ (‖p4NumeratorVariation38 n s (lp.single 2 r (1 : ℂ)) z‖*
          (B*‖z-(n : ℂ)*(Real.pi : ℂ)‖))*‖Lib.sigmaOf s r-z‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hratio m z hz) (norm_nonneg _))
          hbig hD.le (by positivity)
      _ = B*(‖p2FullNumerator38 n s z‖*‖z-(n : ℂ)*(Real.pi : ℂ)‖) := by rw [hnorm];ring
      _ ≤ B*(2*C*‖Complex.sin z‖) := mul_le_mul_of_nonneg_left hp hB.le
      _ = _ := by ring
  have hfinal := (le_div_iff₀ hD).mpr hweighted
  calc
    _ ≤ (2*C*B)*‖Complex.sin z‖/D := hfinal
    _ = ε*‖Complex.sin z‖ := by dsimp [D];field_simp

end
end NlsGge.GK38.P4NumeratorVariation
