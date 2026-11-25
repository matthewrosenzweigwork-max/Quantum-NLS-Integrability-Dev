import NlsGge.GK38.AbelianHilbert
import NlsGge.GK38.TauGamma

/-! A genuine quadratic majorant earns the LITERAL complex quotient in lp2.
The zero-gap case is handled by proving zero numerator BEFORE cancellation;
no analyticity of the totalized quotient at collapsed gaps is asserted. -/
set_option autoImplicit false
namespace NlsGge.GK38
noncomputable section

theorem angleScalar_quadratic_quotient38 (z g : ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hbound : ‖z‖ ≤ ‖g‖*a) : z=g*(z/g) ∧ ‖z/g‖ ≤ a := by
  by_cases hg : g=0
  · have hz : z=0 := norm_eq_zero.mp
      (le_antisymm (by simpa only [hg,norm_zero,zero_mul] using hbound) (norm_nonneg z))
    simp only [hg,hz,zero_div,mul_zero,norm_zero,true_and]
    exact ha
  · constructor
    · rw [← mul_div_assoc,mul_div_cancel_left₀ _ hg]
    · rw [norm_div]
      exact (div_le_iff₀ (norm_pos_iff.mpr hg)).mpr (by simpa only [mul_comm] using hbound)

theorem angleActual_quadratic_quotient_lp38 (n : ℤ) (φ : PotPair) (s : Lib.L2Seq)
    (a : ℤ → ℝ) (ha0 : ∀ m, 0 ≤ a m)
    (has : Summable (fun m : ℤ => a m^2)) (B : ℝ)
    (haB : (∑' m : ℤ,a m^2) ≤ B)
    (hbound : ∀ m : ℤ, n ≠ m →
      ‖Lib.sigmaOf s m-tauN φ m‖ ≤ ‖gamma2 φ m‖*a m) :
    ∃ A : P2Space38 n,
      (∀ m : P2Index38 n,
        A m=(Lib.sigmaOf s m.1-tauN φ m.1)/gamma2 φ m.1) ∧
      Summable (fun m : P2Index38 n => ‖A m‖^2) ∧
      (∑' m : P2Index38 n,‖A m‖^2) ≤ B ∧
      ∀ m : P2Index38 n,
        Lib.sigmaOf s m.1=tauN φ m.1+gamma2 φ m.1*A m := by
  let q : P2Index38 n → ℂ := fun m =>
    (Lib.sigmaOf s m.1-tauN φ m.1)/gamma2 φ m.1
  have hscalar (m : P2Index38 n) := angleScalar_quadratic_quotient38
    (Lib.sigmaOf s m.1-tauN φ m.1) (gamma2 φ m.1) (a m.1) (ha0 m.1)
      (hbound m.1 m.2.symm)
  have hsub : Summable (fun m : P2Index38 n => a m.1^2) :=
    has.comp_injective (i := fun m : P2Index38 n => m.1) Subtype.val_injective
  have hsq (m : P2Index38 n) : ‖q m‖^2 ≤ a m.1^2 := by
    simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg (q m)) (hscalar m).2
  have hqs : Summable (fun m : P2Index38 n => ‖q m‖^2) :=
    hsub.of_nonneg_of_le (fun _ => sq_nonneg _) hsq
  let A : P2Space38 n := ⟨q,
    (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr (by simpa using hqs)⟩
  refine ⟨A,fun _ => rfl,hqs,?_,?_⟩
  · exact (hqs.tsum_le_tsum hsq hsub).trans
      ((Summable.tsum_subtype_le (fun m : ℤ => a m^2) {m : ℤ | m ≠ n}
        (fun _ => sq_nonneg _) has).trans haB)
  · intro m
    change Lib.sigmaOf s m.1=tauN φ m.1+gamma2 φ m.1*q m
    calc
      _ = (Lib.sigmaOf s m.1-tauN φ m.1)+tauN φ m.1 := (sub_add_cancel _ _).symm
      _ = gamma2 φ m.1*q m+tauN φ m.1 := by rw [(hscalar m).1]
      _ = _ := add_comm _ _

end
end NlsGge.GK38
