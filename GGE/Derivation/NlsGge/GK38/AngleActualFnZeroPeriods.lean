import NlsGge.GK38.AbelianPaddedPeriodMapBound

/-! Exact actual Hilbert-zero/scalar-period bridge at FULL complex inputs.
The actual omitted numerator is unchanged by extension/restriction. No
missing coordinate is silently set to zero or assumed to equal its center. -/
set_option autoImplicit false
namespace NlsGge.GK38
noncomputable section

theorem angleActual_Fn_zero_implies_periods38 (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s : Lib.L2Seq) (hzero : p2Fn38 n (φ,p2Restrict38 n s)=0) :
    ∀ m : ℤ, n ≠ m → abelianPeriod38 m φ (p2FullNumerator38 n s)=0 := by
  intro m hnm
  let k : P2Index38 n := ⟨m,Ne.symm hnm⟩
  have hc := congrArg (fun q : P2Space38 n => q k) hzero
  rw [p2Fn_apply38 n (φ,p2Restrict38 n s) hφ k] at hc
  change (((n-m : ℤ) : ℂ))*abelianPeriod38 m φ
    (p2FullNumerator38 n (p2Extend38 n (p2Restrict38 n s)))=0 at hc
  rw [p6Numerator_extend_restrict38] at hc
  have hw : (((n-m : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hnm
  exact (mul_eq_zero.mp hc).resolve_left hw

theorem angleActual_Fn_zero_iff_periods38 (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s : Lib.L2Seq) :
    p2Fn38 n (φ,p2Restrict38 n s)=0 ↔
      ∀ m : ℤ, n ≠ m → abelianPeriod38 m φ (p2FullNumerator38 n s)=0 := by
  constructor
  · exact angleActual_Fn_zero_implies_periods38 n φ hφ s
  · intro hperiod
    apply Subtype.ext
    funext m
    rw [p2Fn_apply38 n (φ,p2Restrict38 n s) hφ m]
    change (((n-m.1 : ℤ) : ℂ))*abelianPeriod38 m.1 φ
      (p2FullNumerator38 n (p2Extend38 n (p2Restrict38 n s)))=0
    rw [p6Numerator_extend_restrict38,hperiod m.1 m.2.symm,mul_zero]

end
end NlsGge.GK38
