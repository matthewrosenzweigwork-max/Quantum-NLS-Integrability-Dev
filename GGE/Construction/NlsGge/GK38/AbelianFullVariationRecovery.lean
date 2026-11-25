import NlsGge.GK38.AbelianFullVariationNullRoots

/-! Recover EVERY full direction coordinate at its actual input root.
These are full-period null-injectivity components, not a Qstar inverse oracle. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38.P6FullNumeratorVariation
noncomputable section

theorem fullVariation_at_input_root (r : ℤ) (s h : Lib.L2Seq) :
    fullVariation s h (Lib.sigmaOf s r)=
      h r*((-2/(Real.pi : ℂ))*Lib.omitProd r s (Lib.sigmaOf s r)) := by
  rw [fullVariation_factor r]
  simp only [sub_self,zero_mul,add_zero]
  unfold p2FullNumerator38
  ring

theorem full_direction_zero_of_variation_zero (s h : Lib.L2Seq)
    (hinj : Function.Injective (Lib.sigmaOf s))
    (hzero : ∀ z : ℂ, fullVariation s h z=0) : h=0 := by
  apply Subtype.ext
  funext r
  change h r=0
  have hprod : Lib.omitProd r s (Lib.sigmaOf s r) ≠ 0 :=
    (Lib.omitProd_root_ne_zero_iff r s).mpr (fun m hmr he => hmr (hinj he))
  have hcol : (-2/(Real.pi : ℂ))*Lib.omitProd r s (Lib.sigmaOf s r) ≠ 0 :=
    mul_ne_zero (div_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) hprod
  have hz := hzero (Lib.sigmaOf s r)
  rw [fullVariation_at_input_root] at hz
  exact (mul_eq_zero.mp hz).resolve_right hcol

theorem input_injective_of_original_family (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (s : Lib.L2Seq)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k)) :
    Function.Injective (Lib.sigmaOf s) := by
  intro i j he
  by_contra hij
  obtain ⟨c,N,hg,_hsp⟩ := hfam
  have hd := (p2OwnSigma_denominator38 C R c N hg i j hij s (hσ i)
    (Lib.sigmaOf s j) (hσ j)).1
  exact hd (sub_eq_zero.mpr he)

theorem full_period_null_direction_zero (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (s h : Lib.L2Seq)
    (hs : ∀ k : ℤ, (s k).im=0) (hh : ∀ k : ℤ, (h k).im=0)
    (hσ : ∀ k : ℤ, Lib.sigmaOf s k ∈ closedBall (C k) (R k))
    (hnull : ∀ m : ℤ, abelianPeriod38 m (realSlice u) (fullVariation s h)=0) : h=0 :=
  full_direction_zero_of_variation_zero s h
    (input_injective_of_original_family u C R hfam s hσ)
    (full_period_null_variation_zero u s h hs hh hnull)

end
end NlsGge.GK38.P6FullNumeratorVariation
