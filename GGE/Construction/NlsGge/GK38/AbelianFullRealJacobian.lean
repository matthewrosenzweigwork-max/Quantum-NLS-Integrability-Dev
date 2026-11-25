import NlsGge.GK38.AbelianFullRealSpace
import NlsGge.GK38.AbelianFullPeriodHilbert
import NlsGge.GK38.AbelianFullVariationRecovery
import NlsGge.GK38.AbelianRealImage

/-! The actual full Qstar preserves genuine real directions at real inputs.
Its real restriction and injectivity are earned from actual scalar periods. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

def p6RealQstar38 (u : PhysicalL2) (s : P6RealSpace38) :
    P6RealSpace38 →L[ℝ] P6RealSpace38 :=
  p6RealPart38.comp
    (((p6Qstar38 (realSlice u) (p6RealInclude38 s)).restrictScalars ℝ).comp p6RealInclude38)

theorem p6Qstar_real_direction38 (u : PhysicalL2) (s h : P6RealSpace38) (m : ℤ) :
    (p6Qstar38 (realSlice u) (p6RealInclude38 s) (p6RealInclude38 h) m).im=0 := by
  rw [p6Qstar_apply38 (realSlice u) (realSlice_mem_gkW u)]
  exact (p2Canonical_period_real38 m u (discC (realSlice u)) (discR (realSlice u))
    (isolating_family38 (realSlice u) (realSlice_mem_gkW u))
    (P6FullNumeratorVariation.fullVariation (p6RealInclude38 s) (p6RealInclude38 h))
    (P6FullNumeratorVariation.fullVariation_entire _ _)
    (P6FullNumeratorVariation.fullVariation_real _ _
      (fun k => Complex.ofReal_im (s k)) (fun k => Complex.ofReal_im (h k)))).2

theorem p6RealQstar_include38 (u : PhysicalL2) (s h : P6RealSpace38) :
    p6RealInclude38 (p6RealQstar38 u s h)=
      p6Qstar38 (realSlice u) (p6RealInclude38 s) (p6RealInclude38 h) := by
  change p6RealInclude38 (p6RealPart38
    (p6Qstar38 (realSlice u) (p6RealInclude38 s) (p6RealInclude38 h))) = _
  exact p6RealInclude_realPart38 _ (p6Qstar_real_direction38 u s h)

theorem p6RealQstar_matrix_coordinate38 (u : PhysicalL2) (s : P6RealSpace38) (m r : ℤ) :
    ((p6RealQstar38 u s (lp.single 2 r (1 : ℝ)) m : ℝ) : ℂ)=
      abelianPeriod38 m (realSlice u)
        (fun z => (-2/(Real.pi : ℂ))*Lib.omitProd r (p6RealInclude38 s) z) := by
  have he := congrArg (fun q : Lib.L2Seq => q m)
    (p6RealQstar_include38 u s (lp.single 2 r (1 : ℝ)))
  rw [p6RealInclude_single38,p6Qstar_unit_column38 (realSlice u) (realSlice_mem_gkW u)] at he
  exact he

theorem p6RealQstar_kernel_zero38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (s h : P6RealSpace38)
    (hσ : ∀ k : ℤ, Lib.sigmaOf (p6RealInclude38 s) k ∈ closedBall (C k) (R k))
    (hnull : p6RealQstar38 u s h=0) : h=0 := by
  have he := p6RealQstar_include38 u s h
  rw [hnull,map_zero] at he
  have hp : ∀ m : ℤ, abelianPeriod38 m (realSlice u)
      (P6FullNumeratorVariation.fullVariation (p6RealInclude38 s) (p6RealInclude38 h))=0 := by
    intro m
    rw [← p6Qstar_apply38 (realSlice u) (realSlice_mem_gkW u),← he]
    rfl
  have hz := P6FullNumeratorVariation.full_period_null_direction_zero u C R hfam
    (p6RealInclude38 s) (p6RealInclude38 h)
    (fun k => Complex.ofReal_im (s k)) (fun k => Complex.ofReal_im (h k)) hσ hp
  have hr := congrArg p6RealPart38 hz
  simpa only [p6RealPart_include38,map_zero] using hr

theorem p6RealQstar_injective38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R) (s : P6RealSpace38)
    (hσ : ∀ k : ℤ, Lib.sigmaOf (p6RealInclude38 s) k ∈ closedBall (C k) (R k)) :
    Function.Injective (p6RealQstar38 u s) := by
  intro h k he
  have hz : p6RealQstar38 u s (h-k)=0 := by rw [map_sub,he,sub_self]
  exact sub_eq_zero.mp (p6RealQstar_kernel_zero38 u C R hfam s (h-k) hσ hz)

end
end NlsGge.GK38
