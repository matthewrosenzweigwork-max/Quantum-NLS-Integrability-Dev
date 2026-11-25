import NlsGge.GK38.AbelianRotatedSquareSectors
import NlsGge.GK38.AbelianSquareAnnulusGeometry
import NlsGge.GK38.AbelianComplexHomotopyCauchy
import Mathlib.Tactic.FunProp

/-! SOURCE ONLY: actual ALL-quarterturn C2 homotopies in the genuine annulus.
Both radial connectors remain explicit. Local supplied discs and ROOT outer
midpoint circle instantiate the SAME concrete generic domain. No integral
cancellation/contour identity oracle. Exact targets+English preceded proofs.
UNCOMPILED, outside next4 science. -/
set_option autoImplicit false
open Set MeasureTheory
open scoped Topology unitInterval
namespace NlsGge.GK38
noncomputable section

def p6RotatedSquareSectorPath38 (c : ℂ) (r : ℝ) (k : ℕ) (t : ℝ) :
    Path (p6RotatedSquareSector38 c r k t (-1)) (p6RotatedSquareSector38 c r k t 1) where
  toFun u := p6RotatedSquareSector38 c r k t (2*(u : ℝ)-1)
  continuous_toFun := Continuous.comp
    (g := fun xy : ℝ × ℝ => p6RotatedSquareSector38 c r k xy.1 xy.2)
    (f := fun u : I => (t,2*(u : ℝ)-1))
    (p6RotatedSquareSector_contDiff38 c r k).continuous (by fun_prop)
  source' := by simp
  target' := by norm_num

def p6RotatedSquareSectorHomotopy38 (c : ℂ) (r : ℝ) (k : ℕ) :
    (p6RotatedSquareSectorPath38 c r k 0 : C(I, ℂ)).Homotopy
      (p6RotatedSquareSectorPath38 c r k 1) where
  toFun p := p6RotatedSquareSector38 c r k (p.1 : ℝ) (2*(p.2 : ℝ)-1)
  continuous_toFun := Continuous.comp
    (g := fun xy : ℝ × ℝ => p6RotatedSquareSector38 c r k xy.1 xy.2)
    (f := fun p : I × I => ((p.1 : ℝ),2*(p.2 : ℝ)-1))
    (p6RotatedSquareSector_contDiff38 c r k).continuous (by fun_prop)
  map_zero_left := by intro u; rfl
  map_one_left := by intro u; rfl

theorem p6RotatedSquareSectorHomotopy_contDiffOn38 (c : ℂ) (r : ℝ) (k : ℕ) :
    ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one
        ((p6RotatedSquareSectorHomotopy38 c r k).extend xy.1) xy.2)
      (Set.Icc 0 1) := by
  have hglobal : ContDiff ℝ 2
      (fun xy : ℝ × ℝ => p6RotatedSquareSector38 c r k xy.1 (2*xy.2-1)) :=
    ContDiff.comp
      (g := fun xy : ℝ × ℝ => p6RotatedSquareSector38 c r k xy.1 xy.2)
      (f := fun xy : ℝ × ℝ => (xy.1,2*xy.2-1))
      (p6RotatedSquareSector_contDiff38 c r k) (by fun_prop)
  have heq : EqOn
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one
        ((p6RotatedSquareSectorHomotopy38 c r k).extend xy.1) xy.2)
      (fun xy : ℝ × ℝ => p6RotatedSquareSector38 c r k xy.1 (2*xy.2-1)) (Set.Icc 0 1) := by
    rw [Icc_prod_eq]
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    lift x to I using hx
    lift y to I using hy
    calc
      _ = (p6RotatedSquareSectorHomotopy38 c r k).extend (x : ℝ) y :=
        Set.IccExtend_val zero_le_one ((p6RotatedSquareSectorHomotopy38 c r k).extend (x : ℝ)) y
      _ = (p6RotatedSquareSectorHomotopy38 c r k) (x,y) :=
        (p6RotatedSquareSectorHomotopy38 c r k).extend_apply_coe x y
      _ = _ := rfl
  exact hglobal.contDiffOn.congr heq

theorem p6RotatedSquareSectorHomotopy_range38 (c : ℂ) (r : ℝ) (k : ℕ) (hr : 0 ≤ r) :
    Set.range (p6RotatedSquareSectorHomotopy38 c r k) ⊆ p6SquareAnnulus38 c r := by
  rintro z ⟨⟨t,u⟩,rfl⟩
  have hy : |2*(u : ℝ)-1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [u.property.1,u.property.2]
  have hg := p6RotatedSquareSector_geometry38 c r k (t : ℝ) (2*(u : ℝ)-1) hr t.property hy
  exact ⟨hg.1,hg.2.1⟩

theorem p6Rotated_square_sector_boundary38 (c : ℂ) (r : ℝ) (k : ℕ) (hr : 0 ≤ r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (p6SquareAnnulus38 c r)) :
    (∫ᶜ z in p6RotatedSquareSectorPath38 c r k 0, p6ComplexForm38 f z) +
    (∫ᶜ z in (p6RotatedSquareSectorHomotopy38 c r k).evalAt 1, p6ComplexForm38 f z) =
    (∫ᶜ z in p6RotatedSquareSectorPath38 c r k 1, p6ComplexForm38 f z) +
    (∫ᶜ z in (p6RotatedSquareSectorHomotopy38 c r k).evalAt 0, p6ComplexForm38 f z) := by
  exact p6Complex_homotopy_boundary38 (p6RotatedSquareSectorHomotopy38 c r k) f
    (hf.mono (p6RotatedSquareSectorHomotopy_range38 c r k hr))
    (p6RotatedSquareSectorHomotopy_contDiffOn38 c r k)

end
end NlsGge.GK38
