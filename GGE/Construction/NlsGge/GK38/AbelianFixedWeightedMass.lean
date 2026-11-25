import NlsGge.GK38.AbelianShiftedSquareMass

/-! UNCOMPILED genuine common-row majorants. The product row is proved square
summable BEFORE shifted masses or their limits are used. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p6ProductRow_square_summable38 (E d : ℤ → ℝ)
    (hE : Summable (fun m : ℤ => E m^2))
    (hd : Summable (fun m : ℤ => d m^2)) :
    Summable (fun m : ℤ => (E m*d m)^2) := by
  have hdom := hE.mul_left (∑' k : ℤ, d k^2)
  apply hdom.of_nonneg_of_le (fun _ => sq_nonneg _)
  intro m
  have hb : d m^2 ≤ ∑' k : ℤ, d k^2 := hd.le_tsum m (fun k _ => sq_nonneg _)
  calc
    _ = E m^2*d m^2 := by ring
    _ ≤ E m^2*(∑' k : ℤ, d k^2) := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by ring

theorem p6WeightedMass_common_majorant38 (e E d : ℤ → ℝ)
    (he0 : ∀ m, 0 ≤ e m) (hE0 : ∀ m, 0 ≤ E m) (heE : ∀ m, e m ≤ E m)
    (hE : Summable (fun m : ℤ => E m^2))
    (hd : Summable (fun m : ℤ => d m^2))
    (a g : ℝ) (ha : 0 ≤ a) (hag : a ≤ g) (n : ℤ) :
    Summable (fun m : ℤ => e m^2*(a+d m)^2*Lib.c3w m n^2) ∧
      (∑' m : ℤ, e m^2*(a+d m)^2*Lib.c3w m n^2) ≤
        2*g^2*(∑' m : ℤ, E m^2*Lib.c3w m n^2)+
          2*(∑' m : ℤ, (E m*d m)^2*Lib.c3w m n^2) := by
  have hEs := p6ShiftedSquareMass_summable38 E hE n
  have hFs := p6ShiftedSquareMass_summable38 (fun m => E m*d m)
    (p6ProductRow_square_summable38 E d hE hd) n
  have hdom := (hEs.mul_left (2*g^2)).add (hFs.mul_left 2)
  have hpoint (m : ℤ) : e m^2*(a+d m)^2*Lib.c3w m n^2 ≤
      (2*g^2)*(E m^2*Lib.c3w m n^2)+2*((E m*d m)^2*Lib.c3w m n^2) := by
    have he2 : e m^2 ≤ E m^2 := by nlinarith [he0 m,hE0 m,heE m]
    have ha2 : a^2 ≤ g^2 := by nlinarith
    have had : (a+d m)^2 ≤ 2*g^2+2*d m^2 := by nlinarith [sq_nonneg (a-d m)]
    calc
      _ ≤ E m^2*(a+d m)^2*Lib.c3w m n^2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right he2 (sq_nonneg _)) (sq_nonneg _)
      _ ≤ E m^2*(2*g^2+2*d m^2)*Lib.c3w m n^2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left had (sq_nonneg _)) (sq_nonneg _)
      _ = _ := by ring
  have hs := hdom.of_nonneg_of_le
    (fun m => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)) hpoint
  refine ⟨hs,?_⟩
  have hb := hs.tsum_le_tsum hpoint hdom
  rw [(hEs.mul_left (2*g^2)).tsum_add (hFs.mul_left 2),tsum_mul_left,tsum_mul_left] at hb
  exact hb

theorem p6FixedWeightedMass_majorant_cofinite_zero38 (g E d : ℤ → ℝ)
    (hg : Summable (fun n : ℤ => g n^2))
    (hE : Summable (fun m : ℤ => E m^2))
    (hd : Summable (fun m : ℤ => d m^2)) :
    Tendsto (fun n : ℤ =>
      2*g n^2*(∑' m : ℤ, E m^2*Lib.c3w m n^2)+
        2*(∑' m : ℤ, (E m*d m)^2*Lib.c3w m n^2))
      cofinite (𝓝 (0 : ℝ)) := by
  have hfirst := ((tendsto_const_nhds (x := (2 : ℝ))).mul hg.tendsto_cofinite_zero).mul
    (p6ShiftedSquareMass_cofinite_zero38 E hE)
  have hsecond := (tendsto_const_nhds (x := (2 : ℝ))).mul
    (p6ShiftedSquareMass_cofinite_zero38 (fun m => E m*d m)
      (p6ProductRow_square_summable38 E d hE hd))
  simpa only [mul_zero,zero_mul,zero_add] using hfirst.add hsecond

end
end NlsGge.GK38
