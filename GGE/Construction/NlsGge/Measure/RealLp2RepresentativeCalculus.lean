import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace NlsGge.Measure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The difference of two `MemLp` representatives agrees in the quotient
with the `toLp` representative of their pointwise difference. -/
theorem toLp_sub_eq_of_memLp
    {f g : α → ℝ}
    (hf : MeasureTheory.MemLp f 2 μ)
    (hg : MeasureTheory.MemLp g 2 μ)
    (hd : MeasureTheory.MemLp (fun a => f a - g a) 2 μ) :
    hf.toLp f - hg.toLp g = hd.toLp (fun a => f a - g a) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g),
    hf.coeFn_toLp, hg.coeFn_toLp, hd.coeFn_toLp]
    with a hsub hfval hgval hdval
  calc
    (hf.toLp f - hg.toLp g) a = (hf.toLp f) a - (hg.toLp g) a := hsub
    _ = f a - g a := by rw [hfval, hgval]
    _ = (fun a => f a - g a) a := rfl
    _ = (hd.toLp (fun a => f a - g a)) a := hdval.symm

/-- The real `L²` norm of a `toLp` representative squared is the integral of
the pointwise square. The MemLp proof supplies the needed finiteness. -/
theorem norm_sq_toLp_eq_integral_sq
    {f : α → ℝ}
    (hf : MeasureTheory.MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ a, f a ^ 2 ∂μ := by
  calc
    ‖hf.toLp f‖ ^ 2 =
        RCLike.re (inner ℝ (hf.toLp f) (hf.toLp f)) :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) (hf.toLp f)
    _ = ∫ a, (hf.toLp f) a ^ 2 ∂μ := by
      rw [MeasureTheory.L2.inner_def]
      simp
    _ = ∫ a, f a ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with a ha
      rw [ha]

end NlsGge.Measure
