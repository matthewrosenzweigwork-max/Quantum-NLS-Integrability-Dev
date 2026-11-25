import QuantumNLS.LinearFundamental

/-!
DEF-013, L¹-coefficient Volterra construction on a finite physical period.
Source: model.tex eq:lax and ROOT_spectral_density.tex, first proof paragraph.
Frozen SpatialTransfer and LinearFundamental are consumed read-only.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped Nat Interval
namespace QuantumNLS.L1SpatialTransfer

section Scalar

/-- Absolute continuity is stable under nonnegative integer powers. -/
theorem ac_pow {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (n : ℕ) :
    AbsolutelyContinuousOnInterval (fun x => f x ^ n) a b := by
  induction n with
  | zero => simpa using (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  | succ n ih => simpa [pow_succ] using ih.fun_mul hf

/-- Integrated chain rule for the cumulative L¹ majorant; no continuity of the density. -/
theorem integral_control_pow {g : ℝ → ℝ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (n : ℕ) :
    ∫ x in a..b, g x * (∫ t in a..x, g t) ^ n =
      (∫ t in a..b, g t) ^ (n + 1) / (n + 1) := by
  let F : ℝ → ℝ := fun x => ∫ t in a..x, g t
  have hF := hg.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hpow := ac_pow hF (n + 1)
  have hderiv : ∀ᵐ x, x ∈ uIoc a b →
      deriv (fun y => F y ^ (n + 1)) x = (n + 1 : ℝ) * (g x * F x ^ n) := by
    filter_upwards [hg.ae_hasDerivAt_integral] with x hx hxab
    have hd := (hx (uIoc_subset_uIcc hxab) a (by simp)).pow (n + 1)
    convert hd.deriv using 1
    simp [F]
    ring
  have hi := hpow.integral_deriv_eq_sub
  rw [intervalIntegral.integral_congr_ae hderiv, intervalIntegral.integral_const_mul] at hi
  simp only [F, intervalIntegral.integral_same, zero_pow (Nat.succ_ne_zero _), sub_zero] at hi
  exact (eq_div_iff (by positivity : (n + 1 : ℝ) ≠ 0)).2 (by nlinarith [hi])


/-- Absolute continuity passes through a distance majorant. -/
theorem ac_of_dist_le {E : Type*} [PseudoMetricSpace E]
    {f : ℝ → E} {g : ℝ → ℝ} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (h : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (f x) (f y) ≤ dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := hg ε hε
  refine ⟨δ, hδ, fun I hI hlen => lt_of_le_of_lt ?_ (hd I hI hlen)⟩
  apply Finset.sum_le_sum
  intro i hi
  exact h _ (hI.1 i hi).1 _ (hI.1 i hi).2

/-- Bochner primitives are absolutely continuous, including matrix-valued primitives. -/
theorem ac_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in a..x, f t) a b := by
  apply ac_of_dist_le (hf.norm.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp))
  intro x hx y hy
  have hax := hf.mono_set (uIcc_subset_uIcc left_mem_uIcc hx)
  have hay := hf.mono_set (uIcc_subset_uIcc left_mem_uIcc hy)
  rw [dist_eq_norm, Real.dist_eq,
    intervalIntegral.integral_interval_sub_left hax hay,
    intervalIntegral.integral_interval_sub_left hax.norm hay.norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

end Scalar

section General
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
open QuantumNLS.LinearFundamental

/-- Even with merely L¹ coefficients every finite Dyson iterate is continuous. -/
theorem continuousOn_dyson {A : ℝ → 𝔸} {L : ℝ}
    (hA : IntervalIntegrable A volume 0 L) :
    ∀ n, ContinuousOn (dyson A n) (uIcc 0 L)
  | 0 => continuousOn_const
  | n + 1 => by
    have hi := hA.mul_continuousOn (continuousOn_dyson hA n)
    exact intervalIntegral.continuousOn_primitive_interval
      ((intervalIntegrable_iff' (by finiteness)).mp hi)

/-- Each product in the Volterra iteration is genuinely integrable. -/
theorem integrable_dyson_product {A : ℝ → 𝔸} {L : ℝ}
    (hA : IntervalIntegrable A volume 0 L) (n : ℕ) :
    IntervalIntegrable (fun x => A x * dyson A n x) volume 0 L :=
  hA.mul_continuousOn (continuousOn_dyson hA n)

/-- L¹ factorial estimate, with the accumulated coefficient norm in place of an L∞ bound. -/
theorem norm_dyson_le_control {A : ℝ → 𝔸} {L : ℝ}
    (hL : 0 ≤ L) (hA : IntervalIntegrable A volume 0 L) :
    ∀ n, ∀ x ∈ Icc 0 L, ‖dyson A n x‖ ≤
      ‖(1 : 𝔸)‖ * (∫ t in (0 : ℝ)..x, ‖A t‖) ^ n / (n.factorial : ℝ) := by
  intro n
  induction n with
  | zero => intro x hx; simp [dyson]
  | succ n ih =>
    intro x hx
    have hsub : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) L := by
      rw [uIcc_of_le hx.1, uIcc_of_le hL]; exact Icc_subset_Icc_right hx.2
    have hAx := hA.mono_set hsub
    have hF : ContinuousOn (fun s => (∫ t in (0 : ℝ)..s, ‖A t‖) ^ n) (uIcc 0 x) :=
      (intervalIntegral.continuousOn_primitive_interval
        ((intervalIntegrable_iff' (by finiteness)).mp hAx.norm)).pow n
    have hint : IntervalIntegrable
        (fun s => ‖(1 : 𝔸)‖ * (‖A s‖ * (∫ t in (0 : ℝ)..s, ‖A t‖) ^ n) / (n.factorial : ℝ)) volume 0 x :=
      ((hAx.norm.mul_continuousOn hF).const_mul _).div_const _
    calc
      ‖dyson A (n + 1) x‖ ≤ ∫ s in (0 : ℝ)..x, ‖A s * dyson A n s‖ :=
        intervalIntegral.norm_integral_le_integral_norm hx.1
      _ ≤ ∫ s in (0 : ℝ)..x,
          ‖(1 : 𝔸)‖ * (‖A s‖ * (∫ t in (0 : ℝ)..s, ‖A t‖) ^ n) / (n.factorial : ℝ) := by
        refine intervalIntegral.integral_mono_on hx.1
          ((integrable_dyson_product hA n).mono_set hsub).norm hint fun s hs => ?_
        calc
          ‖A s * dyson A n s‖ ≤ ‖A s‖ * ‖dyson A n s‖ := norm_mul_le _ _
          _ ≤ ‖A s‖ * (‖(1 : 𝔸)‖ * (∫ t in (0 : ℝ)..s, ‖A t‖) ^ n / (n.factorial : ℝ)) :=
            mul_le_mul_of_nonneg_left (ih s ⟨hs.1, hs.2.trans hx.2⟩) (norm_nonneg _)
          _ = _ := by ring
      _ = ‖(1 : 𝔸)‖ * (∫ t in (0 : ℝ)..x, ‖A t‖) ^ (n + 1) / (n + 1)! := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
          integral_control_pow hAx.norm n, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring


/-- Canonical Volterra series, independent of any arbitrary solution choice. -/
def transfer (A : ℝ → 𝔸) (x : ℝ) : 𝔸 := ∑' n, dyson A n x

/-- A single summable majorant controls the whole period. -/
theorem uniform_dyson_bound {A : ℝ → 𝔸} {L : ℝ}
    (hL : 0 ≤ L) (hA : IntervalIntegrable A volume 0 L) :
    Summable (fun n : ℕ => ‖(1 : 𝔸)‖ * (∫ t in (0 : ℝ)..L, ‖A t‖) ^ n / (n.factorial : ℝ)) ∧
    ∀ n, ∀ x ∈ Icc 0 L, ‖dyson A n x‖ ≤
      ‖(1 : 𝔸)‖ * (∫ t in (0 : ℝ)..L, ‖A t‖) ^ n / (n.factorial : ℝ) := by
  refine ⟨?_, fun n x hx => (norm_dyson_le_control hL hA n x hx).trans ?_⟩
  · simpa [mul_div_assoc] using
      (Real.summable_pow_div_factorial (∫ t in (0 : ℝ)..L, ‖A t‖)).mul_left ‖(1 : 𝔸)‖
  · have h0 := intervalIntegral.integral_nonneg (μ := volume) hx.1 (fun t _ => norm_nonneg (A t))
    have hle := intervalIntegral.integral_mono_interval (a := (0 : ℝ)) (b := x)
      le_rfl hx.1 hx.2 (ae_of_all _ fun t => norm_nonneg (A t)) hA.norm
    gcongr

/-- Uniform convergence makes the L¹-coefficient transfer continuous on the period. -/
theorem continuousOn_transfer {A : ℝ → 𝔸} {L : ℝ}
    (hL : 0 ≤ L) (hA : IntervalIntegrable A volume 0 L) :
    ContinuousOn (transfer A) (Icc 0 L) := by
  obtain ⟨hs, hb⟩ := uniform_dyson_bound hL hA
  exact continuousOn_tsum (fun n => by simpa [uIcc_of_le hL] using continuousOn_dyson hA n) hs hb

/-- The series solves the actual Volterra integral equation, with no smallness premise. -/
theorem transfer_integral_eq {A : ℝ → 𝔸} {L : ℝ}
    (hL : 0 ≤ L) (hA : IntervalIntegrable A volume 0 L) {x : ℝ} (hx : x ∈ Icc 0 L) :
    transfer A x = 1 + ∫ s in (0 : ℝ)..x, A s * transfer A s := by
  obtain ⟨hs, hb⟩ := uniform_dyson_bound hL hA
  let c : ℕ → ℝ := fun n => ‖(1 : 𝔸)‖ * (∫ t in (0 : ℝ)..L, ‖A t‖) ^ n / (n.factorial : ℝ)
  have hsub : uIcc (0 : ℝ) x ⊆ Icc 0 L := by
    rw [uIcc_of_le hx.1]; exact Icc_subset_Icc_right hx.2
  have hS : HasSum (fun n => dyson A n x) (transfer A x) :=
    (Summable.of_norm_bounded hs (fun n => hb n x hx)).hasSum
  have hI : HasSum (fun n => ∫ s in (0 : ℝ)..x, A s * dyson A n s)
      (∫ s in (0 : ℝ)..x, A s * transfer A s) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n s => ‖A s‖ * c n) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
    · have hn : IntervalIntegrable (fun s => A s * dyson A n s) volume 0 x :=
        (integrable_dyson_product hA n).mono_set (by rw [uIcc_of_le hL]; exact hsub)
      exact hn.aestronglyMeasurable_restrict_uIoc
    · exact ae_of_all _ fun s h => (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (hb n s (hsub (uIoc_subset_uIcc h))) (norm_nonneg _))
    · exact ae_of_all _ fun s _ => hs.mul_left ‖A s‖
    · simpa only [c, tsum_mul_left] using
        ((hA.norm.mono_set (by simpa [uIcc_of_le hL] using hsub)).mul_const (∑' n, c n))
    · exact ae_of_all _ fun s h =>
        ((Summable.of_norm_bounded hs (fun n => hb n s (hsub (uIoc_subset_uIcc h)))).hasSum).mul_left (A s)
  have hS1 : HasSum (fun n => dyson A (n + 1) x) (transfer A x - 1) := by
    simpa [dyson] using (hasSum_nat_add_iff' 1).mpr hS
  have he := hS1.unique hI
  rw [← he]; abel

/-- Almost everywhere equality of coefficients gives equality of every iterate, at every point. -/
theorem dyson_eq_of_ae {A B : ℝ → 𝔸} {L : ℝ} (_hL : 0 ≤ L)
    (hAB : A =ᵐ[volume.restrict (Icc 0 L)] B) :
    ∀ n, ∀ x ∈ Icc 0 L, dyson A n x = dyson B n x := by
  intro n
  induction n with
  | zero => intro x hx; rfl
  | succ n ih =>
    intro x hx
    apply intervalIntegral.integral_congr_ae
    have hab := (ae_restrict_iff' measurableSet_Icc).mp hAB
    filter_upwards [hab] with s hs h
    have hs0 : s ∈ Icc 0 L := by
      have hh := uIoc_subset_uIcc h
      rw [uIcc_of_le hx.1] at hh
      exact ⟨hh.1, hh.2.trans hx.2⟩
    rw [hs hs0, ih s hs0]

/-- Representative independence of the series, including all endpoint values. -/
theorem transfer_eq_of_ae {A B : ℝ → 𝔸} {L : ℝ} (_hL : 0 ≤ L)
    (hAB : A =ᵐ[volume.restrict (Icc 0 L)] B) {x : ℝ} (hx : x ∈ Icc 0 L) :
    transfer A x = transfer B x := by
  exact tsum_congr (fun n => dyson_eq_of_ae _hL hAB n x hx)


/-- The actual summed transfer is absolutely continuous on the whole period. -/
theorem ac_transfer {A : ℝ → 𝔸} {L : ℝ}
    (hL : 0 ≤ L) (hA : IntervalIntegrable A volume 0 L) :
    AbsolutelyContinuousOnInterval (transfer A) 0 L := by
  have hp : IntervalIntegrable (fun s => A s * transfer A s) volume 0 L :=
    hA.mul_continuousOn (by simpa [uIcc_of_le hL] using continuousOn_transfer hL hA)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : 𝔸)) 0 L :=
    (LipschitzWith.const (1 : 𝔸)).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hc.add (ac_integral hp)).congr
  intro x hx
  exact (transfer_integral_eq hL hA (by simpa [uIcc_of_le hL] using hx)).symm

/-- Carathéodory differential equation: the derivative equals A M almost everywhere. -/
theorem ae_hasDerivAt_transfer {A : ℝ → 𝔸} {L : ℝ}
    (hL : 0 ≤ L) (hA : IntervalIntegrable A volume 0 L) :
    ∀ᵐ x ∂volume.restrict (Icc 0 L), HasDerivAt (transfer A) (A x * transfer A x) x := by
  have hp : IntervalIntegrable (fun s => A s * transfer A s) volume 0 L :=
    hA.mul_continuousOn (by simpa [uIcc_of_le hL] using continuousOn_transfer hL hA)
  rw [ae_restrict_iff' measurableSet_Icc]
  have hz : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
  have hlast : ∀ᵐ x : ℝ ∂volume, x ≠ L := by simp [ae_iff]
  filter_upwards [hp.ae_hasDerivAt_integral, hz, hlast] with x hd hz hl hx
  have hi : x ∈ Ioo 0 L := ⟨lt_of_le_of_ne hx.1 (Ne.symm hz), lt_of_le_of_ne hx.2 hl⟩
  have hd' := (hd (by simpa [uIcc_of_le hL] using hx) 0 left_mem_uIcc).const_add (1 : 𝔸)
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hi.1 hi.2] with y hy
  exact transfer_integral_eq hL hA ⟨hy.1.le, hy.2.le⟩

/-- Uniqueness for the homogeneous Volterra equation; no coefficient smallness. -/
theorem eq_zero_of_integral {A f : ℝ → 𝔸} {L : ℝ}
    (hL : 0 ≤ L) (hA : IntervalIntegrable A volume 0 L)
    (hc : ContinuousOn f (Icc 0 L))
    (hf : ∀ x ∈ Icc 0 L, f x = ∫ s in (0 : ℝ)..x, A s * f s) :
    ∀ x ∈ Icc 0 L, f x = 0 := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hL⟩)
  have hp : IntervalIntegrable (fun s => A s * f s) volume 0 L :=
    hA.mul_continuousOn (by simpa [uIcc_of_le hL] using hc)
  have hb : ∀ n : ℕ, ∀ x ∈ Icc 0 L, ‖f x‖ ≤
      B * (∫ s in (0 : ℝ)..x, ‖A s‖) ^ n / (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hB x hx
    | succ n ih =>
      intro x hx
      have hsub : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) L := by
        rw [uIcc_of_le hx.1, uIcc_of_le hL]; exact Icc_subset_Icc_right hx.2
      have hAx := hA.mono_set hsub
      have hF : ContinuousOn (fun s => (∫ t in (0 : ℝ)..s, ‖A t‖) ^ n) (uIcc 0 x) :=
        (intervalIntegral.continuousOn_primitive_interval
          ((intervalIntegrable_iff' (by finiteness)).mp hAx.norm)).pow n
      have hint : IntervalIntegrable
          (fun s => B * (‖A s‖ * (∫ t in (0 : ℝ)..s, ‖A t‖) ^ n) / (n.factorial : ℝ)) volume 0 x :=
        ((hAx.norm.mul_continuousOn hF).const_mul _).div_const _
      calc
        ‖f x‖ = ‖∫ s in (0 : ℝ)..x, A s * f s‖ := by rw [hf x hx]
        _ ≤ ∫ s in (0 : ℝ)..x, ‖A s * f s‖ := intervalIntegral.norm_integral_le_integral_norm hx.1
        _ ≤ ∫ s in (0 : ℝ)..x,
            B * (‖A s‖ * (∫ t in (0 : ℝ)..s, ‖A t‖) ^ n) / (n.factorial : ℝ) := by
          refine intervalIntegral.integral_mono_on hx.1 (hp.mono_set hsub).norm hint fun s hs => ?_
          calc
            ‖A s * f s‖ ≤ ‖A s‖ * ‖f s‖ := norm_mul_le _ _
            _ ≤ ‖A s‖ * (B * (∫ t in (0 : ℝ)..s, ‖A t‖) ^ n / (n.factorial : ℝ)) :=
              mul_le_mul_of_nonneg_left (ih s ⟨hs.1, hs.2.trans hx.2⟩) (norm_nonneg _)
            _ = _ := by ring
        _ = B * (∫ t in (0 : ℝ)..x, ‖A t‖) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
          rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
            integral_control_pow hAx.norm n, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
  intro x hx
  have hs : Summable (fun n : ℕ => B * (∫ t in (0 : ℝ)..x, ‖A t‖) ^ n / (n.factorial : ℝ)) := by
    simpa [mul_div_assoc] using
      (Real.summable_pow_div_factorial (∫ t in (0 : ℝ)..x, ‖A t‖)).mul_left B
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  exact ge_of_tendsto' hs.tendsto_atTop_zero (fun n => hb n x hx)

/-- Uniqueness of continuous solutions of the inhomogeneous fundamental integral equation. -/
theorem integral_solution_unique {A M N : ℝ → 𝔸} {L : ℝ}
    (hL : 0 ≤ L) (hA : IntervalIntegrable A volume 0 L)
    (hM : ContinuousOn M (Icc 0 L)) (hN : ContinuousOn N (Icc 0 L))
    (hMe : ∀ x ∈ Icc 0 L, M x = 1 + ∫ s in (0 : ℝ)..x, A s * M s)
    (hNe : ∀ x ∈ Icc 0 L, N x = 1 + ∫ s in (0 : ℝ)..x, A s * N s) :
    EqOn M N (Icc 0 L) := by
  have hpM := hA.mul_continuousOn (by simpa [uIcc_of_le hL] using hM)
  have hpN := hA.mul_continuousOn (by simpa [uIcc_of_le hL] using hN)
  have hz := eq_zero_of_integral hL hA (hM.sub hN) (fun x hx => by
    simp only [Pi.sub_apply]
    rw [hMe x hx, hNe x hx]
    simp only [mul_sub]
    rw [intervalIntegral.integral_sub
      (hpM.mono_set (uIcc_subset_uIcc left_mem_uIcc (by simpa [uIcc_of_le hL] using hx)))
      (hpN.mono_set (uIcc_subset_uIcc left_mem_uIcc (by simpa [uIcc_of_le hL] using hx)))]
    abel)
  exact fun x hx => sub_eq_zero.mp (hz x hx)


/-- All initial-value, AC, a.e.-ODE and uniqueness assertions for the constructed transfer. -/
theorem fundamental_spec {A : ℝ → 𝔸} {L : ℝ}
    (hL : 0 ≤ L) (hA : IntervalIntegrable A volume 0 L) :
    transfer A 0 = 1 ∧ AbsolutelyContinuousOnInterval (transfer A) 0 L ∧
      (∀ᵐ x ∂volume.restrict (Icc 0 L), HasDerivAt (transfer A) (A x * transfer A x) x) ∧
      ∀ M : ℝ → 𝔸, ContinuousOn M (Icc 0 L) →
        (∀ x ∈ Icc 0 L, M x = 1 + ∫ s in (0 : ℝ)..x, A s * M s) →
        EqOn M (transfer A) (Icc 0 L) := by
  refine ⟨?_, ac_transfer hL hA, ae_hasDerivAt_transfer hL hA, ?_⟩
  · simpa using transfer_integral_eq hL hA (x := 0) ⟨le_rfl, hL⟩
  · intro M hc he
    exact integral_solution_unique hL hA hc (continuousOn_transfer hL hA) he
      (fun _ hx => transfer_integral_eq hL hA hx)

end General
end QuantumNLS.L1SpatialTransfer

#print axioms QuantumNLS.L1SpatialTransfer.ac_pow
#print axioms QuantumNLS.L1SpatialTransfer.integral_control_pow
#print axioms QuantumNLS.L1SpatialTransfer.ac_of_dist_le
#print axioms QuantumNLS.L1SpatialTransfer.ac_integral
#print axioms QuantumNLS.L1SpatialTransfer.continuousOn_dyson
#print axioms QuantumNLS.L1SpatialTransfer.integrable_dyson_product
#print axioms QuantumNLS.L1SpatialTransfer.norm_dyson_le_control
#print axioms QuantumNLS.L1SpatialTransfer.transfer
#print axioms QuantumNLS.L1SpatialTransfer.uniform_dyson_bound
#print axioms QuantumNLS.L1SpatialTransfer.continuousOn_transfer
#print axioms QuantumNLS.L1SpatialTransfer.transfer_integral_eq
#print axioms QuantumNLS.L1SpatialTransfer.dyson_eq_of_ae
#print axioms QuantumNLS.L1SpatialTransfer.transfer_eq_of_ae
#print axioms QuantumNLS.L1SpatialTransfer.ac_transfer
#print axioms QuantumNLS.L1SpatialTransfer.ae_hasDerivAt_transfer
#print axioms QuantumNLS.L1SpatialTransfer.eq_zero_of_integral
#print axioms QuantumNLS.L1SpatialTransfer.integral_solution_unique
#print axioms QuantumNLS.L1SpatialTransfer.fundamental_spec

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.L1SpatialTransfer." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
