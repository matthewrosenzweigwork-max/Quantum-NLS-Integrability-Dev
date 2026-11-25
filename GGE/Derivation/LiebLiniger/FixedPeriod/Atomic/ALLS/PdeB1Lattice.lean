import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB1Bracket

/-! # Track B, step B1: the uniform quadratic lattice sum

Pro report, equation (latticesum): for `p = 4a - 1 = 5/8 > 1/2`,
`sup_{A ∈ ℝ, θ ∈ {0, 1/2}} Σ_{k ∈ ℤ} ⟨A + 8π²(k - θ)²⟩^{-p} < ∞`.

We prove the general statement for every `c > 0`, every `p > 1/2`, uniformly in all real `A`
and all real shifts `θ` (`lattice_sum_bound`), and record Pro's instance
(`lattice_sum_bound_pro`). Summability is proved before any `tsum` is used.

Route (an elementary equivalent of Pro's root-counting argument; the conclusion is identical):
with `R = √(max(-A,0)/c)` one has the pointwise bound `c(|y| - R)² ≤ |A + c y²|`, so each term is
dominated by the two "resonant" one-dimensional sums `Σ_k ⟨c(k - a)²⟩^{-p}`, `a = θ ± R`; each of
these is bounded, uniformly in the real centre `a`, by `Σ_m ⟨c (max(|m|-1,0))²⟩^{-p}`, which is
summable because `2p > 1`.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

/-- The resonance radius `R = √(max(-A,0)/c)`. -/
def latticeRadius (c A : ℝ) : ℝ := Real.sqrt (max (-A) 0 / c)

/-- Key pointwise bound: `c (|y| - R)² ≤ |A + c y²|` with `R = latticeRadius c A`. -/
theorem sq_sub_radius_le {c : ℝ} (hc : 0 < c) (A y : ℝ) :
    c * (|y| - latticeRadius c A) ^ 2 ≤ |A + c * y ^ 2| := by
  unfold latticeRadius
  by_cases hA : 0 ≤ A
  · have hm : max (-A) 0 = 0 := max_eq_right (by linarith)
    rw [hm, zero_div, Real.sqrt_zero, sub_zero, sq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ A + c * y ^ 2)]
    linarith
  · replace hA : A < 0 := not_le.mp hA
    have hm : max (-A) 0 = -A := max_eq_left (by linarith)
    rw [hm]
    set R := Real.sqrt (-A / c) with hRdef
    have hR0 : 0 ≤ R := Real.sqrt_nonneg _
    have hR2 : R ^ 2 = -A / c := Real.sq_sqrt (div_nonneg (by linarith) hc.le)
    have hAeq : A = -(c * R ^ 2) := by
      rw [hR2]; field_simp
    have hy2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
    have hfac : A + c * y ^ 2 = c * ((|y| - R) * (|y| + R)) := by
      rw [hAeq, hy2]; ring
    rw [hfac, abs_mul, abs_of_pos hc, abs_mul, abs_of_nonneg (by positivity : 0 ≤ |y| + R)]
    have h1 : |(|y| - R)| ≤ |y| + R := by
      rw [abs_le]; constructor <;> linarith [abs_nonneg y]
    have h2 : (|y| - R) ^ 2 ≤ |(|y| - R)| * (|y| + R) := by
      rw [← sq_abs]
      have := mul_le_mul_of_nonneg_left h1 (abs_nonneg (|y| - R))
      nlinarith
    exact mul_le_mul_of_nonneg_left h2 hc.le

/-- Each lattice term is dominated by the two resonant terms centred at `θ ± R`. -/
theorem lattice_term_le {c p : ℝ} (hc : 0 < c) (hp : 0 ≤ p) (A θ : ℝ) (k : ℤ) :
    brk (A + c * ((k : ℝ) - θ) ^ 2) ^ (-p) ≤
      brk (c * ((k : ℝ) - (θ + latticeRadius c A)) ^ 2) ^ (-p) +
        brk (c * ((k : ℝ) - (θ - latticeRadius c A)) ^ 2) ^ (-p) := by
  set R := latticeRadius c A with hRdef
  set y : ℝ := (k : ℝ) - θ with hydef
  have hkey := sq_sub_radius_le hc A y
  have hle : brk (A + c * y ^ 2) ^ (-p) ≤ brk (c * (|y| - R) ^ 2) ^ (-p) := by
    apply brk_rpow_neg_le hp
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ c * (|y| - R) ^ 2)]
    exact hkey
  refine hle.trans ?_
  rcases le_or_gt 0 y with hy | hy
  · have : (|y| - R) ^ 2 = ((k : ℝ) - (θ + R)) ^ 2 := by
      rw [abs_of_nonneg hy, hydef]; ring
    rw [this]
    linarith [brk_rpow_nonneg (c * ((k : ℝ) - (θ - R)) ^ 2) (-p)]
  · have : (|y| - R) ^ 2 = ((k : ℝ) - (θ - R)) ^ 2 := by
      rw [abs_of_neg hy, hydef]; ring
    rw [this]
    linarith [brk_rpow_nonneg (c * ((k : ℝ) - (θ + R)) ^ 2) (-p)]

/-- The centre-independent majorant `G m = ⟨c (max(|m|-1,0))²⟩^{-p}`. -/
def latticeMajorant (c p : ℝ) (m : ℤ) : ℝ := brk (c * (max (|(m : ℝ)| - 1) 0) ^ 2) ^ (-p)

/-- A one-dimensional resonant term is dominated by the majorant at `k - ⌊a⌋`. -/
theorem resonant_term_le {c p : ℝ} (hc : 0 < c) (hp : 0 ≤ p) (a : ℝ) (k : ℤ) :
    brk (c * ((k : ℝ) - a) ^ 2) ^ (-p) ≤ latticeMajorant c p (k - ⌊a⌋) := by
  unfold latticeMajorant
  apply brk_rpow_neg_le hp
  set M := max (|((k - ⌊a⌋ : ℤ) : ℝ)| - 1) 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hfl1 : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a
  have hfl2 : a < (⌊a⌋ : ℝ) + 1 := Int.lt_floor_add_one a
  have hMle : M ≤ |(k : ℝ) - a| := by
    apply max_le _ (abs_nonneg _)
    have hcast : ((k - ⌊a⌋ : ℤ) : ℝ) = ((k : ℝ) - a) + (a - ⌊a⌋) := by push_cast; ring
    rw [hcast]
    have := abs_add_le ((k : ℝ) - a) (a - ⌊a⌋)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - ⌊a⌋)] at this
    linarith
  have hsq : M ^ 2 ≤ ((k : ℝ) - a) ^ 2 := by
    have := pow_le_pow_left₀ hM0 hMle 2
    rwa [sq_abs] at this
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ c * M ^ 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ c * ((k : ℝ) - a) ^ 2)]
  exact mul_le_mul_of_nonneg_left hsq hc.le

/-- For `|m| ≥ 2`, the majorant is at most `(c/4)^{-p} |m|^{-2p}`. -/
theorem latticeMajorant_le_pow {c p : ℝ} (hc : 0 < c) (hp : 0 ≤ p) (m : ℤ)
    (hm : 2 ≤ |(m : ℝ)|) :
    latticeMajorant c p m ≤ (c / 4) ^ (-p) * |(m : ℝ)| ^ (-(2 * p)) := by
  unfold latticeMajorant
  set x := |(m : ℝ)| with hx
  have hx0 : 0 < x := by linarith
  have hmax : max (x - 1) 0 = x - 1 := max_eq_left (by linarith)
  rw [hmax]
  have hlow : c / 4 * x ^ 2 ≤ brk (c * (x - 1) ^ 2) := by
    refine le_trans ?_ (abs_le_brk _)
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ c * (x - 1) ^ 2)]
    have : x ^ 2 / 4 ≤ (x - 1) ^ 2 := by nlinarith
    nlinarith
  have hpos : 0 < c / 4 * x ^ 2 := by positivity
  refine (brk_rpow_neg_le_of_le hpos hlow hp).trans (le_of_eq ?_)
  rw [Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
  congr 1
  push_cast
  ring

/-- The majorant is summable when `2p > 1`. -/
theorem summable_latticeMajorant {c p : ℝ} (hc : 0 < c) (hp : 1 / 2 < p) :
    Summable (latticeMajorant c p) := by
  have hp0 : 0 ≤ p := by linarith
  refine summable_of_isBigO (Real.summable_abs_int_rpow (b := 2 * p) (by linarith)) ?_
  refine Asymptotics.IsBigO.of_bound ((c / 4) ^ (-p)) ?_
  have hfin : {m : ℤ | ¬ (2 ≤ |(m : ℝ)|)}.Finite := by
    refine (Set.finite_Icc (-1 : ℤ) 1).subset ?_
    intro m hm
    simp only [Set.mem_ofPred_eq, not_le] at hm
    rw [abs_lt] at hm
    obtain ⟨h1, h2⟩ := hm
    have h1' : (-2 : ℤ) < m := by exact_mod_cast h1
    have h2' : m < (2 : ℤ) := by exact_mod_cast h2
    simp only [Set.mem_Icc]
    omega
  filter_upwards [Filter.eventually_cofinite.2 hfin] with m hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by unfold latticeMajorant; exact brk_rpow_nonneg _ _),
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact latticeMajorant_le_pow hc hp0 m hm

/-- One resonant sum: summable, and bounded by `Σ G` uniformly in the real centre `a`. -/
theorem resonant_sum_bound {c p : ℝ} (hc : 0 < c) (hp : 1 / 2 < p) (a : ℝ) :
    Summable (fun k : ℤ => brk (c * ((k : ℝ) - a) ^ 2) ^ (-p)) ∧
      ∑' k : ℤ, brk (c * ((k : ℝ) - a) ^ 2) ^ (-p) ≤ ∑' m : ℤ, latticeMajorant c p m := by
  have hp0 : 0 ≤ p := by linarith
  have hG := summable_latticeMajorant hc hp
  have hshift : Summable (fun k : ℤ => latticeMajorant c p (k - ⌊a⌋)) :=
    (Equiv.subRight ⌊a⌋).summable_iff.2 hG
  have hsum : Summable (fun k : ℤ => brk (c * ((k : ℝ) - a) ^ 2) ^ (-p)) :=
    Summable.of_nonneg_of_le (fun _ => brk_rpow_nonneg _ _) (resonant_term_le hc hp0 a) hshift
  refine ⟨hsum, ?_⟩
  calc ∑' k : ℤ, brk (c * ((k : ℝ) - a) ^ 2) ^ (-p)
      ≤ ∑' k : ℤ, latticeMajorant c p (k - ⌊a⌋) :=
        hsum.tsum_le_tsum (resonant_term_le hc hp0 a) hshift
    _ = ∑' m : ℤ, latticeMajorant c p m := (Equiv.subRight ⌊a⌋).tsum_eq (latticeMajorant c p)

/-- **Uniform quadratic lattice sum** (Pro, eq. (latticesum), general form): for `c > 0` and
`p > 1/2` there is one constant `C` such that for every real `A` and every real shift `θ` the
series `Σ_k ⟨A + c (k - θ)²⟩^{-p}` converges and its sum is at most `C`. -/
theorem lattice_sum_bound {c p : ℝ} (hc : 0 < c) (hp : 1 / 2 < p) :
    ∃ C : ℝ, ∀ A θ : ℝ,
      Summable (fun k : ℤ => brk (A + c * ((k : ℝ) - θ) ^ 2) ^ (-p)) ∧
        ∑' k : ℤ, brk (A + c * ((k : ℝ) - θ) ^ 2) ^ (-p) ≤ C := by
  have hp0 : 0 ≤ p := by linarith
  refine ⟨2 * ∑' m : ℤ, latticeMajorant c p m, fun A θ => ?_⟩
  obtain ⟨hs1, hb1⟩ := resonant_sum_bound hc hp (θ + latticeRadius c A)
  obtain ⟨hs2, hb2⟩ := resonant_sum_bound hc hp (θ - latticeRadius c A)
  have hsum12 := hs1.add hs2
  have hsum : Summable (fun k : ℤ => brk (A + c * ((k : ℝ) - θ) ^ 2) ^ (-p)) :=
    Summable.of_nonneg_of_le (fun _ => brk_rpow_nonneg _ _) (lattice_term_le hc hp0 A θ) hsum12
  refine ⟨hsum, ?_⟩
  calc ∑' k : ℤ, brk (A + c * ((k : ℝ) - θ) ^ 2) ^ (-p)
      ≤ ∑' k : ℤ, (brk (c * ((k : ℝ) - (θ + latticeRadius c A)) ^ 2) ^ (-p) +
          brk (c * ((k : ℝ) - (θ - latticeRadius c A)) ^ 2) ^ (-p)) :=
        hsum.tsum_le_tsum (lattice_term_le hc hp0 A θ) hsum12
    _ = ∑' k : ℤ, brk (c * ((k : ℝ) - (θ + latticeRadius c A)) ^ 2) ^ (-p) +
          ∑' k : ℤ, brk (c * ((k : ℝ) - (θ - latticeRadius c A)) ^ 2) ^ (-p) :=
        hs1.tsum_add hs2
    _ ≤ 2 * ∑' m : ℤ, latticeMajorant c p m := by linarith

/-- Pro's instance of (latticesum): `c = 8π²`, `p = 4a - 1` with `a = 13/32` (so `p = 5/8`),
uniformly in real `A` and in every real `θ` (in particular `θ ∈ {0, 1/2}`). -/
theorem lattice_sum_bound_pro :
    ∃ C : ℝ, ∀ A θ : ℝ,
      Summable (fun k : ℤ =>
        brk (A + 8 * Real.pi ^ 2 * ((k : ℝ) - θ) ^ 2) ^ (-(4 * (13 / 32 : ℝ) - 1))) ∧
        ∑' k : ℤ, brk (A + 8 * Real.pi ^ 2 * ((k : ℝ) - θ) ^ 2) ^ (-(4 * (13 / 32 : ℝ) - 1)) ≤ C :=
  lattice_sum_bound (by positivity) (by norm_num)

end LiebLiniger.FixedPeriod.ALLS.PdeB
