import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import QuantumNLS.Prop024ScalarSeriesR52

/-! Round 53 scalar majorant preparation for PROP-024.  This module proves
the factorial and cellwise bounds used by the full Wick double-series
reindexing.  It does not define an interaction operator or assert Weyl
translation compatibility. -/
noncomputable section
set_option autoImplicit false
namespace QuantumNLS.Prop024DoubleSeriesR53

open QuantumNLS.Prop024ScalarEstimateR51
open QuantumNLS.Prop024ScalarSeriesR52

/-- Stirling's lower bound in the form needed for the j-th Wick moment. -/
theorem factorial_ge_pow_div_exp (j : ℕ) (hj : 1 ≤ j) :
    ((j : ℝ) / Real.exp 1) ^ j ≤ (j.factorial : ℝ) := by
  have hjreal : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hroot : 1 ≤ Real.sqrt (2 * Real.pi * (j : ℝ)) := by
    apply Real.one_le_sqrt.mpr
    nlinarith [Real.pi_gt_three]
  have hpow : 0 ≤ ((j : ℝ) / Real.exp 1) ^ j := by positivity
  have hstirling := Stirling.le_factorial_stirling j
  calc
    ((j : ℝ) / Real.exp 1) ^ j = 1 * ((j : ℝ) / Real.exp 1) ^ j := by ring
    _ ≤ Real.sqrt (2 * Real.pi * (j : ℝ)) * ((j : ℝ) / Real.exp 1) ^ j :=
      mul_le_mul_of_nonneg_right hroot hpow
    _ ≤ (j.factorial : ℝ) := by exact_mod_cast hstirling

/-- The square-rooted factorial denominator absorbs the source moment
factor, leaving the geometric factor with the exact `32 e Q/N` scale. -/
theorem wick_moment_factorial_le (Q N : ℝ) (hQ : 0 ≤ Q) (hN : 0 < N)
    (j : ℕ) (hj : 1 ≤ j) :
    (Real.sqrt (32 * Q * j / N)) ^ j / Real.sqrt (j.factorial : ℝ) ≤
      (Real.sqrt (32 * Real.exp 1 * Q / N)) ^ j := by
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast hj
  have hfpos : 0 < (j.factorial : ℝ) := by positivity
  have hepos : 0 < Real.exp 1 := Real.exp_pos _
  have hfac := factorial_ge_pow_div_exp j hj
  have hdiv : ((j : ℝ) ^ j) / (j.factorial : ℝ) ≤ (Real.exp 1) ^ j := by
    have hfacdiv : ((j : ℝ) ^ j) / (Real.exp 1) ^ j ≤ (j.factorial : ℝ) := by
      simpa only [div_pow] using hfac
    have hcross := (div_le_iff₀ (pow_pos hepos j)).mp hfacdiv
    apply (div_le_iff₀ hfpos).2
    simpa [mul_comm] using hcross
  have hC : 0 ≤ 32 * Q / N := by positivity
  have hX : 0 ≤ 32 * Q * j / N := by positivity
  have hY : 0 ≤ 32 * Real.exp 1 * Q / N := by positivity
  have hpow : (32 * Q * j / N) ^ j / (j.factorial : ℝ) ≤
      (32 * Real.exp 1 * Q / N) ^ j := by
    have hsplit : 32 * Q * j / N = (32 * Q / N) * (j : ℝ) := by ring
    rw [hsplit, mul_pow]
    calc
      (32 * Q / N) ^ j * (j : ℝ) ^ j / (j.factorial : ℝ) =
          (32 * Q / N) ^ j * ((j : ℝ) ^ j / (j.factorial : ℝ)) := by ring
      _ ≤ (32 * Q / N) ^ j * (Real.exp 1) ^ j :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = (32 * Real.exp 1 * Q / N) ^ j := by
        rw [← mul_pow]
        congr 1
        field_simp
  have hsqrt :
      ((Real.sqrt (32 * Q * j / N)) ^ j / Real.sqrt (j.factorial : ℝ)) ^ 2 =
        (32 * Q * j / N) ^ j / (j.factorial : ℝ) := by
    rw [div_pow, ← pow_mul, show j * 2 = 2 * j by omega, pow_mul,
      Real.sq_sqrt hX, Real.sq_sqrt (le_of_lt hfpos)]
  have htarget :
      ((Real.sqrt (32 * Real.exp 1 * Q / N)) ^ j) ^ 2 =
        (32 * Real.exp 1 * Q / N) ^ j := by
    rw [← pow_mul, show j * 2 = 2 * j by omega, pow_mul,
      Real.sq_sqrt hY]
  have hleft : 0 ≤ (Real.sqrt (32 * Q * j / N) ^ j /
      Real.sqrt (j.factorial : ℝ)) := by positivity
  have hright : 0 ≤ Real.sqrt (32 * Real.exp 1 * Q / N) ^ j := by positivity
  have hsq :
      (Real.sqrt (32 * Q * j / N) ^ j / Real.sqrt (j.factorial : ℝ)) ^ 2 ≤
        ((Real.sqrt (32 * Real.exp 1 * Q / N)) ^ j) ^ 2 := by
    rw [hsqrt, htarget]
    exact hpow
  exact (sq_le_sq₀ hleft hright).mp hsq

/-- Source scalar cell before the `(m,j)` to `(j,l)` reindexing. -/
def wickCell (A Q N : ℝ) (m j : ℕ) : ℝ :=
  (A ^ m / Real.sqrt ((2*m).factorial : ℝ)) *
    (Nat.choose (2*m) j : ℝ) * (Real.sqrt (32 * Q * j / N)) ^ j

/-- The separated `(j,l)` majorant cell. -/
def reindexedCell (A Q N : ℝ) (j l : ℕ) : ℝ :=
  (wickRatio A Q N) ^ j * factorialRootTerm (Real.sqrt (2*A)) l

/-- Factorial splitting and the Stirling moment estimate bound each source
cell by its reindexed geometric/factorial cell. -/
theorem wickCell_le_reindexedCell (A Q N : ℝ) (hA : 0 < A)
    (hQ : 0 ≤ Q) (hN : 0 < N) (m j : ℕ) (hj : 3 ≤ j) (hjm : j ≤ 2*m) :
    wickCell A Q N m j ≤ reindexedCell A Q N j (2*m-j) := by
  let l : ℕ := 2*m-j
  have hj1 : 1 ≤ j := by omega
  have hsplit := choose_factorial_product_le (2*m) j (by omega)
  have hchoose : (Nat.choose (2*m) j : ℝ) /
      Real.sqrt ((2*m).factorial : ℝ) ≤
      (2 : ℝ)^m / Real.sqrt ((j.factorial : ℝ) * (l.factorial : ℝ)) := by
    have hnpos : 0 < ((2*m).factorial : ℝ) := by positivity
    have hjpos : 0 < (j.factorial : ℝ) := by positivity
    have hlpos : 0 < (l.factorial : ℝ) := by positivity
    have hprodpos : 0 < (j.factorial : ℝ) * (l.factorial : ℝ) := by positivity
    have hsq :
        ((Nat.choose (2*m) j : ℝ) / Real.sqrt ((2*m).factorial : ℝ)) ^ 2 ≤
        ((2 : ℝ)^m / Real.sqrt ((j.factorial : ℝ) * (l.factorial : ℝ))) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (le_of_lt hnpos), div_pow,
        Real.sq_sqrt (le_of_lt hprodpos)]
      apply (div_le_div_iff₀ hnpos hprodpos).2
      have hpow : ((2 : ℝ)^m) ^ 2 = (2 : ℝ) ^ (2*m) := by
        rw [← pow_mul]
        congr 1
        omega
      calc
        (Nat.choose (2*m) j : ℝ) ^ 2 *
            ((j.factorial : ℝ) * (l.factorial : ℝ)) =
          (Nat.choose (2*m) j : ℝ) ^ 2 * (j.factorial : ℝ) *
            (l.factorial : ℝ) := by ring
        _ ≤ (2 : ℝ) ^ (2*m) * ((2*m).factorial : ℝ) := by
          simpa [l] using hsplit
        _ = ((2 : ℝ)^m)^2 * ((2*m).factorial : ℝ) := by rw [hpow]
    have hx : 0 ≤ (Nat.choose (2*m) j : ℝ) / Real.sqrt ((2*m).factorial : ℝ) := by
      positivity
    have hy : 0 ≤ (2 : ℝ)^m / Real.sqrt ((j.factorial : ℝ) * (l.factorial : ℝ)) := by
      positivity
    nlinarith
  have hmoment := wick_moment_factorial_le Q N hQ hN j hj1
  have hjpos : 0 < (j.factorial : ℝ) := by positivity
  have hlpos : 0 < (l.factorial : ℝ) := by positivity
  have hB : 0 ≤ Real.sqrt (2*A) := by positivity
  have hSqrtFactor :
      Real.sqrt ((j.factorial : ℝ) * (l.factorial : ℝ)) =
        Real.sqrt (j.factorial : ℝ) * Real.sqrt (l.factorial : ℝ) := by
    rw [Real.sqrt_mul (by positivity)]
  let B : ℝ := Real.sqrt (2*A)
  have hcoeff :
      A ^ m * ((Nat.choose (2*m) j : ℝ) /
        Real.sqrt ((2*m).factorial : ℝ)) ≤
      (B ^ j / Real.sqrt (j.factorial : ℝ)) *
        (B ^ l / Real.sqrt (l.factorial : ℝ)) := by
    have hnonneg : 0 ≤ A ^ m := by positivity
    have hchoose' := mul_le_mul_of_nonneg_left hchoose hnonneg
    rw [hSqrtFactor] at hchoose'
    have hsum : j+l = 2*m := by dsimp [l]; omega
    have hBpow : B ^ j * B ^ l = (2*A)^m := by
      calc
        B ^ j * B ^ l = B ^ (j+l) := by rw [← pow_add]
        _ = B ^ (2*m) := by rw [hsum]
        _ = (B^2)^m := by rw [pow_mul]
        _ = (2*A)^m := by dsimp [B]; rw [Real.sq_sqrt (by positivity)]
    have hApow : A ^ m * (2 : ℝ)^m = (2*A)^m := by
      calc
        A ^ m * (2 : ℝ)^m = (A*2)^m := by rw [← mul_pow]
        _ = (2*A)^m := by rw [mul_comm]
    calc
      A ^ m * ((Nat.choose (2*m) j : ℝ) / Real.sqrt ((2*m).factorial : ℝ)) ≤
          A ^ m * ((2 : ℝ)^m /
            (Real.sqrt (j.factorial : ℝ) * Real.sqrt (l.factorial : ℝ))) := hchoose'
      _ = (B ^ j / Real.sqrt (j.factorial : ℝ)) *
          (B ^ l / Real.sqrt (l.factorial : ℝ)) := by
        have hjroot : Real.sqrt (j.factorial : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hjpos)
        have hlroot : Real.sqrt (l.factorial : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hlpos)
        field_simp [hjroot, hlroot]
        exact hApow.trans hBpow.symm
  have hratio :
      (Real.sqrt (32 * Q * j / N)) ^ j / Real.sqrt (j.factorial : ℝ) ≤
        (Real.sqrt (32 * Real.exp 1 * Q / N)) ^ j := hmoment
  have hbase : 0 ≤ (B ^ l / Real.sqrt (l.factorial : ℝ)) := by positivity
  have hgeom : (B * Real.sqrt (32 * Real.exp 1 * Q / N)) ^ j =
      (wickRatio A Q N) ^ j := by
    rw [show wickRatio A Q N = B * Real.sqrt (32 * Real.exp 1 * Q / N) by
      dsimp [B, wickRatio]]
  change (A ^ m / Real.sqrt ((2*m).factorial : ℝ)) *
      (Nat.choose (2*m) j : ℝ) * (Real.sqrt (32 * Q * j / N)) ^ j ≤
    (wickRatio A Q N) ^ j *
      (Real.sqrt (2*A) ^ (2*m-j) / Real.sqrt ((2*m-j).factorial : ℝ))
  calc
    (A ^ m / Real.sqrt ((2*m).factorial : ℝ)) *
        (Nat.choose (2*m) j : ℝ) * (Real.sqrt (32 * Q * j / N)) ^ j =
        (A ^ m * ((Nat.choose (2*m) j : ℝ) /
          Real.sqrt ((2*m).factorial : ℝ))) *
          (Real.sqrt (32 * Q * j / N)) ^ j := by ring
    _ ≤ ((B ^ j / Real.sqrt (j.factorial : ℝ)) *
          (B ^ l / Real.sqrt (l.factorial : ℝ))) *
          (Real.sqrt (32 * Q * j / N)) ^ j :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = (B ^ l / Real.sqrt (l.factorial : ℝ)) *
          (B ^ j * ((Real.sqrt (32 * Q * j / N)) ^ j /
            Real.sqrt (j.factorial : ℝ))) := by
        have hjroot : Real.sqrt (j.factorial : ℝ) ≠ 0 :=
          ne_of_gt (Real.sqrt_pos.2 hjpos)
        have hlroot : Real.sqrt (l.factorial : ℝ) ≠ 0 :=
          ne_of_gt (Real.sqrt_pos.2 hlpos)
        field_simp [hjroot, hlroot]
    _ ≤ (B ^ l / Real.sqrt (l.factorial : ℝ)) *
          (wickRatio A Q N) ^ j := by
        calc
          _ = (B ^ l / Real.sqrt (l.factorial : ℝ)) *
              (B ^ j * ((Real.sqrt (32 * Q * j / N)) ^ j /
                Real.sqrt (j.factorial : ℝ))) := rfl
          _ ≤ (B ^ l / Real.sqrt (l.factorial : ℝ)) *
              (B ^ j * (Real.sqrt (32 * Real.exp 1 * Q / N)) ^ j) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hratio (by positivity)) hbase
          _ = (B ^ l / Real.sqrt (l.factorial : ℝ)) *
              (wickRatio A Q N) ^ j := by
            rw [← mul_pow, ← hgeom]
    _ = reindexedCell A Q N j (2*m-j) := by
        change (B ^ l / Real.sqrt (l.factorial : ℝ)) * (wickRatio A Q N) ^ j =
          (wickRatio A Q N) ^ j *
            (Real.sqrt (2*A) ^ (2*m-j) /
              Real.sqrt ((2*m-j).factorial : ℝ))
        dsimp [B, l]
        ring

/-- The admissible source cells: `j ≥ 3` and `j ≤ 2m`. -/
abbrev WickSourceIndex := {p : ℕ × ℕ // 3 ≤ p.2 ∧ p.2 ≤ 2*p.1}

/-- The first reindexed coordinate retains the source lower cutoff `j ≥ 3`. -/
abbrev WickTailIndex := {j : ℕ // 3 ≤ j}

/-- A source pair `(m,j)` is sent to `(j,l)` with `l=2m-j`. -/
def wickSourceMap (p : WickSourceIndex) : WickTailIndex × ℕ :=
  (⟨p.val.2, p.property.1⟩, 2*p.val.1-p.val.2)

theorem wickSourceMap_injective : Function.Injective wickSourceMap := by
  intro x y h
  have hj : x.val.2 = y.val.2 := congrArg (fun z : WickTailIndex × ℕ => z.1.1) h
  have hl : 2*x.val.1-x.val.2 = 2*y.val.1-y.val.2 := congrArg Prod.snd h
  apply Subtype.ext
  apply Prod.ext <;> omega

/-- The factorial/geometric summand after the change of indices. -/
def wickTargetCell (r B : ℝ) (p : WickTailIndex × ℕ) : ℝ :=
  r ^ p.1.1 * factorialRootTerm B p.2

/-- The full admissible Wick double series, indexed by its literal `(m,j)` cells. -/
def wickDoubleSeries (A Q N : ℝ) : ℝ :=
  ∑' p : WickSourceIndex, wickCell A Q N p.val.1 p.val.2

def wickTailEquiv : ℕ ≃ WickTailIndex where
  toFun n := ⟨n+3, by omega⟩
  invFun j := j.1-3
  left_inv n := by simp
  right_inv j := by
    apply Subtype.ext
    exact Nat.sub_add_cancel j.property

/-- Reindexing the complete admissible `(m,j)` series gives the product of
the source-scale geometric tail and the square-root factorial series. -/
theorem wickDoubleSeries_le_reindexed_product (A Q N : ℝ) (hA : 0 < A)
    (hQ : 1 ≤ Q) (hN : 256 * Real.exp 1 * A * Q ≤ N) :
    wickDoubleSeries A Q N ≤
      factorialRootSeries (Real.sqrt (2*A)) *
        (∑' j : ℕ, (wickRatio A Q N) ^ (j+3)) := by
  let B : ℝ := Real.sqrt (2*A)
  let r : ℝ := wickRatio A Q N
  have hQ0 : 0 ≤ Q := by linarith
  have hr0 : 0 ≤ r := by dsimp [r, wickRatio]; positivity
  have hrhalf : r ≤ 1/2 := by
    dsimp [r]
    exact wickRatio_le_half A Q N hA hQ hN
  have hr1 : r < 1 := by linarith
  have hNpos : 0 < N := by
    have hlow : 0 < 256 * Real.exp 1 * A * Q := by positivity
    exact lt_of_lt_of_le hlow hN
  have hGeom : Summable (fun j : ℕ => r^j) :=
    summable_geometric_of_lt_one hr0 hr1
  have hTailGeom : Summable (fun j : WickTailIndex => r^j.1) :=
    hGeom.comp_injective (fun _ _ h => Subtype.ext h)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hFactorial : Summable (factorialRootTerm B) :=
    factorialRootTerm_summable hB
  have hTargetNonneg (p : WickTailIndex × ℕ) : 0 ≤ wickTargetCell r B p := by
    dsimp [wickTargetCell]
    exact mul_nonneg (pow_nonneg hr0 _) (factorialRootTerm_nonneg hB _)
  have hTarget : Summable (wickTargetCell r B) := by
    rw [summable_prod_of_nonneg hTargetNonneg]
    constructor
    · intro j
      exact (hFactorial.mul_left (r^j.1)).congr (by intro l; rfl)
    · have houter : Summable (fun j : WickTailIndex =>
          r^j.1 * factorialRootSeries B) := hTailGeom.mul_right _
      have hinner (j : WickTailIndex) :
          (∑' l : ℕ, wickTargetCell r B (j,l)) =
            r^j.1 * factorialRootSeries B := by
        calc
          (∑' l : ℕ, wickTargetCell r B (j,l)) =
              ∑' l : ℕ, r^j.1 * factorialRootTerm B l := by
            exact tsum_congr (fun l => rfl)
          _ = r^j.1 * ∑' l : ℕ, factorialRootTerm B l := tsum_mul_left
          _ = r^j.1 * factorialRootSeries B := rfl
      exact houter.congr (by intro j; exact (hinner j).symm)
  have hTargetComp : Summable (fun p : WickSourceIndex =>
      wickTargetCell r B (wickSourceMap p)) :=
    hTarget.comp_injective wickSourceMap_injective
  have hSourceNonneg (p : WickSourceIndex) :
      0 ≤ wickCell A Q N p.val.1 p.val.2 := by
    dsimp [wickCell]
    positivity
  have hSourceLeComp (p : WickSourceIndex) :
      wickCell A Q N p.val.1 p.val.2 ≤ wickTargetCell r B (wickSourceMap p) := by
    have h := wickCell_le_reindexedCell A Q N hA hQ0
      hNpos p.val.1 p.val.2 p.property.1 p.property.2
    simpa [wickTargetCell, wickSourceMap, reindexedCell, factorialRootTerm, B, r]
      using h
  have hSource : Summable (fun p : WickSourceIndex =>
      wickCell A Q N p.val.1 p.val.2) :=
    Summable.of_nonneg_of_le hSourceNonneg hSourceLeComp hTargetComp
  have hTailEq : (∑' j : WickTailIndex, r^j.1) =
      ∑' j : ℕ, r^(j+3) := by
    rw [← wickTailEquiv.tsum_eq (fun j : WickTailIndex => r^j.1)]
    apply tsum_congr
    intro j
    simp [wickTailEquiv]
  have hProduct := hTailGeom.tsum_mul_tsum hFactorial hTarget
  calc
    wickDoubleSeries A Q N ≤
        ∑' p : WickSourceIndex, wickTargetCell r B (wickSourceMap p) :=
      Summable.tsum_le_tsum hSourceLeComp hSource hTargetComp
    _ ≤ ∑' p : WickTailIndex × ℕ, wickTargetCell r B p :=
      tsum_comp_le_tsum_of_inj hTarget hTargetNonneg wickSourceMap_injective
    _ = (∑' j : WickTailIndex, r^j.1) *
          (∑' l : ℕ, factorialRootTerm B l) := hProduct.symm
    _ = factorialRootSeries (Real.sqrt (2*A)) *
          (∑' j : ℕ, r^(j+3)) := by
      rw [hTailEq]
      simp only [factorialRootSeries, B]
      ring

/-- The full scalar double-series estimate in PROP-024, including the
`(m,j)` to `(j,l=2m-j)` reindexing and the source cutoff scale. -/
theorem wickDoubleSeries_source_bound (A Q N M : ℝ) (hA : 0 < A)
    (hQ : 1 ≤ Q) (hN : 256 * Real.exp 1 * A * Q ≤ N) (hM : 0 ≤ M) :
    M * N * wickDoubleSeries A Q N ≤
      2 * factorialRootSeries (Real.sqrt (2*A)) * (Real.sqrt (2*A))^3 *
        (Real.sqrt (32 * Real.exp 1))^3 * M * (Real.sqrt Q)^3 / Real.sqrt N := by
  have hseries := wickDoubleSeries_le_reindexed_product A Q N hA hQ hN
  have hMN : 0 ≤ M*N := mul_nonneg hM (le_of_lt (by
    have hlow : 0 < 256 * Real.exp 1 * A * Q := by positivity
    exact lt_of_lt_of_le hlow hN))
  calc
    M * N * wickDoubleSeries A Q N ≤
        M * N * (factorialRootSeries (Real.sqrt (2*A)) *
          (∑' j : ℕ, (wickRatio A Q N)^(j+3))) :=
      mul_le_mul_of_nonneg_left hseries hMN
    _ = M * N * factorialRootSeries (Real.sqrt (2*A)) *
          (∑' j : ℕ, (wickRatio A Q N)^(j+3)) := by ring
    _ ≤ 2 * factorialRootSeries (Real.sqrt (2*A)) * (Real.sqrt (2*A))^3 *
        (Real.sqrt (32 * Real.exp 1))^3 * M * (Real.sqrt Q)^3 / Real.sqrt N :=
      source_scale_geometric_tail A Q N M hA hQ hN hM

end QuantumNLS.Prop024DoubleSeriesR53

#print axioms QuantumNLS.Prop024DoubleSeriesR53.factorial_ge_pow_div_exp
#print axioms QuantumNLS.Prop024DoubleSeriesR53.wick_moment_factorial_le
#print axioms QuantumNLS.Prop024DoubleSeriesR53.wickCell_le_reindexedCell
#print axioms QuantumNLS.Prop024DoubleSeriesR53.wickDoubleSeries_le_reindexed_product
#print axioms QuantumNLS.Prop024DoubleSeriesR53.wickDoubleSeries_source_bound

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024DoubleSeriesR53." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024DoubleSeriesR53." then
      pending := pending.push n
  let roots := pending.size
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
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"PROP-024 R53 scalar audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."
