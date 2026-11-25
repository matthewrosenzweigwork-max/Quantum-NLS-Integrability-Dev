import QuantumNLS.Prop024AssemblyR58
import QuantumNLS.Prop024WOrder

/-! PROP-024 operator-level Wick expansion, module 5 (Prop024WNorms): norm bounds for the Wick cells.

`norm_wickFock_le`: `‖𝒲_{a,b}(C) y‖ ≤ ‖C‖ ‖(N+a+b)^{(a+b)/2} y‖` (the printed `Q7B:eq:wickbound`, summed over sectors), and `norm_cellVec_le_contractedCell`: under the printed polynomial moment bounds `‖(N+j)^{j/2} y‖ ≤ (32 Q j)^{j/2}` every Wick cell vector satisfies `‖cellVec N m a b‖ ≤ N · contractedCell m a b` for the frozen R54 `contractedCell`. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate Topology
open Filter
namespace QuantumNLS.Prop024WNorms
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors Ext006PhysFockCoord
open Prop024WWeylPhysical Prop022TensorCompressionR115 Ext006NumberPhase
open Prop024WBlock Prop024WSector Prop024WWords Prop024WOrder
open Prop024ContractionsR54 Prop024PhysicalHamiltonianR54 Prop024WickCellsR54
variable {L : ℝ} [Fact (0 < L)]

/-- The two displayed estimates of `Q7B:eq:mgf`, polynomial form: `E(N+j)^j ≤ (32 Q j)^j`. -/
def PolyMoments (Q : ℝ) (x : Fock L) : Prop :=
  ∀ j : ℕ, 1 ≤ j → ∃ hx : x ∈ (polynomialRoot (L := L) j).domain,
    ‖polynomialRoot j ⟨x, hx⟩‖ ≤ Real.rpow (32 * Q * j) ((j : ℝ) / 2)

lemma mem_polyRoot_of_momentFinite (j : ℕ) {x : Fock L} (hx : MomentFinite x) :
    x ∈ (polynomialRoot (L := L) j).domain := by
  change Memℓp (fun n => polynomialRootFamily j n (x n)) 2
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have hs := (hx j).mul_left (((j : ℝ) + 1) ^ j)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  rw [Prop023SpectralMoments.root_sector_norm_sq]
  have h1 : ((n : ℝ) + j) ^ j ≤ ((j : ℝ) + 1) ^ j * ((n : ℝ) + 1) ^ j := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) j,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (Nat.cast_nonneg (α := ℝ) j)]
  calc ((n : ℝ) + j) ^ j * ‖x n‖ ^ 2 ≤ (((j : ℝ) + 1) ^ j * ((n : ℝ) + 1) ^ j) * ‖x n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = ((j : ℝ) + 1) ^ j * (((n : ℝ) + 1) ^ j * ‖x n‖ ^ 2) := by ring

/-- The squared norm of the polynomial root is the number-moment series. -/
lemma hasSum_polyRoot (j : ℕ) (x : (polynomialRoot (L := L) j).domain) :
    HasSum (fun n : ℕ => ((n : ℝ) + j) ^ j * ‖x.1 n‖ ^ 2) (‖polynomialRoot j x‖ ^ 2) := by
  have hs := lp.hasSum_norm (E := fun n => HN L n) (p := 2) (by norm_num) (polynomialRoot j x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
  have hf : (fun n => ‖(polynomialRoot j x : Fock L) n‖ ^ 2) = (fun n : ℕ => ((n : ℝ) + j) ^ j * ‖x.1 n‖ ^ 2) := by
    funext n
    rw [Prop023SpectralMoments.root_apply, Prop023SpectralMoments.root_sector_norm_sq]
  rw [hf] at hs
  exact hs


/-- **The Wick bound** `Q7B:eq:wickbound`, in the form `‖𝒲_{a,b}(C) y‖ ≤ ‖C‖ ‖(N+a+b)^{(a+b)/2} y‖`. -/
lemma norm_wickFock_le (a b : ℕ) (C : HN L b →L[ℂ] HN L a) {y : Fock L} (hy : MomentFinite y)
    (hyj : y ∈ (polynomialRoot (L := L) (a+b)).domain) :
    ‖wickFock a b C y‖ ≤ ‖C‖ * ‖polynomialRoot (a+b) ⟨y, hyj⟩‖ := by
  set V := wickFock a b C y with hV
  set j := a + b with hj
  have hsum := hasSum_polyRoot j ⟨y, hyj⟩
  have hg : HasSum (fun n : ℕ => ‖C‖ ^ 2 * (((n : ℝ) + j) ^ j * ‖y n‖ ^ 2)) (‖C‖ ^ 2 * ‖polynomialRoot j ⟨y, hyj⟩‖ ^ 2) :=
    hsum.mul_left (‖C‖ ^ 2)
  have hVsq : HasSum (fun n => ‖(V : Fock L) n‖ ^ 2) (‖V‖ ^ 2) := by
    have hs := lp.hasSum_norm (E := fun n => HN L n) (p := 2) (by norm_num) V
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs
  have hzero : ∀ n ∈ Finset.range a, ‖(V : Fock L) n‖ ^ 2 = 0 := by
    intro n hn
    rw [wickFock_sector_lt a b C hy n (Finset.mem_range.mp hn), norm_zero]; ring
  have hshift := Summable.sum_add_tsum_nat_add a hVsq.summable
  rw [Finset.sum_eq_zero hzero, zero_add, hVsq.tsum_eq] at hshift
  have hle : ∀ k, ‖(V : Fock L) (k + a)‖ ^ 2 ≤ ‖C‖ ^ 2 * ((((b + k : ℕ) : ℝ) + j) ^ j * ‖y (b + k)‖ ^ 2) := by
    intro k
    rw [Nat.add_comm k a, wickFock_sector a b C hy k]
    have h1 := norm_wickBlock_apply_le a b k C (y (b + k))
    have h2 := wickCoeff_sq_le a b k
    have h3 : (((b + k + a : ℕ) : ℝ)) ^ (a + b) ≤ (((b + k : ℕ) : ℝ) + j) ^ j := by
      apply pow_le_pow_left₀ (by positivity)
      push_cast; rw [hj]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) b]
    calc ‖wickBlock a b k C (y (b + k))‖ ^ 2 ≤ (wickCoeff a b k * ‖C‖ * ‖y (b + k)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = ‖C‖ ^ 2 * (wickCoeff a b k ^ 2 * ‖y (b + k)‖ ^ 2) := by ring
      _ ≤ ‖C‖ ^ 2 * ((((b + k : ℕ) : ℝ) + j) ^ j * ‖y (b + k)‖ ^ 2) := by
          gcongr
          exact h2.trans h3
  have hsub : Summable (fun k : ℕ => ‖C‖ ^ 2 * ((((b + k : ℕ) : ℝ) + j) ^ j * ‖y (b + k)‖ ^ 2)) :=
    hg.summable.comp_injective (show Function.Injective (fun k : ℕ => b + k) from fun x y h => by simpa using h)
  have h4 : ∑' k : ℕ, ‖(V : Fock L) (k + a)‖ ^ 2 ≤ ∑' k : ℕ, ‖C‖ ^ 2 * ((((b + k : ℕ) : ℝ) + j) ^ j * ‖y (b + k)‖ ^ 2) :=
    Summable.tsum_le_tsum hle ((summable_nat_add_iff a).mpr hVsq.summable) hsub
  have h5 : ∑' k : ℕ, ‖C‖ ^ 2 * ((((b + k : ℕ) : ℝ) + j) ^ j * ‖y (b + k)‖ ^ 2) ≤
      ∑' n : ℕ, ‖C‖ ^ 2 * (((n : ℝ) + j) ^ j * ‖y n‖ ^ 2) :=
    tsum_comp_le_tsum_of_inj hg.summable (fun n => by positivity)
      (show Function.Injective (fun k : ℕ => b + k) from fun x y h => by simpa using h)
  rw [hg.tsum_eq] at h5
  have hfin : ‖V‖ ^ 2 ≤ (‖C‖ * ‖polynomialRoot j ⟨y, hyj⟩‖) ^ 2 := by
    rw [mul_pow]; linarith
  exact le_of_sq_le_sq hfin (by positivity) |> fun h => by simpa using h


lemma cellCoeff_nonneg (N m a b : ℕ) : 0 ≤ cellCoeff N m a b := by
  unfold cellCoeff; positivity

lemma norm_cellVec_le (N m a b : ℕ) (hab : a ≤ m ∧ b ≤ m) (Bm : HN L m →L[ℂ] HN L m) (u : L2T L)
    (x : physSmooth L) (hxj : x.1 ∈ (polynomialRoot (L := L) (a+b)).domain) :
    ‖cellVec N m a b Bm u x.1‖ ≤
      cellCoeff N m a b * ‖ck m a b hab.1 hab.2 Bm u‖ * ‖polynomialRoot (a+b) ⟨x.1, hxj⟩‖ := by
  unfold cellVec
  rw [dif_pos hab, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cellCoeff_nonneg N m a b),
    mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_wickFock_le a b _ (momentFinite_of_mem x) hxj)
    (cellCoeff_nonneg N m a b)

/-- **The cell norm is the R54 contraction cell.**  Under the printed number-moment bounds,
`‖cellVec‖ ≤ N · contractedCell`, with the frozen R54 `contractedCell`. -/
lemma norm_cellVec_le_contractedCell (N m a b : ℕ) (hN : 0 < N) (hab : a ≤ m ∧ b ≤ m)
    (B : ∀ r, HN L r →L[ℂ] HN L r) (u : L2T L) (x : physSmooth L) (Q : ℝ) (hQ : 1 ≤ Q)
    (hMom : PolyMoments Q x.1) (hj : 1 ≤ a + b) :
    ‖cellVec N m a b (B m) u x.1‖ ≤ (N : ℝ) * contractedCell m a b hab.1 hab.2 B u Q N := by
  obtain ⟨hxj, hnu⟩ := hMom (a+b) hj
  have h1 := norm_cellVec_le N m a b hab (B m) u x hxj
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hQ0 : 0 ≤ Q := by linarith
  set j := a + b with hjdef
  have hx0 : 0 ≤ 32 * Q * (j : ℝ) := by positivity
  have hrp : Real.rpow (32 * Q * (j : ℝ)) ((j : ℝ) / 2) = (Real.sqrt (32 * Q * (j : ℝ))) ^ j := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    congr 1; ring
  have hdiv : (Real.sqrt (32 * Q * ((a : ℝ) + b) / N)) ^ (a + b) =
      (Real.sqrt (32 * Q * (j : ℝ))) ^ j / (Real.sqrt (N : ℝ)) ^ j := by
    rw [show ((a : ℝ) + b) = (j : ℝ) by rw [hjdef]; push_cast; ring, Real.sqrt_div hx0, div_pow]
  have hnu' : ‖polynomialRoot j ⟨x.1, hxj⟩‖ ≤ (Real.sqrt (32 * Q * (j : ℝ))) ^ j := by
    rw [← hrp]; exact hnu
  have hck := norm_nonneg (ck m a b hab.1 hab.2 (B m) u)
  have hcc := cellCoeff_nonneg N m a b
  refine h1.trans ?_
  unfold contractedCell
  rw [hdiv]
  unfold cellCoeff
  have hC1 : (0 : ℝ) ≤ (m.choose a : ℝ) := Nat.cast_nonneg _
  have hC2 : (0 : ℝ) ≤ (m.choose b : ℝ) := Nat.cast_nonneg _
  calc (N : ℝ) / Real.sqrt (N : ℝ) ^ (a + b) * (m.choose a : ℝ) * (m.choose b : ℝ) *
        ‖ck m a b hab.1 hab.2 (B m) u‖ * ‖polynomialRoot (a + b) ⟨x.1, hxj⟩‖
      ≤ (N : ℝ) / Real.sqrt (N : ℝ) ^ (a + b) * (m.choose a : ℝ) * (m.choose b : ℝ) *
        ‖ck m a b hab.1 hab.2 (B m) u‖ * (Real.sqrt (32 * Q * (j : ℝ))) ^ j := by
          apply mul_le_mul_of_nonneg_left hnu'
          positivity
    _ = (N : ℝ) * (‖contractedKernel m a b hab.1 hab.2 B u‖ * (m.choose a : ℝ) * (m.choose b : ℝ) *
        ((Real.sqrt (32 * Q * (j : ℝ))) ^ j / Real.sqrt (N : ℝ) ^ j)) := by
          rw [contractedKernel_eq_ck, hjdef]; ring

end QuantumNLS.Prop024WNorms

#print axioms QuantumNLS.Prop024WNorms.norm_wickFock_le
#print axioms QuantumNLS.Prop024WNorms.norm_cellVec_le
#print axioms QuantumNLS.Prop024WNorms.norm_cellVec_le_contractedCell
#print axioms QuantumNLS.Prop024WNorms.hasSum_polyRoot
#print axioms QuantumNLS.Prop024WNorms.mem_polyRoot_of_momentFinite

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WNorms." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WNorms." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"Prop024WNorms aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."
