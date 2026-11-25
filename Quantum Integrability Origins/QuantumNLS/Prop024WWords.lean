import QuantumNLS.Prop024WMonomial
import QuantumNLS.Prop024ContractionsR54
import QuantumNLS.Prop022ACoherent
import QuantumNLS.Prop022AWeyl
import QuantumNLS.Prop024WBlock
import QuantumNLS.Prop024WSector

/-! PROP-024 operator-level Wick expansion, module 3 (Prop024WWords): normal-ordered words are Wick operators of rank-one power kernels.

`wickFock a b C y = ∑'_k inclusion (a+k) (wickBlock a b k C (y (b+k)))` is the Fock-space Wick operator `𝒲_{a,b}(C)` (sector `b+k ↦ a+k`).  Main results: `wickBlock_rk`: on the sector `b+k`, `a*(g)^a a(f)^b` is the Wick block of `|g^a⟩⟨f^b|` (proved by testing against power vectors with `clm_ext_powers`, from `powers_total`, `annSec_power`, `inner_creB`); `wickFock_rk`: on the whole smooth domain, `wickFock a b |g^a⟩⟨f^b| y = (a*(g)^a a(f)^b) y` (sector locality of the iterates). -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.Prop024WWords
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors Ext006PhysFockCoord
open Prop024WWeylPhysical Prop022ACoherent Prop022TensorCompressionR115
open Prop024WBlock Prop024WSector
variable {L : ℝ} [Fact (0 < L)]

/-- Two bounded operators between symmetric sectors that agree in all power-vector matrix elements
coincide. -/
lemma clm_ext_powers {n m : ℕ} (S T : HN L n →L[ℂ] HN L m)
    (h : ∀ g h' : L2T L, ⟪power m g, S (power n h')⟫_ℂ = ⟪power m g, T (power n h')⟫_ℂ) : S = T := by
  have hP : (Submodule.span ℂ (Set.range (fun h' : L2T L => (power n h' : HN L n)))).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_orthogonal'] at hx
    apply powers_total n x
    intro g
    exact inner_eq_zero_symm.mp (hx _ (Submodule.subset_span ⟨g, rfl⟩))
  have hker : ∀ h' : L2T L, S (power n h') = T (power n h') := by
    intro h'
    apply sub_eq_zero.mp
    apply powers_total m
    intro g
    rw [inner_sub_right, h g h', sub_self]
  have hle : Submodule.span ℂ (Set.range (fun h' : L2T L => (power n h' : HN L n))) ≤ LinearMap.ker ((S - T : HN L n →L[ℂ] HN L m) : HN L n →ₗ[ℂ] HN L m) := by
    rw [Submodule.span_le]
    rintro _ ⟨h', rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    change (S - T) (power n h') = 0
    rw [ContinuousLinearMap.sub_apply, hker h', sub_self]
  have hcl := Submodule.topologicalClosure_minimal _ hle (ContinuousLinearMap.isClosed_ker (S - T : HN L n →L[ℂ] HN L m))
  rw [hP] at hcl
  ext y
  have : y ∈ LinearMap.ker ((S - T : HN L n →L[ℂ] HN L m) : HN L n →ₗ[ℂ] HN L m) := hcl Submodule.mem_top
  simpa [sub_eq_zero] using this


/-- The rank-one power kernel `|g^a⟩⟨f^b|`. -/
def rk (a b : ℕ) (g f : L2T L) : HN L b →L[ℂ] HN L a :=
  (innerSL ℂ (power b f)).smulRight (power a g)

lemma rk_apply (a b : ℕ) (g f : L2T L) (x : HN L b) : rk a b g f x = ⟪power b f, x⟫_ℂ • power a g := rfl

lemma inner_power (n : ℕ) (g h : L2T L) : ⟪power n g, power n h⟫_ℂ = ⟪g, h⟫_ℂ ^ n := by
  change ⟪(htpow n g : TP L n), (htpow n h : TP L n)⟫_ℂ = _
  exact IntrinsicContact.inner_htpow n g h

lemma wickCoeff_eq_prod (a b k : ℕ) :
    wickCoeff a b k = Real.sqrt (((a+k).factorial : ℝ) / (k.factorial : ℝ)) *
      Real.sqrt (((b+k).factorial : ℝ) / (k.factorial : ℝ)) := by
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  rw [← Real.sqrt_mul (by positivity)]
  unfold wickCoeff
  rw [mul_comm (((a+k).factorial : ℝ) / _), div_mul_div_comm, ← sq, Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq hk.le]

/-- **Words are Wick operators of power kernels (sector form).**  On the sector `b+k`,
`a*(g)^a a(f)^b` is the Wick block of the rank-one power kernel `|g^a⟩⟨f^b|`. -/
theorem wickBlock_rk (a b k : ℕ) (g f : L2T L) :
    wickBlock a b k (rk a b g f) = (creB g a k).comp (annB f b k) := by
  apply clm_ext_powers
  intro h' h
  rw [symbol_wickBlock, ContinuousLinearMap.comp_apply, inner_creB, annB_power, annB_power,
    inner_smul_left, inner_smul_right, inner_power, rk_apply, inner_smul_right, inner_power,
    wickCoeff_eq_prod]
  simp only [map_mul, map_pow, Complex.conj_ofReal, Complex.ofReal_mul]
  rw [inner_power a h' g, inner_conj_symm h' g]
  ring


/-! ### The Wick operator on the Fock space -/

/-- The normally ordered Wick operator `𝒲_{a,b}(C)` on the Fock space: the sector `b+k` is sent
to the sector `a+k` by `wickBlock a b k C`.  The sum is meaningful whenever it is Hilbert-norm
summable (for example on the smooth domain). -/
def wickFock (a b : ℕ) (C : HN L b →L[ℂ] HN L a) (y : Fock L) : Fock L :=
  ∑' k : ℕ, inclusion L (a+k) (wickBlock a b k C (y (b+k)))

lemma inclusion_eq_projection (n : ℕ) (x : Fock L) : inclusion L n (x n) = projection L n x := rfl

lemma wickFock_of_sectors (a b : ℕ) (C : HN L b →L[ℂ] HN L a) (y x : Fock L)
    (h0 : ∀ j < a, x j = 0) (hk : ∀ k, x (a+k) = wickBlock a b k C (y (b+k))) :
    wickFock a b C y = x := by
  have hs := projection_hasSum L x
  have hs' : HasSum (fun k => projection L (k + a) x) (x - ∑ i ∈ Finset.range a, projection L i x) :=
    (hasSum_nat_add_iff' a).mpr hs
  have hz : ∑ i ∈ Finset.range a, projection L i x = 0 :=
    Finset.sum_eq_zero (fun i hi => by
      rw [projection_eq_single, h0 i (Finset.mem_range.mp hi)]; simp)
  rw [hz, sub_zero] at hs'
  unfold wickFock
  have h1 : (fun k => inclusion L (a+k) (wickBlock a b k C (y (b+k)))) =
      fun k => projection L (k+a) x := by
    funext k
    rw [← hk k, inclusion_eq_projection, Nat.add_comm a k]
  rw [h1]
  exact hs'.tsum_eq

/-! ### Sector locality of the iterates on the smooth domain -/

lemma castHN_fock {m n : ℕ} (h : m = n) (x : Fock L) : castHN h (x m) = x n := by
  subst h; rfl

lemma annPow_sector (f : L2T L) (b : ℕ) (y : physSmooth L) (k : ℕ) :
    (((annP f) ^ b) y).1 k = annB f b k (y.1 (b+k)) := by
  induction b generalizing y with
  | zero =>
    rw [pow_zero, Module.End.one_apply, annB_zero, castHN_fock]
  | succ b ih =>
    rw [pow_succ, Module.End.mul_apply, ih, annP_sector, annB_succ, castHN_fock (Nat.succ_add b k) y.1]

lemma crePow_sector_ge (f : L2T L) (a : ℕ) (z : physSmooth L) (k : ℕ) :
    (((creP f) ^ a) z).1 (a+k) = creB f a k (z.1 k) := by
  induction a generalizing k with
  | zero =>
    rw [pow_zero, Module.End.one_apply, creB_zero]
    exact (castHN_fock (Nat.zero_add k).symm z.1).symm
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h2 : (creP f (((creP f) ^ a) z)).1 ((a+1)+k) =
        castHN (Nat.succ_add a k).symm ((creP f (((creP f) ^ a) z)).1 (a+k+1)) :=
      (castHN_fock (Nat.succ_add a k).symm _).symm
    rw [h2, creP_sector_succ, ih k, creB_succ]

lemma crePow_sector_lt (f : L2T L) (a : ℕ) (z : physSmooth L) (j : ℕ) (hj : j < a) :
    (((creP f) ^ a) z).1 j = 0 := by
  induction a generalizing j with
  | zero => omega
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply]
    cases j with
    | zero => exact creP_sector_zero f _
    | succ j' =>
      rw [creP_sector_succ, ih j' (by omega)]
      exact map_zero _

/-- **Words are Wick operators of power kernels (Fock form).**  On the smooth domain,
`a*(g)^a a(f)^b = 𝒲_{a,b}(|g^a⟩⟨f^b|)`. -/
theorem wickFock_rk (a b : ℕ) (g f : L2T L) (y : physSmooth L) :
    wickFock a b (rk a b g f) y.1 = (((creP g) ^ a * (annP f) ^ b) y).1 := by
  apply wickFock_of_sectors
  · intro j hj
    rw [Module.End.mul_apply]
    exact crePow_sector_lt g a _ j hj
  · intro k
    rw [Module.End.mul_apply, crePow_sector_ge, annPow_sector, wickBlock_rk]
    rfl

end QuantumNLS.Prop024WWords

#print axioms QuantumNLS.Prop024WWords.clm_ext_powers
#print axioms QuantumNLS.Prop024WWords.wickBlock_rk
#print axioms QuantumNLS.Prop024WWords.wickFock_of_sectors
#print axioms QuantumNLS.Prop024WWords.annPow_sector
#print axioms QuantumNLS.Prop024WWords.crePow_sector_ge
#print axioms QuantumNLS.Prop024WWords.crePow_sector_lt
#print axioms QuantumNLS.Prop024WWords.wickFock_rk

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WWords." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WWords." then
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
  Lean.logInfo m!"Prop024WWords aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."
