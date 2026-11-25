import Mathlib
import QuantumNLS.Prop022OVacuum
import QuantumNLS.Prop022GTensor

/-! PROP-022 route A, stage A2a: single-sector occupation coordinates of power vectors.

For a sector vector `x : HN L n` let `secEmb n x ∈ ℓ²(Occ)` be its free occupation coordinates
(`Phi (single n x)`).  This module proves:
* `emb_apply_of_total`, `emb_apply_of_ne`, `emb_smooth` (coordinates and smoothness);
* `emb_power_of_total`: the coordinates of `u^{⊗n}` are `N_m ∏ û_a^{m_a}` (from `U3_htpow`, `U4_htpow`);
* `ann_emb_power`: the frozen coordinate annihilation operator `A h` acts on `u^{⊗(n+1)}` as
  `√(n+1) ⟨h, û⟩ u^{⊗n}`;
* `powers_total`: the power vectors `u^{⊗n}` have dense span in the sector `HN L n`
  (a vector orthogonal to all of them is zero; polynomial identity in finitely many variables). -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.Prop022ACoherent
open Occupation OccupationUnitary TensorCarrier PhysicalTensor BetheCoefficientTransform
open Ext025B3PhysicalSectors Ext006PhysFockCoord Ext006PhysicalVacuum Prop022TensorCompressionR115
open Ext006SmoothOperatorsR34a Ext006ModeDomainR33a Ext006SmearedDomainR33a Ext006QuasifreeWeak
variable {L : ℝ} [Fact (0 < L)]

abbrev OF := Ext006VacuumRecurrence.Fock

/-- Free occupation coordinates of a vector of the sector `n`. -/
def secEmb (n : ℕ) (x : HN L n) : OF := Phi (lp.single 2 n x : Fock L)

lemma emb_apply_of_total (n : ℕ) (x : HN L n) (m : Occ) (h : total m = n) :
    secEmb n x m = physicalOccupation L n x ⟨m, h⟩ := by
  subst h
  change occupationCoefficient (freeBasis L (total m))
    ((lp.single 2 (total m) x : Fock L) (total m)) ⟨m, rfl⟩ = _
  rw [lp.single_apply_self, occupationCoefficient_free]

lemma emb_apply_of_ne (n : ℕ) (x : HN L n) (m : Occ) (h : total m ≠ n) :
    secEmb n x m = 0 := by
  change occupationCoefficient (freeBasis L (total m))
    ((lp.single 2 n x : Fock L) (total m)) ⟨m, rfl⟩ = 0
  rw [lp.single_apply_ne _ _ _ h]
  simp

lemma emb_smooth (n : ℕ) (x : HN L n) : Smooth (secEmb n x) := by
  intro p
  have hs : Summable (fun m : Occ => ‖secEmb n x m‖ ^ 2) := summable_sq' (secEmb n x)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_) (hs.mul_left (((n : ℝ) + 1) ^ p))
  by_cases h : total m = n
  · rw [h]
  · rw [emb_apply_of_ne n x m h]
    simp

lemma emb_smul (n : ℕ) (c : ℂ) (x : HN L n) : secEmb n (c • x) = c • secEmb n x := by
  unfold secEmb
  rw [← map_smul, ← lp.single_smul]

lemma emb_add (n : ℕ) (x y : HN L n) : secEmb n (x + y) = secEmb n x + secEmb n y := by
  unfold secEmb
  rw [← map_add, ← lp.single_add]

/-! ### Power vectors -/

/-- The Fourier coordinates of `g ∈ L²(𝕋_L)`. -/
def ghat (g : L2T L) : OneParticle := QuantumNLS.Fourier.fourierL2 L g

lemma emb_power_of_total (n : ℕ) (g : L2T L) (m : Occ) (h : total m = n) :
    secEmb n (power n g) m =
      (normalization (⟨m, h⟩ : Arr n) : ℂ) * m.prod (fun a k => ghat g a ^ k) := by
  rw [emb_apply_of_total n _ m h]
  change OccupationUnitary.U4 n (TensorFourier.U3 L n
    ⟨htpow n g, htpow_mem_symSector n g⟩) ⟨m, h⟩ = _
  rw [TensorFourier.U3_htpow]
  exact OccupationUnitary.U4_htpow n (QuantumNLS.Fourier.fourierL2 L g) ⟨m, h⟩

lemma emb_power_of_ne (n : ℕ) (g : L2T L) (m : Occ) (h : total m ≠ n) :
    secEmb n (power n g) m = 0 := emb_apply_of_ne n _ m h

lemma multiplicityFactorial_add_e (m : Occ) (a : ℤ) :
    (multiplicityFactorial (m + e a) : ℝ) = (multiplicityFactorial m : ℝ) * ((m a : ℝ) + 1) := by
  classical
  have hS : ∀ f : Occ, f.support ⊆ insert a m.support → ∀ k : Occ,
      k.support ⊆ insert a m.support →
      multiplicityFactorial k = ∏ b ∈ insert a m.support, (k b).factorial := by
    intro f _ k hk
    unfold multiplicityFactorial
    exact Finsupp.prod_of_support_subset k hk _ (fun _ _ => Nat.factorial_zero)
  have h1 : multiplicityFactorial m = ∏ b ∈ insert a m.support, (m b).factorial :=
    hS m (Finset.subset_insert _ _) m (Finset.subset_insert _ _)
  have h2 : multiplicityFactorial (m + e a) = ∏ b ∈ insert a m.support, ((m + e a) b).factorial :=
    hS m (Finset.subset_insert _ _) (m + e a) (by
      intro b hb
      rw [Finsupp.mem_support_iff] at hb
      by_cases hba : b = a
      · exact Finset.mem_insert.mpr (Or.inl hba)
      · apply Finset.mem_insert_of_mem
        rw [Finsupp.mem_support_iff]
        intro h0
        apply hb
        simp [h0, Finsupp.single_apply, Ne.symm hba])
  rw [h1, h2, ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self a m.support),
    ← Finset.mul_prod_erase _ (fun b => (m b).factorial) (Finset.mem_insert_self a m.support)]
  have h3 : ∏ b ∈ (insert a m.support).erase a, ((m + e a) b).factorial =
      ∏ b ∈ (insert a m.support).erase a, (m b).factorial := by
    apply Finset.prod_congr rfl
    intro b hb
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    simp [Finsupp.single_apply, Ne.symm hba]
  rw [h3]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_mul, Nat.factorial_succ]
  push_cast
  ring

lemma normalization_add_e (n : ℕ) (m : Occ) (a : ℤ) (h : total m = n) :
    normalization (⟨m + e a, by simp [IsArray, total_add_e, h]⟩ : Arr (n + 1)) *
        Real.sqrt ((m a : ℝ) + 1) =
      Real.sqrt ((n : ℝ) + 1) * normalization (⟨m, h⟩ : Arr n) := by
  unfold normalization
  simp only
  rw [multiplicityFactorial_add_e, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
  congr 1
  have hf : (0 : ℝ) < (multiplicityFactorial m : ℝ) := by exact_mod_cast multiplicityFactorial_pos m
  have hm : (0 : ℝ) < (m a : ℝ) + 1 := by positivity
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- The frozen coordinate annihilation `A h` on a power vector. -/
lemma ann_emb_power (n : ℕ) (g : L2T L) (h : OneParticle) :
    (A h ⟨secEmb (n + 1) (power (n + 1) g), emb_smooth _ _⟩).1 =
      ((Real.sqrt ((n : ℝ) + 1) : ℂ) * inner ℂ h (ghat g)) • secEmb n (power n g) := by
  apply lp.ext
  funext m
  change inner ℂ h (xvec (secEmb (n + 1) (power (n + 1) g)) m) = _
  have hx : xvec (secEmb (n + 1) (power (n + 1) g)) m =
      ((Real.sqrt ((n : ℝ) + 1) : ℂ) * secEmb n (power n g) m) • ghat g := by
    apply lp.ext
    funext a
    change (Real.sqrt ((m a : ℝ) + 1) : ℂ) * secEmb (n + 1) (power (n + 1) g) (m + e a) = _
    by_cases hm : total m = n
    · have hm' : total (m + e a) = n + 1 := by simp [total_add_e, hm]
      rw [emb_power_of_total (n + 1) g (m + e a) hm', emb_power_of_total n g m hm]
      have hp : (m + e a).prod (fun b k => ghat g b ^ k) = m.prod (fun b k => ghat g b ^ k) * ghat g a := by
        have h1 : (e a).prod (fun b k => ghat g b ^ k) = ghat g a := by
          simpa using Finsupp.prod_single_index (a := a) (b := 1) (h := fun b k => ghat g b ^ k)
            (by simp)
        rw [Finsupp.prod_add_index' (h := fun b k => ghat g b ^ k) (fun _ => pow_zero _)
          (fun _ _ _ => pow_add _ _ _), h1]
      rw [hp]
      have hN := normalization_add_e n m a hm
      have hN' : (normalization (⟨m + e a, hm'⟩ : Arr (n + 1)) : ℂ) * (Real.sqrt ((m a : ℝ) + 1) : ℂ) =
          (Real.sqrt ((n : ℝ) + 1) : ℂ) * (normalization (⟨m, hm⟩ : Arr n) : ℂ) := by
        exact_mod_cast hN
      change _ = ((Real.sqrt ((n : ℝ) + 1) : ℂ) * _) * ghat g a
      calc (Real.sqrt ((m a : ℝ) + 1) : ℂ) * ((normalization (⟨m + e a, hm'⟩ : Arr (n + 1)) : ℂ) *
            (m.prod (fun b k => ghat g b ^ k) * ghat g a))
          = ((normalization (⟨m + e a, hm'⟩ : Arr (n + 1)) : ℂ) * (Real.sqrt ((m a : ℝ) + 1) : ℂ)) *
            (m.prod (fun b k => ghat g b ^ k) * ghat g a) := by ring
        _ = _ := by rw [hN']; ring
    · have hm' : total (m + e a) ≠ n + 1 := by simp [total_add_e, hm]
      rw [emb_power_of_ne (n + 1) g (m + e a) hm', emb_apply_of_ne n _ m hm]
      simp
  rw [hx, inner_smul_right]
  change _ = ((Real.sqrt ((n : ℝ) + 1) : ℂ) * inner ℂ h (ghat g)) * secEmb n (power n g) m
  ring

/-! ### Totality of the power vectors -/

lemma physOcc_power_apply (n : ℕ) (g : L2T L) (m : Arr n) :
    physicalOccupation L n (power n g) m =
      (normalization m : ℂ) * m.val.prod (fun a k => ghat g a ^ k) := by
  have := emb_power_of_total n g m.val m.2
  rw [emb_apply_of_total n _ m.val m.2] at this
  exact this

/-- Finitely supported `ℓ²(ℤ)` vector with prescribed values on a finite set. -/
def finSupp (S : Finset ℤ) (y : ℤ → ℂ) : OneParticle :=
  ⟨fun b => if b ∈ S then y b else 0, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    apply summable_of_ne_finset_zero (s := S)
    intro b hb
    simp [hb]⟩

lemma finSupp_apply (S : Finset ℤ) (y : ℤ → ℂ) (b : ℤ) :
    finSupp S y b = if b ∈ S then y b else 0 := rfl

lemma sum_eq_total (m : Occ) (S : Finset ℤ) (h : m.support ⊆ S) : S.sum m = total m := by
  unfold total Finsupp.degree
  exact (Finset.sum_subset h (fun b _ hb => by simpa using hb)).symm

lemma powers_total (n : ℕ) (x : HN L n)
    (hx : ∀ g : L2T L, inner ℂ (power n g) x = 0) : x = 0 := by
  classical
  apply (physicalOccupation L n).injective
  rw [map_zero]
  apply lp.ext
  funext m0
  rcases m0 with ⟨m0, h0⟩
  set X := physicalOccupation L n x with hX
  set S := m0.support with hS
  -- the polynomial
  let c : Occ → ℂ := fun m => if h : total m = n then (normalization (⟨m, h⟩ : Arr n) : ℂ) * X ⟨m, h⟩ else 0
  let Q : MvPolynomial ℤ ℂ := ∑ m ∈ Finset.finsuppAntidiag S n, MvPolynomial.monomial m (c m)
  have hQ : ∀ y : ℤ → ℂ, MvPolynomial.eval y Q = 0 := by
    intro y
    let u : ℤ → ℂ := fun b => if b ∈ S then y b else 0
    have hev : MvPolynomial.eval y Q = MvPolynomial.eval u Q := by
      simp only [Q, map_sum, MvPolynomial.eval_monomial]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_finsuppAntidiag] at hm
      congr 1
      apply Finsupp.prod_congr
      intro b hb
      have : b ∈ S := hm.2 hb
      simp [u, this]
    rw [hev]
    set g : L2T L := (QuantumNLS.Fourier.fourierL2 L).symm (finSupp S (fun b => conj (u b))) with hg
    have hgh : ghat g = finSupp S (fun b => conj (u b)) := by
      simp [ghat, hg]
    have h1 := hx g
    rw [← LinearIsometryEquiv.inner_map_map (physicalOccupation L n), lp.inner_eq_tsum] at h1
    simp only [physOcc_power_apply, hgh] at h1
    have hterm : ∀ i : Arr n, inner ℂ ((normalization i : ℂ) * i.val.prod
        (fun a k => (finSupp S (fun b => conj (u b))) a ^ k)) (X i) =
        (normalization i : ℂ) * i.val.prod (fun a k => u a ^ k) * X i := by
      intro i
      have hP : conj (i.val.prod (fun a k => (finSupp S (fun b => conj (u b))) a ^ k)) =
          i.val.prod (fun a k => u a ^ k) := by
        simp only [Finsupp.prod, map_prod, map_pow]
        apply Finset.prod_congr rfl
        intro a _
        by_cases ha : a ∈ S
        · simp [finSupp_apply, ha]
        · simp [finSupp_apply, ha, u]
      simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal, hP]
      ring
    rw [← hX] at h1
    simp only [hterm] at h1
    have key : ∑' i : Arr n, (normalization i : ℂ) * i.val.prod (fun a k => u a ^ k) * X i =
        ∑ m ∈ Finset.finsuppAntidiag S n, c m * m.prod (fun a k => u a ^ k) := by
      have hsupp : ∀ i : Arr n, i ∉ (Finset.finsuppAntidiag S n).subtype (IsArray n) →
          (normalization i : ℂ) * i.val.prod (fun a k => u a ^ k) * X i = 0 := by
        intro i hi
        have hns : ¬ i.val.support ⊆ S := by
          intro hsub
          apply hi
          rw [Finset.mem_subtype, Finset.mem_finsuppAntidiag]
          refine ⟨?_, hsub⟩
          rw [sum_eq_total i.val S hsub]
          exact i.2
        obtain ⟨a, ha, haS⟩ := Finset.not_subset.mp hns
        have hz : i.val.prod (fun a k => u a ^ k) = 0 := by
          apply Finset.prod_eq_zero ha
          have : u a = 0 := by simp [u, haS]
          show u a ^ i.val a = 0
          rw [this]
          exact zero_pow (Finsupp.mem_support_iff.mp ha)
        rw [hz]
        simp
      rw [tsum_eq_sum hsupp]
      have hmem : ∀ x ∈ Finset.finsuppAntidiag S n, IsArray n x := by
        intro x hx
        rw [Finset.mem_finsuppAntidiag] at hx
        rw [IsArray, ← sum_eq_total x S hx.2]
        exact hx.1
      rw [← Finset.sum_subtype_of_mem (fun m : Occ => c m * m.prod (fun a k => u a ^ k)) hmem]
      apply Finset.sum_congr rfl
      intro i _
      have hci : c i.val = (normalization i : ℂ) * X i := by
        show (if h : total i.val = n then (normalization (⟨i.val, h⟩ : Arr n) : ℂ) *
          X ⟨i.val, h⟩ else 0) = _
        have hi : total i.val = n := i.2
        rw [dif_pos hi]
      beta_reduce
      rw [hci]
      ring
    rw [key] at h1
    simpa only [Q, map_sum, MvPolynomial.eval_monomial] using h1
  have hQ0 : Q = 0 := MvPolynomial.funext (fun y => by rw [hQ y, map_zero])
  have hm0 : m0 ∈ Finset.finsuppAntidiag S n := by
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, subset_rfl⟩
    rw [sum_eq_total m0 S subset_rfl]
    exact h0
  have hq : Q.coeff m0 = c m0 := by
    simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single m0 (fun b _ hb => by simp [hb]) (fun h => absurd hm0 h)]
    simp
  have hc0 : c m0 = 0 := by
    rw [← hq, hQ0]
    simp
  have hcm : c m0 = (normalization (⟨m0, h0⟩ : Arr n) : ℂ) * X ⟨m0, h0⟩ := by
    show (if h : total m0 = n then (normalization (⟨m0, h⟩ : Arr n) : ℂ) * X ⟨m0, h⟩ else 0) = _
    have h0' : total m0 = n := h0
    rw [dif_pos h0']
  rw [hcm] at hc0
  have hN : (normalization (⟨m0, h0⟩ : Arr n) : ℂ) ≠ 0 := by
    exact_mod_cast (normalization_pos _).ne'
  have := (mul_eq_zero.mp hc0).resolve_left hN
  simpa [hX] using this

end QuantumNLS.Prop022ACoherent
