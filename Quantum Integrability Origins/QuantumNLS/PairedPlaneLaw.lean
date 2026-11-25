import Mathlib

/-!
# `intr:plane:lem:pc-product` (R-D6286EDD): the paired plane-wave count law is a probability

Source: `source/chapters/intrinsic/plane.tex`, the lemma following eq. (pc-paired-law).
Printed objects (`L, κ > 0`; `j ≥ 1` is a positive integer, `j : ℕ+`):
`g = κ/L`, `k_j = 2π j / L`, `h_j = k_j² + 2g`, `ω_j = k_j √(k_j² + 4g)`,
`ζ_j = (h_j - ω_j)/(h_j + ω_j)`, `p_* = ∏_{j ≥ 1} (1 - ζ_j)` (a Mathlib unconditional infinite
product `tprod` over `ℕ+`), the configuration space `𝒞` of finitely supported `η : ℤ∖{0} → ℕ`
(`Config := ({j : ℤ // j ≠ 0} →₀ ℕ)`), and the paired law
`P η = p_* ∏_{j ≥ 1} ζ_j^{η_j}` if `η_j = η_{-j}` for all `j ≥ 1`, else `0`.
-/

open scoped BigOperators ENNReal Topology
open Filter

namespace QuantumNLS.PairedPlaneLaw

noncomputable section

/-! ### Printed parameters -/

def gC (L κ : ℝ) : ℝ := κ / L
def kC (L : ℝ) (j : ℕ+) : ℝ := 2 * Real.pi * (j : ℝ) / L
def hC (L κ : ℝ) (j : ℕ+) : ℝ := kC L j ^ 2 + 2 * gC L κ
def omegaC (L κ : ℝ) (j : ℕ+) : ℝ := kC L j * Real.sqrt (kC L j ^ 2 + 4 * gC L κ)
def zetaC (L κ : ℝ) (j : ℕ+) : ℝ :=
  (hC L κ j - omegaC L κ j) / (hC L κ j + omegaC L κ j)
/-- `p_* = ∏_{j ≥ 1} (1 - ζ_j)`, the Mathlib unconditional infinite product over `ℕ+`. -/
def pStar (L κ : ℝ) : ℝ := ∏' j : ℕ+, (1 - zetaC L κ j)

/-! ### Elementary estimates on `ζ_j` -/

section Analytic

variable {L κ : ℝ}

theorem gC_pos (hL : 0 < L) (hκ : 0 < κ) : 0 < gC L κ := div_pos hκ hL

theorem kC_pos (hL : 0 < L) (j : ℕ+) : 0 < kC L j := by
  unfold kC
  have : (0 : ℝ) < (j : ℝ) := by exact_mod_cast j.pos
  positivity

theorem hC_pos (hL : 0 < L) (hκ : 0 < κ) (j : ℕ+) : 0 < hC L κ j := by
  have := gC_pos hL hκ
  have := kC_pos hL j
  unfold hC; positivity

theorem omegaC_pos (hL : 0 < L) (hκ : 0 < κ) (j : ℕ+) : 0 < omegaC L κ j := by
  have := gC_pos hL hκ
  have := kC_pos hL j
  unfold omegaC
  exact mul_pos ‹_› (Real.sqrt_pos.2 (by positivity))

/-- The printed identity `h_j² - ω_j² = 4 g²`. -/
theorem h_sq_sub_omega_sq (hL : 0 < L) (hκ : 0 < κ) (j : ℕ+) :
    hC L κ j ^ 2 - omegaC L κ j ^ 2 = 4 * gC L κ ^ 2 := by
  have hg := gC_pos hL hκ
  have hk := kC_pos hL j
  have hs : Real.sqrt (kC L j ^ 2 + 4 * gC L κ) ^ 2 = kC L j ^ 2 + 4 * gC L κ :=
    Real.sq_sqrt (by positivity)
  unfold hC omegaC
  rw [mul_pow, hs]
  ring

theorem omegaC_lt_hC (hL : 0 < L) (hκ : 0 < κ) (j : ℕ+) : omegaC L κ j < hC L κ j := by
  have h1 := h_sq_sub_omega_sq hL hκ j
  have hg := gC_pos hL hκ
  have hh := hC_pos hL hκ j
  have ho := omegaC_pos hL hκ j
  by_contra hcon
  have hcon' := not_lt.mp hcon
  nlinarith

theorem zetaC_pos (hL : 0 < L) (hκ : 0 < κ) (j : ℕ+) : 0 < zetaC L κ j := by
  have := omegaC_lt_hC hL hκ j
  have := omegaC_pos hL hκ j
  have := hC_pos hL hκ j
  unfold zetaC
  apply div_pos <;> linarith

theorem zetaC_lt_one (hL : 0 < L) (hκ : 0 < κ) (j : ℕ+) : zetaC L κ j < 1 := by
  have := omegaC_pos hL hκ j
  have := hC_pos hL hκ j
  unfold zetaC
  rw [div_lt_one (by linarith)]
  linarith

/-- The printed form `ζ_j = 4g²/(h_j + ω_j)²`. -/
theorem zetaC_eq (hL : 0 < L) (hκ : 0 < κ) (j : ℕ+) :
    zetaC L κ j = 4 * gC L κ ^ 2 / (hC L κ j + omegaC L κ j) ^ 2 := by
  have h1 := h_sq_sub_omega_sq hL hκ j
  have := omegaC_pos hL hκ j
  have := hC_pos hL hκ j
  unfold zetaC
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (hC L κ j + omegaC L κ j) * h1

/-- The printed bound `ζ_j ≤ 4 g² / k_j⁴`. -/
theorem zetaC_le (hL : 0 < L) (hκ : 0 < κ) (j : ℕ+) :
    zetaC L κ j ≤ 4 * gC L κ ^ 2 / kC L j ^ 4 := by
  rw [zetaC_eq hL hκ j]
  have hk := kC_pos hL j
  have hg := gC_pos hL hκ
  have ho := omegaC_pos hL hκ j
  have hh : kC L j ^ 2 ≤ hC L κ j := by unfold hC; linarith
  have h4 : kC L j ^ 4 ≤ (hC L κ j + omegaC L κ j) ^ 2 := by
    have : kC L j ^ 4 = (kC L j ^ 2) ^ 2 := by ring
    rw [this]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) h4

theorem summable_zetaC (hL : 0 < L) (hκ : 0 < κ) : Summable (zetaC L κ) := by
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 4)⁻¹) :=
    Real.summable_nat_pow_inv.2 (by norm_num)
  have hs' : Summable (fun j : ℕ+ => ((j : ℝ) ^ 4)⁻¹) :=
    hs.comp_injective PNat.coe_injective
  refine Summable.of_nonneg_of_le (fun j => (zetaC_pos hL hκ j).le)
    (fun j => ?_) (hs'.mul_left (4 * gC L κ ^ 2 / (2 * Real.pi / L) ^ 4))
  refine (zetaC_le hL hκ j).trans (le_of_eq ?_)
  have hj : (0 : ℝ) < (j : ℝ) := by exact_mod_cast j.pos
  have hpi := Real.pi_pos
  unfold kC
  field_simp


/-! ### The infinite product `p_*` -/

theorem one_sub_zetaC_pos (hL : 0 < L) (hκ : 0 < κ) (j : ℕ+) : 0 < 1 - zetaC L κ j := by
  linarith [zetaC_lt_one hL hκ j]

theorem summable_log_one_sub (hL : 0 < L) (hκ : 0 < κ) :
    Summable (fun j : ℕ+ => Real.log (1 - zetaC L κ j)) := by
  have := Real.summable_log_one_add_of_summable (f := fun j : ℕ+ => - zetaC L κ j)
    (summable_zetaC hL hκ).neg
  simpa [sub_eq_add_neg] using this

/-- Convergence of the infinite product: `∏_{j ≥ 1} (1 - ζ_j)` converges (unconditionally,
`HasProd`) to `exp (∑ log (1 - ζ_j))`. -/
theorem hasProd_one_sub_zetaC (hL : 0 < L) (hκ : 0 < κ) :
    HasProd (fun j : ℕ+ => 1 - zetaC L κ j)
      (Real.exp (∑' j : ℕ+, Real.log (1 - zetaC L κ j))) :=
  Real.hasProd_of_hasSum_log (fun j => one_sub_zetaC_pos hL hκ j)
    (summable_log_one_sub hL hκ).hasSum

theorem pStar_eq_exp (hL : 0 < L) (hκ : 0 < κ) :
    pStar L κ = Real.exp (∑' j : ℕ+, Real.log (1 - zetaC L κ j)) :=
  (hasProd_one_sub_zetaC hL hκ).tprod_eq

theorem hasProd_pStar (hL : 0 < L) (hκ : 0 < κ) :
    HasProd (fun j : ℕ+ => 1 - zetaC L κ j) (pStar L κ) := by
  rw [pStar_eq_exp hL hκ]; exact hasProd_one_sub_zetaC hL hκ

/-- Convergence of the partial products `∏_{j=1}^{J} (1 - ζ_j) → p_*`. -/
theorem tendsto_partial_pStar (hL : 0 < L) (hκ : 0 < κ) :
    Tendsto (fun J : ℕ => ∏ n ∈ Finset.range J, (1 - zetaC L κ n.succPNat)) atTop
      (𝓝 (pStar L κ)) := by
  have h := (Equiv.hasProd_iff (Equiv.pnatEquivNat.symm)
    (f := fun j : ℕ+ => 1 - zetaC L κ j) (a := pStar L κ)).2 (hasProd_pStar hL hκ)
  exact h.tendsto_prod_nat

theorem pStar_pos (hL : 0 < L) (hκ : 0 < κ) : 0 < pStar L κ := by
  rw [pStar_eq_exp hL hκ]; exact Real.exp_pos _

theorem pStar_lt_one (hL : 0 < L) (hκ : 0 < κ) : pStar L κ < 1 := by
  rw [pStar_eq_exp hL hκ]
  have hneg : ∀ j : ℕ+, Real.log (1 - zetaC L κ j) < 0 := fun j =>
    Real.log_neg (one_sub_zetaC_pos hL hκ j) (by linarith [zetaC_pos hL hκ j])
  have hs : HasSum (fun j : ℕ+ => - Real.log (1 - zetaC L κ j))
      (- ∑' j : ℕ+, Real.log (1 - zetaC L κ j)) := (summable_log_one_sub hL hκ).hasSum.neg
  have h1 := le_hasSum hs 1 (fun j _ => neg_nonneg.2 (hneg j).le)
  have h2 := hneg 1
  have : ∑' j : ℕ+, Real.log (1 - zetaC L κ j) < 0 := by linarith
  exact Real.exp_lt_one_iff.2 this

end Analytic

/-! ### Configuration space and the paired law -/

/-- Index set `ℤ ∖ {0}`. -/
abbrev Idx : Type := {j : ℤ // j ≠ 0}

/-- The configuration space `𝒞`: finitely supported tuples `η = (η_j)_{j ∈ ℤ∖{0}}` of
nonnegative integers (a countable set). -/
abbrev Config : Type := Idx →₀ ℕ

/-- The index `+j ∈ ℤ∖{0}` for `j ≥ 1`. -/
def posIdx (j : ℕ+) : Idx := ⟨((j : ℕ) : ℤ), by exact_mod_cast j.ne_zero⟩
/-- The index `-j ∈ ℤ∖{0}` for `j ≥ 1`. -/
def negIdx (j : ℕ+) : Idx := ⟨-((j : ℕ) : ℤ), by
  have : ((j : ℕ) : ℤ) ≠ 0 := by exact_mod_cast j.ne_zero
  omega⟩

/-- The pairing condition `η_j = η_{-j}` for every `j ≥ 1`. -/
def Paired (η : Config) : Prop := ∀ j : ℕ+, η (posIdx j) = η (negIdx j)

open scoped Classical in
/-- The printed law (pc-paired-law): `P η = p_* ∏_{j ≥ 1} ζ_j^{η_j}` if `η_j = η_{-j}` for all
`j ≥ 1`, and `0` otherwise. The product is the Mathlib `tprod` over `ℕ+` (all but finitely
many factors equal `1`). -/
def pairedLaw (L κ : ℝ) (η : Config) : ℝ :=
  if Paired η then pStar L κ * ∏' j : ℕ+, zetaC L κ j ^ η (posIdx j) else 0

theorem posIdx_injective : Function.Injective posIdx := by
  intro a b h
  have := congrArg Subtype.val h
  simp only [posIdx] at this
  exact PNat.coe_injective (by exact_mod_cast this)

theorem negIdx_injective : Function.Injective negIdx := by
  intro a b h
  have := congrArg Subtype.val h
  simp only [negIdx] at this
  exact PNat.coe_injective (by exact_mod_cast neg_injective this)

theorem posIdx_ne_negIdx (a b : ℕ+) : posIdx a ≠ negIdx b := by
  intro h
  have := congrArg Subtype.val h
  simp only [posIdx, negIdx] at this
  have ha : (0 : ℤ) < ((a : ℕ) : ℤ) := by exact_mod_cast a.pos
  have hb : (0 : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast b.pos
  omega

theorem negIdx_ne_posIdx (a b : ℕ+) : negIdx a ≠ posIdx b := (posIdx_ne_negIdx b a).symm

/-- Every index is `±(n+1)`. -/
theorem idx_cases (a : Idx) :
    ∃ n : ℕ, a = posIdx n.succPNat ∨ a = negIdx n.succPNat := by
  obtain ⟨j, hj⟩ := a
  rcases lt_or_gt_of_ne hj with h | h
  · refine ⟨(-j).toNat - 1, Or.inr ?_⟩
    apply Subtype.ext
    simp only [negIdx, Nat.succPNat_coe, Nat.succ_eq_add_one]
    omega
  · refine ⟨j.toNat - 1, Or.inl ?_⟩
    apply Subtype.ext
    simp only [posIdx, Nat.succPNat_coe, Nat.succ_eq_add_one]
    omega

/-- The unpaired data: a finitely supported `ν : ℕ →₀ ℕ` (`ν n = η_{n+1} = η_{-(n+1)}`) gives
the paired configuration `Φ ν`. -/
def Phi (ν : ℕ →₀ ℕ) : Config :=
  Finsupp.mapDomain (fun n : ℕ => posIdx n.succPNat) ν +
    Finsupp.mapDomain (fun n : ℕ => negIdx n.succPNat) ν

theorem injective_pos_succ : Function.Injective (fun n : ℕ => posIdx n.succPNat) :=
  posIdx_injective.comp Nat.succPNat_injective

theorem injective_neg_succ : Function.Injective (fun n : ℕ => negIdx n.succPNat) :=
  negIdx_injective.comp Nat.succPNat_injective

theorem Phi_pos (ν : ℕ →₀ ℕ) (n : ℕ) : Phi ν (posIdx n.succPNat) = ν n := by
  unfold Phi
  have h1 : (Finsupp.mapDomain (fun n : ℕ => posIdx n.succPNat) ν) (posIdx n.succPNat) = ν n :=
    Finsupp.mapDomain_apply_of_injective injective_pos_succ ν n
  have h2 : (Finsupp.mapDomain (fun n : ℕ => negIdx n.succPNat) ν) (posIdx n.succPNat) = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨m, hm⟩
    exact negIdx_ne_posIdx _ _ hm
  rw [Finsupp.add_apply, h1, h2, add_zero]

theorem Phi_neg (ν : ℕ →₀ ℕ) (n : ℕ) : Phi ν (negIdx n.succPNat) = ν n := by
  unfold Phi
  have h1 : (Finsupp.mapDomain (fun n : ℕ => negIdx n.succPNat) ν) (negIdx n.succPNat) = ν n :=
    Finsupp.mapDomain_apply_of_injective injective_neg_succ ν n
  have h2 : (Finsupp.mapDomain (fun n : ℕ => posIdx n.succPNat) ν) (negIdx n.succPNat) = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨m, hm⟩
    exact posIdx_ne_negIdx _ _ hm
  rw [Finsupp.add_apply, h1, h2, zero_add]

theorem Phi_paired (ν : ℕ →₀ ℕ) : Paired (Phi ν) := by
  intro j
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = n.succPNat := ⟨j.natPred, (PNat.succPNat_natPred j).symm⟩
  rw [Phi_pos, Phi_neg]

theorem Phi_injective : Function.Injective Phi := by
  intro ν ν' h
  ext n
  rw [← Phi_pos ν n, ← Phi_pos ν' n, h]

theorem exists_Phi_of_paired (η : Config) (hη : Paired η) : ∃ ν : ℕ →₀ ℕ, Phi ν = η := by
  refine ⟨Finsupp.comapDomain (fun n : ℕ => posIdx n.succPNat) η
    injective_pos_succ.injOn, ?_⟩
  ext a
  obtain ⟨n, ha | ha⟩ := idx_cases a
  · subst ha
    rw [Phi_pos, Finsupp.comapDomain_apply]
  · subst ha
    rw [Phi_neg, Finsupp.comapDomain_apply]
    exact hη n.succPNat

theorem pairedLaw_of_not_paired {η : Config} (h : ¬ Paired η) (L κ : ℝ) :
    pairedLaw L κ η = 0 := by
  simp [pairedLaw, h]

/-- `ζ'_n = ζ_{n+1}` (zero-based index). -/
def zeta' (L κ : ℝ) (n : ℕ) : ℝ := zetaC L κ n.succPNat

/-- Weight of an unpaired datum: `∏_n ζ'_n^{ν_n}` (a finite product). -/
def weight (L κ : ℝ) (ν : ℕ →₀ ℕ) : ℝ := ν.prod (fun n a => zeta' L κ n ^ a)

theorem pairedLaw_Phi (L κ : ℝ) (ν : ℕ →₀ ℕ) :
    pairedLaw L κ (Phi ν) = pStar L κ * weight L κ ν := by
  classical
  unfold pairedLaw
  simp only [Phi_paired ν, ite_true]
  congr 1
  have e : ∏' n : ℕ, zeta' L κ n ^ ν n = ∏' j : ℕ+, zetaC L κ j ^ (Phi ν) (posIdx j) := by
    rw [← Equiv.tprod_eq (Equiv.pnatEquivNat.symm)]
    refine tprod_congr (fun n => ?_)
    show zeta' L κ n ^ ν n = zetaC L κ n.succPNat ^ (Phi ν) (posIdx n.succPNat)
    rw [Phi_pos]; rfl
  rw [← e]
  unfold weight Finsupp.prod
  exact tprod_eq_prod (fun n hn => by simp [Finsupp.notMem_support_iff.mp hn])


/-! ### Total mass: geometric series over `ℝ≥0∞` (the printed independent-geometric argument,
carried out as a sum over finitely supported `ν : ℕ →₀ ℕ`) -/

section Core

/-- Finite geometric product: `∑_{μ : Fin J → ℕ} ∏_i z_i^{μ_i} = ∏_{i<J} (1 - z_i)⁻¹`. -/
theorem tsum_fin_geometric (z : ℕ → ℝ≥0∞) (hz : ∀ n, z n < 1) :
    ∀ J : ℕ, ∑' μ : Fin J → ℕ, ∏ i : Fin J, z i ^ μ i = ∏ i : Fin J, (1 - z i)⁻¹ := by
  intro J
  induction J generalizing z with
  | zero => simp
  | succ J ih =>
    have e := (Fin.consEquiv (fun _ : Fin (J + 1) => ℕ)).tsum_eq
      (fun μ : Fin (J + 1) → ℕ => ∏ i : Fin (J + 1), z i ^ μ i)
    rw [← e, ENNReal.tsum_prod']
    have key : ∀ (a : ℕ) (ν : Fin J → ℕ),
        ∏ i : Fin (J + 1), z i ^ ((Fin.consEquiv (fun _ : Fin (J + 1) => ℕ)) (a, ν)) i =
          z 0 ^ a * ∏ i : Fin J, (fun n => z (n + 1)) i ^ ν i := by
      intro a ν
      rw [Fin.prod_univ_succ]
      simp [Fin.consEquiv]
    simp_rw [key]
    simp_rw [ENNReal.tsum_mul_left]
    rw [ih (fun n => z (n + 1)) (fun n => hz _), ENNReal.tsum_mul_right,
      ENNReal.tsum_geometric, Fin.prod_univ_succ]
    simp

/-- The finitely supported embedding of `Fin J → ℕ`. -/
def embedFin (J : ℕ) (μ : Fin J → ℕ) : ℕ →₀ ℕ :=
  Finsupp.onFinset (Finset.range J) (fun n => if h : n < J then μ ⟨n, h⟩ else 0) (by
    intro n hn
    rw [Finset.mem_range]
    by_contra hc
    simp [hc] at hn)

theorem embedFin_apply (J : ℕ) (μ : Fin J → ℕ) (i : Fin J) : embedFin J μ i = μ i := by
  simp [embedFin, Finsupp.onFinset_apply]

theorem embedFin_injective (J : ℕ) : Function.Injective (embedFin J) := by
  intro μ μ' h
  funext i
  rw [← embedFin_apply J μ i, ← embedFin_apply J μ' i, h]

theorem support_embedFin (J : ℕ) (μ : Fin J → ℕ) :
    (embedFin J μ).support ⊆ Finset.range J := Finsupp.support_onFinset_subset

theorem embedFin_weight (z : ℕ → ℝ≥0∞) (J : ℕ) (μ : Fin J → ℕ) :
    (embedFin J μ).prod (fun n a => z n ^ a) = ∏ i : Fin J, z i ^ μ i := by
  rw [Finsupp.prod_of_support_subset _ (support_embedFin J μ) _ (by intros; simp),
    Finset.prod_range (fun n => z n ^ (embedFin J μ n))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [embedFin_apply]

theorem embedFin_of_support_subset (J : ℕ) (ν : ℕ →₀ ℕ) (h : ν.support ⊆ Finset.range J) :
    embedFin J (fun i : Fin J => ν i) = ν := by
  ext n
  by_cases hn : n < J
  · have := embedFin_apply J (fun i : Fin J => ν i) ⟨n, hn⟩
    simpa using this
  · have h1 : ν n = 0 := by
      by_contra hc
      exact hn (Finset.mem_range.1 (h (Finsupp.mem_support_iff.2 hc)))
    simp [embedFin, Finsupp.onFinset_apply, hn, h1]

/-- Total mass of the unpaired weights: `∑_ν ∏ z_n^{ν_n} = ⨆_J ∏_{n<J} (1 - z_n)⁻¹`. -/
theorem tsum_weight_eq_iSup (z : ℕ → ℝ≥0∞) (hz : ∀ n, z n < 1) :
    ∑' ν : ℕ →₀ ℕ, ν.prod (fun n a => z n ^ a) =
      ⨆ J : ℕ, ∏ n ∈ Finset.range J, (1 - z n)⁻¹ := by
  have hT : ∀ J : ℕ, ∏ n ∈ Finset.range J, (1 - z n)⁻¹ =
      ∑' μ : Fin J → ℕ, (embedFin J μ).prod (fun n a => z n ^ a) := by
    intro J
    simp_rw [embedFin_weight]
    rw [tsum_fin_geometric z hz J, Finset.prod_range (fun n => (1 - z n)⁻¹)]
  apply le_antisymm
  · rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le (fun s => ?_)
    obtain ⟨J, hJ⟩ := Finset.exists_nat_subset_range (s.biUnion Finsupp.support)
    have hsub : ∀ ν ∈ s, ν.support ⊆ Finset.range J := fun ν hν =>
      (Finset.subset_biUnion_of_mem Finsupp.support hν).trans hJ
    let r : (ℕ →₀ ℕ) → (Fin J → ℕ) := fun ν i => ν i
    have hr : ∀ ν ∈ s, embedFin J (r ν) = ν := fun ν hν => embedFin_of_support_subset J ν (hsub ν hν)
    have hinj : Set.InjOn r s := by
      intro a ha b hb hab
      rw [← hr a ha, ← hr b hb, hab]
    calc ∑ ν ∈ s, ν.prod (fun n a => z n ^ a)
        = ∑ ν ∈ s, (embedFin J (r ν)).prod (fun n a => z n ^ a) :=
          Finset.sum_congr rfl (fun ν hν => by rw [hr ν hν])
      _ = ∑ μ ∈ s.image r, (embedFin J μ).prod (fun n a => z n ^ a) := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑' μ : Fin J → ℕ, (embedFin J μ).prod (fun n a => z n ^ a) :=
          ENNReal.sum_le_tsum _
      _ = ∏ n ∈ Finset.range J, (1 - z n)⁻¹ := (hT J).symm
      _ ≤ _ := le_iSup (fun J : ℕ => ∏ n ∈ Finset.range J, (1 - z n)⁻¹) J
  · refine iSup_le (fun J => ?_)
    rw [hT J]
    exact ENNReal.tsum_comp_le_tsum_of_injective (embedFin_injective J)
      (fun ν : ℕ →₀ ℕ => ν.prod (fun n a => z n ^ a))

end Core

section Total

variable {L κ : ℝ}

theorem weight_nonneg (hL : 0 < L) (hκ : 0 < κ) (ν : ℕ →₀ ℕ) : 0 ≤ weight L κ ν := by
  unfold weight Finsupp.prod
  exact Finset.prod_nonneg (fun n _ => pow_nonneg (zetaC_pos hL hκ _).le _)

theorem pairedLaw_nonneg (hL : 0 < L) (hκ : 0 < κ) (η : Config) : 0 ≤ pairedLaw L κ η := by
  by_cases h : Paired η
  · obtain ⟨ν, rfl⟩ := exists_Phi_of_paired η h
    rw [pairedLaw_Phi]
    exact mul_nonneg (pStar_pos hL hκ).le (weight_nonneg hL hκ ν)
  · rw [pairedLaw_of_not_paired h]

theorem ofReal_weight (hL : 0 < L) (hκ : 0 < κ) (ν : ℕ →₀ ℕ) :
    ENNReal.ofReal (weight L κ ν) =
      ν.prod (fun n a => ENNReal.ofReal (zeta' L κ n) ^ a) := by
  unfold weight Finsupp.prod
  have h := ENNReal.ofReal_prod_of_nonneg (s := ν.support)
    (f := fun a => zeta' L κ a ^ ν a) (fun n _ => pow_nonneg (zetaC_pos hL hκ _).le _)
  refine h.trans (Finset.prod_congr rfl (fun n _ => ?_))
  exact ENNReal.ofReal_pow (zetaC_pos hL hκ _).le _

theorem iSup_partial_inv (hL : 0 < L) (hκ : 0 < κ) :
    ⨆ J : ℕ, ∏ n ∈ Finset.range J, (1 - ENNReal.ofReal (zeta' L κ n))⁻¹ =
      ENNReal.ofReal (pStar L κ)⁻¹ := by
  set a : ℕ → ℝ := fun J => ∏ n ∈ Finset.range J, (1 - zeta' L κ n) with ha
  have hpos : ∀ J, 0 < a J := fun J =>
    Finset.prod_pos (fun n _ => one_sub_zetaC_pos hL hκ _)
  have hconv : Tendsto a atTop (𝓝 (pStar L κ)) := tendsto_partial_pStar hL hκ
  have hT : ∀ J, ∏ n ∈ Finset.range J, (1 - ENNReal.ofReal (zeta' L κ n))⁻¹ =
      ENNReal.ofReal (a J)⁻¹ := by
    intro J
    rw [ha]
    simp only
    rw [← Finset.prod_inv_distrib]
    have h := ENNReal.ofReal_prod_of_nonneg (s := Finset.range J)
      (f := fun n => (1 - zeta' L κ n)⁻¹)
      (fun n _ => inv_nonneg.2 (one_sub_zetaC_pos hL hκ _).le)
    rw [h]
    refine Finset.prod_congr rfl (fun n _ => ?_)
    have h1 : 0 < 1 - zeta' L κ n := one_sub_zetaC_pos hL hκ _
    have h2 : 0 ≤ zeta' L κ n := (zetaC_pos hL hκ _).le
    rw [ENNReal.ofReal_inv_of_pos h1, ENNReal.ofReal_sub _ h2, ENNReal.ofReal_one]
  simp_rw [hT]
  have hmono : Monotone (fun J => ENNReal.ofReal (a J)⁻¹) := by
    refine monotone_nat_of_le_succ (fun J => ?_)
    apply ENNReal.ofReal_le_ofReal
    apply inv_anti₀ (hpos _)
    rw [ha]
    simp only [Finset.prod_range_succ]
    have := zetaC_pos hL hκ (J.succPNat)
    have h2 := hpos J
    have : 1 - zeta' L κ J ≤ 1 := by unfold zeta'; linarith
    nlinarith [hpos J]
  have ht : Tendsto (fun J => ENNReal.ofReal (a J)⁻¹) atTop
      (𝓝 (ENNReal.ofReal (pStar L κ)⁻¹)) :=
    ENNReal.tendsto_ofReal (hconv.inv₀ (pStar_pos hL hκ).ne')
  exact tendsto_nhds_unique (tendsto_atTop_iSup hmono) ht

/-- Total mass of the paired law is `1` (in `ℝ≥0∞`). -/
theorem tsum_ofReal_pairedLaw (hL : 0 < L) (hκ : 0 < κ) :
    ∑' η : Config, ENNReal.ofReal (pairedLaw L κ η) = 1 := by
  have hsupp : Function.support (fun η : Config => ENNReal.ofReal (pairedLaw L κ η)) ⊆
      Set.range Phi := by
    intro η hη
    by_contra hc
    apply hη
    have : ¬ Paired η := fun h => hc (exists_Phi_of_paired η h)
    simp [pairedLaw_of_not_paired this]
  rw [← Phi_injective.tsum_eq hsupp]
  simp_rw [pairedLaw_Phi]
  have hz : ∀ n, ENNReal.ofReal (zeta' L κ n) < 1 := fun n => by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (zetaC_lt_one hL hκ _)
  have hmain := tsum_weight_eq_iSup (fun n => ENNReal.ofReal (zeta' L κ n)) hz
  simp_rw [ENNReal.ofReal_mul (pStar_pos hL hκ).le, ofReal_weight hL hκ]
  rw [ENNReal.tsum_mul_left, hmain, iSup_partial_inv hL hκ,
    ← ENNReal.ofReal_mul (pStar_pos hL hκ).le,
    mul_inv_cancel₀ (pStar_pos hL hκ).ne', ENNReal.ofReal_one]


theorem summable_pairedLaw (hL : 0 < L) (hκ : 0 < κ) : Summable (pairedLaw L κ) := by
  have h := ENNReal.summable_toReal (f := fun η : Config => ENNReal.ofReal (pairedLaw L κ η))
    (by rw [tsum_ofReal_pairedLaw hL hκ]; exact ENNReal.one_ne_top)
  refine h.congr (fun η => ?_)
  exact ENNReal.toReal_ofReal (pairedLaw_nonneg hL hκ η)

/-- The weights `P η` are nonnegative and sum (unconditionally) to `1` over `𝒞`. -/
theorem hasSum_pairedLaw (hL : 0 < L) (hκ : 0 < κ) : HasSum (pairedLaw L κ) 1 := by
  rw [(summable_pairedLaw hL hκ).hasSum_iff]
  have h := ENNReal.tsum_toReal_eq (f := fun η : Config => ENNReal.ofReal (pairedLaw L κ η))
    (fun _ => ENNReal.ofReal_ne_top)
  rw [tsum_ofReal_pairedLaw hL hκ] at h
  simp only [ENNReal.toReal_one] at h
  rw [h]
  exact (tsum_congr (fun η => ENNReal.toReal_ofReal (pairedLaw_nonneg hL hκ η))).symm

/-- The paired law as a probability mass function on `𝒞`. -/
def pairedPMF (hL : 0 < L) (hκ : 0 < κ) : PMF Config :=
  ⟨fun η => ENNReal.ofReal (pairedLaw L κ η),
    ENNReal.summable.hasSum_iff.2 (tsum_ofReal_pairedLaw hL hκ)⟩

theorem pairedPMF_apply (hL : 0 < L) (hκ : 0 < κ) (η : Config) :
    pairedPMF hL hκ η = ENNReal.ofReal (pairedLaw L κ η) := rfl

end Total

/-! ### The lemma `intr:plane:lem:pc-product` -/

/-- **Lemma `intr:plane:lem:pc-product` (R-D6286EDD).** For `L, κ > 0`:
`0 < ζ_j < 1` for every `j ≥ 1`; `∑_j ζ_j < ∞`; the infinite product `p_* = ∏_{j≥1}(1-ζ_j)`
converges (unconditionally, `HasProd`, and as the limit of the partial products) to a number with
`0 < p_* < 1`; and formula (pc-paired-law) defines a probability on `𝒞`: the weights are
nonnegative, sum to `1`, and are the point masses of a probability mass function on `𝒞`. -/
theorem pc_product {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) :
    (∀ j : ℕ+, 0 < zetaC L κ j ∧ zetaC L κ j < 1) ∧
    Summable (zetaC L κ) ∧
    HasProd (fun j : ℕ+ => 1 - zetaC L κ j) (pStar L κ) ∧
    Tendsto (fun J : ℕ => ∏ n ∈ Finset.range J, (1 - zetaC L κ n.succPNat)) atTop
      (𝓝 (pStar L κ)) ∧
    (0 < pStar L κ ∧ pStar L κ < 1) ∧
    ((∀ η : Config, 0 ≤ pairedLaw L κ η) ∧ HasSum (pairedLaw L κ) 1 ∧
      ∃ μ : PMF Config, ∀ η : Config, μ η = ENNReal.ofReal (pairedLaw L κ η)) :=
  ⟨fun j => ⟨zetaC_pos hL hκ j, zetaC_lt_one hL hκ j⟩, summable_zetaC hL hκ,
    hasProd_pStar hL hκ, tendsto_partial_pStar hL hκ, ⟨pStar_pos hL hκ, pStar_lt_one hL hκ⟩,
    pairedLaw_nonneg hL hκ, hasSum_pairedLaw hL hκ, pairedPMF hL hκ, fun _ => rfl⟩

/-- The same as a probability measure on `𝒞` (discrete σ-algebra `⊤`) with mass function `P`. -/
theorem pc_product_measure {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) :
    ∃ μ : @MeasureTheory.Measure Config ⊤,
      @MeasureTheory.IsProbabilityMeasure Config ⊤ μ ∧
      ∀ η : Config, μ {η} = ENNReal.ofReal (pairedLaw L κ η) := by
  let _ : MeasurableSpace Config := ⊤
  refine ⟨(pairedPMF hL hκ).toMeasure, inferInstance, fun η => ?_⟩
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton η)]
  rfl

end

end QuantumNLS.PairedPlaneLaw

#print axioms QuantumNLS.PairedPlaneLaw.pc_product
#print axioms QuantumNLS.PairedPlaneLaw.pc_product_measure
#print axioms QuantumNLS.PairedPlaneLaw.tsum_ofReal_pairedLaw
#print axioms QuantumNLS.PairedPlaneLaw.hasSum_pairedLaw
#print axioms QuantumNLS.PairedPlaneLaw.h_sq_sub_omega_sq
#print axioms QuantumNLS.PairedPlaneLaw.zetaC_le
#print axioms QuantumNLS.PairedPlaneLaw.summable_zetaC
#print axioms QuantumNLS.PairedPlaneLaw.hasProd_pStar
#print axioms QuantumNLS.PairedPlaneLaw.tendsto_partial_pStar
#print axioms QuantumNLS.PairedPlaneLaw.pStar_pos
#print axioms QuantumNLS.PairedPlaneLaw.pStar_lt_one
#print axioms QuantumNLS.PairedPlaneLaw.pairedLaw_Phi
#print axioms QuantumNLS.PairedPlaneLaw.exists_Phi_of_paired
#print axioms QuantumNLS.PairedPlaneLaw.tsum_weight_eq_iSup
#print axioms QuantumNLS.PairedPlaneLaw.tsum_fin_geometric
#print axioms QuantumNLS.PairedPlaneLaw.iSup_partial_inv
