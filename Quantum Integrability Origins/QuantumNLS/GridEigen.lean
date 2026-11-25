import Mathlib
import QuantumNLS.HaarEigenbasis

/-!
# R-E67FE3C4 item 1: closed form of the grid eigenvalues `Λ̃_k(ωm)` of `K_{r,ωm}`

Source: `source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:365-420` (`QG:prop:haar-grid-weights`), its proof:
for even `r` the grid eigenvalue is `2 i^r/(r! ω^r) Π_j (m − k_j − 1/2)^{-1}`; for odd `r` it vanishes unless
`m` is one of the distinct `k_j`, and at `m = k_j` it equals `−i^{r+1} L/(r! ω^{r−1}) Π_{ℓ≠j} (k_j−k_ℓ)^{-1}`.

Realized objects used read-only (`HaarEigenbasis`, accepted R-F611926F):
* `lamTilde L n k z` (`Λ̃_k(z) = ⟨B_k, K_{r,z} B_k⟩`, `r = n+1`), continuous, equal to the printed `Lam` off the
  poles (`lamTilde_eq`), and `K_{r,z} B_k = Λ̃_k(z) B_k` for every `z` (`eigen_all`);
* `Lam`, `lamFun`, `deltaR`, `omegaL` (`ω = 2π/L`), and the index type `Idx (n+1)` (strictly increasing `k`).

Statement: the closed form of `lamTilde` at the grid points `z = ω m`, `m ∈ ℤ`, split by the parity of `r`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
open QuantumNLS.HaarEigenbasis QuantumNLS.HaarSlaterBasis QuantumNLS.HaarKernelFactorizationSym

namespace QuantumNLS.GridEigen

variable (L : ℝ) [Fact (0 < L)]

/-- The grid point `ω m`, as a complex number. -/
def gridPt (m : ℤ) : ℂ := ((omegaL L * (m : ℝ) : ℝ) : ℂ)

theorem omegaL_pos : 0 < omegaL L := by
  unfold omegaL
  have := (Fact.out : (0 : ℝ) < L)
  positivity

/-- `e^{iωmL} = 1` at every grid point. -/
theorem exp_grid (m : ℤ) : Complex.exp (Complex.I * gridPt L m * L) = 1 := by
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : (0 : ℝ) < L).ne'
  have h : Complex.I * gridPt L m * L = (m : ℂ) * (2 * Real.pi * Complex.I) := by
    unfold gridPt omegaL
    push_cast
    field_simp
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- Near a grid point, away from it, `e^{izL} ≠ 1`. -/
theorem exp_ne_one_near (m : ℤ) : ∀ᶠ z in 𝓝[≠] (gridPt L m), Complex.exp (Complex.I * z * L) ≠ 1 := by
  have hω := omegaL_pos L
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : (0 : ℝ) < L).ne'
  have hloc : ∀ᶠ z in 𝓝 (gridPt L m), z ≠ gridPt L m → Complex.exp (Complex.I * z * L) ≠ 1 := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨omegaL L / 2, by positivity, fun z hz hne h1 => ?_⟩
    obtain ⟨t, ht⟩ := Complex.exp_eq_one_iff.1 h1
    have h2 : z * (L : ℂ) = (t : ℂ) * (2 * Real.pi) := by
      apply mul_left_cancel₀ Complex.I_ne_zero
      linear_combination ht
    have hz' : z = ((omegaL L * (t : ℝ) : ℝ) : ℂ) := by
      apply mul_right_cancel₀ hL
      have hcast : ((omegaL L * (t : ℝ) : ℝ) : ℂ) * (L : ℂ) = (t : ℂ) * (2 * Real.pi) := by
        unfold omegaL
        push_cast
        field_simp
      rw [hcast, h2]
    have hd : ‖z - gridPt L m‖ = omegaL L * |((t : ℝ) - (m : ℝ))| := by
      rw [hz']
      unfold gridPt
      rw [← Complex.ofReal_sub, ← mul_sub, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos hω]
    have hdist : ‖z - gridPt L m‖ < omegaL L / 2 := by
      rw [← dist_eq_norm]
      exact hz
    rw [hd] at hdist
    have hlt : |((t : ℝ) - (m : ℝ))| < 1 / 2 := by
      by_contra hc
      push_neg at hc
      nlinarith
    have hlt' : |(t : ℤ) - m| < 1 := by
      have : ((|(t : ℤ) - m| : ℤ) : ℝ) < 1 := by
        rw [Int.cast_abs]; push_cast; linarith
      exact_mod_cast this
    have htm : t = m := by
      rw [abs_lt] at hlt'
      omega
    apply hne
    rw [hz', htm]
    rfl
  exact eventually_nhdsWithin_iff.2 (hloc.mono fun z hz hz' => hz hz')

/-- **Even `r`** (`n` odd, `δ_r = 1/2`, `ρ_r = −1`): the grid eigenvalue is `2 i^r/(r! ω^r) Π_j (m − k_j − 1/2)^{-1}`
(`QG:prop:haar-grid-weights`, even case). -/
theorem lamTilde_grid_even {n : ℕ} (hn : Odd n) (k : Idx (n + 1)) (m : ℤ) :
    lamTilde L n k (gridPt L m) =
      2 * Complex.I ^ (n + 1) / (((n + 1).factorial : ℂ) * (omegaL L : ℂ) ^ (n + 1)) *
        ∏ i, 1 / ((m : ℂ) - (k.1 i : ℂ) - 1 / 2) := by
  have hω := omegaL_pos L
  have hωC : (omegaL L : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
  have hδ : deltaR (n + 1) = 1 / 2 := by
    unfold deltaR; rw [if_pos hn.add_one]
  have hq : (-1 : ℂ) ^ n * Complex.exp (Complex.I * gridPt L m * L) ≠ 1 := by
    rw [exp_grid, mul_one, hn.neg_one_pow]; norm_num
  rw [lamTilde_eq L n (gridPt L m) hq k]
  unfold Lam
  rw [exp_grid, mul_one, hn.neg_one_pow]
  have hfac : ∀ i, lamFun L n (gridPt L m) (k.1 i) =
      (Complex.I / (omegaL L : ℂ)) * (1 / ((m : ℂ) - (k.1 i : ℂ) - 1 / 2)) := by
    intro i
    unfold lamFun
    rw [hδ, div_mul_div_comm, mul_one]
    congr 1
    unfold gridPt
    push_cast
    ring
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  ring

/-- Odd `r`, grid point not among the `k_j`: the eigenvalue vanishes (`QG:prop:haar-grid-weights`, odd case). -/
theorem lamTilde_grid_odd_zero {n : ℕ} (hn : Even n) (k : Idx (n + 1)) (m : ℤ) (hm : ∀ i, k.1 i ≠ m) :
    lamTilde L n k (gridPt L m) = 0 := by
  have hω := omegaL_pos L
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : (0 : ℝ) < L).ne'
  have hδ0 : deltaR (n + 1) = 0 := by
    unfold deltaR; rw [if_neg (Nat.not_even_iff_odd.mpr hn.add_one)]
  set g := gridPt L m with hg
  -- the eigenvalue function off the grid, with the signs simplified (n even)
  set Lamf : ℂ → ℂ := fun z => (1 - Complex.exp (Complex.I * z * L)) / ((n + 1).factorial : ℂ) *
    ∏ i, Complex.I / (z - ((omegaL L * ((k.1 i : ℝ) + 0) : ℝ) : ℂ)) with hLamf
  have hLam_eq : ∀ z, Lam L n z k.1 = Lamf z := by
    intro z
    unfold Lam lamFun
    rw [hδ0, hn.neg_one_pow]
    simp only [hLamf, one_mul, add_zero]
  -- the limit of Lamf along the punctured neighbourhood is 0
  have hne : ∀ i, g - ((omegaL L * ((k.1 i : ℝ) + 0) : ℝ) : ℂ) ≠ 0 := by
    intro i h0
    apply hm i
    have hgm : g = ((omegaL L * (m : ℝ) : ℝ) : ℂ) := rfl
    have h1 : ((omegaL L * ((k.1 i : ℝ) + 0) : ℝ) : ℂ) = ((omegaL L * (m : ℝ) : ℝ) : ℂ) := by
      rw [hgm] at h0
      exact (sub_eq_zero.1 h0).symm
    have h2 : omegaL L * ((k.1 i : ℝ) + 0) = omegaL L * (m : ℝ) := by
      exact_mod_cast h1
    have h3 : (k.1 i : ℝ) = (m : ℝ) := by
      have := mul_left_cancel₀ hω.ne' (h2.trans (by ring) : omegaL L * ((k.1 i : ℝ) + 0) = omegaL L * (m : ℝ))
      linarith
    exact_mod_cast h3
  have hLim : Tendsto Lamf (𝓝[≠] g) (𝓝 0) := by
    have hF : Tendsto (fun z : ℂ => 1 - Complex.exp (Complex.I * z * L)) (𝓝 g) (𝓝 0) := by
      have hc : Continuous (fun z : ℂ => 1 - Complex.exp (Complex.I * z * L)) := by fun_prop
      have := hc.tendsto g
      rw [hg] at this ⊢
      simpa [exp_grid] using this
    have hP : Tendsto (fun z : ℂ => ∏ i, Complex.I / (z - ((omegaL L * ((k.1 i : ℝ) + 0) : ℝ) : ℂ)))
        (𝓝 g) (𝓝 (∏ i, Complex.I / (g - ((omegaL L * ((k.1 i : ℝ) + 0) : ℝ) : ℂ)))) := by
      apply tendsto_finsetProd
      intro i _
      exact tendsto_const_nhds.div (tendsto_id.sub tendsto_const_nhds) (hne i)
    have hprod := (hF.div_const ((n + 1).factorial : ℂ)).mul hP
    have hlim : Tendsto Lamf (𝓝 g) (𝓝 (0 / ((n + 1).factorial : ℂ) *
        ∏ i, Complex.I / (g - ((omegaL L * ((k.1 i : ℝ) + 0) : ℝ) : ℂ)))) := by
      simpa [hLamf] using hprod
    rw [zero_div, zero_mul] at hlim
    exact hlim.mono_left nhdsWithin_le_nhds
  -- lamTilde is continuous and equals Lamf off the grid
  have hcont : Tendsto (lamTilde L n k) (𝓝[≠] g) (𝓝 (lamTilde L n k g)) :=
    ((lamTilde_continuous L n k).continuousAt (x := g)).tendsto.mono_left nhdsWithin_le_nhds
  have hcongr : (lamTilde L n k) =ᶠ[𝓝[≠] g] Lamf := by
    filter_upwards [exp_ne_one_near L m] with z hz
    have hq : (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) ≠ 1 := by
      rw [hn.neg_one_pow, one_mul]; exact hz
    rw [lamTilde_eq L n z hq k, hLam_eq z]
  have h2 : Tendsto (lamTilde L n k) (𝓝[≠] g) (𝓝 0) := hLim.congr' hcongr.symm
  exact tendsto_nhds_unique hcont h2

/-- Odd `r`, grid point `m = k_j`: the removable limit gives `−i^{r+1} L/(r! ω^{r−1}) Π_{ℓ≠j} (k_j−k_ℓ)^{-1}`
(`QG:prop:haar-grid-weights`, odd case; `r − 1 = n`). -/
theorem lamTilde_grid_odd_pole {n : ℕ} (hn : Even n) (k : Idx (n + 1)) (m : ℤ) (j : Fin (n + 1))
    (hj : k.1 j = m) :
    lamTilde L n k (gridPt L m) =
      -(Complex.I ^ (n + 2) * (L : ℂ)) / (((n + 1).factorial : ℂ) * (omegaL L : ℂ) ^ n) *
        ∏ i ∈ Finset.univ.erase j, 1 / ((k.1 j : ℂ) - (k.1 i : ℂ)) := by
  have hω := omegaL_pos L
  have hωC : (omegaL L : ℂ) ≠ 0 := by exact_mod_cast hω.ne'
  have hδ0 : deltaR (n + 1) = 0 := by
    unfold deltaR; rw [if_neg (Nat.not_even_iff_odd.mpr hn.add_one)]
  set g := gridPt L m with hg
  set c : Fin (n + 1) → ℂ := fun i => ((omegaL L * ((k.1 i : ℝ) + 0) : ℝ) : ℂ) with hc
  have hgc : c j = g := by
    rw [hc, hg]; simp only [hj, gridPt, add_zero]
  set F : ℂ → ℂ := fun z => 1 - Complex.exp (Complex.I * z * L) with hF
  set Hf : ℂ → ℂ := fun z => (Complex.I / ((n + 1).factorial : ℂ)) *
    ∏ i ∈ Finset.univ.erase j, Complex.I / (z - c i) with hHf
  have hFg : F g = 0 := by
    rw [hF]; simp only; rw [exp_grid]; ring
  -- the factorisation off the grid
  have hgj : g = ((omegaL L * (k.1 j : ℝ) : ℝ) : ℂ) := by
    rw [hg]; unfold gridPt; rw [← hj]
  have hfactor : ∀ z, z ≠ g → Lam L n z k.1 = (z - g)⁻¹ * (1 - Complex.exp (Complex.I * z * L)) * Hf z := by
    intro z hz
    have hzg : z - g ≠ 0 := sub_ne_zero.mpr hz
    unfold Lam lamFun
    rw [hδ0, hn.neg_one_pow, one_mul]
    simp only [add_zero]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), ← hgj, hHf]
    simp only [hc, add_zero]
    field_simp
  -- the derivative of F at g
  have hderiv : HasDerivAt F (-(Complex.exp (Complex.I * g * L) * (Complex.I * 1 * L))) g := by
    have h1 : HasDerivAt (fun z : ℂ => Complex.I * z * L) (Complex.I * 1 * L) g :=
      ((hasDerivAt_id g).const_mul Complex.I).mul_const (L : ℂ)
    exact (h1.cexp).const_sub 1
  have hF' : -(Complex.exp (Complex.I * g * L) * (Complex.I * 1 * L)) = -(Complex.I * L) := by
    rw [hg, exp_grid]; ring
  have hslope : Tendsto (slope F g) (𝓝[≠] g) (𝓝 (-(Complex.I * L))) := by
    rw [← hF']
    exact hasDerivAt_iff_tendsto_slope.1 hderiv
  -- continuity of H at g: the denominators g − c_i are nonzero for i ≠ j
  have hne : ∀ i ∈ Finset.univ.erase j, g - c i ≠ 0 := by
    intro i hi h0
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    apply hij
    apply k.2.injective
    have h1 : c i = c j := by rw [hgc]; exact (sub_eq_zero.1 h0).symm
    have h2 : omegaL L * ((k.1 i : ℝ) + 0) = omegaL L * ((k.1 j : ℝ) + 0) := by
      have := congrArg (fun w : ℂ => w) h1
      simp only [hc] at this
      exact_mod_cast this
    have h3 := mul_left_cancel₀ hω.ne' h2
    simp only [add_zero] at h3
    exact_mod_cast h3
  have hHtend : Tendsto Hf (𝓝 g) (𝓝 (Hf g)) := by
    apply Tendsto.const_mul
    apply tendsto_finsetProd
    intro i hi
    exact tendsto_const_nhds.div (tendsto_id.sub tendsto_const_nhds) (hne i hi)
  -- the eigenvalue function tends to `(−iL) · H(g)`
  have key : ∀ z, z ≠ g → Lam L n z k.1 = slope F g z * Hf z := by
    intro z hz
    rw [hfactor z hz, slope_def_field, hFg, sub_zero]
    simp only [hF]
    ring
  have hLamf : Tendsto (fun z => Lam L n z k.1) (𝓝[≠] g) (𝓝 ((-(Complex.I * L)) * Hf g)) := by
    have hprod := hslope.mul (hHtend.mono_left nhdsWithin_le_nhds)
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (key z (Set.mem_compl_singleton_iff.mp hz)).symm
  -- lamTilde agrees with Lam on the punctured neighbourhood (`e^{izL} ≠ 1` there)
  have hcont : Tendsto (lamTilde L n k) (𝓝[≠] g) (𝓝 (lamTilde L n k g)) :=
    ((lamTilde_continuous L n k).continuousAt (x := g)).tendsto.mono_left nhdsWithin_le_nhds
  have hcongr : (lamTilde L n k) =ᶠ[𝓝[≠] g] fun z => Lam L n z k.1 := by
    filter_upwards [exp_ne_one_near L m] with z hz
    have hq : (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) ≠ 1 := by
      rw [hn.neg_one_pow, one_mul]; exact hz
    rw [lamTilde_eq L n z hq k]
  have h2 : Tendsto (lamTilde L n k) (𝓝[≠] g) (𝓝 ((-(Complex.I * L)) * Hf g)) :=
    hLamf.congr' hcongr.symm
  have hvalue : lamTilde L n k g = (-(Complex.I * L)) * Hf g := tendsto_nhds_unique hcont h2
  -- evaluate `H(g)` using `g − c_i = ω(k_j − k_i)`
  have hgi : ∀ i, g - c i = (omegaL L : ℂ) * ((k.1 j : ℂ) - (k.1 i : ℂ)) := by
    intro i
    rw [hc, hg]
    simp only [gridPt, add_zero]
    rw [← hj]
    push_cast
    ring
  have hprodeq : ∏ i ∈ Finset.univ.erase j, Complex.I / (g - c i) =
      (Complex.I / (omegaL L : ℂ)) ^ n * ∏ i ∈ Finset.univ.erase j, 1 / ((k.1 j : ℂ) - (k.1 i : ℂ)) := by
    have hfac : ∀ i ∈ Finset.univ.erase j, Complex.I / (g - c i) =
        (Complex.I / (omegaL L : ℂ)) * (1 / ((k.1 j : ℂ) - (k.1 i : ℂ))) := by
      intro i _
      rw [hgi i, div_mul_div_comm, mul_one]
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
      Nat.add_sub_cancel]
  have hHg : Hf g = (Complex.I / ((n + 1).factorial : ℂ)) *
      ((Complex.I / (omegaL L : ℂ)) ^ n * ∏ i ∈ Finset.univ.erase j, 1 / ((k.1 j : ℂ) - (k.1 i : ℂ))) := by
    rw [hHf]
    simp only
    rw [hprodeq]
  rw [hvalue, hHg]
  ring

end QuantumNLS.GridEigen

#print axioms QuantumNLS.GridEigen.exp_grid
#print axioms QuantumNLS.GridEigen.exp_ne_one_near
#print axioms QuantumNLS.GridEigen.lamTilde_grid_even
#print axioms QuantumNLS.GridEigen.lamTilde_grid_odd_zero
#print axioms QuantumNLS.GridEigen.lamTilde_grid_odd_pole
