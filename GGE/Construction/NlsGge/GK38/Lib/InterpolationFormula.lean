import NlsGge.GK38.Lib.InterpolationTail
import NlsGge.GK38.Lib.InterpolationContour

/-!
# L4b, part 6: the Hermite remainder formula for the interpolation lemma

Source: proof of Grébert–Kappeler book Lemma F.4 (GKP Lemma 22.4).  The book applies the residue
theorem to `g(λ) = φ(λ)/((λ - z) ψ(λ))` on the circle `C_N` (`ψ = -∏ (σ_m - λ)/π_m`).  Here the
residues are computed by the Lagrange partial-fraction identity (`circle_divided_difference`)
applied to `Φ_N = φ/T_N`, where `ψ = P_N T_N` (`psiProd_eq`) and `T_N` is holomorphic and zero-free
inside `C_N` (`tail_diff_ne`).  The result is the exact finite identity

`φ(z) - Σ_{|n|≤N} φ(σ_n) c_n(z) = ψ(z) · (1/2πi) ∮_{C_N} φ(λ)/(ψ(λ)(λ - z)) dλ`

(`hermite_remainder`), where `c_n(z) = ∏'[sym]_{m≠n} (σ_m - z)/(σ_m - σ_n)` is the infinite
Lagrange coefficient; its multipliability and its value `c_N,n(z) T_N(z)/T_N(σ_n)` come from the
tail products (`hasProd_cfam`).  Injectivity of `σ` is used to make the nodes distinct.
-/

set_option autoImplicit false

open Filter Topology SummationFilter Metric Complex

namespace NlsGge.GK38.Lib

noncomputable section

/-- The `m`-th factor of the Lagrange coefficient `c_n(z)`. -/
def cfam (σ : ℤ → ℂ) (z : ℂ) (n m : ℤ) : ℂ :=
  if m = n then 1 else (σ m - z) / (σ m - σ n)

/-- The finite Lagrange coefficient over the window `{-N,…,N}`. -/
def cFin (σ : ℤ → ℂ) (N : ℕ) (z : ℂ) (n : ℤ) : ℂ :=
  ∏ m ∈ (win N).erase n, (σ m - z) / (σ m - σ n)

theorem prod_cfam_win (σ : ℤ → ℂ) (N : ℕ) (z : ℂ) {n : ℤ} (hn : n ∈ win N) {M : ℕ} (hNM : N ≤ M) :
    ∏ m ∈ win M, cfam σ z n m
      = cFin σ N z n * ((∏ m ∈ win M, tailFam σ N z m) / ∏ m ∈ win M, tailFam σ N (σ n) m) := by
  rw [prod_win_split _ hNM, prod_win_tail σ N z hNM, prod_win_tail σ N (σ n) hNM]
  congr 1
  · rw [← Finset.prod_erase _ (show cfam σ z n n = 1 by simp [cfam])]
    refine Finset.prod_congr rfl fun m hm => ?_
    simp [cfam, Finset.ne_of_mem_erase hm]
  · rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun m hm => ?_
    have hmn : m ≠ n := by
      rintro rfl; exact (Finset.mem_sdiff.mp hm).2 hn
    have hπ : (piN m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (piN_ne_zero m)
    simp only [cfam, hmn, ite_false, prodFactor]
    rw [div_div_div_cancel_right₀ hπ]

/-- Multipliability of the Lagrange coefficient, and its value in terms of the tail products. -/
theorem hasProd_cfam {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) {N : ℕ} {n : ℤ}
    (z : ℂ) (hn : n ∈ win N) (hT : tailProd σ N (σ n) ≠ 0) :
    HasProd (cfam σ z n) (cFin σ N z n * (tailProd σ N z / tailProd σ N (σ n))) (symmetricIcc ℤ) := by
  rw [hasProd_symmetricIcc_iff]
  have h1 := hasProd_tail hσ N z
  have h2 := hasProd_tail hσ N (σ n)
  rw [hasProd_symmetricIcc_iff] at h1 h2
  have h3 := (h1.div h2 hT).const_mul (cFin σ N z n)
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop N] with M hM
  simp only [prod_Icc_eq_prod_win]
  exact (prod_cfam_win σ N z hn hM).symm

/-! ### Finite algebra for the nodes -/

section Algebra

variable {σ : ℤ → ℂ}

theorem prod_nodes (hinj : Function.Injective σ) (I : Finset ℤ) (z : ℂ) (hz : ∀ m ∈ I, σ m ≠ z)
    (l : ℂ) :
    ∏ a ∈ insert z (I.image σ), (l - a) = (l - z) * ∏ m ∈ I, (l - σ m) := by
  have hnot : z ∉ I.image σ := by
    intro h
    obtain ⟨m, hm, e⟩ := Finset.mem_image.mp h
    exact hz m hm e
  rw [Finset.prod_insert hnot, Finset.prod_image fun a _ b _ h => hinj h]

theorem sum_nodes (hinj : Function.Injective σ) (I : Finset ℤ) (z : ℂ) (hz : ∀ m ∈ I, σ m ≠ z)
    (Φ : ℂ → ℂ) :
    ∑ a ∈ insert z (I.image σ), Φ a / ∏ b ∈ (insert z (I.image σ)).erase a, (a - b)
      = Φ z / ∏ m ∈ I, (z - σ m)
        + ∑ n ∈ I, Φ (σ n) / ((σ n - z) * ∏ m ∈ I.erase n, (σ n - σ m)) := by
  classical
  have hnot : z ∉ I.image σ := by
    intro h
    obtain ⟨m, hm, e⟩ := Finset.mem_image.mp h
    exact hz m hm e
  rw [Finset.sum_insert hnot, Finset.erase_insert hnot, Finset.prod_image fun a _ b _ h => hinj h]
  congr 1
  rw [Finset.sum_image fun a _ b _ h => hinj h]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hne : z ≠ σ n := (hz n hn).symm
  have hz2 : z ∉ (I.image σ).erase (σ n) := fun h => hnot (Finset.mem_of_mem_erase h)
  rw [Finset.erase_insert_of_ne hne, Finset.prod_insert hz2, ← Finset.image_erase hinj,
    Finset.prod_image fun a _ b _ h => hinj h]

/-- `P(z)/((σ_n - z) ∏_{m≠n}(σ_n - σ_m)) = - ∏_{m≠n} (σ_m - z)/(σ_m - σ_n)`. -/
theorem lagrange_coeff_eq (I : Finset ℤ) {n : ℤ} (hn : n ∈ I) (z : ℂ) (hz : σ n ≠ z) :
    (∏ m ∈ I, (z - σ m)) / ((σ n - z) * ∏ m ∈ I.erase n, (σ n - σ m))
      = -∏ m ∈ I.erase n, (σ m - z) / (σ m - σ n) := by
  have hsz : σ n - z ≠ 0 := sub_ne_zero.mpr hz
  rw [← Finset.mul_prod_erase I (fun m => z - σ m) hn]
  have e : ∏ m ∈ I.erase n, (σ m - z) / (σ m - σ n)
      = ∏ m ∈ I.erase n, (z - σ m) / (σ n - σ m) := by
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [← neg_sub z, ← neg_sub (σ n), neg_div_neg_eq]
  rw [e, Finset.prod_div_distrib]
  have : (z - σ n) = -(σ n - z) := by ring
  rw [this]
  field_simp

end Algebra

end

end NlsGge.GK38.Lib
