import NlsGge.Spectral.ActualPhysicalUnitHalfTraceGeneralRescaling35V3
import NlsGge.Spectral.ActualPhysicalInteractionDysonIdentification32V2
import NlsGge.Spectral.ActualPhysicalInteractionStripMajorant36V3
import NlsGge.Spectral.ActualInteractionDysonParity32V1
import NlsGge.Spectral.GenericRoughDysonAECongruence36V4
import NlsGge.Batch37.ActualPhysicalVacuumInteractionHalfTrace37V2
import NlsGge.Batch37.ActualPhysicalCouplingCommonFactorialMajorant37V1
import NlsGge.Batch37.ActualPhysicalDyson00FixedOrderFourierDecay37V1
import NlsGge.Batch37.ActualPhysicalDyson11FixedOrderFourierDecay37V2
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis
open Filter
open CumulativePowerV3

/-- Abstract uniform tail lemma: a family of series with a common summable
majorant, whose every fixed term is eventually uniformly small along `l`,
is eventually uniformly small. -/
theorem e02_uniform_tsum_small38 {α β : Type*} (l : Filter α)
    (F : α → β → ℕ → ℂ) (g : ℕ → ℝ) (hg : Summable g)
    (hb : ∀ x p n, ‖F x p n‖ ≤ g n)
    (hlim : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, ∀ p, ‖F x p n‖ < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, ∀ p, ‖∑' n, F x p n‖ < ε := by
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨M, hM⟩ := ((tendsto_sum_nat_add g).eventually
    (gt_mem_nhds hε3)).exists
  have hfin : ∀ᶠ x in l, ∀ n ∈ Finset.range M, ∀ p,
      ‖F x p n‖ < ε / (3 * ((M : ℝ) + 1)) := by
    rw [Filter.eventually_all_finset]
    intro n _
    exact hlim n _ (by positivity)
  filter_upwards [hfin] with x hx p
  have hsum : Summable (fun n => F x p n) :=
    Summable.of_norm_bounded hg (hb x p)
  rw [← hsum.sum_add_tsum_nat_add M]
  have hg' : Summable (fun k => g (k + M)) := (summable_nat_add_iff M).2 hg
  have htail : ‖∑' k, F x p (k + M)‖ ≤ ∑' k, g (k + M) :=
    tsum_of_norm_bounded hg'.hasSum (fun k => hb x p (k + M))
  have hhead : ‖∑ n ∈ Finset.range M, F x p n‖ ≤ ε / 3 := by
    calc ‖∑ n ∈ Finset.range M, F x p n‖
        ≤ ∑ n ∈ Finset.range M, ‖F x p n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range M, ε / (3 * ((M : ℝ) + 1)) :=
          Finset.sum_le_sum (fun n hn => (hx n hn p).le)
      _ = (M : ℝ) * (ε / (3 * ((M : ℝ) + 1))) := by
          simp
      _ ≤ ε / 3 := by
          have h1 : (M : ℝ) * (ε / (3 * ((M : ℝ) + 1))) =
              ε / 3 * ((M : ℝ) / ((M : ℝ) + 1)) := by
            field_simp
          rw [h1]
          have h2 : (M : ℝ) / ((M : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          nlinarith
  calc ‖∑ n ∈ Finset.range M, F x p n + ∑' k, F x p (k + M)‖
      ≤ ‖∑ n ∈ Finset.range M, F x p n‖ + ‖∑' k, F x p (k + M)‖ := norm_add_le _ _
    _ < ε := by linarith


/-- Exact algebraic identity for the coupled half trace minus cosine, after
splitting off the (identity) zeroth Dyson term.  Summability is proved from the
actual bounded-height majorant before the zeroth term is split off. -/
theorem e02_identity38 (u : PhysicalL2) (τ : ℝ) (z : ℂ) (Y₀ : ℝ)
    (hY₀ : 0 ≤ Y₀) (hz : 0 ≤ z.im) (hz' : z.im ≤ Y₀) :
    Complex.exp (Complex.I*z) *
        (actualPhysicalUnitHalfTrace32 ((τ : ℂ) • u) z - Complex.cos z) =
      ((∑' n : ℕ, genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32
            (fun s => naturalPhysicalCoverL2 ((τ : ℂ) • u) (s : SpectralCircle)) z)
          (n+1) 1 0 0) +
        Complex.exp (2*Complex.I*z) * (∑' n : ℕ, genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32
            (fun s => naturalPhysicalCoverL2 ((τ : ℂ) • u) (s : SpectralCircle)) z)
          (n+1) 1 1 1)) / 2 := by
  have hst := actualPhysicalInteractionState_unit_eq_Dyson32 ((τ : ℂ) • u) z
  have hres := actualPhysicalUnitHalfTrace_generalRescaling35 ((τ : ℂ) • u) z
  rw [hst] at hres
  set B := actualZsInteractionCoefficient32
    (fun s => naturalPhysicalCoverL2 ((τ : ℂ) • u) (s : SpectralCircle)) z with hB
  have hs : ∀ i j : Fin 2, Summable (fun n : ℕ => genericRoughMatrixDysonTerm32 B n 1 i j) :=
    fun i j => actualPhysicalInteractionDysonTerm_summable_boundedHeight36V3
      ((τ : ℂ) • u) z Y₀ hY₀ hz hz' 1 (by norm_num) i j
  have h00 : (genericRoughMatrixDysonTsum32 B 1) 0 0 =
      1 + ∑' n : ℕ, genericRoughMatrixDysonTerm32 B (n+1) 1 0 0 := by
    change (∑' n : ℕ, genericRoughMatrixDysonTerm32 B n 1 0 0) = _
    rw [(hs 0 0).tsum_eq_zero_add]
    simp [genericRoughMatrixDysonTerm32]
  have h11 : (genericRoughMatrixDysonTsum32 B 1) 1 1 =
      1 + ∑' n : ℕ, genericRoughMatrixDysonTerm32 B (n+1) 1 1 1 := by
    change (∑' n : ℕ, genericRoughMatrixDysonTerm32 B n 1 1 1) = _
    rw [(hs 1 1).tsum_eq_zero_add]
    simp [genericRoughMatrixDysonTerm32]
  rw [h00, h11] at hres
  have hneg : Complex.exp (Complex.I*z)*Complex.exp (-z*Complex.I) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    ring
  have hdouble : Complex.exp (Complex.I*z)*Complex.exp (z*Complex.I) =
      Complex.exp (2*Complex.I*z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hcos : Complex.exp (Complex.I*z)*Complex.cos z =
      (1+Complex.exp (2*Complex.I*z))/2 := by
    calc
      _ = (Complex.exp (Complex.I*z)*Complex.exp (z*Complex.I)+
        Complex.exp (Complex.I*z)*Complex.exp (-z*Complex.I))/2 := by
        simp only [Complex.cos, mul_div, mul_add, neg_mul]
      _ = _ := by rw [hdouble, hneg]; ring
  rw [mul_sub, hres, hcos]
  ring


/-- Real coupling in `[0,1]` does not increase the norm of any fixed-order
Dyson entry at unit endpoint. -/
theorem e02_coupled_entry_norm_le38 (u : PhysicalL2) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (z : ℂ) (m : ℕ) (i j : Fin 2) :
    ‖genericRoughMatrixDysonTerm32
      (actualZsInteractionCoefficient32
        (fun s => naturalPhysicalCoverL2 ((τ : ℂ) • u) (s : SpectralCircle)) z) m 1 i j‖ ≤
    ‖genericRoughMatrixDysonTerm32
      (actualZsInteractionCoefficient32
        (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)) z) m 1 i j‖ := by
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j)
    (actualPhysicalInteractionDysonTerm_realCoupling36V4 u τ z m 1 (by norm_num))
  simp only [Matrix.smul_apply, smul_eq_mul] at he
  have hnorm : ‖(τ : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ.1] using hτ.2
  have hp : ‖(τ : ℂ)^m‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hnorm
  rw [he, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hp

theorem e02_norm_exp_two_I38 (x Y : ℝ) :
    ‖Complex.exp (2*Complex.I*((x : ℂ)+Complex.I*(Y : ℂ)))‖ = Real.exp (-2*Y) := by
  rw [Complex.norm_exp]
  congr 1
  simp

theorem e02_norm_exp_I38 (x Y : ℝ) :
    ‖Complex.exp (Complex.I*((x : ℂ)+Complex.I*(Y : ℂ)))‖ = Real.exp (-Y) := by
  rw [Complex.norm_exp]
  congr 1
  simp

theorem e02_majorant_summable38 (C : ℝ) :
    Summable (fun n : ℕ => C ^ (n+1) / ((n+1).factorial : ℝ)) :=
  (summable_nat_add_iff 1).2 (Real.summable_pow_div_factorial C)

/-- Fixed-order (positive order) decay of the coupled 00 Dyson entries, uniform in
coupling in `[0,1]` and height in `[0,Y₀]`. -/
theorem e02_fixedOrder00_coupled38 (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in cocompact ℝ,
      ∀ p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀,
        ‖genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32
            (fun s => naturalPhysicalCoverL2 (((p.1 : ℝ) : ℂ) • u) (s : SpectralCircle))
            ((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))) m 1 0 0‖ < ε := by
  intro ε hε
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' m
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    filter_upwards [actualPhysicalDyson00_fixedOrder_uniformFourierDecay37V1 u Y₀ hY₀ k' ε hε]
      with x hx p
    rw [hk]
    have h1 := hx (⟨1, by norm_num⟩, p.2)
    exact lt_of_le_of_lt (e02_coupled_entry_norm_le38 u p.1 p.1.2 _ _ 0 0) h1
  · filter_upwards with x p
    have h := (actualInteractionDyson_odd_diagonal_zero32
      (fun s => naturalPhysicalCoverL2 (((p.1 : ℝ) : ℂ) • u) (s : SpectralCircle))
      ((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ)) k 1).1
    rw [hk, h]
    simpa using hε

/-- Fixed-order decay of the coupled 11 entries weighted by `exp(2iz)`. -/
theorem e02_fixedOrder11_coupled38 (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀)
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in cocompact ℝ,
      ∀ p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀,
        ‖Complex.exp (2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))) *
          genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32
            (fun s => naturalPhysicalCoverL2 (((p.1 : ℝ) : ℂ) • u) (s : SpectralCircle))
            ((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))) m 1 1 1‖ < ε := by
  intro ε hε
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' m
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    filter_upwards [actualPhysicalDyson11_fixedOrder_uniformFourierDecay37V2 u Y₀ hY₀ k' ε hε]
      with x hx p
    rw [hk, norm_mul, e02_norm_exp_two_I38]
    have h1 := hx (⟨1, by norm_num⟩, p.2)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at h1
    have h2 : Real.exp (-2*((p.2 : ℝ))) *
        ‖genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32
            (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle))
            ((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))) (2*(k'+1)) 1 1 1‖ < ε := by
      simpa using h1
    refine lt_of_le_of_lt ?_ h2
    exact mul_le_mul_of_nonneg_left (e02_coupled_entry_norm_le38 u p.1 p.1.2 _ _ 1 1)
      (Real.exp_pos _).le
  · filter_upwards with x p
    have h := (actualInteractionDyson_odd_diagonal_zero32
      (fun s => naturalPhysicalCoverL2 (((p.1 : ℝ) : ℂ) • u) (s : SpectralCircle))
      ((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ)) k 1).2
    rw [hk, h]
    simpa using hε


/-- Common factorial majorant (shifted by one order) over the whole strip. -/
theorem e02_bound38 (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀) (x : ℝ)
    (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) (n : ℕ) (i j : Fin 2) :
    ‖genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32
            (fun s => naturalPhysicalCoverL2 (((p.1 : ℝ) : ℂ) • u) (s : SpectralCircle))
            ((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))) (n+1) 1 i j‖ ≤
      (2 * actualCumulativeRealIntegral
        (actualPhysicalInteractionStripMajorant36V3 u Y₀) 1) ^ (n+1) /
        ((n+1).factorial : ℝ) := by
  have h1 : (0 : ℝ) ≤ ((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ)).im := by simpa using p.2.2.1
  have h2 : ((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ)).im ≤ Y₀ := by simpa using p.2.2.2
  exact actualPhysicalInteractionDysonTerm_coupling_commonFactorialMajorant37V1
    u p.1 p.1.2 _ Y₀ hY₀ h1 h2 (n+1) 1 (by norm_num) i j

theorem e02_sum00_small38 (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in cocompact ℝ,
      ∀ p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀,
        ‖∑' n : ℕ, genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32
            (fun s => naturalPhysicalCoverL2 (((p.1 : ℝ) : ℂ) • u) (s : SpectralCircle))
            ((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))) (n+1) 1 0 0‖ < ε :=
  e02_uniform_tsum_small38 (cocompact ℝ)
    (fun (x : ℝ) (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) (n : ℕ) =>
      genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32
            (fun s => naturalPhysicalCoverL2 (((p.1 : ℝ) : ℂ) • u) (s : SpectralCircle))
            ((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))) (n+1) 1 0 0)
    (fun n : ℕ => (2 * actualCumulativeRealIntegral
        (actualPhysicalInteractionStripMajorant36V3 u Y₀) 1) ^ (n+1) /
        ((n+1).factorial : ℝ))
    (e02_majorant_summable38 _) (fun x p n => e02_bound38 u Y₀ hY₀ x p n 0 0)
    (fun n => e02_fixedOrder00_coupled38 u Y₀ hY₀ (n+1) (by omega))

theorem e02_sum11_small38 (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in cocompact ℝ,
      ∀ p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀,
        ‖Complex.exp (2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))) *
          ∑' n : ℕ, genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32
            (fun s => naturalPhysicalCoverL2 (((p.1 : ℝ) : ℂ) • u) (s : SpectralCircle))
            ((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))) (n+1) 1 1 1‖ < ε := by
  intro ε hε
  have hb : ∀ (x : ℝ) (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) (n : ℕ),
      ‖Complex.exp (2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))) *
        genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32
            (fun s => naturalPhysicalCoverL2 (((p.1 : ℝ) : ℂ) • u) (s : SpectralCircle))
            ((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))) (n+1) 1 1 1‖ ≤
      (2 * actualCumulativeRealIntegral
        (actualPhysicalInteractionStripMajorant36V3 u Y₀) 1) ^ (n+1) /
        ((n+1).factorial : ℝ) := by
    intro x p n
    have hY : (0 : ℝ) ≤ (p.2 : ℝ) := p.2.2.1
    refine le_trans ?_ (e02_bound38 u Y₀ hY₀ x p n 1 1)
    rw [norm_mul, e02_norm_exp_two_I38]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [Real.exp_le_one_iff]
    linarith
  have h := e02_uniform_tsum_small38 (cocompact ℝ)
    (fun (x : ℝ) (p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀) (n : ℕ) =>
      Complex.exp (2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))) *
      genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32
            (fun s => naturalPhysicalCoverL2 (((p.1 : ℝ) : ℂ) • u) (s : SpectralCircle))
            ((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))) (n+1) 1 1 1)
    (fun n : ℕ => (2 * actualCumulativeRealIntegral
        (actualPhysicalInteractionStripMajorant36V3 u Y₀) 1) ^ (n+1) /
        ((n+1).factorial : ℝ))
    (e02_majorant_summable38 _) hb
    (fun n => e02_fixedOrder11_coupled38 u Y₀ hY₀ (n+1) (by omega)) ε hε
  filter_upwards [h] with x hx p
  rw [← tsum_mul_left]
  exact hx p

/-- E02 coupling-strip cosine asymptotic for the actual period-one half trace:
uniformly in coupling `τ ∈ [0,1]` and height `Y ∈ [0,Y₀]`, the half trace of
`τ u` converges to `cos z` as the real part escapes to infinity. -/
theorem actualPhysicalUnitHalfTrace_couplingStrip_cosineAsymptotic_E02_38
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.cocompact ℝ,
      ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ Y ∈ Set.Icc (0:ℝ) Y₀,
        ‖actualPhysicalUnitHalfTrace32 ((τ:ℂ) • u) ((x:ℂ) + Complex.I*(Y:ℂ)) -
          Complex.cos ((x:ℂ) + Complex.I*(Y:ℂ))‖ < ε := by
  intro ε hε
  have hδ : 0 < ε / Real.exp Y₀ := div_pos hε (Real.exp_pos _)
  filter_upwards [e02_sum00_small38 u Y₀ hY₀ _ hδ, e02_sum11_small38 u Y₀ hY₀ _ hδ]
    with x h0 h1 τ hτ Y hY
  have hid := e02_identity38 u τ ((x:ℂ) + Complex.I*(Y:ℂ)) Y₀ hY₀ (by simpa using hY.1)
    (by simpa using hY.2)
  have hA := h0 (⟨τ, hτ⟩, ⟨Y, hY⟩)
  have hB := h1 (⟨τ, hτ⟩, ⟨Y, hY⟩)
  simp only at hA hB
  set D := actualPhysicalUnitHalfTrace32 ((τ:ℂ) • u) ((x:ℂ) + Complex.I*(Y:ℂ)) -
    Complex.cos ((x:ℂ) + Complex.I*(Y:ℂ)) with hD
  have hnorm : ‖Complex.exp (Complex.I*((x:ℂ) + Complex.I*(Y:ℂ))) * D‖ < ε / Real.exp Y₀ := by
    rw [hid, norm_div]
    have h2 : ‖(2:ℂ)‖ = 2 := by simp
    rw [h2]
    calc _ ≤ (‖_‖ + ‖_‖) / 2 := by
          gcongr
          exact norm_add_le _ _
      _ < _ := by linarith
  rw [norm_mul, e02_norm_exp_I38] at hnorm
  have hY1 : Real.exp Y ≤ Real.exp Y₀ := Real.exp_le_exp.2 hY.2
  have hpos : 0 < Real.exp Y := Real.exp_pos _
  have hexp : Real.exp (-Y) * Real.exp Y = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖D‖ = Real.exp Y * (Real.exp (-Y) * ‖D‖) := by
        rw [← mul_assoc, mul_comm (Real.exp Y), hexp, one_mul]
    _ < Real.exp Y * (ε / Real.exp Y₀) := by gcongr
    _ ≤ Real.exp Y₀ * (ε / Real.exp Y₀) := by gcongr
    _ = ε := by field_simp

end NlsGge.SpectralFoundations
end
