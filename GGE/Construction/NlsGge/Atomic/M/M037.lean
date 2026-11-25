import NlsGge.ThirdConsultation.M.M037Interp
import NlsGge.ThirdConsultation.M.M037Jet
import NlsGge.ThirdConsultation.M.M037Producer

                                                                                                            
                                                                                                      
                                                                                                                   
                                                                                        
                                                                                                             
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal BigOperators
open NlsGge.Pilot NlsGge.Atomic.Common
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.M

theorem hierarchy_monomial_subquadratic
    (m : ℕ) (hm : 1 ≤ m)
    (q : NlsGge.HierarchyRiccati.Core.Jet →₀ ℕ)
    (hq : ChargeMonomialBounds m q)
    (hr : fieldCount q ≤ 2*m+2) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SobolevR m,
    ‖integralMonomial q u‖ ≤
      C * ‖u‖ ^ (2 - ((fieldCount q : ℝ)-2)/(2*(m : ℝ))) *
        ‖physicalOfSobolev u‖ ^
          ((1 + 1/(2*(m : ℝ))) * ((fieldCount q : ℝ)-2)) := by
  classical
  have hm0 : 0 < m := by omega
  obtain ⟨C, hC0, hCb⟩ := NlsGge.ThirdConsultation.M.M037Jet.gn_const m hm0
  obtain ⟨K, hK1, hKk⟩ : ∃ K : ℝ, 1 ≤ K ∧ ∀ k, k < m → C k ≤ K :=
    ⟨1 + ∑ k ∈ Finset.range m, C k, by
      have hs : 0 ≤ ∑ k ∈ Finset.range m, C k := Finset.sum_nonneg (fun k _ => hC0 k)
      linarith, fun k hk => by
      have hs := Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_range.2 hk)
      linarith⟩
  have hK0 : 0 ≤ K := by linarith
  refine ⟨K ^ fieldCount q, pow_nonneg hK0 _, fun u => ?_⟩
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = ‖u‖ ^ ((1:ℝ) / (2 * (m:ℝ))) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = ‖physicalOfSobolev u‖ ^ ((1:ℝ) / (2 * (m:ℝ))) := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := by rw [hα]; exact Real.rpow_nonneg (norm_nonneg _) _
  have hβ0 : 0 ≤ β := by rw [hβ]; exact Real.rpow_nonneg (norm_nonneg _) _
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- exponent conversions: real exponents n/(2m) become natural powers of α, β
  have convS : ∀ k, k < m → ‖u‖ ^ (((k : ℝ) + (1/2 : ℝ)) / (m : ℝ)) = α ^ (2 * k + 1) := by
    intro k _
    have e : ((k : ℝ) + (1/2 : ℝ)) / (m : ℝ) = ((2 * k + 1 : ℕ) : ℝ) / (2 * (m : ℝ)) := by
      push_cast
      field_simp
    rw [e, NlsGge.ThirdConsultation.M.M037Interp.rpow_nat_div_two_mul _ (norm_nonneg _) m (2 * k + 1), hα]
  have convS' : ∀ k, k < m →
      ‖physicalOfSobolev u‖ ^ (1 - ((k : ℝ) + (1/2 : ℝ)) / (m : ℝ)) = β ^ (2 * m - (2 * k + 1)) := by
    intro k hk
    have hk2 : 2 * k + 1 ≤ 2 * m := by omega
    have e : 1 - ((k : ℝ) + (1/2 : ℝ)) / (m : ℝ) = ((2 * m - (2 * k + 1) : ℕ) : ℝ) / (2 * (m : ℝ)) := by
      rw [Nat.cast_sub hk2]
      push_cast
      field_simp
    rw [e, NlsGge.ThirdConsultation.M.M037Interp.rpow_nat_div_two_mul _ (norm_nonneg _) m
      (2 * m - (2 * k + 1)), hβ]
  have convL : ∀ k, k < m → ‖u‖ ^ ((k : ℝ) / (m : ℝ)) = α ^ (2 * k) := by
    intro k _
    have e : (k : ℝ) / (m : ℝ) = ((2 * k : ℕ) : ℝ) / (2 * (m : ℝ)) := by
      push_cast
      field_simp
    rw [e, NlsGge.ThirdConsultation.M.M037Interp.rpow_nat_div_two_mul _ (norm_nonneg _) m (2 * k), hα]
  have convL' : ∀ k, k < m →
      ‖physicalOfSobolev u‖ ^ (1 - (k : ℝ) / (m : ℝ)) = β ^ (2 * m - 2 * k) := by
    intro k hk
    have hk2 : 2 * k ≤ 2 * m := by omega
    have e : 1 - (k : ℝ) / (m : ℝ) = ((2 * m - 2 * k : ℕ) : ℝ) / (2 * (m : ℝ)) := by
      rw [Nat.cast_sub hk2]
      push_cast
      field_simp
    rw [e, NlsGge.ThirdConsultation.M.M037Interp.rpow_nat_div_two_mul _ (norm_nonneg _) m
      (2 * m - 2 * k), hβ]
  -- support and multiset form of the monomial
  have hcardS : Multiset.card q.toMultiset = fieldCount q := by
    rw [Finsupp.card_toMultiset]
    rfl
  have hmemS : ∀ v ∈ q.toMultiset, v ∈ q.support := by
    intro v hv
    have := Multiset.mem_toFinset.2 hv
    rwa [Finsupp.toFinset_toMultiset] at this
  have hsumS : (q.toMultiset.map fun v => v.2).sum =
      riccatiJetDerivativeOrderSumNativeRecovery q := by
    rw [NlsGge.ThirdConsultation.M.M037Interp.toMultiset_map_sum]
    simp only [riccatiJetDerivativeOrderSumNativeRecovery, smul_eq_mul]
  have hD : riccatiJetDerivativeOrderSumNativeRecovery q = 2 * m + 2 - fieldCount q := hq.2.2.1
  have hpos : 0 < Multiset.card q.toMultiset := by
    rw [hcardS]
    have := hq.1
    omega
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 hpos
  have hcons1 := Multiset.cons_erase ha
  have hcard1 : Multiset.card (q.toMultiset.erase a) = fieldCount q - 1 := by
    rw [Multiset.card_erase_of_mem ha, hcardS]
    rfl
  have hpos1 : 0 < Multiset.card (q.toMultiset.erase a) := by
    rw [hcard1]
    have := hq.1
    omega
  obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.1 hpos1
  have hcons2 := Multiset.cons_erase hb
  have hs : q.toMultiset = a ::ₘ b ::ₘ ((q.toMultiset.erase a).erase b) := by
    rw [hcons2, hcons1]
  generalize ht : (q.toMultiset.erase a).erase b = t at hs
  have hcardT : Multiset.card t + 2 = fieldCount q := by
    have h := hcardS
    rw [hs] at h
    simpa using h
  have hmemT : ∀ v ∈ t, v ∈ q.support := by
    intro v hv
    apply hmemS
    rw [hs]
    exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hv)
  have hsumT : (q.toMultiset.map fun v => v.2).sum = a.2 + (b.2 + (t.map fun v => v.2).sum) := by
    rw [hs]
    simp [Multiset.map_cons, Multiset.sum_cons]
  -- every factor index is in range
  have hrange : ∀ v ∈ t, v.2 < m := by
    intro v hv
    have := hq.2.2.2 v (hmemT v hv)
    omega
  have hkrange_a : a.2 < m := by
    have := hq.2.2.2 a (hmemS a ha)
    omega
  have hkrange_b : b.2 < m := by
    have := hq.2.2.2 b (hmemS b (by rw [hs]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)))
    omega
  -- the integrand as a multiset product
  have hint : integralMonomial q u = ∫ x : PhysicalCircle,
      (q.toMultiset.map fun v => sobolevJetContinuous m v u x).prod ∂spatialMeasure := by
    unfold integralMonomial
    apply integral_congr_ae
    refine ae_of_all _ fun x => ?_
    dsimp only
    rw [NlsGge.ThirdConsultation.M.M037Interp.toMultiset_map_prod]
    rfl
  have hpt : ∀ x : PhysicalCircle,
      ‖(q.toMultiset.map fun v => sobolevJetContinuous m v u x).prod‖ =
        (‖sobolevJetContinuous m a u x‖ * ‖sobolevJetContinuous m b u x‖) *
          (t.map fun v => ‖sobolevJetContinuous m v u x‖).prod := by
    intro x
    rw [NlsGge.ThirdConsultation.M.M037Interp.norm_multiset_map_prod, hs]
    simp only [Multiset.map_cons, Multiset.prod_cons]
    ring
  -- pointwise tail bound
  have tailB : ∀ x : PhysicalCircle, ∀ v ∈ t,
      ‖sobolevJetContinuous m v u x‖ ≤ K * (α ^ (2 * v.2 + 1) * β ^ (2 * m - (2 * v.2 + 1))) := by
    intro x v hv
    have hvm : v.2 < m := hrange v hv
    rcases v with ⟨bv, kv⟩
    have hkm : kv + 1 ≤ m := by
      have h : kv < m := hvm
      omega
    have hkm' : kv < m := by omega
    calc ‖sobolevJetContinuous m (bv, kv) u x‖
        ≤ NlsGge.ThirdConsultation.MEstimates.derivativeSupNorm kv u :=
          NlsGge.ThirdConsultation.M.M037Jet.norm_jet_le_sup m bv kv hkm u x
      _ ≤ C kv * ‖u‖ ^ (((kv : ℝ) + (1/2 : ℝ)) / (m : ℝ)) *
            ‖physicalOfSobolev u‖ ^ (1 - ((kv : ℝ) + (1/2 : ℝ)) / (m : ℝ)) := (hCb kv hkm').1 u
      _ = C kv * (α ^ (2 * kv + 1) * β ^ (2 * m - (2 * kv + 1))) := by
          rw [convS kv hkm', convS' kv hkm']
          ring
      _ ≤ K * (α ^ (2 * kv + 1) * β ^ (2 * m - (2 * kv + 1))) :=
          mul_le_mul_of_nonneg_right (hKk kv hkm')
            (mul_nonneg (pow_nonneg hα0 _) (pow_nonneg hβ0 _))
  -- the tail product, as a constant in x
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = (t.map fun v =>
      K * (α ^ (2 * v.2 + 1) * β ^ (2 * m - (2 * v.2 + 1)))).prod := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    apply Multiset.prod_nonneg
    intro y hy
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.1 hy
    exact mul_nonneg hK0 (mul_nonneg (pow_nonneg hα0 _) (pow_nonneg hβ0 _))
  have hQx : ∀ x : PhysicalCircle,
      (t.map fun v => ‖sobolevJetContinuous m v u x‖).prod ≤ Q := by
    intro x
    rw [hQdef]
    exact Multiset.prod_map_le_prod_map₀ _ _ (fun v _ => norm_nonneg _)
      (fun v hv => tailB x v hv)
  -- Hölder pair and the constant tail
  have : IsFiniteMeasure spatialMeasure := by
    unfold spatialMeasure
    infer_instance
  have hPair_int : Integrable
      (fun x : PhysicalCircle =>
        ‖sobolevJetContinuous m a u x‖ * ‖sobolevJetContinuous m b u x‖ * Q) spatialMeasure := by
    have hcont : Continuous (fun x : PhysicalCircle =>
        ‖sobolevJetContinuous m a u x‖ * ‖sobolevJetContinuous m b u x‖ * Q) :=
      ((sobolevJetContinuous m a u).continuous.norm.mul
        (sobolevJetContinuous m b u).continuous.norm).mul continuous_const
    refine Integrable.of_bound hcont.aestronglyMeasurable
      (‖sobolevJetContinuous m a u‖ * ‖sobolevJetContinuous m b u‖ * Q) (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hQ0)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (ContinuousMap.norm_coe_le_norm _ x) (ContinuousMap.norm_coe_le_norm _ x)
        (norm_nonneg _) (norm_nonneg _)) hQ0
  have hI : ∫ x : PhysicalCircle, ‖(q.toMultiset.map fun v => sobolevJetContinuous m v u x).prod‖
      ∂spatialMeasure ≤
      (∫ x : PhysicalCircle,
        ‖sobolevJetContinuous m a u x‖ * ‖sobolevJetContinuous m b u x‖ ∂spatialMeasure) * Q := by
    rw [← integral_mul_const]
    apply integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) hPair_int
    refine ae_of_all _ fun x => ?_
    dsimp only
    rw [hpt x]
    exact mul_le_mul_of_nonneg_left (hQx x) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  -- L² bounds for the two Hölder factors (lowered casts as in the bridge)
  have hL2 : ∀ k (hk : k < m),
      ‖physicalSobolevDerivative38 k
          (NlsGge.ThirdConsultation.M.lowerSobolevCast k m (by omega) u)‖ ≤
        K * (α ^ (2 * k) * β ^ (2 * m - 2 * k)) := by
    intro k hk
    have h := (hCb k hk).2 u
    rw [NlsGge.ThirdConsultation.M.M037Jet.lowerCast_eq m k (by omega) u] at h
    calc _ ≤ C k * ‖u‖ ^ ((k : ℝ) / (m : ℝ)) * ‖physicalOfSobolev u‖ ^ (1 - (k : ℝ) / (m : ℝ)) := h
      _ = C k * (α ^ (2 * k) * β ^ (2 * m - 2 * k)) := by
          rw [convL k hk, convL' k hk]
          ring
      _ ≤ K * (α ^ (2 * k) * β ^ (2 * m - 2 * k)) :=
          mul_le_mul_of_nonneg_right (hKk k hk) (mul_nonneg (pow_nonneg hα0 _) (pow_nonneg hβ0 _))
  have hbound : ‖integralMonomial q u‖ ≤
      (K * (α ^ (2 * a.2) * β ^ (2 * m - 2 * a.2))) * (K * (α ^ (2 * b.2) * β ^ (2 * m - 2 * b.2))) * Q := by
    rw [hint]
    have hPair := NlsGge.ThirdConsultation.M.M037Jet.jet_pair_integral_le m a.1 b.1 a.2 b.2
      (by have := hkrange_a; omega) (by have := hkrange_b; omega) u
    calc ‖∫ x : PhysicalCircle, (q.toMultiset.map fun v => sobolevJetContinuous m v u x).prod ∂spatialMeasure‖
        ≤ ∫ x : PhysicalCircle, ‖(q.toMultiset.map fun v => sobolevJetContinuous m v u x).prod‖ ∂spatialMeasure :=
          norm_integral_le_integral_norm
            (fun x : PhysicalCircle => (q.toMultiset.map fun v => sobolevJetContinuous m v u x).prod)
      _ ≤ (∫ x : PhysicalCircle,
            ‖sobolevJetContinuous m a u x‖ * ‖sobolevJetContinuous m b u x‖ ∂spatialMeasure) * Q := hI
      _ ≤ (‖physicalSobolevDerivative38 a.2
              (NlsGge.ThirdConsultation.M.lowerSobolevCast a.2 m (by omega) u)‖ *
            ‖physicalSobolevDerivative38 b.2
              (NlsGge.ThirdConsultation.M.lowerSobolevCast b.2 m (by omega) u)‖) * Q :=
          mul_le_mul_of_nonneg_right hPair hQ0
      _ ≤ (K * (α ^ (2 * a.2) * β ^ (2 * m - 2 * a.2))) * (K * (α ^ (2 * b.2) * β ^ (2 * m - 2 * b.2))) * Q :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (hL2 a.2 hkrange_a) (hL2 b.2 hkrange_b) (norm_nonneg _)
              (mul_nonneg hK0 (mul_nonneg (pow_nonneg hα0 _) (pow_nonneg hβ0 _))))
            hQ0
  -- multiset exponent bookkeeping (natural numbers only)
  have hQf : Q = K ^ Multiset.card t * α ^ (t.map fun v : Jet => 2 * v.2 + 1).sum *
      β ^ (t.map fun v : Jet => 2 * m - (2 * v.2 + 1)).sum := by
    rw [hQdef]
    exact NlsGge.ThirdConsultation.M.M037Interp.multiset_prod_const_pow_mul t K α β
      (fun v : Jet => 2 * v.2 + 1) (fun v : Jet => 2 * m - (2 * v.2 + 1))
  have hSA : (t.map fun v : Jet => 2 * v.2 + 1).sum =
      2 * (t.map fun v : Jet => v.2).sum + Multiset.card t :=
    NlsGge.ThirdConsultation.M.M037Interp.multiset_sum_two_mul_add_one t (fun v : Jet => v.2)
  have hSS : (t.map fun v : Jet => 2 * v.2 + 1).sum + (t.map fun v : Jet => 2 * m - (2 * v.2 + 1)).sum =
      2 * m * Multiset.card t :=
    NlsGge.ThirdConsultation.M.M037Interp.multiset_sum_add_eq_const t
      (fun v : Jet => 2 * v.2 + 1) (fun v : Jet => 2 * m - (2 * v.2 + 1)) (2 * m)
      (fun v hv => by
        have := hrange v hv
        show 2 * v.2 + 1 + (2 * m - (2 * v.2 + 1)) = 2 * m
        omega)
  obtain ⟨X, hX⟩ : ∃ X : ℕ, X = m * Multiset.card t := ⟨_, rfl⟩
  have h2X : 2 * m * Multiset.card t = 2 * X := by rw [hX]; ring
  have hpoly : (2 * m + 1) * Multiset.card t = 2 * X + Multiset.card t := by rw [hX]; ring
  rw [h2X] at hSS
  obtain ⟨Ta, hTa⟩ : ∃ T : ℕ, T = (t.map fun v : Jet => v.2).sum := ⟨_, rfl⟩
  obtain ⟨SA, hSAdef⟩ : ∃ S : ℕ, S = (t.map fun v : Jet => 2 * v.2 + 1).sum := ⟨_, rfl⟩
  obtain ⟨SB, hSBdef⟩ : ∃ S : ℕ, S = (t.map fun v : Jet => 2 * m - (2 * v.2 + 1)).sum := ⟨_, rfl⟩
  rw [← hSAdef, ← hTa] at hSA
  rw [← hSAdef, ← hSBdef] at hSS
  rw [← hSAdef, ← hSBdef] at hQf
  have hsumT' : a.2 + (b.2 + Ta) = 2 * m + 2 - fieldCount q := by
    rw [hTa, ← hsumT, hsumS, hD]
  obtain ⟨NA, hNA⟩ : ∃ N : ℕ, N = 2 * a.2 + 2 * b.2 + SA := ⟨_, rfl⟩
  obtain ⟨NB, hNB⟩ : ∃ N : ℕ, N = (2 * m - 2 * a.2) + (2 * m - 2 * b.2) + SB := ⟨_, rfl⟩
  have hNAsum : NA + fieldCount q = 4 * m + 2 := by
    have := hr
    omega
  have hNBsum : NB = (2 * m + 1) * Multiset.card t := by
    have := hkrange_a
    have := hkrange_b
    omega
  have hn : (Multiset.card t : ℝ) = (fieldCount q : ℝ) - 2 := by
    have h : ((Multiset.card t + 2 : ℕ) : ℝ) = (fieldCount q : ℝ) := by
      exact_mod_cast hcardT
    push_cast at h
    linarith
  -- the real exponents of the statement are the natural powers
  have hEA : ‖u‖ ^ (2 - ((fieldCount q : ℝ) - 2) / (2 * (m : ℝ))) = α ^ NA := by
    have hc : ((NA : ℕ) : ℝ) + (fieldCount q : ℝ) = 4 * (m : ℝ) + 2 := by
      exact_mod_cast hNAsum
    have e : 2 - ((fieldCount q : ℝ) - 2) / (2 * (m : ℝ)) = ((NA : ℕ) : ℝ) / (2 * (m : ℝ)) := by
      field_simp
      linarith
    rw [e, NlsGge.ThirdConsultation.M.M037Interp.rpow_nat_div_two_mul _ (norm_nonneg _) m NA, hα]
  have hEB : ‖physicalOfSobolev u‖ ^ ((1 + 1 / (2 * (m : ℝ))) * ((fieldCount q : ℝ) - 2)) = β ^ NB := by
    have hNBc : ((NB : ℕ) : ℝ) = (2 * (m : ℝ) + 1) * (Multiset.card t : ℝ) := by
      rw [hNBsum]
      push_cast
      ring
    have e : (1 + 1 / (2 * (m : ℝ))) * ((fieldCount q : ℝ) - 2) = ((NB : ℕ) : ℝ) / (2 * (m : ℝ)) := by
      rw [hNBc, ← hn]
      field_simp
    rw [e, NlsGge.ThirdConsultation.M.M037Interp.rpow_nat_div_two_mul _ (norm_nonneg _) m NB, hβ]
  have hKc : K ^ fieldCount q = K ^ (Multiset.card t + 2) := by
    rw [hcardT]
  have hfinal : ‖integralMonomial q u‖ ≤ K ^ (Multiset.card t + 2) * α ^ NA * β ^ NB := by
    refine le_trans hbound (le_of_eq ?_)
    rw [hQf, hNA, hNB]
    simp only [pow_add]
    ring
  rw [hEA, hEB, hKc]
  exact hfinal

theorem hierarchy_IBP_normal_form_bounded_degree
    (m : ℕ) (hm : 1 ≤ m) :
  ∃ terms : Finset ((NlsGge.HierarchyRiccati.Core.Jet →₀ ℕ) × ℤ),
    ChargeNormalForm m terms ∧
    ∀ t ∈ terms, fieldCount t.1 ≤ 2*m+2 :=
  NlsGge.ThirdConsultation.M.M037Producer.image_normalForm_degree m hm

end NlsGge.ThirdConsultation.M
