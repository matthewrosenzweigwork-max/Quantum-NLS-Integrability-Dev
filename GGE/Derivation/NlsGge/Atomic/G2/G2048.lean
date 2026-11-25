import Mathlib
import NlsGge.Atomic.G2.G2019
import NlsGge.Atomic.G2.G2022

/- G2-048 PROOF01 (proof development, AUTHOR; not self-reviewed).  Statement verbatim from defs3 STATEMENTS/G2.md G2_048; definitions
   doubleRootRatio / psiZeta verbatim from DEFINITIONS/G2.lean.md (hosted here).
   Route: the one-omitted-index limit of G2-022 (index m) applied to the shifted sequence s' = s + c e_n with sigma'_n - z = 1
   gives convergence of the double-omitted symmetric products (so the totalized tprod is earned as a HasProd, including the
   zero cases sigma_m = z, sigma_n = z), then p2FullNumerator_div_root38 for s' and omitProd_add_single. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def doubleRootRatio (φ : PotPair) (s : Lib.L2Seq) (n m : ℤ) (z : ℂ) : ℂ :=
  ∏'[symmetricIcc ℤ] k : ℤ,
    if k=n ∨ k=m then 1 else (Lib.sigmaOf s k-z)/standardRoot φ k z

def psiZeta (φ : PotPair) (s : Lib.L2Seq) (n m : ℤ) (z : ℂ) : ℂ :=
  Complex.I / standardRoot φ n z * doubleRootRatio φ s n m z

namespace G2048Aux

theorem sigma_shift_ne (s : Lib.L2Seq) (n : ℤ) (c : ℂ) (k : ℤ) (hk : k ≠ n) :
    Lib.sigmaOf (s + c • lp.single 2 n (1 : ℂ)) k = Lib.sigmaOf s k := by
  have h := lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ) hk
  simp only [Lib.sigmaOf, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [h, mul_zero, add_zero]

theorem sigma_shift_eq (s : Lib.L2Seq) (n : ℤ) (c : ℂ) :
    Lib.sigmaOf (s + c • lp.single 2 n (1 : ℂ)) n = Lib.sigmaOf s n + c := by
  simp only [Lib.sigmaOf, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    lp.single_apply_self]
  ring

theorem std_ne {φ : PotPair} {z : ℂ} (hz : (φ, z) ∈ rootDomain38) (j : ℤ) : standardRoot φ j z ≠ 0 := by
  have hs := stdRoot_ne_zero38 (lamMinus φ j) (lamPlus φ j) z (rootDomain_avoids38 hz j)
  simpa only [standardRoot, add_comm (lamMinus φ j), ← tauN_value38 φ hz.1 j,
    ← gamma2_value38 φ hz.1 j] using hs

end G2048Aux
open G2048Aux

theorem G2_048 (φ : PotPair) (hφ : φ ∈ gkW) (s : Lib.L2Seq)
    (n m : ℤ) (hmn : m ≠ n) (z : ℂ) (hz : (φ,z) ∈ rootDomain38) :
    Tendsto (fun N : ℕ => ∏ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      if k=n ∨ k=m then (1 : ℂ) else (Lib.sigmaOf s k-z)/standardRoot φ k z)
      atTop (𝓝 (doubleRootRatio φ s n m z)) ∧
    standardRoot φ n z ≠ 0 ∧ standardRoot φ m z ≠ 0 ∧
    p2FullNumerator38 n s z/canonRoot38 φ z =
      (Lib.sigmaOf s m-z)/standardRoot φ m z * psiZeta φ s n m z := by
  have hnm : n ≠ m := fun h => hmn h.symm
  have hsn := std_ne hz n
  have hsm := std_ne hz m
  set c : ℂ := z - Lib.sigmaOf s n + 1 with hc
  set s' : Lib.L2Seq := s + c • lp.single 2 n (1 : ℂ) with hs'
  have hσn : Lib.sigmaOf s' n - z = 1 := by
    rw [hs', sigma_shift_eq, hc]; ring
  have hσm : Lib.sigmaOf s' m = Lib.sigmaOf s m := sigma_shift_ne s n c m hmn
  have hp' : (φ, z) ∈ a5OmittedRootDomain38 m := ⟨hz.1, fun j _ => rootDomain_avoids38 hz j⟩
  have hp0 : ((φ, s'), z) ∈ {p : (PotPair × Lib.L2Seq) × ℂ | (p.1.1, p.2) ∈ a5OmittedRootDomain38 m} := hp'
  have hT := ((G2_022 m).2.tendsto_at hp0)
  set L : ℂ := p2OmittedRatio38 m ((φ, s'), z) with hL
  -- partial products relation
  have hrel : ∀ᶠ N : ℕ in atTop,
      (∏ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        if k=n ∨ k=m then (1 : ℂ) else (Lib.sigmaOf s k-z)/standardRoot φ k z) =
      standardRoot φ n z * ∏ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          if k=m then (1 : ℂ) else (Lib.sigmaOf s' k-z)/standardRoot φ k z := by
    filter_upwards [eventually_ge_atTop n.natAbs] with N hN
    have hn : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    rw [← Finset.mul_prod_erase _ _ hn, ← Finset.mul_prod_erase _ _ hn]
    have e1 : (if n = n ∨ n = m then (1 : ℂ) else (Lib.sigmaOf s n-z)/standardRoot φ n z) = 1 := by simp
    have e2 : (if n = m then (1 : ℂ) else (Lib.sigmaOf s' n-z)/standardRoot φ n z) =
        (standardRoot φ n z)⁻¹ := by
      rw [if_neg hnm, hσn]; simp
    have e3 : ∏ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
        (if k=n ∨ k=m then (1 : ℂ) else (Lib.sigmaOf s k-z)/standardRoot φ k z) =
        ∏ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
          (if k=m then (1 : ℂ) else (Lib.sigmaOf s' k-z)/standardRoot φ k z) := by
      refine Finset.prod_congr rfl (fun k hk => ?_)
      have hkn : k ≠ n := (Finset.mem_erase.1 hk).1
      by_cases hkm : k = m
      · simp [hkm]
      · rw [if_neg (by tauto), if_neg hkm, sigma_shift_ne s n c k hkn]
    rw [e1, e2, e3]
    field_simp
  have hlim : Tendsto (fun N : ℕ => ∏ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      if k=n ∨ k=m then (1 : ℂ) else (Lib.sigmaOf s k-z)/standardRoot φ k z)
      atTop (𝓝 (standardRoot φ n z * L)) := by
    refine Tendsto.congr' (hrel.mono fun N h => h.symm) ?_
    exact hT.const_mul (standardRoot φ n z)
  have hHP : HasProd (fun k : ℤ => if k=n ∨ k=m then (1 : ℂ) else (Lib.sigmaOf s k-z)/standardRoot φ k z)
      (standardRoot φ n z * L) (symmetricIcc ℤ) := hasProd_symmetricIcc_iff.2 hlim
  have hdrr : doubleRootRatio φ s n m z = standardRoot φ n z * L := hHP.tprod_eq
  refine ⟨hdrr ▸ hlim, hsn, hsm, ?_⟩
  have hD := p2FullNumerator_div_root38 n m s' φ z hz (by rw [hσn]; exact one_ne_zero)
  have hnum : p2FullNumerator38 n s' z = p2FullNumerator38 n s z := by
    unfold p2FullNumerator38
    rw [hs', Lib.omitProd_add_single]
  rw [hnum] at hD
  rw [hD, psiZeta, hdrr, hσn, hσm]
  have hstd : stdRoot38 (tauN φ m) (gamma2 φ m) z = standardRoot φ m z := rfl
  rw [hstd]
  field_simp
  rfl


end
end NlsGge.GKDefinitionDesign
