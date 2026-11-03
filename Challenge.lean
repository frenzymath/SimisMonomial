import Mathlib
import SimisFormal.Defs

/-!
Challenge statements for the Simis monomial-ideal benchmark.
The declarations below fix the public API; the completed proofs are exposed through
`Solution.lean` after it imports the `SimisFormal` library.
-/

-- SimisFormal.eq1_full : levels [u_1, u_2]
theorem SimisFormal.eq1_full.{u_1, u_2} {σ : Type u_1} {K : Type u_2} [Field K]
    [DecidableEq σ] [Fintype σ] {I : Ideal (MvPolynomial σ K)}
    (hI : SimisFormal.IsMonomialIdeal (K := K) I) (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤) :
    SimisFormal.HasFiniteIrredundantDecomp (K := K) I ∧
      ∀ (η : Type) [Fintype η] (A : η → Finset σ) (a : η → σ → ℕ),
        SimisFormal.IsIrredundantDecomp (K := K) I A a →
          (∀ j, (A j).Nonempty) ∧
            (∀ j i, i ∈ A j → 0 < a j i) ∧
              (∀ j, (SimisFormal.purePower (A j) (a j) : Ideal (MvPolynomial σ K)).IsPrimary) ∧
                (associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) =
                  Set.range (fun j : η ↦
                    (SimisFormal.primeOf (A j) : Ideal (MvPolynomial σ K)))) ∧
                  ∀ (ξ : Type) [Fintype ξ] (B : ξ → Finset σ) (b : ξ → σ → ℕ),
                    SimisFormal.IsIrredundantDecomp (K := K) I B b →
                      ∃ e : η ≃ ξ, ∀ j, A j = B (e j) ∧ ∀ i ∈ A j, a j i = b (e j) i := by
  sorry

-- SimisFormal.hasFiniteIrredundantDecomp_of_isMonomialIdeal : levels [u_1, u_2]
theorem SimisFormal.hasFiniteIrredundantDecomp_of_isMonomialIdeal.{u_1, u_2} {σ : Type u_1} {K : Type u_2} [Field K] [Fintype σ] {I : Ideal (MvPolynomial σ K)} (hI : SimisFormal.IsMonomialIdeal I) : SimisFormal.HasFiniteIrredundantDecomp I := by
  sorry

-- SimisFormal.irredundantDecomp_unique : levels [u_1, u_2, u_3, u_4]
theorem SimisFormal.irredundantDecomp_unique.{u_1, u_2, u_3, u_4} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} {κ : Type u_4} [Field K] [DecidableEq σ] [Fintype σ] [Fintype ι] [Fintype κ] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} {B : κ → Finset σ} {b : κ → σ → ℕ} (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤) (hA : SimisFormal.IsIrredundantDecomp I A a) (hB : SimisFormal.IsIrredundantDecomp I B b) : ∃ (e : ι ≃ κ), ∀ (j : ι), A j = B (e j) ∧ ∀ i ∈ A j, a j i = b (e j) i := by
  sorry

-- SimisFormal.purePower_radical_eq_primeOf : levels [u_1, u_2]
theorem SimisFormal.purePower_radical_eq_primeOf.{u_1, u_2} {σ : Type u_1} {K : Type u_2} [Field K] [DecidableEq σ] {A : Finset σ} {a : σ → ℕ} (ha : ∀ i ∈ A, 0 < a i) : (SimisFormal.purePower A a).radical = SimisFormal.primeOf (K := K) A := by
  sorry

-- SimisFormal.diagAssoc_quotientAssociatedPrimes_eq_range : levels [u_1, u_2, u_3]
theorem SimisFormal.diagAssoc_quotientAssociatedPrimes_eq_range.{u_1, u_2, u_3}
    {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype σ]
    [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : SimisFormal.HasComponents I A a) (hirr : SimisFormal.IsIrredundant (K := K) A a) :
    associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) =
      Set.range (fun j ↦ (SimisFormal.primeOf (A j) : Ideal (MvPolynomial σ K))) := by
  sorry

-- SimisFormal.minimalPrime_eq_primeOf_of_antichain : levels [u_1, u_2, u_3]
theorem SimisFormal.minimalPrime_eq_primeOf_of_antichain.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} {P : Ideal (MvPolynomial σ K)} (hcomp : SimisFormal.HasComponents I A a) (hpos : ∀ (j : ι), ∀ i ∈ A j, 0 < a j i) (hP : I.IsMinimalPrime P) : ∃ (j : ι), P = SimisFormal.primeOf (A j) := by
  sorry

-- SimisFormal.primeOf_mem_minimalPrimes_of_antichain : levels [u_1, u_2, u_3]
theorem SimisFormal.primeOf_mem_minimalPrimes_of_antichain.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hcomp : SimisFormal.HasComponents I A a) (hpos : ∀ (j : ι), ∀ i ∈ A j, 0 < a j i) (hanti : SimisFormal.SupportsAntichain A a) (j : ι) : I.IsMinimalPrime (SimisFormal.primeOf (A j)) := by
  sorry

-- SimisFormal.radical_iInf_purePower_of_pos : levels [u_1, u_2, u_3]
theorem SimisFormal.radical_iInf_purePower_of_pos.{u_1, u_2, u_3} {σ : Type u_1}
    {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hpos : ∀ j i, i ∈ A j → 0 < a j i) :
    (⨅ j, (SimisFormal.purePower (A j) (a j) : Ideal (MvPolynomial σ K))).radical =
      ⨅ j, (SimisFormal.primeOf (A j) : Ideal (MvPolynomial σ K)) := by
  sorry

-- SimisFormal.associatedPrimes_pow_eq_range_of_componentSimis_antichain : levels [u_1, u_2, u_3]
theorem SimisFormal.associatedPrimes_pow_eq_range_of_componentSimis_antichain.{u_1, u_2, u_3}
    {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype σ]
    [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hcomp : SimisFormal.HasComponents I A a) (hirr : SimisFormal.IsIrredundant (K := K) A a)
    (hanti : SimisFormal.SupportsAntichain A a)
    (hpow : SimisFormal.ComponentSimis I (fun j ↦
      (SimisFormal.purePower (A j) (a j) : Ideal (MvPolynomial σ K)))) {q : ℕ} (hq : 0 < q) :
    associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I ^ q) =
      Set.range (fun j ↦ (SimisFormal.primeOf (A j) : Ideal (MvPolynomial σ K))) := by
  sorry

-- SimisFormal.normallyTorsionFree_of_powerAssociatedPrimes_eq_range : levels [u_1, u_2, u_3]
theorem SimisFormal.normallyTorsionFree_of_powerAssociatedPrimes_eq_range.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] {I : Ideal (MvPolynomial σ K)} {P : ι → Ideal (MvPolynomial σ K)} (hbase : associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) = Set.range P) (hpower : ∀ {q : ℕ}, 0 < q → associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I ^ q) = Set.range P) : SimisFormal.prop21NormallyTorsionFree I := by
  sorry

-- SimisFormal.blocker_blocker_eq_self : levels [u_1]
theorem SimisFormal.blocker_blocker_eq_self.{u_1} {σ : Type u_1} [DecidableEq σ] [Fintype σ] {H : Set (Finset σ)} (hH : SimisFormal.IsClutter H) : SimisFormal.blocker (SimisFormal.blocker H) = H := by
  sorry

-- SimisFormal.blocker_isClutter : levels [u_1]
theorem SimisFormal.blocker_isClutter.{u_1} {σ : Type u_1} [DecidableEq σ] (H : Set (Finset σ)) : SimisFormal.IsClutter (SimisFormal.blocker H) := by
  sorry

-- SimisFormal.eq2_standardSymbolic : levels [u_1, u_2, u_3]
theorem SimisFormal.eq2_standardSymbolic.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hdecomp : SimisFormal.IsIrredundantDecomp I A a) (hanti : SimisFormal.SupportsAntichain A a) : SimisFormal.HasStdSymbolicFormula I fun (j : ι) => SimisFormal.purePower (A j) (a j) := by
  sorry

-- SimisFormal.eq2_groupedSymbolic : levels [u_1, u_2, u_3]
theorem SimisFormal.eq2_groupedSymbolic.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hdecomp : SimisFormal.IsIrredundantDecomp I A a) : SimisFormal.HasStdSymbolicFormula I (SimisFormal.groupedComponents I A a) := by
  sorry

-- SimisFormal.groupedComponents_isPrimary : levels [u_1, u_2, u_3]
theorem SimisFormal.groupedComponents_isPrimary.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hcomp : SimisFormal.HasComponents I A a) (hpos : ∀ (j : ι), ∀ i ∈ A j, 0 < a j i) (P : ↑I.minimalPrimes) : (SimisFormal.groupedComponents I A a P).IsPrimary := by
  sorry

-- SimisFormal.groupedComponents_radical : levels [u_1, u_2, u_3]
theorem SimisFormal.groupedComponents_radical.{u_1, u_2, u_3} {σ : Type u_1}
    {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hcomp : SimisFormal.HasComponents I A a) (hpos : ∀ j i, i ∈ A j → 0 < a j i)
    (P : I.minimalPrimes) :
    (SimisFormal.groupedComponents I A a P).radical = P.1 := by
  sorry

-- SimisFormal.monomial_mem_diagonal : levels [u_1, u_2]
theorem SimisFormal.monomial_mem_diagonal.{u_1, u_2} {σ : Type u_1} {K : Type u_2} [Field K] [DecidableEq σ] [Fintype σ] {I : Ideal (MvPolynomial σ K)} (hI : SimisFormal.IsMonomialIdeal I) {d : σ → ℕ} (hd : ∀ (i : σ), 0 < d i) {e : σ →₀ ℕ} : (MvPolynomial.monomial e) 1 ∈ SimisFormal.diagonal d I ↔ (MvPolynomial.monomial (SimisFormal.floorDiv d e)) 1 ∈ I := by
  sorry

-- SimisFormal.diagExp_le_iff_le_of_pos : levels [u_1]
theorem SimisFormal.diagExp_le_iff_le_of_pos.{u_1} {σ : Type u_1} [Fintype σ] {d : σ → ℕ} (hd : ∀ (i : σ), 0 < d i) (u v : σ →₀ ℕ) : SimisFormal.diagExp d u ≤ SimisFormal.diagExp d v ↔ u ≤ v := by
  sorry

-- SimisFormal.eq4_diagonal_iInf : levels [u_1, u_2, u_3]
theorem SimisFormal.eq4_diagonal_iInf.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} [Field K] [DecidableEq σ] [Fintype σ] {ι : Type u_3} [Fintype ι] {Q : ι → Ideal (MvPolynomial σ K)} (hQ : ∀ (j : ι), SimisFormal.IsMonomialIdeal (Q j)) {d : σ → ℕ} (hd : ∀ (i : σ), 0 < d i) : SimisFormal.diagonal d (⨅ (j : ι), Q j) = ⨅ (j : ι), SimisFormal.diagonal d (Q j) := by
  sorry

-- SimisFormal.eq4_diagonal_le_iff_le : levels [u_1, u_2]
theorem SimisFormal.eq4_diagonal_le_iff_le.{u_1, u_2} {σ : Type u_1} {K : Type u_2} [Field K] [DecidableEq σ] [Fintype σ] {d : σ → ℕ} (hd : ∀ (i : σ), 0 < d i) {I J : Ideal (MvPolynomial σ K)} (hI : SimisFormal.IsMonomialIdeal I) (hJ : SimisFormal.IsMonomialIdeal J) : SimisFormal.diagonal d I ≤ SimisFormal.diagonal d J ↔ I ≤ J := by
  sorry

-- SimisFormal.diagonal_minGens : levels [u_1, u_2]
theorem SimisFormal.diagonal_minGens.{u_1, u_2} {σ : Type u_1} {K : Type u_2} [Field K] [DecidableEq σ] [Fintype σ] {I : Ideal (MvPolynomial σ K)} {d : σ → ℕ} (hI : SimisFormal.IsMonomialIdeal I) (hd : ∀ (i : σ), 0 < d i) : SimisFormal.minGens (SimisFormal.diagonal d I) = SimisFormal.diagExp d '' SimisFormal.minGens I := by
  sorry

-- SimisFormal.diagAssoc_associatedPrimes_diagonal_eq_of_monomial : levels [u_1, u_2]
theorem SimisFormal.diagAssoc_associatedPrimes_diagonal_eq_of_monomial.{u_1, u_2} {σ : Type u_1} {K : Type u_2} [Field K] [DecidableEq σ] [Fintype σ] {L : Ideal (MvPolynomial σ K)} {d : σ → ℕ} (hL : SimisFormal.IsMonomialIdeal L) (hd : ∀ (i : σ), 0 < d i) : associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ SimisFormal.diagonal d L) = associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ L) := by
  sorry

-- SimisFormal.diagAssoc_preservesCanonical_and_Ass : levels [u_1, u_2, u_3]
theorem SimisFormal.diagAssoc_preservesCanonical_and_Ass.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} {d : σ → ℕ} (hd : ∀ (i : σ), 0 < d i) (hI : SimisFormal.HasComponents I A a) (hirr : SimisFormal.IsIrredundant (K := K) A a) : (SimisFormal.diagonal (K := K) d '' SimisFormal.diagAssoc_groupedComponents A a = SimisFormal.diagAssoc_groupedComponents A fun (j : ι) (i : σ) => a j i * d i) ∧ SimisFormal.diagAssoc_IsCanonicalPrimarySet I (SimisFormal.diagAssoc_groupedComponents A a) ∧ SimisFormal.diagAssoc_IsCanonicalPrimarySet (SimisFormal.diagonal d I) (SimisFormal.diagAssoc_groupedComponents A fun (j : ι) (i : σ) => a j i * d i) ∧ associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ SimisFormal.diagonal d I) = associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) := by
  sorry

-- SimisFormal.diagAssoc_associatedPrimes_pow_diagonal_eq_of_monomial : levels [u_1, u_2]
theorem SimisFormal.diagAssoc_associatedPrimes_pow_diagonal_eq_of_monomial.{u_1, u_2} {σ : Type u_1} {K : Type u_2} [Field K] [DecidableEq σ] [Fintype σ] {J : Ideal (MvPolynomial σ K)} {d : σ → ℕ} (hJ : SimisFormal.IsMonomialIdeal J) (hd : ∀ (i : σ), 0 < d i) (q : ℕ) (hq : 1 ≤ q) : associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ SimisFormal.diagonal d J ^ q) = associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ J ^ q) := by
  sorry

-- SimisFormal.prop21_NormallyTorsionFree_diagonal_iff_of_isMonomialIdeal : levels [u_1, u_2]
theorem SimisFormal.prop21_NormallyTorsionFree_diagonal_iff_of_isMonomialIdeal.{u_1, u_2} {σ : Type u_1} {K : Type u_2} [Field K] [DecidableEq σ] [Fintype σ] {J : Ideal (MvPolynomial σ K)} {d : σ → ℕ} (hJ : SimisFormal.IsMonomialIdeal J) (hd : ∀ (i : σ), 0 < d i) : SimisFormal.prop21NormallyTorsionFree (SimisFormal.diagonal d J) ↔ SimisFormal.prop21NormallyTorsionFree J := by
  sorry

-- SimisFormal.eq4_isSimis_diagonal_iff_of_isMonomialIdeal : levels [u_1, u_2]
theorem SimisFormal.eq4_isSimis_diagonal_iff_of_isMonomialIdeal.{u_1, u_2} {σ : Type u_1} {K : Type u_2} [Field K] [DecidableEq σ] [Fintype σ] {J : Ideal (MvPolynomial σ K)} {d : σ → ℕ} (hJ : SimisFormal.IsMonomialIdeal J) (hd : ∀ (i : σ), 0 < d i) : SimisFormal.IsSimis J ↔ SimisFormal.IsSimis (SimisFormal.diagonal d J) := by
  sorry

-- SimisFormal.prop21_NormallyTorsionFree_iff_of_sqRoot_of_fintype : levels [u_1, u_2]
theorem SimisFormal.prop21_NormallyTorsionFree_iff_of_sqRoot_of_fintype.{u_1, u_2} {σ : Type u_1} {K : Type u_2} [Field K] [DecidableEq σ] [Fintype σ] {I J : Ideal (MvPolynomial σ K)} {d : σ → ℕ} (hJ : SimisFormal.IsSquarefreeMonomialIdeal J) (hd : ∀ (i : σ), 0 < d i) (hdiag : SimisFormal.diagonal d J = I) : SimisFormal.prop21NormallyTorsionFree I ↔ SimisFormal.prop21NormallyTorsionFree J := by
  sorry

-- SimisFormal.prop21_main : levels [u_1, u_2, u_3]
theorem SimisFormal.prop21_main.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2}
    {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype σ] [Fintype ι] [LinearOrder ι]
    {I : Ideal (MvPolynomial σ K)} (hBot : I ≠ ⊥) (hTop : I ≠ ⊤)
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hDecomp : SimisFormal.IsIrredundantDecomp I A a) :
    (∀ i, SimisFormal.generatorExponents I i = SimisFormal.componentExponents A a i) ∧
      (SimisFormal.HasSqRoot I ↔ ∀ i, (SimisFormal.generatorExponents I i).Subsingleton) ∧
        (SimisFormal.HasSqRoot I ↔ ∀ i, (SimisFormal.componentExponents A a i).Subsingleton) ∧
          (SimisFormal.HasSqRoot I ↔ SimisFormal.prop21_XI A a = ∅) ∧
            (SimisFormal.HasSqRoot I →
              SimisFormal.IsSquarefreeMonomialIdeal I.radical ∧
                I.radical = ⨅ j, (SimisFormal.primeOf (A j) : Ideal (MvPolynomial σ K)) ∧
                  (∀ (J : Ideal (MvPolynomial σ K)) (d : σ → ℕ),
                    SimisFormal.IsSquarefreeMonomialIdeal J → (∀ i, 0 < d i) →
                      SimisFormal.diagonal d J = I → J = I.radical) ∧
                    (∀ (J₁ J₂ : Ideal (MvPolynomial σ K)) (d₁ d₂ : σ → ℕ),
                      SimisFormal.IsSquarefreeMonomialIdeal J₁ → (∀ i, 0 < d₁ i) →
                        SimisFormal.diagonal d₁ J₁ = I → SimisFormal.IsSquarefreeMonomialIdeal J₂ →
                          (∀ i, 0 < d₂ i) → SimisFormal.diagonal d₂ J₂ = I → J₁ = J₂) ∧
                      SimisFormal.IsIrredundant (K := K) A (fun _ _ ↦ (1 : ℕ)) ∧
                        Function.Injective
                          (fun j ↦ (SimisFormal.primeOf (A j) : Ideal (MvPolynomial σ K))) ∧
                          (∀ j k, j ≠ k → ¬
                            (SimisFormal.primeOf (A j) : Ideal (MvPolynomial σ K)) ≤
                              SimisFormal.primeOf (A k)) ∧
                            associatedPrimes (MvPolynomial σ K)
                                (MvPolynomial σ K ⧸ I) = I.minimalPrimes ∧
                              (∀ (J : Ideal (MvPolynomial σ K)) (d : σ → ℕ) (i : σ) (n : ℕ),
                                SimisFormal.IsSquarefreeMonomialIdeal J → (∀ t, 0 < d t) →
                                  SimisFormal.diagonal d J = I → n ∈ SimisFormal.componentExponents A a i →
                                    n = d i) ∧
                                (∀ d : σ → ℕ, (∀ i, 0 < d i) →
                                  (∀ (j : ι) (i : σ), i ∈ A j → a j i = d i) →
                                    SimisFormal.diagonal d (I.radical) = I)) := by
  sorry

-- thm31_main : levels [u_1]
theorem thm31_main.{u_1} {K : Type u_1} [Field K] (r s : ℕ) (hr : 0 < r) (hs : 0 < s) : SimisFormal.IsIrredundantDecomp (thm31_I (K := K) r s) thm31_support (thm31_componentExp r s) ∧ (associatedPrimes (MvPolynomial thm31_var K) (MvPolynomial thm31_var K ⧸ thm31_I r s) = Set.range fun (j : Fin 4) => SimisFormal.primeOf (thm31_support j)) ∧ ((thm31_I (K := K) r s).minimalPrimes = Set.range fun (j : Fin 4) => SimisFormal.primeOf (thm31_support j)) ∧ associatedPrimes (MvPolynomial thm31_var K) (MvPolynomial thm31_var K ⧸ thm31_I r s) = (thm31_I r s).minimalPrimes ∧ (∀ (q : ℕ), 1 ≤ q → SimisFormal.symbolicPower (thm31_I (K := K) r s) q = thm31_I r s ^ q ∧ thm31_I (K := K) r s ^ q = ⨅ (j : Fin 4), thm31_component r s j ^ q) ∧ SimisFormal.IsSimis (thm31_I (K := K) r s) ∧ SimisFormal.MPVHypotheses (thm31_I (K := K) r s) thm31_support (thm31_componentExp r s) ∧ (thm31_I r s).radical = thm31_M (K := K) ∧ SimisFormal.SupportPreserving (thm31_I (K := K) r s) ∧ SimisFormal.supportComplex (thm31_I (K := K) r s) = SimisFormal.supportComplex thm31_M (K := K) ∧ (SimisFormal.HasSqRoot (thm31_I (K := K) r s) ↔ r = s) ∧ SimisFormal.IsSimis (thm31_M (K := K)) ∧ (SimisFormal.MPVConc (thm31_I (K := K) r s) ↔ r = s) := by
  sorry

-- thm31_main_decomposition : levels [u_1]
theorem thm31_main_decomposition.{u_1} {K : Type u_1} [Field K] (r s : ℕ) (hr : 0 < r) (hs : 0 < s) : SimisFormal.IsIrredundantDecomp (thm31_I (K := K) r s) thm31_support (thm31_componentExp r s) ∧ (∀ (j : Fin 4), (thm31_component (K := K) r s j).radical = SimisFormal.primeOf (thm31_support j)) ∧ (∀ (j k : Fin 4), (thm31_component (K := K) r s j).radical ≤ (thm31_component r s k).radical → j = k) ∧ (Function.Injective fun (j : Fin 4) => (thm31_component (K := K) r s j).radical) ∧ (thm31_component (K := K) r s 0).radical.height = 3 ∧ (thm31_component (K := K) r s 1).radical.height = 2 ∧ (thm31_component (K := K) r s 2).radical.height = 2 ∧ (thm31_component r s (K := K) 3).radical.height = 3 := by
  sorry

-- thm31_main_root : levels [u_1]
theorem thm31_main_root.{u_1} {K : Type u_1} [Field K] (r s : ℕ) (hr : 0 < r) (hs : 0 < s) : (SimisFormal.HasSqRoot (thm31_I (K := K) r s) ↔ r = s) ∧ SimisFormal.IsSimis (thm31_M (K := K)) ∧ (SimisFormal.MPVConc (thm31_I (K := K) r s) ↔ r = s) ∧ (r ≠ s → ¬SimisFormal.MPVConc (thm31_I (K := K) r s)) ∧ (r = s → SimisFormal.IsSquarefreeMonomialIdeal thm31_M (K := K) ∧ (∀ (i : thm31_var), 0 < thm31_weight r i) ∧ SimisFormal.diagonal (thm31_weight r) thm31_M (K := K) = thm31_I r s ∧ ∀ {J : Ideal (MvPolynomial thm31_var K)} {d : thm31_var → ℕ}, SimisFormal.IsSquarefreeMonomialIdeal J → (∀ (i : thm31_var), 0 < d i) → SimisFormal.diagonal d J = thm31_I r s → J = thm31_M ∧ d = thm31_weight r) := by
  sorry

-- SimisFormal.rem32_omittedRoot_isSquarefree : levels [u_1]
theorem SimisFormal.rem32_omittedRoot_isSquarefree.{u_1} {K : Type u_1} [Field K] : SimisFormal.IsSquarefreeMonomialIdeal SimisFormal.rem32_omittedRootIdeal (K := K) := by
  sorry

-- SimisFormal.rem32_cannotOmitZ_fromRoot : levels [u_1]
theorem SimisFormal.rem32_cannotOmitZ_fromRoot.{u_1} {K : Type u_1} [Field K] {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (w : SimisFormal.rem32_var → ℕ) : SimisFormal.diagonal w SimisFormal.rem32_omittedRootIdeal ≠ SimisFormal.rem32_familyIdeal (K := K) r s := by
  sorry

-- SimisFormal.rem32_omittedWeight_diagonal_eq_root_and_ne_family : levels [u_1]
theorem SimisFormal.rem32_omittedWeight_diagonal_eq_root_and_ne_family.{u_1} {K : Type u_1} [Field K] {t : ℕ} (ht : 0 < t) : SimisFormal.diagonal (SimisFormal.rem32_omittedWeight t) SimisFormal.rem32_omittedRootIdeal (K := K) = SimisFormal.rem32_omittedRootIdeal ∧ SimisFormal.rem32_omittedRootIdeal ≠ SimisFormal.rem32_familyIdeal (K := K) t t := by
  sorry

-- SimisFormal.rem32_omittedWeight_ab_mem_root_not_mem_family : levels [u_1]
theorem SimisFormal.rem32_omittedWeight_ab_mem_root_not_mem_family.{u_1} {K : Type u_1} [Field K] {t : ℕ} (ht : 0 < t) : MvPolynomial.X SimisFormal.rem32_var.a * MvPolynomial.X SimisFormal.rem32_var.b ∈ SimisFormal.rem32_omittedRootIdeal (K := K) ∧ MvPolynomial.X SimisFormal.rem32_var.a * MvPolynomial.X SimisFormal.rem32_var.b ∉ SimisFormal.rem32_familyIdeal (K := K) t t := by
  sorry

-- SimisFormal.rem32_generator_isClutter : levels []
theorem SimisFormal.rem32_generator_isClutter : SimisFormal.IsClutter SimisFormal.rem32_generatorClutter := by
  sorry

-- SimisFormal.rem32_component_isClutter : levels []
theorem SimisFormal.rem32_component_isClutter : SimisFormal.IsClutter SimisFormal.rem32_componentClutter := by
  sorry

-- SimisFormal.rem32_family_supportComplex_eq_generator : levels [u_1]
theorem SimisFormal.rem32_family_supportComplex_eq_generator.{u_1} {K : Type u_1} [Field K] {r s : ℕ} (hr : 0 < r) (hs : 0 < s) : SimisFormal.supportComplex (SimisFormal.rem32_familyIdeal (K := K) r s) = SimisFormal.rem32_generatorClutter := by
  sorry

-- SimisFormal.rem32_family_minimalPrimes_eq_image_component : levels [u_1]
theorem SimisFormal.rem32_family_minimalPrimes_eq_image_component.{u_1} {K : Type u_1} [Field K] {r s : ℕ} (hr : 0 < r) (hs : 0 < s) : (SimisFormal.rem32_familyIdeal r s).minimalPrimes = (fun (A : Finset SimisFormal.rem32_var) => SimisFormal.primeOf (K := K) A) '' SimisFormal.rem32_componentClutter := by
  sorry

-- SimisFormal.rem32_blocker_generator : levels []
theorem SimisFormal.rem32_blocker_generator : SimisFormal.blocker SimisFormal.rem32_generatorClutter = SimisFormal.rem32_componentClutter := by
  sorry

-- SimisFormal.rem32_blocker_component : levels []
theorem SimisFormal.rem32_blocker_component : SimisFormal.blocker SimisFormal.rem32_componentClutter = SimisFormal.rem32_generatorClutter := by
  sorry

-- SimisFormal.rem32_generator_hasStrongTriangle : levels []
theorem SimisFormal.rem32_generator_hasStrongTriangle : SimisFormal.HasStrongTriangle SimisFormal.rem32_generatorClutter := by
  sorry

-- SimisFormal.rem32_component_hasStrongTriangle : levels []
theorem SimisFormal.rem32_component_hasStrongTriangle : SimisFormal.HasStrongTriangle SimisFormal.rem32_componentClutter := by
  sorry

-- SimisFormal.rem32_generator_omittedEdge_disjoint_cycleVertices : levels []
theorem SimisFormal.rem32_generator_omittedEdge_disjoint_cycleVertices : Disjoint SimisFormal.rem32_bd (Finset.image SimisFormal.rem32_generatorCycleVertices Finset.univ) := by
  sorry

-- SimisFormal.rem32_component_omittedEdge_disjoint_cycleVertices : levels []
theorem SimisFormal.rem32_component_omittedEdge_disjoint_cycleVertices : Disjoint SimisFormal.rem32_bc (Finset.image SimisFormal.rem32_componentCycleVertices Finset.univ) := by
  sorry

-- SimisFormal.rem32_generator_not_balanced : levels []
theorem SimisFormal.rem32_generator_not_balanced : ¬SimisFormal.IsBalanced SimisFormal.rem32_generatorClutter := by
  sorry

-- SimisFormal.rem32_component_not_balanced : levels []
theorem SimisFormal.rem32_component_not_balanced : ¬SimisFormal.IsBalanced SimisFormal.rem32_componentClutter := by
  sorry

-- SimisFormal.cor33_main : levels [u_2, u_3, u_4]
theorem SimisFormal.cor33_main.{u_2, u_3, u_4} {K : Type u_2} [Field K] {r s : ℕ} (hr : 0 < r) (hs : 0 < s) : SimisFormal.Cor33Conclusion.{u_2, u_3, u_4} (K := K) hr hs := by
  sorry

-- SimisFormal.coneClutter_hasStrongCycle_iff : levels [u_1]
theorem SimisFormal.coneClutter_hasStrongCycle_iff.{u_1} {σ : Type u_1} [DecidableEq σ] {H : Set (Finset σ)} {q : ℕ} : SimisFormal.HasStrongCycle (SimisFormal.coneClutter H) q ↔ SimisFormal.HasStrongCycle H q := by
  sorry

-- SimisFormal.coneClutter_isBalanced_iff : levels [u_1]
theorem SimisFormal.coneClutter_isBalanced_iff.{u_1} {σ : Type u_1} [DecidableEq σ] {H : Set (Finset σ)} : SimisFormal.IsBalanced (SimisFormal.coneClutter H) ↔ SimisFormal.IsBalanced H := by
  sorry

-- SimisFormal.cor33_cone_supportComplex_hasStrongTriangle : levels [u_2]
theorem SimisFormal.cor33_cone_supportComplex_hasStrongTriangle.{u_2} {K : Type u_2} [Field K] {r s : ℕ} (hr : 0 < r) (hs : 0 < s) : SimisFormal.HasStrongTriangle (SimisFormal.supportComplex (SimisFormal.cor33ConeIdeal (K := K) r s)) := by
  sorry

-- SimisFormal.cor33_cone_supportComplex_not_isBalanced : levels [u_2]
theorem SimisFormal.cor33_cone_supportComplex_not_isBalanced.{u_2} {K : Type u_2} [Field K] {r s : ℕ} (hr : 0 < r) (hs : 0 < s) : ¬SimisFormal.IsBalanced (SimisFormal.supportComplex (SimisFormal.cor33ConeIdeal (K := K) r s)) := by
  sorry

-- SimisFormal.cor33_coneComponentClutter_hasStrongTriangle : levels []
theorem SimisFormal.cor33_coneComponentClutter_hasStrongTriangle : SimisFormal.HasStrongTriangle SimisFormal.cor33ConeComponentClutter := by
  sorry

-- SimisFormal.cor33_coneComponentClutter_not_isBalanced : levels []
theorem SimisFormal.cor33_coneComponentClutter_not_isBalanced : ¬SimisFormal.IsBalanced SimisFormal.cor33ConeComponentClutter := by
  sorry

-- SimisFormal.cor33_cone_component_radical : levels [u_2]
theorem SimisFormal.cor33_cone_component_radical.{u_2} {K : Type u_2} [Field K] {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (j : Option SimisFormal.Cor33Comp) : (SimisFormal.purePower (SimisFormal.conePureSupport SimisFormal.cor33ComponentSupport j) (SimisFormal.conePureExp (SimisFormal.cor33ComponentExp r s) j)).radical = SimisFormal.purePower (K := K) (SimisFormal.conePureSupport SimisFormal.cor33ComponentSupport j) fun (x : Option SimisFormal.Cor33Var) => 1 := by
  sorry

-- SimisFormal.cor33_cone_minGens : levels [u_2]
theorem SimisFormal.cor33_cone_minGens.{u_2} {K : Type u_2} [Field K] {r s : ℕ} : SimisFormal.minGens (SimisFormal.cor33ConeIdeal (K := K) r s) = SimisFormal.coneExp '' ↑(SimisFormal.cor33BaseGens r s) := by
  sorry

-- SimisFormal.lem42 : levels [u_1, u_2, u_3]
theorem SimisFormal.lem42.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hmpv : SimisFormal.MPVHypotheses I A a) (hsp : SimisFormal.SupportPreserving I) (hstd : SimisFormal.HasStdSymbolicFormula I fun (j : ι) => SimisFormal.purePower (A j) (a j)) : (∀ F ∈ SimisFormal.supportComplex I, ∃! e : σ →₀ ℕ, e ∈ SimisFormal.minGens I ∧ e.support = F) ∧ ∀ (F G : Finset σ), F ∈ SimisFormal.supportComplex I → G ∈ SimisFormal.supportComplex I → F ≠ G → {E : Finset σ | E ∈ SimisFormal.supportComplex I ∧ E ⊆ F ∪ G} = {F, G} → ∀ (u v : σ →₀ ℕ), u ∈ SimisFormal.minGens I → v ∈ SimisFormal.minGens I → u.support = F → v.support = G → ∀ i ∈ F, i ∈ G → u i = v i := by
  sorry

-- SimisFormal.lem42_oneGenerator : levels [u_1, u_2, u_3]
theorem SimisFormal.lem42_oneGenerator.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hmpv : SimisFormal.MPVHypotheses I A a) (hsp : SimisFormal.SupportPreserving I) (hstd : SimisFormal.HasStdSymbolicFormula I fun (j : ι) => SimisFormal.purePower (A j) (a j)) (F : Finset σ) : F ∈ SimisFormal.supportComplex I → ∃! e : σ →₀ ℕ, e ∈ SimisFormal.minGens I ∧ e.support = F := by
  sorry

-- SimisFormal.lem42_isolatedEqualExponents : levels [u_1, u_2, u_3]
theorem SimisFormal.lem42_isolatedEqualExponents.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hmpv : SimisFormal.MPVHypotheses I A a) (hsp : SimisFormal.SupportPreserving I) (hstd : SimisFormal.HasStdSymbolicFormula I fun (j : ι) => SimisFormal.purePower (A j) (a j)) {F G : Finset σ} (hF : F ∈ SimisFormal.supportComplex I) (hG : G ∈ SimisFormal.supportComplex I) (hFG : F ≠ G) (hIso : {E : Finset σ | E ∈ SimisFormal.supportComplex I ∧ E ⊆ F ∪ G} = {F, G}) {u v : σ →₀ ℕ} (hu : u ∈ SimisFormal.minGens I) (hv : v ∈ SimisFormal.minGens I) (hsuppU : u.support = F) (hsuppV : v.support = G) {i : σ} (hiF : i ∈ F) (hiG : i ∈ G) : u i = v i := by
  sorry

-- SimisFormal.lem42_of_mpv : levels [u_1, u_2, u_3]
theorem SimisFormal.lem42_of_mpv.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hmpv : SimisFormal.MPVHypotheses I A a) (hsp : SimisFormal.SupportPreserving I) : (∀ F ∈ SimisFormal.supportComplex I, ∃! e : σ →₀ ℕ, e ∈ SimisFormal.minGens I ∧ e.support = F) ∧ ∀ (F G : Finset σ), F ∈ SimisFormal.supportComplex I → G ∈ SimisFormal.supportComplex I → F ≠ G → {E : Finset σ | E ∈ SimisFormal.supportComplex I ∧ E ⊆ F ∪ G} = {F, G} → ∀ (u v : σ →₀ ℕ), u ∈ SimisFormal.minGens I → v ∈ SimisFormal.minGens I → u.support = F → v.support = G → ∀ i ∈ F, i ∈ G → u i = v i := by
  sorry

-- SimisFormal.lem42_oneGenerator_of_mpv : levels [u_1, u_2, u_3]
theorem SimisFormal.lem42_oneGenerator_of_mpv.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hmpv : SimisFormal.MPVHypotheses I A a) (hsp : SimisFormal.SupportPreserving I) (F : Finset σ) : F ∈ SimisFormal.supportComplex I → ∃! e : σ →₀ ℕ, e ∈ SimisFormal.minGens I ∧ e.support = F := by
  sorry

-- SimisFormal.lem42_isolatedEqualExponents_of_mpv : levels [u_1, u_2, u_3]
theorem SimisFormal.lem42_isolatedEqualExponents_of_mpv.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hmpv : SimisFormal.MPVHypotheses I A a) (hsp : SimisFormal.SupportPreserving I) {F G : Finset σ} (hF : F ∈ SimisFormal.supportComplex I) (hG : G ∈ SimisFormal.supportComplex I) (hFG : F ≠ G) (hIso : {E : Finset σ | E ∈ SimisFormal.supportComplex I ∧ E ⊆ F ∪ G} = {F, G}) {u v : σ →₀ ℕ} (hu : u ∈ SimisFormal.minGens I) (hv : v ∈ SimisFormal.minGens I) (hsuppU : u.support = F) (hsuppV : v.support = G) {i : σ} (hiF : i ∈ F) (hiG : i ∈ G) : u i = v i := by
  sorry

-- SimisFormal.lem43_isolation_of_nonconstant : levels [u_1, u_2]
theorem SimisFormal.lem43_isolation_of_nonconstant.{u_1, u_2} {σ : Type u_1} {Λ : Type u_2} [DecidableEq σ] {H : Set (Finset σ)} {z : σ} (hcl : SimisFormal.IsClutter H) (htri : ¬SimisFormal.HasStrongTriangle H) (lab : SimisFormal.lem43_facetsThrough H z → Λ) (hnc : ∃ (A : SimisFormal.lem43_facetsThrough H z) (B : SimisFormal.lem43_facetsThrough H z), lab A ≠ lab B) : ∃ (A : SimisFormal.lem43_facetsThrough H z) (B : SimisFormal.lem43_facetsThrough H z), lab A ≠ lab B ∧ {E : Finset σ | E ∈ H ∧ E ⊆ ↑A ∪ ↑B} = {↑A, ↑B} := by
  sorry

-- SimisFormal.thm41_full : levels [u_1, u_2, u_3]
theorem SimisFormal.thm41_full.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} [Field K] [DecidableEq σ] {ι : Type u_3} [Fintype σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hI0 : I ≠ ⊥) (hIproper : I ≠ ⊤) (hMPV : SimisFormal.MPVHypotheses I A a) (hsp : SimisFormal.SupportPreserving I) (hno : ¬SimisFormal.HasStrongTriangle (SimisFormal.supportComplex I)) : SimisFormal.thm41_lem42OneGenerator I ∧ SimisFormal.thm41_generatorCoherence I ∧ ∃ (d : σ → ℕ), (∀ (i : σ), 0 < d i) ∧ (∀ (i : σ) (F : Finset σ) (u : σ →₀ ℕ), F ∈ SimisFormal.supportComplex I → i ∈ F → u ∈ SimisFormal.minGens I → u.support = F → d i = u i) ∧ (∀ (i : σ), (∀ F ∈ SimisFormal.supportComplex I, i ∉ F) → d i = 1) ∧ SimisFormal.IsSquarefreeMonomialIdeal (SimisFormal.thm41_squarefreeRoot I) ∧ SimisFormal.thm41_squarefreeRoot I = I.radical ∧ I = SimisFormal.diagonal d (SimisFormal.thm41_squarefreeRoot I) ∧ SimisFormal.IsSimis (SimisFormal.thm41_squarefreeRoot I) := by
  sorry

-- SimisFormal.thm41_full_of_balanced : levels [u_1, u_2, u_3]
theorem SimisFormal.thm41_full_of_balanced.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} [Field K] [DecidableEq σ] {ι : Type u_3} [Fintype σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hI0 : I ≠ ⊥) (hIproper : I ≠ ⊤) (hMPV : SimisFormal.MPVHypotheses I A a) (hsp : SimisFormal.SupportPreserving I) (hbal : SimisFormal.IsBalanced (SimisFormal.supportComplex I)) : SimisFormal.thm41_lem42OneGenerator I ∧ SimisFormal.thm41_generatorCoherence I ∧ ∃ (d : σ → ℕ), (∀ (i : σ), 0 < d i) ∧ (∀ (i : σ) (F : Finset σ) (u : σ →₀ ℕ), F ∈ SimisFormal.supportComplex I → i ∈ F → u ∈ SimisFormal.minGens I → u.support = F → d i = u i) ∧ (∀ (i : σ), (∀ F ∈ SimisFormal.supportComplex I, i ∉ F) → d i = 1) ∧ SimisFormal.IsSquarefreeMonomialIdeal (SimisFormal.thm41_squarefreeRoot I) ∧ SimisFormal.thm41_squarefreeRoot I = I.radical ∧ I = SimisFormal.diagonal d (SimisFormal.thm41_squarefreeRoot I) ∧ SimisFormal.IsSimis (SimisFormal.thm41_squarefreeRoot I) := by
  sorry

-- SimisFormal.lem51_twoComponents : levels [u_1]
theorem SimisFormal.lem51_twoComponents.{u_1} {K : Type u_1} [Field K]
    {l m a b : ℕ} (hl : 0 < l) (hlm : l < m) (ha : 0 < a) (hb : 0 < b) :
    let A : Ideal (MvPolynomial (Fin 3) K) :=
      SimisFormal.purePower (K := K) ({0, 1} : Finset (Fin 3)) (![l, a, 0] : Fin 3 → ℕ)
    let B : Ideal (MvPolynomial (Fin 3) K) :=
      SimisFormal.purePower (K := K) ({0, 2} : Finset (Fin 3)) (![m, 0, b] : Fin 3 → ℕ)
    (A ⊓ B) ^ 2 < A ^ 2 ⊓ B ^ 2 := by
  sorry

-- SimisFormal.lem51_threeComponents_C2 : levels [u_1]
theorem SimisFormal.lem51_threeComponents_C2.{u_1} {K : Type u_1} [Field K]
    {l m a b g d : ℕ} (hl : 0 < l) (hlm : l < m) (ha : 0 < a) (hb : 0 < b)
    (hg : 0 < g) (hd : 0 < d) :
    let A : Ideal (MvPolynomial (Fin 3) K) :=
      SimisFormal.purePower (K := K) ({0, 1} : Finset (Fin 3)) (![l, a, 0] : Fin 3 → ℕ)
    let B : Ideal (MvPolynomial (Fin 3) K) :=
      SimisFormal.purePower (K := K) ({0, 2} : Finset (Fin 3)) (![m, 0, b] : Fin 3 → ℕ)
    let C : Ideal (MvPolynomial (Fin 3) K) :=
      SimisFormal.purePower (K := K) ({1, 2} : Finset (Fin 3)) (![0, g, d] : Fin 3 → ℕ)
    (A ⊓ B ⊓ C) ^ 2 < A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2 := by
  sorry

-- SimisFormal.lem51_threeComponents_C3 : levels [u_1]
theorem SimisFormal.lem51_threeComponents_C3.{u_1} {K : Type u_1} [Field K]
    {l m a b t g d : ℕ} (hl : 0 < l) (hlm : l < m) (ha : 0 < a) (hb : 0 < b)
    (ht : 0 < t) (hg : 0 < g) (hd : 0 < d) :
    let A : Ideal (MvPolynomial (Fin 3) K) :=
      SimisFormal.purePower (K := K) ({0, 1} : Finset (Fin 3)) (![l, a, 0] : Fin 3 → ℕ)
    let B : Ideal (MvPolynomial (Fin 3) K) :=
      SimisFormal.purePower (K := K) ({0, 2} : Finset (Fin 3)) (![m, 0, b] : Fin 3 → ℕ)
    let C : Ideal (MvPolynomial (Fin 3) K) :=
      SimisFormal.purePower (K := K) ({0, 1, 2} : Finset (Fin 3)) (![t, g, d] : Fin 3 → ℕ)
    (A ⊓ B ⊓ C) ^ 2 < A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2 := by
  sorry

-- SimisFormal.comparison51_bk25 : levels [u_1, u_2, u_3]
theorem SimisFormal.comparison51_bk25.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype σ] [Fintype ι] [LinearOrder ι] [DecidableEq ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (_hI0 : I ≠ ⊥) (_hItop : I ≠ ⊤) (hdec : SimisFormal.IsIrredundantDecomp I A a) (hNoEmb : associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) = I.minimalPrimes) (hDistinct : ∀ (j k : ι), SimisFormal.primeOf (K := K) (A j) = SimisFormal.primeOf (A k) → j = k) (_hUsed : Finset.univ.biUnion A = Finset.univ) (hcond : SimisFormal.comparison51_Condition13 A a) : SimisFormal.IsSimis I ↔ SimisFormal.MPVConc I := by
  sorry

-- SimisFormal.comparison51_bk25_heightTwo : levels [u_1, u_2, u_3]
theorem SimisFormal.comparison51_bk25_heightTwo.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype σ] [Fintype ι] [LinearOrder ι] [DecidableEq ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (_hI0 : I ≠ ⊥) (_hItop : I ≠ ⊤) (hdec : SimisFormal.IsIrredundantDecomp I A a) (hNoEmb : associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) = I.minimalPrimes) (hDistinct : ∀ (j k : ι), SimisFormal.primeOf (K := K) (A j) = SimisFormal.primeOf (A k) → j = k) (_hUsed : Finset.univ.biUnion A = Finset.univ) (hcard : ∀ (j : ι), (A j).card = 2) : SimisFormal.IsSimis I ↔ SimisFormal.MPVConc I := by
  sorry

-- SimisFormal.comparison51_counterexample : levels [u_2]
theorem SimisFormal.comparison51_counterexample.{u_2} {K : Type u_2} [Field K] : SimisFormal.comparison51_I (K := K) = SimisFormal.primeOf Finset.univ ^ 2 ∧ SimisFormal.IsIrredundantDecomp SimisFormal.comparison51_I (K := K) SimisFormal.comparison51_A SimisFormal.comparison51_a ∧ (SimisFormal.purePower (K := K) (SimisFormal.comparison51_A 0) (SimisFormal.comparison51_a 0)).radical = (SimisFormal.purePower (SimisFormal.comparison51_A 1) (SimisFormal.comparison51_a 1)).radical ∧ (¬Function.Injective fun (j : Fin 2) => (SimisFormal.purePower (K := K) (SimisFormal.comparison51_A j) (SimisFormal.comparison51_a j)).radical) ∧ associatedPrimes (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) K ⧸ SimisFormal.comparison51_I) = SimisFormal.comparison51_I.minimalPrimes ∧ SimisFormal.IsSimis (SimisFormal.comparison51_I (K := K)) ∧ thm52_IncidenceBound SimisFormal.comparison51_A ∧ SimisFormal.comparison51_Condition13 SimisFormal.comparison51_A SimisFormal.comparison51_a ∧ ¬SimisFormal.HasSqRoot SimisFormal.comparison51_I (K := K) := by
  sorry

-- SimisFormal.comparison51_representedMPV_noSeparation : levels [u_1, u_2, u_3]
theorem SimisFormal.comparison51_representedMPV_noSeparation.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype σ] [Fintype ι] [LinearOrder ι] [DecidableEq ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (_hI0 : I ≠ ⊥) (_hItop : I ≠ ⊤) (hdec : SimisFormal.IsIrredundantDecomp I A a) (hmpv : SimisFormal.MPVConc I) :
  have U := SimisFormal.comparison51_usedVariables A;
  have A' := SimisFormal.comparison51_restrictFinset U A;
  have a' := SimisFormal.comparison51_restrictWeight U a;
  have I' := SimisFormal.comparison51_restrictIdeal U A a;
  SimisFormal.IsIrredundantDecomp I' A' a' ∧ SimisFormal.SupportsAntichain A' a' ∧ Finset.univ.biUnion A' = Finset.univ ∧ SimisFormal.comparison51_Condition13 A' a' ∧ associatedPrimes (MvPolynomial (↥U) K) (MvPolynomial (↥U) K ⧸ I') = I'.minimalPrimes ∧ (∀ (j k : ι), SimisFormal.primeOf (K := K) (A' j) = SimisFormal.primeOf (A' k) → j = k) ∧ SimisFormal.IsSimis I' ∧ SimisFormal.MPVConc I' ∧ (SimisFormal.IsSimis I' ↔ SimisFormal.MPVConc I') ∧ (SimisFormal.IsSimis I ↔ SimisFormal.IsSimis I') ∧ (SimisFormal.MPVConc I ↔ SimisFormal.MPVConc I') := by
  sorry

-- SimisFormal.prop21_hasSqRoot_iff_XI_eq_empty : levels [u_1, u_2, u_3]
theorem SimisFormal.prop21_hasSqRoot_iff_XI_eq_empty.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype σ] [LinearOrder ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hI : SimisFormal.HasComponents I A a) (hIrr : SimisFormal.IsIrredundant (K := K) A a) : SimisFormal.HasSqRoot I ↔ SimisFormal.prop21_XI A a = ∅ := by
  sorry

-- SimisFormal.comparison51_condition13_of_hasSqRoot : levels [u_1, u_2, u_3]
theorem SimisFormal.comparison51_condition13_of_hasSqRoot.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype σ] [Fintype ι] [LinearOrder ι] [DecidableEq ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hI : SimisFormal.HasComponents I A a) (hIrr : SimisFormal.IsIrredundant (K := K) A a) (hroot : SimisFormal.HasSqRoot I) : SimisFormal.comparison51_Condition13 A a := by
  sorry

-- SimisFormal.comparison51_restrict_package : levels [u_1, u_2, u_3]
theorem SimisFormal.comparison51_restrict_package.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype σ] [Fintype ι] [LinearOrder ι] [DecidableEq ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hdec : SimisFormal.IsIrredundantDecomp I A a) (hroot : SimisFormal.HasSqRoot I) :
  have U := SimisFormal.comparison51_usedVariables A;
  have A' := SimisFormal.comparison51_restrictFinset U A;
  have a' := SimisFormal.comparison51_restrictWeight U a;
  have I' := SimisFormal.comparison51_restrictIdeal U A a;
  SimisFormal.IsIrredundantDecomp I' A' a' ∧ SimisFormal.HasSqRoot I' ∧ SimisFormal.SupportsAntichain A' a' ∧ Finset.univ.biUnion A' = Finset.univ ∧ (SimisFormal.IsSimis I ↔ SimisFormal.IsSimis I') ∧ (SimisFormal.MPVConc I ↔ SimisFormal.MPVConc (K := K) I') := by
  sorry

-- thm52_of_paperHypotheses : levels [u_1, u_2, u_3]
theorem thm52_of_paperHypotheses.{u_1, u_2, u_3} {σ : Type u_1} {ι : Type u_2} [DecidableEq σ] {K : Type u_3} [Field K] [Fintype σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤) (hdec : SimisFormal.IsIrredundantDecomp I A a) (hNoEmb : associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) = I.minimalPrimes) (hDistinct : ∀ (j k : ι), SimisFormal.primeOf (K := K) (A j) = SimisFormal.primeOf (A k) → j = k) (hinc : thm52_IncidenceBound A) (hsymbolic2 : SimisFormal.symbolicPower I 2 = I ^ 2) : (∀ (j k : ι), ∀ i ∈ A j, i ∈ A k → a j i = a k i) ∧ ∃ (d : σ → ℕ), (∀ (i : σ), 0 < d i) ∧ (∀ (j : ι), ∀ i ∈ A j, d i = a j i) ∧ SimisFormal.IsSquarefreeMonomialIdeal (thm52_root (K := K) A) ∧ (SimisFormal.IsIrredundantDecomp (thm52_root (K := K) A) A fun (x : ι) (x_1 : σ) => 1) ∧ thm52_root A = I.radical ∧ SimisFormal.diagonal d (thm52_root A) = I := by
  sorry

-- thm52 : levels [u_1, u_2, u_3]
theorem thm52.{u_1, u_2, u_3} {σ : Type u_1} {ι : Type u_2} [DecidableEq σ] {K : Type u_3} [Field K] [Fintype σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (_hI0 : I ≠ ⊥) (_hItop : I ≠ ⊤) (hdec : SimisFormal.IsIrredundantDecomp I A a) (hanti : SimisFormal.SupportsAntichain A a) (hinc : thm52_IncidenceBound A) (hsymbolic2 : SimisFormal.symbolicPower I 2 = I ^ 2) : (∀ (j k : ι), ∀ i ∈ A j, i ∈ A k → a j i = a k i) ∧ ∃ (d : σ → ℕ), (∀ (i : σ), 0 < d i) ∧ (∀ (j : ι), ∀ i ∈ A j, d i = a j i) ∧ SimisFormal.IsSquarefreeMonomialIdeal (thm52_root (K := K) A) ∧ (SimisFormal.IsIrredundantDecomp (thm52_root (K := K) A) A fun (x : ι) (x_1 : σ) => 1) ∧ thm52_root A = I.radical ∧ SimisFormal.diagonal d (thm52_root A) = I := by
  sorry

-- thm52_hasSqRoot : levels [u_1, u_2, u_3]
theorem thm52_hasSqRoot.{u_1, u_2, u_3} {σ : Type u_1} {ι : Type u_2} [DecidableEq σ] {K : Type u_3} [Field K] [Fintype σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤) (hdec : SimisFormal.IsIrredundantDecomp I A a) (hanti : SimisFormal.SupportsAntichain A a) (hinc : thm52_IncidenceBound A) (hsymbolic2 : SimisFormal.symbolicPower I 2 = I ^ 2) : SimisFormal.HasSqRoot I := by
  sorry

-- thm52_bound_one_sharp : levels [u_3]
theorem thm52_bound_one_sharp.{u_3} {K : Type u_3} [Field K] (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) : ∃ (I : Ideal (MvPolynomial thm31_var K)) (A : Fin 4 → Finset thm31_var) (a : Fin 4 → thm31_var → ℕ), I ≠ ⊥ ∧ I ≠ ⊤ ∧ SimisFormal.IsIrredundantDecomp I A a ∧ SimisFormal.SupportsAntichain A a ∧ ¬thm52_IncidenceBound A ∧ thm52_TwoIntervenorBound A ∧ SimisFormal.IsSimis I ∧ SimisFormal.symbolicPower I 2 = I ^ 2 ∧ ¬SimisFormal.HasSqRoot I ∧ ¬SimisFormal.MPVConc I := by
  sorry

-- thm52_IncidenceBound_of_card_eq_two : levels [u_1, u_2]
theorem thm52_IncidenceBound_of_card_eq_two.{u_1, u_2} {σ : Type u_1} {ι : Type u_2} [DecidableEq σ] {A : ι → Finset σ} {a : ι → σ → ℕ} (hanti : SimisFormal.SupportsAntichain A a) (hcard : ∀ (j : ι), (A j).card = 2) : thm52_IncidenceBound A := by
  sorry

-- thm52_diagonal_root_eq_of_agreement : levels [u_1, u_2, u_3]
theorem thm52_diagonal_root_eq_of_agreement.{u_1, u_2, u_3} {σ : Type u_1} {ι : Type u_2} [DecidableEq σ] {K : Type u_3} [Field K] [Fintype σ] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} {d : σ → ℕ} (hI : SimisFormal.HasComponents I A a) (hd : ∀ (i : σ), 0 < d i) (hdEq : ∀ (j : ι), ∀ i ∈ A j, d i = a j i) : SimisFormal.diagonal d (thm52_root A) = I := by
  sorry

-- thm52_supportsAntichain_of_paperHypotheses : levels [u_1, u_2, u_3]
theorem thm52_supportsAntichain_of_paperHypotheses.{u_1, u_2, u_3} {σ : Type u_1} {ι : Type u_2} [DecidableEq σ] {K : Type u_3} [Field K] [Fintype σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hdec : SimisFormal.IsIrredundantDecomp I A a) (hNoEmb : associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) = I.minimalPrimes) (hDistinct : ∀ (j k : ι), SimisFormal.primeOf (K := K) (A j) = SimisFormal.primeOf (A k) → j = k) : SimisFormal.SupportsAntichain A a := by
  sorry

-- thm31_isIntervenor_ABZ_CDZ_iff : levels []
theorem thm31_isIntervenor_ABZ_CDZ_iff (j : Fin 4) : thm52_isIntervenor thm31_support 0 3 j ↔ j = 1 ∨ j = 2 := by
  sorry

-- thm31_support_thm52_TwoIntervenorBound : levels []
theorem thm31_support_thm52_TwoIntervenorBound : thm52_TwoIntervenorBound thm31_support := by
  sorry

-- thm31_I_ne_bot : levels [u_1]
theorem thm31_I_ne_bot.{u_1} {K : Type u_1} [Field K] (r s : ℕ) : thm31_I (K := K) r s ≠ ⊥ := by
  sorry

-- thm31_I_ne_top : levels [u_1]
theorem thm31_I_ne_top.{u_1} {K : Type u_1} [Field K] (r s : ℕ) : thm31_I (K := K) r s ≠ ⊤ := by
  sorry

-- thm31_isIrredundantDecomp : levels [u_1]
theorem thm31_isIrredundantDecomp.{u_1} {K : Type u_1} [Field K] (r s : ℕ) (hr : 0 < r) (hs : 0 < s) : SimisFormal.IsIrredundantDecomp (thm31_I (K := K) r s) thm31_support (thm31_componentExp r s) := by
  sorry

-- thm31_supportsAntichain : levels []
theorem thm31_supportsAntichain (r s : ℕ) : SimisFormal.SupportsAntichain thm31_support (thm31_componentExp r s) := by
  sorry

-- thm31_isSimis : levels [u_1]
theorem thm31_isSimis.{u_1} {K : Type u_1} [Field K] (r s : ℕ) (hr : 0 < r) (hs : 0 < s) : SimisFormal.IsSimis (thm31_I (K := K) r s) := by
  sorry

-- thm31_symbolicPower_eq_pow : levels [u_1]
theorem thm31_symbolicPower_eq_pow.{u_1} {K : Type u_1} [Field K] (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (q : ℕ) (hq : 1 ≤ q) : SimisFormal.symbolicPower (thm31_I (K := K) r s) q = thm31_I r s ^ q := by
  sorry

-- thm31_hasSqRoot_iff : levels [u_1]
theorem thm31_hasSqRoot_iff.{u_1} {K : Type u_1} [Field K] (r s : ℕ) (hr : 0 < r) (hs : 0 < s) : SimisFormal.HasSqRoot (thm31_I (K := K) r s) ↔ r = s := by
  sorry

-- thm31_MPVConc_iff : levels [u_1]
theorem thm31_MPVConc_iff.{u_1} {K : Type u_1} [Field K] (r s : ℕ) (hr : 0 < r) (hs : 0 < s) : SimisFormal.MPVConc (thm31_I (K := K) r s) ↔ r = s := by
  sorry

-- SimisFormal.cor53_of_paperHypotheses : levels [u_1, u_2, u_3]
theorem SimisFormal.cor53_of_paperHypotheses.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤) (hdec : SimisFormal.IsIrredundantDecomp I A a) (hNoEmb : associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) = I.minimalPrimes) (hDistinct : ∀ (j k : ι), SimisFormal.primeOf (K := K) (A j) = SimisFormal.primeOf (A k) → j = k) (hinc : thm52_IncidenceBound A) (hSimis : SimisFormal.IsSimis I) : SimisFormal.IsSimis (thm52_root (K := K) A) ∧ SimisFormal.MPVConc I ∧ thm52_root A = I.radical ∧ SimisFormal.IsSimis I.radical ∧ ∃ (d : σ → ℕ), (∀ (i : σ), 0 < d i) ∧ SimisFormal.IsSquarefreeMonomialIdeal (thm52_root (K := K) A) ∧ SimisFormal.diagonal d (thm52_root A) = I := by
  sorry

-- SimisFormal.cor53_forcedRootData_verified : levels [u_1, u_2, u_3]
theorem SimisFormal.cor53_forcedRootData_verified.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype σ] [Fintype ι] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} (hstruct : SimisFormal.cor53_StructuralHypotheses I A a) (hinc : SimisFormal.cor53_AtMostOneIntervenor A) (hsimis : SimisFormal.IsSimis I) : ∃ (d : σ → ℕ), (∀ (i : σ), 0 < d i) ∧ SimisFormal.IsSquarefreeMonomialIdeal (thm52_root (K := K) A) ∧ (SimisFormal.IsIrredundantDecomp (thm52_root (K := K) A) A fun (x : ι) (x_1 : σ) => 1) ∧ SimisFormal.IsSimis (thm52_root (K := K) A) ∧ thm52_root A = I.radical ∧ SimisFormal.diagonal d (thm52_root A) = I := by
  sorry

-- SimisFormal.eq4_isSimis_diagonal_iff_of_irredundantDecomp : levels [u_1, u_2, u_3]
theorem SimisFormal.eq4_isSimis_diagonal_iff_of_irredundantDecomp.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2} [Field K] [DecidableEq σ] [Fintype σ] {ι : Type u_3} [Fintype ι] {J : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} {d : σ → ℕ} (hd : ∀ (i : σ), 0 < d i) (hdecomp : SimisFormal.IsIrredundantDecomp J A a) (hanti : SimisFormal.SupportsAntichain A a) : SimisFormal.IsSimis J ↔ SimisFormal.IsSimis (SimisFormal.diagonal d J) := by
  sorry

-- thm52_arbitraryUnusedWeights : levels [u_1, u_2, u_3]
theorem thm52_arbitraryUnusedWeights.{u_1, u_2, u_3} {σ : Type u_1} {ι : Type u_2} [DecidableEq σ] {K : Type u_3} [Field K] [Fintype σ] {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} {w : σ → ℕ} (_hI0 : I ≠ ⊥) (_hItop : I ≠ ⊤) (hdec : SimisFormal.IsIrredundantDecomp I A a) (_hanti : SimisFormal.SupportsAntichain A a) (_hinc : thm52_IncidenceBound A) (_hsymbolic2 : SimisFormal.symbolicPower I 2 = I ^ 2) (hwpos : ∀ (i : σ), 0 < w i) (hwEq : ∀ (j : ι), ∀ i ∈ A j, w i = a j i) : SimisFormal.diagonal w (thm52_root A) = I := by
  sorry

-- SimisFormal.prop21_sqRoot_unique : levels [u_1, u_2]
theorem SimisFormal.prop21_sqRoot_unique.{u_1, u_2} {σ : Type u_1} {K : Type u_2} [Field K] [DecidableEq σ] [Fintype σ] {I J₁ J₂ : Ideal (MvPolynomial σ K)} {d₁ d₂ : σ → ℕ} (hJ₁ : SimisFormal.IsSquarefreeMonomialIdeal J₁) (hd₁ : ∀ (i : σ), 0 < d₁ i) (hdiag₁ : SimisFormal.diagonal d₁ J₁ = I) (hJ₂ : SimisFormal.IsSquarefreeMonomialIdeal J₂) (hd₂ : ∀ (i : σ), 0 < d₂ i) (hdiag₂ : SimisFormal.diagonal d₂ J₂ = I) : J₁ = J₂ := by
  sorry

-- SimisFormal.prop61_main_full_with_prose : levels [u_1]
theorem SimisFormal.prop61_main_full_with_prose.{u_1} {K : Type u_1} [Field K] {m : ℕ} (hm : 2 ≤ m) {d : SimisFormal.prop61_var m → ℕ} (hd : ∀ (i : SimisFormal.prop61_var m), 0 < d i) : ((SimisFormal.minGens (SimisFormal.prop61_J (K := K) m) = SimisFormal.characteristicExp '' SimisFormal.prop61_H m ∧ SimisFormal.minGens (SimisFormal.prop61_I (K := K) m d) = SimisFormal.diagExp d '' SimisFormal.characteristicExp '' SimisFormal.prop61_H m ∧ (SimisFormal.prop61_I m d).radical = SimisFormal.prop61_J (K := K) m ∧ SimisFormal.supportComplex (SimisFormal.prop61_J (K := K) m) = SimisFormal.prop61_H m ∧ SimisFormal.supportComplex (SimisFormal.prop61_I (K := K) m d) = SimisFormal.prop61_H m ∧ (∀ E ∈ SimisFormal.prop61_H m, E.card = 4) ∧ SimisFormal.IsBalanced (SimisFormal.prop61_H m) ∧ ¬SimisFormal.IsSimplicialForest (SimisFormal.prop61_H m) ∧ (∀ U ⊂ SimisFormal.prop61_H m, U.Nonempty → SimisFormal.IsSimplicialForest U) ∧ SimisFormal.prop61_DecompositionInput (K := K) m d ∧ SimisFormal.IsSimis (SimisFormal.prop61_J (K := K) m) ∧ SimisFormal.IsSimis (SimisFormal.prop61_I (K := K) m d) ∧ SimisFormal.MPVConc (SimisFormal.prop61_I (K := K) m d)) ∧ (associatedPrimes (MvPolynomial (SimisFormal.prop61_var m) K) (MvPolynomial (SimisFormal.prop61_var m) K ⧸ SimisFormal.prop61_J m) = Set.range fun (C : SimisFormal.prop61_componentIndex m) => (SimisFormal.primeOf C.1 : Ideal (MvPolynomial (SimisFormal.prop61_var m) K))) ∧ (associatedPrimes (MvPolynomial (SimisFormal.prop61_var m) K) (MvPolynomial (SimisFormal.prop61_var m) K ⧸ SimisFormal.prop61_I m d) = Set.range fun (C : SimisFormal.prop61_componentIndex m) => (SimisFormal.primeOf C.1 : Ideal (MvPolynomial (SimisFormal.prop61_var m) K))) ∧ SimisFormal.prop21NormallyTorsionFree (SimisFormal.prop61_J (K := K) m) ∧ SimisFormal.prop21NormallyTorsionFree (SimisFormal.prop61_I (K := K) m d) ∧ ∀ (q : ℕ), 1 ≤ q → associatedPrimes (MvPolynomial (SimisFormal.prop61_var m) K) (MvPolynomial (SimisFormal.prop61_var m) K ⧸ SimisFormal.prop61_I m d ^ q) = Set.range fun (C : SimisFormal.prop61_componentIndex m) => (SimisFormal.primeOf C.1 : Ideal (MvPolynomial (SimisFormal.prop61_var m) K))) ∧ ((d ≠ fun (x : SimisFormal.prop61_var m) => 1) → ¬SimisFormal.IsSquarefreeMonomialIdeal (SimisFormal.prop61_I (K := K) m d)) ∧ (SimisFormal.IsSquarefreeMonomialIdeal (SimisFormal.prop61_I (K := K) m d) ↔ d = fun (x : SimisFormal.prop61_var m) => 1) ∧ (∀ E ∈ SimisFormal.prop61_H m, SimisFormal.IsSimplicialForest (SimisFormal.prop61_H m \ {E})) ∧ (∀ e ∈ SimisFormal.minGens (SimisFormal.prop61_J (K := K) m), 3 < e.support.card) ∧ ∀ e ∈ SimisFormal.minGens (SimisFormal.prop61_I (K := K) m d), 3 < e.support.card := by
  sorry

-- SimisFormal.prop61_I_eq_diagonal : levels [u_1]
theorem SimisFormal.prop61_I_eq_diagonal.{u_1} {K : Type u_1} [Field K] (m : ℕ) (d : SimisFormal.prop61_var m → ℕ) : SimisFormal.prop61_I m d = SimisFormal.diagonal d (SimisFormal.prop61_J (K := K) m) := by
  sorry

-- SimisFormal.prop61_var_natCard : levels []
theorem SimisFormal.prop61_var_natCard (m : ℕ) : Nat.card (SimisFormal.prop61_var m) = 6 * m := by
  sorry

-- SimisFormal.prop61_ringKrullDim : levels [u_1]
theorem SimisFormal.prop61_ringKrullDim.{u_1} {K : Type u_1} [Field K] (m : ℕ) : ringKrullDim (MvPolynomial (SimisFormal.prop61_var m) K) = ↑(6 * m) := by
  sorry

-- SimisFormal.prop61_ambientRings_pairwise_not_ringEquiv : levels [u_1]
theorem SimisFormal.prop61_ambientRings_pairwise_not_ringEquiv.{u_1} {K : Type u_1} [Field K] {m n : ℕ} (hmn : m ≠ n) : IsEmpty (MvPolynomial (SimisFormal.prop61_var m) K ≃+* MvPolynomial (SimisFormal.prop61_var n) K) := by
  sorry

-- SimisFormal.prop61_ambientFamily_pairwiseDistinct : levels [u_1]
theorem SimisFormal.prop61_ambientFamily_pairwiseDistinct.{u_1} {K : Type u_1} [Field K] {m n : ℕ} : 2 ≤ m → 2 ≤ n → m ≠ n → IsEmpty (MvPolynomial (SimisFormal.prop61_var m) K ≃+* MvPolynomial (SimisFormal.prop61_var n) K) := by
  sorry

-- SimisFormal.prop61_associatedPrimes_J_pow_eq_of_ntf : levels [u_1]
theorem SimisFormal.prop61_associatedPrimes_J_pow_eq_of_ntf.{u_1} {K : Type u_1} [Field K] (m : ℕ) (hntfJ : SimisFormal.prop21NormallyTorsionFree (SimisFormal.prop61_J (K := K) m)) (q : ℕ) : 1 ≤ q → associatedPrimes (MvPolynomial (SimisFormal.prop61_var m) K) (MvPolynomial (SimisFormal.prop61_var m) K ⧸ SimisFormal.prop61_J m ^ q) = Set.range fun (C : SimisFormal.prop61_componentIndex m) => (SimisFormal.primeOf C.1 : Ideal (MvPolynomial (SimisFormal.prop61_var m) K)) := by
  sorry

-- SimisFormal.prop62_main : levels [u_1, u_2, u_3]
theorem SimisFormal.prop62_main.{u_1, u_2, u_3} {σ : Type u_1} {K : Type u_2}
    {ι : Type u_3} [Field K] [DecidableEq σ] [Fintype σ] [Fintype ι]
    {B : ι → Finset σ} (hB : SimisFormal.prop62_BlockFamily B) {a : σ → ℕ}
    (ha : ∀ x : σ, 0 < a x) :
    let R := MvPolynomial σ K
    let I : Ideal R := SimisFormal.prop62_weightedIdeal (K := K) B a
    let J : Ideal R := SimisFormal.prop62_rootIdeal (K := K) B
    let A : ι → σ → ℕ := fun _ ↦ a
    let O : ι → σ → ℕ := fun _ ↦ fun _ ↦ 1
    let Q : ι → Ideal R := fun h ↦ SimisFormal.purePower (K := K) (B h) a
    let P : ι → Ideal R := fun h ↦ SimisFormal.primeOf (K := K) (B h)
    SimisFormal.HasComponents I B A ∧
      SimisFormal.HasComponents J B O ∧
      SimisFormal.IsIrredundant (K := K) B A ∧
      SimisFormal.IsIrredundant (K := K) B O ∧
      SimisFormal.IsIrredundantDecomp I B A ∧
      SimisFormal.IsIrredundantDecomp J B O ∧
      SimisFormal.SupportsAntichain B A ∧
      SimisFormal.SupportsAntichain B O ∧
      (∀ h, (P h).height = ((B h).card : ℕ∞)) ∧
      (∀ h, (Q h).height = ((B h).card : ℕ∞)) ∧
      SimisFormal.minGens I = SimisFormal.prop62_weightedTransversalGens B a ∧
      SimisFormal.minGens J = SimisFormal.prop62_transversalGens B ∧
      (∀ q : ℕ, I ^ q = SimisFormal.componentSymbolic Q q) ∧
      (∀ q : ℕ, J ^ q = SimisFormal.componentSymbolic P q) ∧
      SimisFormal.HasStdSymbolicFormula I Q ∧
      SimisFormal.HasStdSymbolicFormula J P ∧
      SimisFormal.IsSimis I ∧
      SimisFormal.IsSimis J ∧
      SimisFormal.MPVConc I ∧
      associatedPrimes R (R ⧸ I) = Set.range P ∧
      associatedPrimes R (R ⧸ J) = Set.range P ∧
      (∀ q : ℕ, 1 ≤ q → associatedPrimes R (R ⧸ I ^ q) = Set.range P) ∧
      (∀ q : ℕ, 1 ≤ q → associatedPrimes R (R ⧸ J ^ q) = Set.range P) ∧
      SimisFormal.prop21NormallyTorsionFree I ∧
      SimisFormal.prop21NormallyTorsionFree J ∧
      SimisFormal.SupportPreserving I ∧
      I.radical = J ∧
      SimisFormal.diagonal a J = I ∧
      SimisFormal.IsSquarefreeMonomialIdeal J ∧
      SimisFormal.supportComplex I = SimisFormal.prop62_facets B ∧
      SimisFormal.supportComplex J = SimisFormal.prop62_facets B ∧
      SimisFormal.mismatchPairs B A = ∅ ∧
      (∀ k l, SimisFormal.prop62_intervenorSet B k l = ∅) ∧
      (SimisFormal.prop62_twoLargeBlocks B →
        ¬ ∃ F, SimisFormal.IsLeaf (SimisFormal.prop62_facets B) F) ∧
      (SimisFormal.prop62_threeLargeBlocks B →
        SimisFormal.HasStrongTriangle (SimisFormal.prop62_facets B)) ∧
      (SimisFormal.IsSquarefreeMonomialIdeal I ↔ a = fun _ : σ ↦ 1) ∧
      (∀ {J' : Ideal R} {d : σ → ℕ}, SimisFormal.IsSquarefreeMonomialIdeal J' →
        (∀ x, 0 < d x) → SimisFormal.diagonal d J' = I → J' = J ∧ d = a) ∧
      (∀ {J₁ J₂ : Ideal R} {d₁ d₂ : σ → ℕ},
        SimisFormal.IsSquarefreeMonomialIdeal J₁ → (∀ x, 0 < d₁ x) →
          SimisFormal.diagonal d₁ J₁ = I →
        SimisFormal.IsSquarefreeMonomialIdeal J₂ → (∀ x, 0 < d₂ x) →
          SimisFormal.diagonal d₂ J₂ = I →
          J₁ = J₂) ∧
      ∀ {J' : Ideal R} {d : σ → ℕ}, SimisFormal.IsSquarefreeMonomialIdeal J' →
        (∀ x, 0 < d x) → SimisFormal.diagonal d J' = I →
          ∀ h x, x ∈ B h → d x = a x := by
  sorry

-- ex63_main : levels [u_1]
theorem ex63_main.{u_1} {K : Type u_1} [Field K] : ex63_MainCombinatorics (K := K) ∧ ex63_MainAlgebra (K := K) := by
  sorry

-- ex63_minGens_J : levels [u_1]
theorem ex63_minGens_J.{u_1} {K : Type u_1} [Field K] : SimisFormal.minGens ex63_J (K := K) = ↑(ex63_transversalGens 1) := by
  sorry

-- ex63_minGens_I : levels [u_1]
theorem ex63_minGens_I.{u_1} {K : Type u_1} [Field K] : SimisFormal.minGens ex63_I (K := K) = ↑(ex63_transversalGens 2) := by
  sorry

-- ex63_transversalGens_card : levels []
theorem ex63_transversalGens_card (w : ℕ) (hw : w ≠ 0) : (ex63_transversalGens w).card = 24 := by
  sorry

-- ex63_blockProduct_eq_monomialIdeal : levels [u_1]
theorem ex63_blockProduct_eq_monomialIdeal.{u_1} {K : Type u_1} [Field K] (w : ℕ) : ex63_blockProduct (K := K) w = SimisFormal.monomialIdeal (Set.range (ex63_transExpWeight w)) := by
  sorry

-- ex63_J_eq_monomialIdeal : levels [u_1]
theorem ex63_J_eq_monomialIdeal.{u_1} {K : Type u_1} [Field K] : ex63_J (K := K) = SimisFormal.monomialIdeal (Set.range (ex63_transExpWeight 1)) := by
  sorry

-- ex63_I_eq_blockProduct : levels [u_1]
theorem ex63_I_eq_blockProduct.{u_1} {K : Type u_1} [Field K] : ex63_I (K := K) = ex63_blockProduct 2 := by
  sorry

-- ex63_supportComplex_J : levels [u_1]
theorem ex63_supportComplex_J.{u_1} {K : Type u_1} [Field K] : SimisFormal.supportComplex ex63_J (K := K) = ↑ex63_facets := by
  sorry

-- ex63_supportComplex_I : levels [u_1]
theorem ex63_supportComplex_I.{u_1} {K : Type u_1} [Field K] : SimisFormal.supportComplex ex63_I (K := K) = ↑ex63_facets := by
  sorry

-- ex63_triangleVertices_injective : levels []
theorem ex63_triangleVertices_injective : Function.Injective ex63_triangleVertices := by
  sorry

-- ex63_triangleEdges_injective : levels []
theorem ex63_triangleEdges_injective : Function.Injective ex63_triangleEdges := by
  sorry

-- ex63_triangleEdges_mem_facets : levels []
theorem ex63_triangleEdges_mem_facets (i : Fin 3) :
    ex63_triangleEdges i ∈ (ex63_facets : Set (Finset ex63_var)) := by
  sorry

-- ex63_triangle_incidence : levels []
theorem ex63_triangle_incidence (i : Fin 3) : ex63_triangleEdges i ∩ Finset.image ex63_triangleVertices Finset.univ = {ex63_triangleVertices i, ex63_triangleVertices (SimisFormal.finSuccMod i)} := by
  sorry

-- ex63_ComponentCriterion : levels [u_1]
theorem ex63_ComponentCriterion.{u_1} {K : Type u_1} [Field K] : ex63_I (K := K) ≠ ⊥ ∧ ex63_I (K := K) ≠ ⊤ ∧ (SimisFormal.IsIrredundantDecomp ex63_I (K := K) ex63_block fun (x : Fin 4) (x_1 : ex63_var) => 2) ∧ (SimisFormal.SupportsAntichain ex63_block fun (x : Fin 4) (x_1 : ex63_var) => 2) ∧ ex63_IncidenceBound ∧ SimisFormal.symbolicPower (ex63_I (K := K)) 2 = ex63_I ^ 2 := by
  sorry

-- ex63_incidenceBound_thm52 : levels []
theorem ex63_incidenceBound_thm52 : thm52_IncidenceBound ex63_block := by
  sorry

-- ex63_XI_eq_empty : levels []
theorem ex63_XI_eq_empty : ex63_XI = ∅ := by
  sorry

-- ex63_mismatchPairs_eq_empty : levels []
theorem ex63_mismatchPairs_eq_empty : (SimisFormal.mismatchPairs ex63_block fun (x : Fin 4) (x_1 : ex63_var) => 2) = ∅ := by
  sorry

-- ex63_intervenors_empty : levels []
theorem ex63_intervenors_empty (k l : Fin 4) : ex63_intervenors k l = ∅ := by
  sorry

-- ex63_notSeparatingMismatchCriterion : levels []
theorem ex63_notSeparatingMismatchCriterion : ¬ex63_XI.Nonempty := by
  sorry
