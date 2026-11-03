import SimisFormal.Defs
import SimisFormal.Basic
import SimisFormal.Prop2_1
import SimisFormal.Thm5_2
import SimisFormal.Eq2_GroupedSymbolic
import SimisFormal.Eq4_DiagonalSimis
import SimisFormal.DiagAssociatedPreserve

namespace SimisFormal
open MvPolynomial
variable {σ K ι : Type*} [Field K] [DecidableEq σ]
/-- A squarefree diagonal representation forces condition (13). -/
theorem comparison51_condition13_of_hasSqRoot
    [Fintype σ] [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hIrr : IsIrredundant (K := K) A a) (hroot : HasSqRoot I) :
    comparison51_Condition13 A a := by
  intro p hp
  have hX : prop21_XI A a = ∅ :=
    (prop21_hasSqRoot_iff_XI_eq_empty (K := K) hI hIrr).mp hroot
  rw [hX] at hp
  exact hp.elim

/-- The displayed intersection is the square of the maximal variable ideal. -/
theorem comparison51_I_eq_primeOf_sq :
    (comparison51_I : Ideal (MvPolynomial (Fin 2) K)) =
      (primeOf (Finset.univ : Finset (Fin 2)) : Ideal (MvPolynomial (Fin 2) K)) ^ 2 := by
  let S : Set (Fin 2 →₀ ℕ) :=
    {e | ∃ i ∈ (Finset.univ : Finset (Fin 2)), e = Finsupp.single i 1}
  have hPrime : (primeOf (Finset.univ : Finset (Fin 2)) :
      Ideal (MvPolynomial (Fin 2) K)) = monomialIdeal S := rfl
  apply eq4_eq_of_monomial_mem
  · unfold IsMonomialIdeal
    rw [comparison51_I]
    simp only [purePower]
    rw [monomialIdeal_inf]
    exact ⟨_, rfl⟩
  · exact eq4_isMonomialIdeal_pow (⟨S, hPrime⟩ : IsMonomialIdeal
        (primeOf (Finset.univ : Finset (Fin 2)) : Ideal (MvPolynomial (Fin 2) K))) 2
  · intro e
    rw [comparison51_I, hPrime,
      _root_.thm52_monomial_mem_monomialIdeal_sq_iff (K := K) (S := S) (e := e)]
    constructor
    · intro h
      have h0 := monomial_mem_purePower.mp h.1
      have h1 := monomial_mem_purePower.mp h.2
      simp [comparison51_A, comparison51_a] at h0 h1
      rcases h0 with hx2 | hy
      · refine ⟨Finsupp.single 0 1, ?_, Finsupp.single 0 1, ?_, ?_⟩ <;>
          try simp [S]
        intro i
        fin_cases i <;> simp [hx2]
      · rcases h1 with hx | hy2
        · refine ⟨Finsupp.single 0 1, ?_, Finsupp.single 1 1, ?_, ?_⟩ <;>
            try simp [S]
          intro i
          fin_cases i <;> simp [hx, hy]
        · refine ⟨Finsupp.single 1 1, ?_, Finsupp.single 1 1, ?_, ?_⟩ <;>
            try simp [S]
          intro i
          fin_cases i <;> simp [hy2]
    · rintro ⟨u, ⟨i, -, rfl⟩, v, ⟨j, -, rfl⟩, huv⟩
      fin_cases i <;> fin_cases j
      all_goals
        have h0 := huv (0 : Fin 2)
        have h1 := huv (1 : Fin 2)
        simp at h0 h1
        simp [monomial_mem_purePower, comparison51_A, comparison51_a]
        omega

/-- The displayed two-component family is an irredundant decomposition. -/
theorem comparison51_isIrredundantDecomp :
    IsIrredundantDecomp (K := K) comparison51_I comparison51_A comparison51_a := by
  constructor
  · rw [HasComponents, comparison51_I, _root_.thm52_iInf_fin_two]
  · intro j hle
    let x : MvPolynomial (Fin 2) K := monomial (Finsupp.single 0 1) 1
    let y : MvPolynomial (Fin 2) K := monomial (Finsupp.single 1 1) 1
    fin_cases j
    · have hx : x ∈ decompOmit (K := K) comparison51_A comparison51_a 0 := by
        rw [decompOmit]
        refine Ideal.mem_iInf.mpr ?_
        rintro ⟨k, hk⟩
        fin_cases k
        · exact (hk rfl).elim
        · exact monomial_mem_purePower.mpr ⟨0, by simp [comparison51_A], by simp [comparison51_a]⟩
      have hnx : x ∉ purePower (K := K) (comparison51_A 0) (comparison51_a 0) := by
        simp [x, monomial_mem_purePower, comparison51_A, comparison51_a]
      exact hnx (hle hx)
    · have hy : y ∈ decompOmit (K := K) comparison51_A comparison51_a 1 := by
        rw [decompOmit]
        refine Ideal.mem_iInf.mpr ?_
        rintro ⟨k, hk⟩
        fin_cases k
        · exact monomial_mem_purePower.mpr
            ⟨1, by simp [comparison51_A], by simp [comparison51_a]⟩
        · exact (hk rfl).elim
      have hny : y ∉ purePower (K := K) (comparison51_A 1) (comparison51_a 1) := by
        simp [y, monomial_mem_purePower, comparison51_A, comparison51_a]
      exact hny (hle hy)

/-- Both displayed component radicals are the same maximal variable prime. -/
theorem comparison51_component_radical (j : Fin 2) :
    (purePower (K := K) (comparison51_A j) (comparison51_a j) :
      Ideal (MvPolynomial (Fin 2) K)).radical =
        primeOf (Finset.univ : Finset (Fin 2)) := by
  have hpos : ∀ i ∈ comparison51_A j, 0 < comparison51_a j i := by
    intro i hi
    fin_cases j <;> fin_cases i <;> simp [comparison51_a]
  simpa [comparison51_A] using (purePower_radical_eq_primeOf (K := K) hpos)

/-- The example has no embedded primes. -/
theorem comparison51_associatedPrimes_eq_minimalPrimes :
    associatedPrimes (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) K ⧸ comparison51_I) =
      (comparison51_I : Ideal (MvPolynomial (Fin 2) K)).minimalPrimes := by
  have hdec := comparison51_isIrredundantDecomp (K := K)
  have hrad : (comparison51_I : Ideal (MvPolynomial (Fin 2) K)).radical =
      primeOf (Finset.univ : Finset (Fin 2)) := by
    simpa [comparison51_A] using prop21_radical_eq_iInf_primeOf hdec.1 hdec.2
  have hp : (primeOf (Finset.univ : Finset (Fin 2)) :
      Ideal (MvPolynomial (Fin 2) K)).IsPrime := primeOf_isPrime _
  have hmin : (comparison51_I : Ideal (MvPolynomial (Fin 2) K)).minimalPrimes =
      {primeOf (Finset.univ : Finset (Fin 2))} := by
    calc
      _ = (comparison51_I : Ideal (MvPolynomial (Fin 2) K)).radical.minimalPrimes :=
        (Ideal.radical_minimalPrimes
          (I := (comparison51_I : Ideal (MvPolynomial (Fin 2) K)))).symm
      _ = (primeOf (Finset.univ : Finset (Fin 2)) :
          Ideal (MvPolynomial (Fin 2) K)).minimalPrimes := by rw [hrad]
      _ = _ := Ideal.minimalPrimes_eq_subsingleton_self
  calc
    associatedPrimes (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) K ⧸ comparison51_I) =
        Set.range (fun j ↦ (primeOf (comparison51_A j) : Ideal (MvPolynomial (Fin 2) K))) :=
      diagAssoc_quotientAssociatedPrimes_eq_range hdec.1 hdec.2
    _ = {primeOf (Finset.univ : Finset (Fin 2))} := by
      ext P
      simp [comparison51_A]
    _ = (comparison51_I : Ideal (MvPolynomial (Fin 2) K)).minimalPrimes := hmin.symm

/-- Every positive power of the example is \((x,y)\)-primary, hence Simis. -/
theorem comparison51_isSimis : IsSimis (comparison51_I : Ideal (MvPolynomial (Fin 2) K)) := by
  classical
  have hdec := comparison51_isIrredundantDecomp (K := K)
  have hpos : ∀ j i, i ∈ comparison51_A j → 0 < comparison51_a j i :=
    exponents_pos_of_irredundant (K := K) hdec.2
  have htop : (comparison51_I : Ideal (MvPolynomial (Fin 2) K)) ≠ ⊤ := by
    intro ht
    have hOne : (1 : MvPolynomial (Fin 2) K) ∈ comparison51_I := by simp [ht]
    rw [comparison51_I] at hOne
    have hx : (monomial (0 : Fin 2 →₀ ℕ) (1 : K) : MvPolynomial (Fin 2) K) ∈
        purePower (K := K) (comparison51_A 0) (comparison51_a 0) := by
      simpa using hOne.1
    have hnot : (monomial (0 : Fin 2 →₀ ℕ) (1 : K) : MvPolynomial (Fin 2) K) ∉
        purePower (K := K) (comparison51_A 0) (comparison51_a 0) := by
      intro hm
      have hm' := monomial_mem_purePower.mp hm
      simp [comparison51_A, comparison51_a] at hm'
    exact hnot hx
  have hne : Nonempty (comparison51_I : Ideal (MvPolynomial (Fin 2) K)).minimalPrimes :=
    Ideal.nonempty_minimalPrimes htop
  have hgroup (P : (comparison51_I : Ideal (MvPolynomial (Fin 2) K)).minimalPrimes) :
      groupedComponents comparison51_I comparison51_A comparison51_a P = comparison51_I := by
    obtain ⟨j₀, hPj₀⟩ := minimalPrime_eq_primeOf hdec.1 hpos P.2
    apply le_antisymm
    · intro x hx
      dsimp only [groupedComponents] at hx
      rw [hdec.1]
      refine Ideal.mem_iInf.mpr ?_
      intro j
      have hj : primeOf (comparison51_A j) = P.1 := by
        rw [← hPj₀]
      exact Ideal.mem_iInf.mp hx ⟨j, hj⟩
    · intro x hx
      rw [hdec.1] at hx
      dsimp only [groupedComponents]
      refine Ideal.mem_iInf.mpr ?_
      intro j
      exact Ideal.mem_iInf.mp hx j.1
  refine (isSimis_iff_componentSimis_of_stdSymbolic (eq2_groupedSymbolic hdec)).mpr ?_
  intro q hq
  simp [componentSymbolic, hgroup]

/-- With only two components there are no intervenors, so condition (11) holds. -/
theorem comparison51_IncidenceBound : _root_.thm52_IncidenceBound comparison51_A := by
  intro k l hkl hmeet j₁ j₂ hj₁ hj₂
  fin_cases k <;> fin_cases l <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp_all [_root_.thm52_isIntervenor, comparison51_A]

/-- Condition (13) is also satisfied, despite the nonempty set of mismatch pairs. -/
theorem comparison51_condition13 : comparison51_Condition13 comparison51_A comparison51_a := by
  rintro ⟨k, l⟩ hp
  fin_cases k <;> fin_cases l <;>
    simp [comparison51_N, prop21_XI, mismatchPairs, comparison51_A, comparison51_a] at hp ⊢

/-- Unequal occurrence exponents preclude any squarefree diagonal root. -/
theorem comparison51_not_hasSqRoot :
    ¬ HasSqRoot (comparison51_I : Ideal (MvPolynomial (Fin 2) K)) := by
  have hdec := comparison51_isIrredundantDecomp (K := K)
  intro hroot
  have hX := (prop21_hasSqRoot_iff_XI_eq_empty (K := K) hdec.1 hdec.2).mp hroot
  have hp : ((0 : Fin 2), (1 : Fin 2)) ∈ prop21_XI comparison51_A comparison51_a := by
    refine ⟨by decide, ?_⟩
    exact ⟨0, by simp [comparison51_A], by simp [comparison51_A], by decide⟩
  rw [hX] at hp
  exact hp.elim

/-- Manuscript §5.1: the distinct-radical hypothesis cannot simply be deleted. -/
theorem comparison51_counterexample :
    (comparison51_I : Ideal (MvPolynomial (Fin 2) K)) =
        (primeOf (Finset.univ : Finset (Fin 2)) : Ideal (MvPolynomial (Fin 2) K)) ^ 2 ∧
      IsIrredundantDecomp (K := K) comparison51_I comparison51_A comparison51_a ∧
      (purePower (K := K) (comparison51_A 0) (comparison51_a 0) :
          Ideal (MvPolynomial (Fin 2) K)).radical =
        (purePower (K := K) (comparison51_A 1) (comparison51_a 1) :
          Ideal (MvPolynomial (Fin 2) K)).radical ∧
      ¬ Function.Injective (fun j : Fin 2 ↦
        (purePower (K := K) (comparison51_A j) (comparison51_a j) :
          Ideal (MvPolynomial (Fin 2) K)).radical) ∧
      associatedPrimes (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) K ⧸ comparison51_I) =
        (comparison51_I : Ideal (MvPolynomial (Fin 2) K)).minimalPrimes ∧
      IsSimis (comparison51_I : Ideal (MvPolynomial (Fin 2) K)) ∧
      _root_.thm52_IncidenceBound comparison51_A ∧
      comparison51_Condition13 comparison51_A comparison51_a ∧
      ¬ HasSqRoot (comparison51_I : Ideal (MvPolynomial (Fin 2) K)) := by
  have hradEq :
      (purePower (K := K) (comparison51_A 0) (comparison51_a 0) :
          Ideal (MvPolynomial (Fin 2) K)).radical =
        (purePower (K := K) (comparison51_A 1) (comparison51_a 1) :
          Ideal (MvPolynomial (Fin 2) K)).radical :=
    (comparison51_component_radical (K := K) (0 : Fin 2)).trans
      (comparison51_component_radical (K := K) (1 : Fin 2)).symm
  have hnotinj : ¬ Function.Injective (fun j : Fin 2 ↦
      (purePower (K := K) (comparison51_A j) (comparison51_a j) :
        Ideal (MvPolynomial (Fin 2) K)).radical) := by
    intro hinj
    exact (by decide : (0 : Fin 2) ≠ 1) (hinj hradEq)
  exact ⟨comparison51_I_eq_primeOf_sq (K := K),
    comparison51_isIrredundantDecomp (K := K), hradEq, hnotinj,
    comparison51_associatedPrimes_eq_minimalPrimes (K := K),
    comparison51_isSimis (K := K), comparison51_IncidenceBound,
    comparison51_condition13, comparison51_not_hasSqRoot (K := K)⟩

end SimisFormal
