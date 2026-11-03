import SimisFormal.Defs
import SimisFormal.Basic
import SimisFormal.MonomialDecompExists
import SimisFormal.Eq2_GroupedSymbolic
import SimisFormal.DiagAssociatedPreserve

namespace SimisFormal
open MvPolynomial
open scoped BigOperators
variable {σ K ι κ : Type*} [Field K] [DecidableEq σ]
omit [DecidableEq σ] in
/-- In a decomposition of a nonzero ideal every displayed component has nonempty support. -/
theorem eq1_nonempty_supports_of_irredundantDecomp [Fintype σ]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI0 : I ≠ ⊥) (hdec : IsIrredundantDecomp (K := K) I A a) : ∀ j, (A j).Nonempty := by
  classical
  intro j
  by_contra hne
  have hEmpty : A j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  have hbot : (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) = ⊥ := by
    simp [hEmpty, purePower, monomialIdeal]
  have hle : I ≤ (⊥ : Ideal (MvPolynomial σ K)) := by
    rw [← hbot]
    intro x hx
    rw [hdec.1] at hx
    exact Ideal.mem_iInf.mp hx j
  exact hI0 (le_bot_iff.mp hle)

/-- Irredundancy can be witnessed by one monomial lying in all the other components. -/
lemma eq1_exists_monomial_omit_witness {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hirr : IsIrredundant (K := K) A a) (j : ι) :
    ∃ u : σ →₀ ℕ,
      (∀ k : ι, k ≠ j → (monomial u (1 : K) : MvPolynomial σ K) ∈
        purePower (A k) (a k)) ∧
      (monomial u (1 : K) : MvPolynomial σ K) ∉ purePower (A j) (a j) := by
  classical
  have hex : ∃ x : MvPolynomial σ K,
      x ∈ decompOmit (K := K) A a j ∧
        x ∉ (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) := by
    by_contra h
    apply hirr j
    intro x hx
    by_contra hxQ
    exact h ⟨x, hx, hxQ⟩
  obtain ⟨p, hpOmit, hpNot⟩ := hex
  have hexmon : ∃ u ∈ p.support,
      (monomial u (1 : K) : MvPolynomial σ K) ∉ purePower (A j) (a j) := by
    by_contra h
    apply hpNot
    rw [purePower]
    apply mem_monomialIdeal.mpr
    intro e he
    have hmon : (monomial e (1 : K) : MvPolynomial σ K) ∈
        purePower (A j) (a j) := by
      by_contra heQ
      exact h ⟨e, he, heQ⟩
    rw [purePower] at hmon
    exact monomial_mem_monomialIdeal.mp hmon
  obtain ⟨u, huSupport, huNot⟩ := hexmon
  refine ⟨u, ?_, huNot⟩
  intro k hk
  rw [decompOmit] at hpOmit
  have hpK : p ∈ (purePower (A k) (a k) : Ideal (MvPolynomial σ K)) :=
    Ideal.mem_iInf.mp hpOmit ⟨k, hk⟩
  rw [purePower] at hpK ⊢
  exact monomial_mem_monomialIdeal.mpr ((mem_monomialIdeal.mp hpK) u huSupport)

/-- Containment of irreducible components from containment of supports and reverse bounds. -/
lemma eq1_purePower_le_of_subset_of_le {A B : Finset σ} {a b : σ → ℕ}
    (hsub : B ⊆ A) (hle : ∀ i ∈ B, a i ≤ b i) :
    (purePower B b : Ideal (MvPolynomial σ K)) ≤ purePower A a := by
  rw [purePower, purePower]
  apply monomialIdeal_le_iff.mpr
  intro e he
  rcases he with ⟨u, hu, hule⟩
  rcases hu with ⟨i, hiB, rfl⟩
  refine ⟨Finsupp.single i (a i), ⟨i, hsub hiB, rfl⟩, ?_⟩
  exact Finsupp.single_le_iff.mpr
    ((hle i hiB).trans (Finsupp.single_le_iff.mp hule))

omit [DecidableEq σ] in
/-- An irredundant family has no strict containments among its components. -/
lemma eq1_index_eq_of_component_le {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hirr : IsIrredundant (K := K) A a) {j k : ι}
    (hle : (purePower (A k) (a k) : Ideal (MvPolynomial σ K)) ≤
      purePower (A j) (a j)) : k = j := by
  classical
  by_contra hkj
  apply hirr j
  intro x hx
  rw [decompOmit] at hx
  exact hle (Ideal.mem_iInf.mp hx ⟨k, hkj⟩)

/-- For each component of one irredundant family, the other family contains a component
lying below it.  This is the comparison step that does not require an antichain hypothesis. -/
lemma eq1_other_component_le [Fintype σ] [Fintype κ]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    {B : κ → Finset σ} {b : κ → σ → ℕ}
    (hAcomp : HasComponents (K := K) I A a) (hAirr : IsIrredundant (K := K) A a)
    (hBcomp : HasComponents (K := K) I B b) (j : ι) :
    ∃ l : κ, (purePower (B l) (b l) : Ideal (MvPolynomial σ K)) ≤
      purePower (A j) (a j) := by
  classical
  obtain ⟨u, huOther, huNot⟩ := eq1_exists_monomial_omit_witness (K := K) hAirr j
  have hpos : ∀ i, i ∈ A j → 0 < a j i := by
    intro i hi
    exact exponents_pos_of_irredundant (K := K) hAirr j i hi
  have huLt : ∀ i, i ∈ A j → u i < a j i := by
    intro i hi
    by_contra hnot
    exact huNot (monomial_mem_purePower.mpr ⟨i, hi, le_of_not_gt hnot⟩)
  let v : σ →₀ ℕ :=
    (Finsupp.equivFunOnFinite : (σ →₀ ℕ) ≃ (σ → ℕ)).symm
      (fun i ↦ if i ∈ A j then a j i - 1 else max (u i) (∑ l : κ, b l i))
  have hv : ∀ i, v i = if i ∈ A j then a j i - 1 else max (u i) (∑ l : κ, b l i) := by
    intro i
    rfl
  have hvNot : (monomial v (1 : K) : MvPolynomial σ K) ∉ purePower (A j) (a j) := by
    intro hvMem
    rcases monomial_mem_purePower.mp hvMem with ⟨i, hiA, hai⟩
    rw [hv i, if_pos hiA] at hai
    have hiPos := hpos i hiA
    omega
  have hvOther : ∀ k : ι, k ≠ j →
      (monomial v (1 : K) : MvPolynomial σ K) ∈ purePower (A k) (a k) := by
    intro k hkj
    rcases monomial_mem_purePower.mp (huOther k hkj) with ⟨i, hiAk, haki⟩
    refine monomial_mem_purePower.mpr ⟨i, hiAk, ?_⟩
    by_cases hiAj : i ∈ A j
    · rw [hv i, if_pos hiAj]
      have hui := huLt i hiAj
      omega
    · have huvi : u i ≤ v i := by
        rw [hv i, if_neg hiAj]
        exact le_max_left _ _
      exact haki.trans huvi
  have hexNotB : ∃ l : κ,
      (monomial v (1 : K) : MvPolynomial σ K) ∉ purePower (B l) (b l) := by
    by_contra h
    have hall : ∀ l : κ,
        (monomial v (1 : K) : MvPolynomial σ K) ∈ purePower (B l) (b l) := by
      intro l
      by_contra hvl
      exact h ⟨l, hvl⟩
    have hvI : (monomial v (1 : K) : MvPolynomial σ K) ∈ I := by
      rw [hBcomp]
      exact Ideal.mem_iInf.mpr hall
    have hvAj : (monomial v (1 : K) : MvPolynomial σ K) ∈ purePower (A j) (a j) := by
      rw [hAcomp] at hvI
      exact Ideal.mem_iInf.mp hvI j
    exact hvNot hvAj
  obtain ⟨l, hvNotBl⟩ := hexNotB
  have hSub : B l ⊆ A j := by
    intro i hiBl
    by_contra hiAj
    apply hvNotBl
    refine monomial_mem_purePower.mpr ⟨i, hiBl, ?_⟩
    have hsum : b l i ≤ ∑ k : κ, b k i := by
      simpa using (Finset.single_le_sum_of_canonicallyOrdered (s := Finset.univ)
        (f := fun k : κ ↦ b k i) (Finset.mem_univ l))
    have hsumv : (∑ k : κ, b k i) ≤ v i := by
      rw [hv i, if_neg hiAj]
      exact le_max_right _ _
    exact hsum.trans hsumv
  have hExp : ∀ i ∈ B l, a j i ≤ b l i := by
    intro i hiBl
    have hiAj : i ∈ A j := hSub hiBl
    have hnle : ¬ b l i ≤ v i := by
      intro hlei
      exact hvNotBl (monomial_mem_purePower.mpr ⟨i, hiBl, hlei⟩)
    rw [hv i, if_pos hiAj] at hnle
    have hiPos := hpos i hiAj
    omega
  exact ⟨l, eq1_purePower_le_of_subset_of_le (K := K) hSub hExp⟩

/-- Positive pure-power data are uniquely determined by the ideal they generate.  Values
outside the displayed support are deliberately ignored. -/
lemma eq1_support_eq_and_exponents_eq_of_purePower_eq {A B : Finset σ} {a b : σ → ℕ}
    (hApos : ∀ i ∈ A, 0 < a i) (hBpos : ∀ i ∈ B, 0 < b i)
    (hEq : (purePower A a : Ideal (MvPolynomial σ K)) = purePower B b) :
    A = B ∧ ∀ i ∈ A, a i = b i := by
  have hAB : A ⊆ B := by
    intro i hiA
    have hmemA : (monomial (Finsupp.single i (a i)) (1 : K) : MvPolynomial σ K) ∈
        purePower A a := by
      exact monomial_mem_purePower.mpr ⟨i, hiA, by simp⟩
    rw [hEq] at hmemA
    rcases monomial_mem_purePower.mp hmemA with ⟨k, hkB, hle⟩
    by_cases hki : k = i
    · simpa [hki] using hkB
    · exfalso
      have hle0 : b k ≤ 0 := by
        simpa [Finsupp.single_apply, Ne.symm hki] using hle
      have hkpos := hBpos k hkB
      omega
  have hBA : B ⊆ A := by
    intro i hiB
    have hmemB : (monomial (Finsupp.single i (b i)) (1 : K) : MvPolynomial σ K) ∈
        purePower B b := by
      exact monomial_mem_purePower.mpr ⟨i, hiB, by simp⟩
    rw [← hEq] at hmemB
    rcases monomial_mem_purePower.mp hmemB with ⟨k, hkA, hle⟩
    by_cases hki : k = i
    · simpa [hki] using hkA
    · exfalso
      have hle0 : a k ≤ 0 := by
        simpa [Finsupp.single_apply, Ne.symm hki] using hle
      have hkpos := hApos k hkA
      omega
  refine ⟨?_, ?_⟩
  · ext i
    constructor
    · intro hi
      exact hAB hi
    · intro hi
      exact hBA hi
  · intro i hiA
    have hiB : i ∈ B := hAB hiA
    have hba : b i ≤ a i := by
      have hmemA : (monomial (Finsupp.single i (a i)) (1 : K) : MvPolynomial σ K) ∈
          purePower A a := by
        exact monomial_mem_purePower.mpr ⟨i, hiA, by simp⟩
      rw [hEq] at hmemA
      rcases monomial_mem_purePower.mp hmemA with ⟨k, hkB, hle⟩
      by_cases hki : k = i
      · subst k
        simpa using hle
      · exfalso
        have hle0 : b k ≤ 0 := by
          simpa [Finsupp.single_apply, Ne.symm hki] using hle
        have hkpos := hBpos k hkB
        omega
    have hab : a i ≤ b i := by
      have hmemB : (monomial (Finsupp.single i (b i)) (1 : K) : MvPolynomial σ K) ∈
          purePower B b := by
        exact monomial_mem_purePower.mpr ⟨i, hiB, by simp⟩
      rw [← hEq] at hmemB
      rcases monomial_mem_purePower.mp hmemB with ⟨k, hkA, hle⟩
      by_cases hki : k = i
      · subst k
        simpa using hle
      · exfalso
        have hle0 : a k ≤ 0 := by
          simpa [Finsupp.single_apply, Ne.symm hki] using hle
        have hkpos := hApos k hkA
        omega
    exact le_antisymm hab hba

/-- Two finite irredundant irreducible monomial decompositions agree up to an order.  Neither
distinct radicals nor the absence of embedded primes is assumed. -/
theorem irredundantDecomp_unique [Fintype σ] [Fintype ι] [Fintype κ]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    {B : κ → Finset σ} {b : κ → σ → ℕ}
    (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤)
    (hA : IsIrredundantDecomp (K := K) I A a)
    (hB : IsIrredundantDecomp (K := K) I B b) :
    ∃ e : ι ≃ κ, ∀ j, A j = B (e j) ∧ ∀ i ∈ A j, a j i = b (e j) i := by
  classical
  have _ : (∀ j : ι, (A j).Nonempty) ∧ (∀ l : κ, (B l).Nonempty) :=
    ⟨eq1_nonempty_supports_of_irredundantDecomp hI0 hA,
      eq1_nonempty_supports_of_irredundantDecomp hI0 hB⟩
  have _ : Nonempty ι ∧ Nonempty κ := by
    constructor
    · by_contra hne
      have _ : IsEmpty ι := not_nonempty_iff.mp hne
      apply hItop
      rw [hA.1]
      exact iInf_of_empty _
    · by_contra hne
      have _ : IsEmpty κ := not_nonempty_iff.mp hne
      apply hItop
      rw [hB.1]
      exact iInf_of_empty _
  have hforward : ∀ j : ι, ∃ l : κ,
      (purePower (B l) (b l) : Ideal (MvPolynomial σ K)) ≤
        purePower (A j) (a j) := by
    intro j
    exact eq1_other_component_le (K := K) hA.1 hA.2 hB.1 j
  choose f hf using hforward
  have hbackward : ∀ l : κ, ∃ j : ι,
      (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) ≤
        purePower (B l) (b l) := by
    intro l
    exact eq1_other_component_le (K := K) hB.1 hB.2 hA.1 l
  choose g hg using hbackward
  have hgf : ∀ j : ι, g (f j) = j := by
    intro j
    apply eq1_index_eq_of_component_le (K := K) hA.2
    exact (hg (f j)).trans (hf j)
  have hfg : ∀ l : κ, f (g l) = l := by
    intro l
    apply eq1_index_eq_of_component_le (K := K) hB.2
    exact (hf (g l)).trans (hg l)
  let e : ι ≃ κ :=
    { toFun := f
      invFun := g
      left_inv := hgf
      right_inv := hfg }
  refine ⟨e, ?_⟩
  intro j
  have hIdeal : (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) =
      purePower (B (f j)) (b (f j)) := by
    apply le_antisymm
    · simpa [hgf j] using hg (f j)
    · exact hf j
  have hApos : ∀ i ∈ A j, 0 < a j i := by
    intro i hi
    exact exponents_pos_of_irredundant (K := K) hA.2 j i hi
  have hBpos : ∀ i ∈ B (f j), 0 < b (f j) i := by
    intro i hi
    exact exponents_pos_of_irredundant (K := K) hB.2 (f j) i hi
  have hparams := eq1_support_eq_and_exponents_eq_of_purePower_eq
    (K := K) hApos hBpos hIdeal
  simpa [e] using hparams

/-- Paper Eq. (1), packaged as existence plus all asserted properties of every finite
irredundant irreducible decomposition, including uniqueness up to order. -/
theorem eq1_full [Fintype σ] {I : Ideal (MvPolynomial σ K)}
    (hI : IsMonomialIdeal (K := K) I) (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤) :
    HasFiniteIrredundantDecomp (K := K) I ∧
    ∀ (η : Type) [Fintype η] (A : η → Finset σ) (a : η → σ → ℕ),
      IsIrredundantDecomp (K := K) I A a →
        (∀ j, (A j).Nonempty) ∧
        (∀ j i, i ∈ A j → 0 < a j i) ∧
        (∀ j, (purePower (A j) (a j) : Ideal (MvPolynomial σ K)).IsPrimary) ∧
        (associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) =
          Set.range (fun j : η ↦ (primeOf (A j) : Ideal (MvPolynomial σ K)))) ∧
        ∀ (ξ : Type) [Fintype ξ] (B : ξ → Finset σ) (b : ξ → σ → ℕ),
          IsIrredundantDecomp (K := K) I B b →
            ∃ e : η ≃ ξ, ∀ j, A j = B (e j) ∧ ∀ i ∈ A j, a j i = b (e j) i := by
  classical
  refine ⟨hasFiniteIrredundantDecomp_of_isMonomialIdeal (K := K) hI, ?_⟩
  intro η _instη A a hdec
  have hpos : ∀ j i, i ∈ A j → 0 < a j i :=
    exponents_pos_of_irredundant (K := K) hdec.2
  refine ⟨eq1_nonempty_supports_of_irredundantDecomp hI0 hdec, hpos, ?_, ?_, ?_⟩
  · intro j
    exact purePower_isPrimary (K := K) (hpos j)
  · exact diagAssoc_quotientAssociatedPrimes_eq_range (K := K) hdec.1 hdec.2
  · intro ξ _instξ B b hdecB
    exact irredundantDecomp_unique (K := K) hI0 hItop hdec hdecB

end SimisFormal
