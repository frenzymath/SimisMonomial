import SimisFormal.Defs
import SimisFormal.Basic

namespace SimisFormal
/-!
# Remark 3.2

The generator and component clutters from Remark 3.2, together with their displayed strong
triangles. The last comparison shows that deleting `z` from the two three-element facets of the
squarefree candidate never yields \(I_{r,s}\), even if the diagonal weights are allowed to vary.
-/
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K]
open rem32_var
instance rem32_Fintype : Fintype rem32_var where
  elems := {a, b, c, d, z}
  complete := by
    intro x
    cases x <;> simp

/-- Witness edges \(\{a,c\},\{c,d,z\},\{a,b,z\}\) for the generator triangle. -/
def rem32_generatorCycleEdges : Fin 3 → Finset rem32_var :=
  ![rem32_ac, rem32_cdz, rem32_abz]

/-- Witness edges \(\{a,d\},\{c,d,z\},\{a,b,z\}\) for the component triangle. -/
def rem32_componentCycleEdges : Fin 3 → Finset rem32_var :=
  ![rem32_ad, rem32_cdz, rem32_abz]

theorem rem32_generator_isClutter : IsClutter rem32_generatorClutter := by
  rw [IsClutter, rem32_generatorClutter]
  decide

theorem rem32_component_isClutter : IsClutter rem32_componentClutter := by
  rw [IsClutter, rem32_componentClutter]
  decide

theorem rem32_omitted_isClutter : IsClutter rem32_omittedClutter := by
  rw [IsClutter, rem32_omittedClutter]
  decide

/-- The inclusion-minimal transversals of the generator clutter form the component clutter. -/
theorem rem32_blocker_generator :
    blocker rem32_generatorClutter = rem32_componentClutter := by
  ext T
  simp only [blocker, IsTransversal, Set.mem_ofPred_eq, rem32_generatorClutter,
    rem32_componentClutter, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hT : T = (if a ∈ T then {a} else ∅) ∪ (if b ∈ T then {b} else ∅) ∪
      (if c ∈ T then {c} else ∅) ∪ (if d ∈ T then {d} else ∅) ∪
      (if z ∈ T then {z} else ∅) := by
    by_cases ha' : a ∈ T <;> by_cases hb' : b ∈ T <;> by_cases hc' : c ∈ T <;>
      by_cases hd' : d ∈ T <;> by_cases hz' : z ∈ T
    all_goals
      ext x
      cases x <;> simp [ha', hb', hc', hd', hz']
  by_cases ha : a ∈ T <;> by_cases hb : b ∈ T <;> by_cases hc : c ∈ T <;>
    by_cases hd : d ∈ T <;> by_cases hz : z ∈ T
  all_goals
    rw [hT]
    simp [ha, hb, hc, hd, hz]
  all_goals decide

/-- The inclusion-minimal transversals of the component clutter form the generator clutter. -/
theorem rem32_blocker_component :
    blocker rem32_componentClutter = rem32_generatorClutter := by
  ext T
  simp only [blocker, IsTransversal, Set.mem_ofPred_eq, rem32_componentClutter,
    rem32_generatorClutter, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hT : T = (if a ∈ T then {a} else ∅) ∪ (if b ∈ T then {b} else ∅) ∪
      (if c ∈ T then {c} else ∅) ∪ (if d ∈ T then {d} else ∅) ∪
      (if z ∈ T then {z} else ∅) := by
    by_cases ha' : a ∈ T <;> by_cases hb' : b ∈ T <;> by_cases hc' : c ∈ T <;>
      by_cases hd' : d ∈ T <;> by_cases hz' : z ∈ T
    all_goals
      ext x
      cases x <;> simp [ha', hb', hc', hd', hz']
  by_cases ha : a ∈ T <;> by_cases hb : b ∈ T <;> by_cases hc : c ∈ T <;>
    by_cases hd : d ∈ T <;> by_cases hz : z ∈ T
  all_goals
    rw [hT]
    simp [ha, hb, hc, hd, hz]
  all_goals decide

theorem rem32_generator_hasStrongTriangle : HasStrongTriangle rem32_generatorClutter := by
  rw [HasStrongTriangle, HasStrongCycle]
  refine ⟨by norm_num, ?_⟩
  refine ⟨rem32_generatorCycleVertices, ?_, ?_⟩
  · decide
  refine ⟨rem32_generatorCycleEdges, ?_, ?_, ?_⟩
  · decide
  · intro i
    fin_cases i <;> simp [rem32_generatorCycleEdges, rem32_generatorClutter]
  · intro i
    fin_cases i <;> decide

theorem rem32_component_hasStrongTriangle : HasStrongTriangle rem32_componentClutter := by
  rw [HasStrongTriangle, HasStrongCycle]
  refine ⟨by norm_num, ?_⟩
  refine ⟨rem32_componentCycleVertices, ?_, ?_⟩
  · decide
  refine ⟨rem32_componentCycleEdges, ?_, ?_, ?_⟩
  · decide
  · intro i
    fin_cases i <;> simp [rem32_componentCycleEdges, rem32_componentClutter]
  · intro i
    fin_cases i <;> decide

theorem rem32_generator_not_balanced : ¬ IsBalanced rem32_generatorClutter := by
  intro hb
  exact hb 3 (by norm_num) rem32_generator_hasStrongTriangle

theorem rem32_component_not_balanced : ¬ IsBalanced rem32_componentClutter := by
  intro hb
  exact hb 3 (by norm_num) rem32_component_hasStrongTriangle

/-- The omitted generator-clutter edge avoids the three displayed cycle vertices. -/
theorem rem32_generator_omittedEdge_disjoint_cycleVertices :
    Disjoint rem32_bd (Finset.univ.image rem32_generatorCycleVertices) := by
  rw [Finset.disjoint_left]
  intro x hxEdge hxVertices
  rcases Finset.mem_image.mp hxVertices with ⟨i, -, rfl⟩
  fin_cases i <;> simp [rem32_generatorCycleVertices, rem32_bd] at hxEdge

/-- The omitted component-clutter edge avoids the three displayed cycle vertices. -/
theorem rem32_component_omittedEdge_disjoint_cycleVertices :
    Disjoint rem32_bc (Finset.univ.image rem32_componentCycleVertices) := by
  rw [Finset.disjoint_left]
  intro x hxEdge hxVertices
  rcases Finset.mem_image.mp hxVertices with ⟨i, -, rfl⟩
  fin_cases i <;> simp [rem32_componentCycleVertices, rem32_bc] at hxEdge

/-- With both variable weights positive, the support complex is the stated generator clutter.

The hypotheses are essential: when \(r=0\) or \(s=0\), the corresponding exponent loses `z`. -/
theorem rem32_family_supportComplex_eq_generator {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    supportComplex (rem32_familyIdeal (K := K) r s) = rem32_generatorClutter := by
  let I : Ideal (MvPolynomial rem32_var K) := rem32_familyIdeal (K := K) r s
  have hI : I = monomialIdeal (rem32_familyExps r s) := rfl
  change supportComplex I = rem32_generatorClutter
  have hsupp_ac : (characteristicExp rem32_ac).support = rem32_ac := by
    ext i
    cases i <;> simp [rem32_ac]
  have hsupp_bd : (characteristicExp rem32_bd).support = rem32_bd := by
    ext i
    cases i <;> simp [rem32_bd]
  have hsupp_abz : (rem32_abzExp r).support = rem32_abz := by
    ext i
    cases i <;> simp [rem32_abzExp, rem32_abz, Finsupp.mem_support_iff]
    omega
  have hsupp_cdz : (rem32_cdzExp s).support = rem32_cdz := by
    ext i
    cases i <;> simp [rem32_cdzExp, rem32_cdz, Finsupp.mem_support_iff]
    omega
  have hmin (e : rem32_var →₀ ℕ) (he : e ∈ rem32_familyExps r s)
      (honly : ∀ v ∈ rem32_familyExps r s, v ≤ e → v = e) : e ∈ minGens I := by
    rw [hI, mem_minGens]
    refine ⟨monomial_mem_monomialIdeal.mpr ⟨e, he, le_rfl⟩, ?_⟩
    intro u hu hue
    rw [monomial_mem_monomialIdeal] at hu
    rcases hu with ⟨v, hv, hvu⟩
    have hve : v = e := honly v hv (le_trans hvu hue)
    exact le_antisymm hue (hve ▸ hvu)
  have hmin_ac : characteristicExp rem32_ac ∈ minGens I :=
    hmin (characteristicExp rem32_ac) (by simp [rem32_familyExps]) (by
      intro v hv hve
      simp only [rem32_familyExps, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · rfl
      · have h := hve d
        simp [rem32_ac, rem32_bd] at h
      · have h := hve b
        simp [rem32_ac, rem32_abzExp] at h
      · have h := hve d
        simp [rem32_ac, rem32_cdzExp] at h)
  have hmin_bd : characteristicExp rem32_bd ∈ minGens I :=
    hmin (characteristicExp rem32_bd) (by simp [rem32_familyExps]) (by
      intro v hv hve
      simp only [rem32_familyExps, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · have h := hve a
        simp [rem32_ac, rem32_bd] at h
      · rfl
      · have h := hve a
        simp [rem32_bd, rem32_abzExp] at h
      · have h := hve c
        simp [rem32_bd, rem32_cdzExp] at h)
  have hmin_abz : rem32_abzExp r ∈ minGens I :=
    hmin (rem32_abzExp r) (by simp [rem32_familyExps]) (by
      intro v hv hve
      simp only [rem32_familyExps, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · have h := hve c
        simp [rem32_ac, rem32_abzExp] at h
      · have h := hve d
        simp [rem32_bd, rem32_abzExp] at h
      · rfl
      · have h := hve d
        simp [rem32_abzExp, rem32_cdzExp] at h)
  have hmin_cdz : rem32_cdzExp s ∈ minGens I :=
    hmin (rem32_cdzExp s) (by simp [rem32_familyExps]) (by
      intro v hv hve
      simp only [rem32_familyExps, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · have h := hve a
        simp [rem32_ac, rem32_cdzExp] at h
      · have h := hve b
        simp [rem32_bd, rem32_cdzExp] at h
      · have h := hve a
        simp [rem32_abzExp, rem32_cdzExp] at h
      · rfl)
  ext A
  change (∃ e ∈ minGens I, e.support = A) ↔ A ∈ rem32_generatorClutter
  constructor
  · rintro ⟨e, hemin, hesupp⟩
    rw [mem_minGens] at hemin
    have heI : (monomial e (1 : K) : MvPolynomial rem32_var K) ∈ I := hemin.1
    rw [hI, monomial_mem_monomialIdeal] at heI
    rcases heI with ⟨u, hu, hue⟩
    have huI : (monomial u (1 : K) : MvPolynomial rem32_var K) ∈ I := by
      rw [hI, monomial_mem_monomialIdeal]
      exact ⟨u, hu, le_rfl⟩
    have heu : e = u := (hemin.2 u huI hue).symm
    simp only [rem32_familyExps, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · subst e
      rw [← hesupp]
      simp [rem32_generatorClutter, hsupp_ac]
    · subst e
      rw [← hesupp]
      simp [rem32_generatorClutter, hsupp_bd]
    · subst e
      rw [← hesupp]
      simp [rem32_generatorClutter, hsupp_abz]
    · subst e
      rw [← hesupp]
      simp [rem32_generatorClutter, hsupp_cdz]
  · intro hA
    simp only [rem32_generatorClutter, Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl | rfl | rfl
    · exact ⟨characteristicExp rem32_ac, hmin_ac, hsupp_ac⟩
    · exact ⟨characteristicExp rem32_bd, hmin_bd, hsupp_bd⟩
    · exact ⟨rem32_abzExp r, hmin_abz, hsupp_abz⟩
    · exact ⟨rem32_cdzExp s, hmin_cdz, hsupp_cdz⟩

/-- If the \(abz^r\) weight on \(z\) is zero, \(\{a,b\}\) is an additional minimal support. -/
theorem rem32_family_supportComplex_ne_generator_of_zero_left (s : ℕ) :
    supportComplex (rem32_familyIdeal (K := K) 0 s) ≠ rem32_generatorClutter := by
  intro hEq
  let I : Ideal (MvPolynomial rem32_var K) := rem32_familyIdeal (K := K) 0 s
  have hI : I = monomialIdeal (rem32_familyExps 0 s) := rfl
  change supportComplex I = rem32_generatorClutter at hEq
  let e : rem32_var →₀ ℕ := rem32_abzExp 0
  have hemin : e ∈ minGens I := by
    rw [hI, mem_minGens]
    refine ⟨monomial_mem_monomialIdeal.mpr ⟨e, by simp [e, rem32_familyExps], le_rfl⟩, ?_⟩
    intro u hu hue
    rw [monomial_mem_monomialIdeal] at hu
    rcases hu with ⟨v, hv, hvu⟩
    simp only [rem32_familyExps, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · have h := (le_trans hvu hue) c
      simp [e, rem32_ac, rem32_abzExp] at h
    · have h := (le_trans hvu hue) d
      simp [e, rem32_bd, rem32_abzExp] at h
    · have hve : rem32_abzExp 0 = e := rfl
      exact le_antisymm hue (hve ▸ hvu)
    · have h := (le_trans hvu hue) c
      simp [e, rem32_abzExp, rem32_cdzExp] at h
  have hsupp : e.support = rem32_ab := by
    ext i
    cases i <;> simp [e, rem32_abzExp, rem32_ab, Finsupp.mem_support_iff]
  have hleft : rem32_ab ∈ supportComplex I := by
    change ∃ x ∈ minGens I, x.support = rem32_ab
    exact ⟨e, hemin, hsupp⟩
  have hright : rem32_ab ∉ rem32_generatorClutter := by
    simp only [rem32_generatorClutter, Set.mem_insert_iff, Set.mem_singleton_iff]
    decide
  exact hright (by simpa [hEq] using hleft)

/-- If the \(cdz^s\) weight on \(z\) is zero, \(\{c,d\}\) is an additional minimal support. -/
theorem rem32_family_supportComplex_ne_generator_of_zero_right (r : ℕ) :
    supportComplex (rem32_familyIdeal (K := K) r 0) ≠ rem32_generatorClutter := by
  intro hEq
  let I : Ideal (MvPolynomial rem32_var K) := rem32_familyIdeal (K := K) r 0
  have hI : I = monomialIdeal (rem32_familyExps r 0) := rfl
  change supportComplex I = rem32_generatorClutter at hEq
  let e : rem32_var →₀ ℕ := rem32_cdzExp 0
  have hemin : e ∈ minGens I := by
    rw [hI, mem_minGens]
    refine ⟨monomial_mem_monomialIdeal.mpr ⟨e, by simp [e, rem32_familyExps], le_rfl⟩, ?_⟩
    intro u hu hue
    rw [monomial_mem_monomialIdeal] at hu
    rcases hu with ⟨v, hv, hvu⟩
    simp only [rem32_familyExps, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · have h := (le_trans hvu hue) a
      simp [e, rem32_ac, rem32_cdzExp] at h
    · have h := (le_trans hvu hue) b
      simp [e, rem32_bd, rem32_cdzExp] at h
    · have h := (le_trans hvu hue) a
      simp [e, rem32_abzExp, rem32_cdzExp] at h
    · have hve : rem32_cdzExp 0 = e := rfl
      exact le_antisymm hue (hve ▸ hvu)
  have hsupp : e.support = rem32_cd := by
    ext i
    cases i <;> simp [e, rem32_cdzExp, rem32_cd, Finsupp.mem_support_iff]
  have hleft : rem32_cd ∈ supportComplex I := by
    change ∃ x ∈ minGens I, x.support = rem32_cd
    exact ⟨e, hemin, hsupp⟩
  have hright : rem32_cd ∉ rem32_generatorClutter := by
    simp only [rem32_generatorClutter, Set.mem_insert_iff, Set.mem_singleton_iff]
    decide
  exact hright (by simpa [hEq] using hleft)

/-- With both variable weights positive, the minimal primes are the component variable primes.

The displayed component clutter is therefore not merely notation: its members index
`Ideal.minimalPrimes` of the polynomial ideal from Remark 3.2. -/
theorem rem32_family_minimalPrimes_eq_image_component {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    (rem32_familyIdeal (K := K) r s).minimalPrimes =
      (fun A : Finset rem32_var ↦ (primeOf A : Ideal (MvPolynomial rem32_var K))) ''
        rem32_componentClutter := by
  classical
  let I : Ideal (MvPolynomial rem32_var K) := rem32_familyIdeal (K := K) r s
  have hI : I = monomialIdeal (rem32_familyExps r s) := rfl
  change I.minimalPrimes =
      (fun A : Finset rem32_var ↦ (primeOf A : Ideal (MvPolynomial rem32_var K))) ''
        rem32_componentClutter
  have htrans_of_prime {P : Ideal (MvPolynomial rem32_var K)} (hPprime : P.IsPrime)
      (hIleP : I ≤ P) : IsTransversal rem32_generatorClutter
        (Finset.univ.filter (fun i : rem32_var ↦ (X i : MvPolynomial rem32_var K) ∈ P)) := by
    let T : Finset rem32_var :=
      Finset.univ.filter (fun i : rem32_var ↦ (X i : MvPolynomial rem32_var K) ∈ P)
    change IsTransversal rem32_generatorClutter T
    intro E hE
    simp only [rem32_generatorClutter, Set.mem_insert_iff, Set.mem_singleton_iff] at hE
    rcases hE with rfl | rfl | rfl | rfl
    · have hmem : (monomial (characteristicExp rem32_ac) (1 : K) :
          MvPolynomial rem32_var K) ∈ P := hIleP (by
            rw [hI, monomial_mem_monomialIdeal]
            exact ⟨characteristicExp rem32_ac, by simp [rem32_familyExps], le_rfl⟩)
      have heq : characteristicExp rem32_ac = Finsupp.single a 1 + Finsupp.single c 1 := by
        ext i
        cases i <;> simp [rem32_ac]
      rw [heq] at hmem
      have hprod : (X a : MvPolynomial rem32_var K) * X c ∈ P := by
        simpa [MvPolynomial.X, monomial_mul] using hmem
      rcases hPprime.mem_or_mem hprod with ha | hc
      · exact ⟨a, by simp [rem32_ac, T, ha]⟩
      · exact ⟨c, by simp [rem32_ac, T, hc]⟩
    · have hmem : (monomial (characteristicExp rem32_bd) (1 : K) :
          MvPolynomial rem32_var K) ∈ P := hIleP (by
            rw [hI, monomial_mem_monomialIdeal]
            exact ⟨characteristicExp rem32_bd, by simp [rem32_familyExps], le_rfl⟩)
      have heq : characteristicExp rem32_bd = Finsupp.single b 1 + Finsupp.single d 1 := by
        ext i
        cases i <;> simp [rem32_bd]
      rw [heq] at hmem
      have hprod : (X b : MvPolynomial rem32_var K) * X d ∈ P := by
        simpa [MvPolynomial.X, monomial_mul] using hmem
      rcases hPprime.mem_or_mem hprod with hb | hd
      · exact ⟨b, by simp [rem32_bd, T, hb]⟩
      · exact ⟨d, by simp [rem32_bd, T, hd]⟩
    · have hmem : (monomial (rem32_abzExp r) (1 : K) : MvPolynomial rem32_var K) ∈ P :=
        hIleP (by
          rw [hI, monomial_mem_monomialIdeal]
          exact ⟨rem32_abzExp r, by simp [rem32_familyExps], le_rfl⟩)
      have hprod : (X a * X b * (X z) ^ r : MvPolynomial rem32_var K) ∈ P := by
        simpa [MvPolynomial.X, rem32_abzExp, monomial_mul, monomial_pow] using hmem
      rcases hPprime.mem_or_mem hprod with hab | hzpow
      · rcases hPprime.mem_or_mem hab with ha | hb
        · exact ⟨a, by simp [rem32_abz, T, ha]⟩
        · exact ⟨b, by simp [rem32_abz, T, hb]⟩
      · have hz : (X z : MvPolynomial rem32_var K) ∈ P := hPprime.mem_of_pow_mem r hzpow
        exact ⟨z, by simp [rem32_abz, T, hz]⟩
    · have hmem : (monomial (rem32_cdzExp s) (1 : K) : MvPolynomial rem32_var K) ∈ P :=
        hIleP (by
          rw [hI, monomial_mem_monomialIdeal]
          exact ⟨rem32_cdzExp s, by simp [rem32_familyExps], le_rfl⟩)
      have hprod : (X c * X d * (X z) ^ s : MvPolynomial rem32_var K) ∈ P := by
        simpa [MvPolynomial.X, rem32_cdzExp, monomial_mul, monomial_pow] using hmem
      rcases hPprime.mem_or_mem hprod with hcd | hzpow
      · rcases hPprime.mem_or_mem hcd with hc | hd
        · exact ⟨c, by simp [rem32_cdz, T, hc]⟩
        · exact ⟨d, by simp [rem32_cdz, T, hd]⟩
      · have hz : (X z : MvPolynomial rem32_var K) ∈ P := hPprime.mem_of_pow_mem s hzpow
        exact ⟨z, by simp [rem32_cdz, T, hz]⟩
  have hIle_of_trans {T : Finset rem32_var}
      (hT : IsTransversal rem32_generatorClutter T) :
      I ≤ (primeOf T : Ideal (MvPolynomial rem32_var K)) := by
    rw [hI, monomialIdeal, Ideal.span_le]
    rintro y ⟨u, hu, rfl⟩
    simp only [rem32_familyExps, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · rcases hT rem32_ac (by simp [rem32_generatorClutter]) with ⟨i, hiMem⟩
      have hiEdge : i ∈ rem32_ac := (Finset.mem_inter.mp hiMem).1
      have hiT : i ∈ T := (Finset.mem_inter.mp hiMem).2
      have hiCases : i = a ∨ i = c := by simpa [rem32_ac] using hiEdge
      rcases hiCases with rfl | rfl
      · exact monomial_mem_primeOf.mpr ⟨a, hiT, by simp [rem32_ac]⟩
      · exact monomial_mem_primeOf.mpr ⟨c, hiT, by simp [rem32_ac]⟩
    · rcases hT rem32_bd (by simp [rem32_generatorClutter]) with ⟨i, hiMem⟩
      have hiEdge : i ∈ rem32_bd := (Finset.mem_inter.mp hiMem).1
      have hiT : i ∈ T := (Finset.mem_inter.mp hiMem).2
      have hiCases : i = b ∨ i = d := by simpa [rem32_bd] using hiEdge
      rcases hiCases with rfl | rfl
      · exact monomial_mem_primeOf.mpr ⟨b, hiT, by simp [rem32_bd]⟩
      · exact monomial_mem_primeOf.mpr ⟨d, hiT, by simp [rem32_bd]⟩
    · rcases hT rem32_abz (by simp [rem32_generatorClutter]) with ⟨i, hiMem⟩
      have hiEdge : i ∈ rem32_abz := (Finset.mem_inter.mp hiMem).1
      have hiT : i ∈ T := (Finset.mem_inter.mp hiMem).2
      have hiCases : i = a ∨ i = b ∨ i = z := by simpa [rem32_abz] using hiEdge
      rcases hiCases with rfl | rfl | rfl
      · exact monomial_mem_primeOf.mpr ⟨a, hiT, by simp [rem32_abzExp]⟩
      · exact monomial_mem_primeOf.mpr ⟨b, hiT, by simp [rem32_abzExp]⟩
      · exact monomial_mem_primeOf.mpr ⟨z, hiT, by simp [rem32_abzExp]; omega⟩
    · rcases hT rem32_cdz (by simp [rem32_generatorClutter]) with ⟨i, hiMem⟩
      have hiEdge : i ∈ rem32_cdz := (Finset.mem_inter.mp hiMem).1
      have hiT : i ∈ T := (Finset.mem_inter.mp hiMem).2
      have hiCases : i = c ∨ i = d ∨ i = z := by simpa [rem32_cdz] using hiEdge
      rcases hiCases with rfl | rfl | rfl
      · exact monomial_mem_primeOf.mpr ⟨c, hiT, by simp [rem32_cdzExp]⟩
      · exact monomial_mem_primeOf.mpr ⟨d, hiT, by simp [rem32_cdzExp]⟩
      · exact monomial_mem_primeOf.mpr ⟨z, hiT, by simp [rem32_cdzExp]; omega⟩
  have hOnly {P : Ideal (MvPolynomial rem32_var K)} (hP : P ∈ I.minimalPrimes) :
      ∃ A ∈ rem32_componentClutter, (primeOf A : Ideal (MvPolynomial rem32_var K)) = P := by
    change I.IsMinimalPrime P at hP
    let T : Finset rem32_var :=
      Finset.univ.filter (fun i : rem32_var ↦ (X i : MvPolynomial rem32_var K) ∈ P)
    have hT : IsTransversal rem32_generatorClutter T := by
      change IsTransversal rem32_generatorClutter
        (Finset.univ.filter (fun i : rem32_var ↦ (X i : MvPolynomial rem32_var K) ∈ P))
      exact htrans_of_prime hP.1.1 hP.1.2
    let S : Finset (Finset rem32_var) :=
      T.powerset.filter fun U ↦ IsTransversal rem32_generatorClutter U
    have hTS : T ∈ S := by simp [S, hT]
    obtain ⟨C, hCS, hminC⟩ := Finset.exists_min_image S (fun U ↦ U.card) ⟨T, hTS⟩
    have hCS' := Finset.mem_filter.mp hCS
    have hCT : C ⊆ T := by simpa using hCS'.1
    have hCtrans : IsTransversal rem32_generatorClutter C := hCS'.2
    have hCminimal : ∀ U, U ⊂ C → ¬ IsTransversal rem32_generatorClutter U := by
      intro U hUC hU
      have hUT : U ⊆ T := fun i hi ↦ hCT (hUC.1 hi)
      have hUS : U ∈ S := by simp [S, hUT, hU]
      exact (not_lt_of_ge (hminC U hUS)) (Finset.card_lt_card hUC)
    have hCblock : C ∈ blocker rem32_generatorClutter := ⟨hCtrans, hCminimal⟩
    have hCcomp : C ∈ rem32_componentClutter := by
      simpa [rem32_blocker_generator] using hCblock
    have hCtoP : (primeOf C : Ideal (MvPolynomial rem32_var K)) ≤ P := by
      rw [primeOf, purePower, monomialIdeal, Ideal.span_le]
      rintro y ⟨e, ⟨i, hiC, rfl⟩, rfl⟩
      have hiP : (X i : MvPolynomial rem32_var K) ∈ P := by
        have hiT := hCT hiC
        simpa [T] using hiT
      simpa [MvPolynomial.X] using hiP
    have hIleC : I ≤ (primeOf C : Ideal (MvPolynomial rem32_var K)) := hIle_of_trans hCtrans
    have hPtoC : P ≤ (primeOf C : Ideal (MvPolynomial rem32_var K)) :=
      hP.2 ⟨primeOf_isPrime C, hIleC⟩ hCtoP
    exact ⟨C, hCcomp, le_antisymm hCtoP hPtoC⟩
  ext P
  constructor
  · intro hP
    exact hOnly hP
  · rintro ⟨A, hA, rfl⟩
    have hAblock : A ∈ blocker rem32_generatorClutter := by
      simpa [rem32_blocker_generator] using hA
    have hIleA : I ≤ (primeOf A : Ideal (MvPolynomial rem32_var K)) := hIle_of_trans hAblock.1
    change I.IsMinimalPrime (primeOf A : Ideal (MvPolynomial rem32_var K))
    refine ⟨⟨primeOf_isPrime A, hIleA⟩, ?_⟩
    intro Q hQ hQle
    have hQinst : Q.IsPrime := hQ.1
    obtain ⟨R, hR, hRQ⟩ := Ideal.exists_minimalPrimes_le hQ.2
    obtain ⟨C, hC, hRC⟩ := hOnly hR
    have hCsubA : C ⊆ A :=
      (primeOf_le_iff_subset (K := K)).mp (by
        calc
          (primeOf C : Ideal (MvPolynomial rem32_var K)) = R := hRC
          _ ≤ Q := hRQ
          _ ≤ (primeOf A : Ideal (MvPolynomial rem32_var K)) := hQle)
    have hCA : C = A := rem32_component_isClutter C hC A hA hCsubA
    calc
      (primeOf A : Ideal (MvPolynomial rem32_var K)) = R := by simpa [hCA] using hRC
      _ ≤ Q := hRQ

/-- At \(r=0\), the displayed component prime \((c,d,z)\) does not contain \(abz^0=ab\). -/
theorem rem32_family_minimalPrimes_ne_image_component_of_zero_left (s : ℕ) :
    (rem32_familyIdeal (K := K) 0 s).minimalPrimes ≠
      (fun A : Finset rem32_var ↦ (primeOf A : Ideal (MvPolynomial rem32_var K))) ''
        rem32_componentClutter := by
  intro hEq
  let I : Ideal (MvPolynomial rem32_var K) := rem32_familyIdeal (K := K) 0 s
  have hI : I = monomialIdeal (rem32_familyExps 0 s) := rfl
  change I.minimalPrimes =
      (fun A : Finset rem32_var ↦ (primeOf A : Ideal (MvPolynomial rem32_var K))) ''
        rem32_componentClutter at hEq
  have hright : (primeOf rem32_cdz : Ideal (MvPolynomial rem32_var K)) ∈
      (fun A : Finset rem32_var ↦ (primeOf A : Ideal (MvPolynomial rem32_var K))) ''
        rem32_componentClutter :=
    ⟨rem32_cdz, by simp [rem32_componentClutter], rfl⟩
  have hleft : (primeOf rem32_cdz : Ideal (MvPolynomial rem32_var K)) ∈ I.minimalPrimes := by
    simpa [hEq] using hright
  change I.IsMinimalPrime (primeOf rem32_cdz : Ideal (MvPolynomial rem32_var K)) at hleft
  have hgen : (monomial (rem32_abzExp 0) (1 : K) : MvPolynomial rem32_var K) ∈ I := by
    rw [hI, monomial_mem_monomialIdeal]
    exact ⟨rem32_abzExp 0, by simp [rem32_familyExps], le_rfl⟩
  have hbad := hleft.1.2 hgen
  rw [monomial_mem_primeOf] at hbad
  rcases hbad with ⟨i, hi, hpos⟩
  have hiCases : i = c ∨ i = d ∨ i = z := by simpa [rem32_cdz] using hi
  rcases hiCases with rfl | rfl | rfl <;> simp [rem32_abzExp] at hpos

/-- At \(s=0\), the displayed component prime \((a,b,z)\) does not contain \(cdz^0=cd\). -/
theorem rem32_family_minimalPrimes_ne_image_component_of_zero_right (r : ℕ) :
    (rem32_familyIdeal (K := K) r 0).minimalPrimes ≠
      (fun A : Finset rem32_var ↦ (primeOf A : Ideal (MvPolynomial rem32_var K))) ''
        rem32_componentClutter := by
  intro hEq
  let I : Ideal (MvPolynomial rem32_var K) := rem32_familyIdeal (K := K) r 0
  have hI : I = monomialIdeal (rem32_familyExps r 0) := rfl
  change I.minimalPrimes =
      (fun A : Finset rem32_var ↦ (primeOf A : Ideal (MvPolynomial rem32_var K))) ''
        rem32_componentClutter at hEq
  have hright : (primeOf rem32_abz : Ideal (MvPolynomial rem32_var K)) ∈
      (fun A : Finset rem32_var ↦ (primeOf A : Ideal (MvPolynomial rem32_var K))) ''
        rem32_componentClutter :=
    ⟨rem32_abz, by simp [rem32_componentClutter], rfl⟩
  have hleft : (primeOf rem32_abz : Ideal (MvPolynomial rem32_var K)) ∈ I.minimalPrimes := by
    simpa [hEq] using hright
  change I.IsMinimalPrime (primeOf rem32_abz : Ideal (MvPolynomial rem32_var K)) at hleft
  have hgen : (monomial (rem32_cdzExp 0) (1 : K) : MvPolynomial rem32_var K) ∈ I := by
    rw [hI, monomial_mem_monomialIdeal]
    exact ⟨rem32_cdzExp 0, by simp [rem32_familyExps], le_rfl⟩
  have hbad := hleft.1.2 hgen
  rw [monomial_mem_primeOf] at hbad
  rcases hbad with ⟨i, hi, hpos⟩
  have hiCases : i = a ∨ i = b ∨ i = z := by simpa [rem32_abz] using hi
  rcases hiCases with rfl | rfl | rfl <;> simp [rem32_cdzExp] at hpos

theorem rem32_omittedRoot_isSquarefree :
    IsSquarefreeMonomialIdeal (rem32_omittedRootIdeal : Ideal (MvPolynomial rem32_var K)) := by
  exact ⟨rem32_omittedClutter, rfl⟩

/-- The support complex of the displayed omitted-\(z\) root is its defining clutter. -/
theorem rem32_omittedRoot_supportComplex_eq_omitted :
    supportComplex (rem32_omittedRootIdeal : Ideal (MvPolynomial rem32_var K)) =
      rem32_omittedClutter := by
  let I : Ideal (MvPolynomial rem32_var K) := rem32_omittedRootIdeal
  have hI : I = monomialIdeal (characteristicExp '' rem32_omittedClutter) := rfl
  change supportComplex I = rem32_omittedClutter
  have hchar_support (A : Finset rem32_var) : (characteristicExp A).support = A := by
    ext i
    by_cases hi : i ∈ A <;> simp [Finsupp.mem_support_iff, hi]
  have hchar_le_iff {A B : Finset rem32_var} :
      characteristicExp A ≤ characteristicExp B ↔ A ⊆ B := by
    constructor
    · intro h i hi
      by_contra hnot
      have hle : (1 : ℕ) ≤ 0 := by
        simpa [characteristicExp_apply, hi, hnot] using h i
      omega
    · intro hsub i
      by_cases hi : i ∈ A
      · have hiB := hsub hi
        simp [characteristicExp_apply, hi, hiB]
      · simp [characteristicExp_apply, hi]
  have hminAux (e : rem32_var →₀ ℕ)
      (he : e ∈ characteristicExp '' rem32_omittedClutter)
      (honly : ∀ v ∈ characteristicExp '' rem32_omittedClutter, v ≤ e → v = e) :
      e ∈ minGens I := by
    rw [hI, mem_minGens]
    refine ⟨monomial_mem_monomialIdeal.mpr ⟨e, he, le_rfl⟩, ?_⟩
    intro u hu hue
    rw [monomial_mem_monomialIdeal] at hu
    rcases hu with ⟨v, hv, hvu⟩
    have hve : v = e := honly v hv (le_trans hvu hue)
    exact le_antisymm hue (hve ▸ hvu)
  have hminOf (A : Finset rem32_var) (hA : A ∈ rem32_omittedClutter) :
      characteristicExp A ∈ minGens I :=
    hminAux (characteristicExp A) ⟨A, hA, rfl⟩ (by
      intro v hv hve
      rcases hv with ⟨B, hB, rfl⟩
      have hBA : B = A :=
        rem32_omitted_isClutter B hB A hA (hchar_le_iff.mp hve)
      simp [hBA])
  ext F
  change (∃ e ∈ minGens I, e.support = F) ↔ F ∈ rem32_omittedClutter
  constructor
  · rintro ⟨e, hemin, hesupp⟩
    rw [mem_minGens] at hemin
    have heI : (monomial e (1 : K) : MvPolynomial rem32_var K) ∈ I := hemin.1
    rw [hI, monomial_mem_monomialIdeal] at heI
    rcases heI with ⟨u, hu, hue⟩
    have huI : (monomial u (1 : K) : MvPolynomial rem32_var K) ∈ I := by
      rw [hI, monomial_mem_monomialIdeal]
      exact ⟨u, hu, le_rfl⟩
    have heu : e = u := (hemin.2 u huI hue).symm
    rcases hu with ⟨A, hA, rfl⟩
    subst e
    rw [← hesupp, hchar_support]
    exact hA
  · intro hF
    exact ⟨characteristicExp F, hminOf F hF, hchar_support F⟩

/-- The omitted-\(z\) root is fixed by \(\delta(1,1,1,1,t)\), also when \(t=0\). -/
theorem rem32_omittedWeight_diagonal_root (t : ℕ) :
    diagonal (rem32_omittedWeight t)
        (rem32_omittedRootIdeal : Ideal (MvPolynomial rem32_var K)) =
      rem32_omittedRootIdeal := by
  have hz (A : Finset rem32_var) (hA : A ∈ rem32_omittedClutter) : z ∉ A := by
    intro hzA
    simp only [rem32_omittedClutter, Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with hA | hA | hA | hA
    · subst A
      simp [rem32_ac] at hzA
    · subst A
      simp [rem32_bd] at hzA
    · subst A
      simp [rem32_ab] at hzA
    · subst A
      simp [rem32_cd] at hzA
  have hfix (A : Finset rem32_var) (hA : A ∈ rem32_omittedClutter) :
      diagExp (rem32_omittedWeight t) (characteristicExp A) = characteristicExp A := by
    have hAz : z ∉ A := hz A hA
    ext i
    cases i <;> simp [rem32_omittedWeight, hAz]
  have himage :
      diagExp (rem32_omittedWeight t) '' (characteristicExp '' rem32_omittedClutter) =
        characteristicExp '' rem32_omittedClutter := by
    ext e
    constructor
    · rintro ⟨u, ⟨A, hA, rfl⟩, hue⟩
      exact ⟨A, hA, (hfix A hA).symm.trans hue⟩
    · rintro ⟨A, hA, rfl⟩
      exact ⟨characteristicExp A, ⟨A, hA, rfl⟩, hfix A hA⟩
  rw [rem32_omittedRootIdeal, diagonal_monomialIdeal, himage]

/-- The displayed squarefree candidate cannot be diagonally weighted to \(I_{r,s}\).

The quantified weight `w` is deliberately unconstrained, so this also rules out every positive
diagonal root. Specializing to \(r=s=t\) gives the comparison in Remark 3.2. -/
theorem rem32_cannotOmitZ_fromRoot {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (w : rem32_var → ℕ) :
    diagonal w (rem32_omittedRootIdeal : Ideal (MvPolynomial rem32_var K)) ≠
      rem32_familyIdeal (K := K) r s := by
  intro hdiag
  let e : rem32_var →₀ ℕ := diagExp w (characteristicExp rem32_ab)
  have heRoot : (monomial e (1 : K) : MvPolynomial rem32_var K) ∈
      diagonal w (rem32_omittedRootIdeal : Ideal (MvPolynomial rem32_var K)) := by
    rw [rem32_omittedRootIdeal, diagonal_monomialIdeal]
    apply monomial_mem_monomialIdeal.mpr
    refine ⟨e, ?_, le_rfl⟩
    exact ⟨characteristicExp rem32_ab,
      ⟨rem32_ab, by simp [rem32_omittedClutter], rfl⟩, rfl⟩
  have heFamily : (monomial e (1 : K) : MvPolynomial rem32_var K) ∈
      rem32_familyIdeal (K := K) r s := by
    simpa [hdiag] using heRoot
  rw [rem32_familyIdeal, monomial_mem_monomialIdeal] at heFamily
  rcases heFamily with ⟨u, hu, hule⟩
  simp only [rem32_familyExps, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · have hc := hule c
    simp [e, rem32_ac, rem32_ab] at hc
  · have hcoord := hule d
    simp [e, rem32_bd, rem32_ab] at hcoord
  · have hz := hule z
    simp [e, rem32_abzExp, rem32_ab] at hz
    omega
  · have hz := hule z
    simp [e, rem32_cdzExp, rem32_ab] at hz
    omega

/-- The exact comparison stated at the beginning of Remark 3.2. -/
theorem rem32_omittedWeight_diagonal_eq_root_and_ne_family {t : ℕ} (ht : 0 < t) :
    (diagonal (rem32_omittedWeight t)
        (rem32_omittedRootIdeal : Ideal (MvPolynomial rem32_var K)) =
        rem32_omittedRootIdeal) ∧
      (rem32_omittedRootIdeal : Ideal (MvPolynomial rem32_var K)) ≠
        rem32_familyIdeal (K := K) t t := by
  constructor
  · exact rem32_omittedWeight_diagonal_root t
  · rw [← rem32_omittedWeight_diagonal_root (K := K) t]
    exact rem32_cannotOmitZ_fromRoot (K := K) ht ht (rem32_omittedWeight t)

/-- The same comparison before rewriting the fixed diagonal image. -/
theorem rem32_omittedWeight_diagonal_ne_family {t : ℕ} (ht : 0 < t) :
    diagonal (rem32_omittedWeight t)
        (rem32_omittedRootIdeal : Ideal (MvPolynomial rem32_var K)) ≠
      rem32_familyIdeal (K := K) t t := by
  exact rem32_cannotOmitZ_fromRoot (K := K) ht ht (rem32_omittedWeight t)

/-- The monomial \(ab\) witnesses the non-equality in Remark 3.2. -/
theorem rem32_omittedWeight_ab_mem_root_not_mem_family {t : ℕ} (ht : 0 < t) :
    ((X a * X b : MvPolynomial rem32_var K) ∈
        (rem32_omittedRootIdeal : Ideal (MvPolynomial rem32_var K))) ∧
      (X a * X b : MvPolynomial rem32_var K) ∉ rem32_familyIdeal (K := K) t t := by
  have habEq :
      (X a * X b : MvPolynomial rem32_var K) =
        monomial (characteristicExp rem32_ab) (1 : K) := by
    have heq : characteristicExp rem32_ab = Finsupp.single a 1 + Finsupp.single b 1 := by
      ext i
      cases i <;> simp [rem32_ab]
    rw [heq]
    simp [MvPolynomial.X, monomial_mul]
  have hRoot : (monomial (characteristicExp rem32_ab) (1 : K) :
      MvPolynomial rem32_var K) ∈ rem32_omittedRootIdeal := by
    rw [rem32_omittedRootIdeal, monomial_mem_monomialIdeal]
    exact ⟨characteristicExp rem32_ab,
      ⟨rem32_ab, by simp [rem32_omittedClutter], rfl⟩, le_rfl⟩
  have hNotFamily : (monomial (characteristicExp rem32_ab) (1 : K) :
      MvPolynomial rem32_var K) ∉ rem32_familyIdeal (K := K) t t := by
    intro hmem
    rw [rem32_familyIdeal, monomial_mem_monomialIdeal] at hmem
    rcases hmem with ⟨u, hu, hule⟩
    simp only [rem32_familyExps, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · have hc := hule c
      simp [rem32_ac, rem32_ab] at hc
    · have hd := hule d
      simp [rem32_bd, rem32_ab] at hd
    · have hz := hule z
      simp [rem32_abzExp, rem32_ab] at hz
      omega
    · have hz := hule z
      simp [rem32_cdzExp, rem32_ab] at hz
      omega
  constructor
  · simpa [habEq] using hRoot
  · intro hmem
    exact hNotFamily (by simpa [habEq] using hmem)

end SimisFormal
