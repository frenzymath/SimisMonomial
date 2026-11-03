import SimisFormal.Defs

section
namespace SimisFormal
open MvPolynomial
open scoped BigOperators
section SymbolicPower
variable {R : Type*} [CommRing R]
theorem isSimis_iff_componentSimis_of_stdSymbolic
    {I : Ideal R} {ι : Type*} {Q : ι → Ideal R}
    (hsym : HasStdSymbolicFormula I Q) : IsSimis I ↔ ComponentSimis I Q := by
  constructor
  · intro h q hq
    exact (h q hq).symm.trans (hsym q hq)
  · intro h q hq
    exact (hsym q hq).trans (h q hq).symm

/-- Radical commutes with a finite intersection of ideals. -/
theorem radical_finsetInf_eq_iInf_radical {ι : Type*} (s : Finset ι) (I : ι → Ideal R) :
    (s.inf I).radical = s.inf (fun i ↦ (I i).radical) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp [Ideal.radical_top]
  | insert j s hjs ih =>
      rw [Finset.inf_insert, Finset.inf_insert, Ideal.radical_inf, ih]

/-- Radical commutes with an intersection indexed by a finite type. -/
theorem radical_iInf_fintype {ι : Type*} [Fintype ι] (I : ι → Ideal R) :
    (⨅ i, I i).radical = ⨅ i, (I i).radical := by
  classical
  simpa [Finset.inf_univ_eq_iInf] using
    (radical_finsetInf_eq_iInf_radical (R := R) (Finset.univ : Finset ι) I)

end SymbolicPower
variable {σ K : Type*} [Field K] [DecidableEq σ]
/-- Membership of a monic monomial in a monomial ideal, as divisibility of exponents. -/
theorem monomial_mem_monomialIdeal {S : Set (σ →₀ ℕ)} {e : σ →₀ ℕ} :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ monomialIdeal S ↔ ∃ u ∈ S, u ≤ e := by
  rw [monomialIdeal]
  constructor
  · intro h
    exact (MvPolynomial.mem_ideal_span_monomial_image.mp h) e (by simp)
  · rintro ⟨u, huS, hu⟩
    rw [MvPolynomial.mem_ideal_span_monomial_image]
    intro xi hxi
    have hcoeff : coeff xi (monomial e (1 : K) : MvPolynomial σ K) ≠ 0 := by
      simpa [MvPolynomial.mem_support_iff] using hxi
    have hxie : xi = e := by
      by_contra hne
      have hexi : e ≠ xi := by
        intro h
        exact hne h.symm
      have hcoeff0 : coeff xi (monomial e (1 : K) : MvPolynomial σ K) = 0 := by
        rw [MvPolynomial.coeff_monomial]
        simp [hexi]
      exact hcoeff hcoeff0
    subst xi
    exact ⟨u, huS, hu⟩

omit [DecidableEq σ] in
/-- Membership of an arbitrary polynomial in a monomial ideal, supportwise. -/
theorem mem_monomialIdeal {S : Set (σ →₀ ℕ)} {x : MvPolynomial σ K} :
    x ∈ monomialIdeal S ↔ ∀ e ∈ x.support, ∃ u ∈ S, u ≤ e := by
  rw [monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image]

/-- Inclusion of monomial ideals is detected on monic monomials. -/
theorem monomialIdeal_le_iff {S T : Set (σ →₀ ℕ)} :
    (monomialIdeal S : Ideal (MvPolynomial σ K)) ≤ monomialIdeal T ↔
      ∀ e : σ →₀ ℕ, (∃ u ∈ S, u ≤ e) → ∃ v ∈ T, v ≤ e := by
  constructor
  · intro hle e he
    exact monomial_mem_monomialIdeal.mp
      (hle (monomial_mem_monomialIdeal.mpr he))
  · intro h x hx
    rw [monomialIdeal] at hx ⊢
    rw [MvPolynomial.mem_ideal_span_monomial_image] at hx ⊢
    intro xi hxi
    exact h xi (hx xi hxi)

/-- Equality of monomial ideals is detected on monic monomials. -/
theorem monomialIdeal_eq_iff {S T : Set (σ →₀ ℕ)} :
    (monomialIdeal S : Ideal (MvPolynomial σ K)) = monomialIdeal T ↔
      ∀ e : σ →₀ ℕ, (∃ u ∈ S, u ≤ e) ↔ ∃ v ∈ T, v ≤ e := by
  constructor
  · intro h e
    constructor
    · exact (monomialIdeal_le_iff.mp (le_of_eq h) e)
    · exact (monomialIdeal_le_iff.mp (le_of_eq h.symm) e)
  · intro h
    apply le_antisymm
    · exact monomialIdeal_le_iff.mpr (fun e he => (h e).mp he)
    · exact monomialIdeal_le_iff.mpr (fun e he => (h e).mpr he)

/-- Generators for the intersection of two monomial ideals. -/
def meetGens (S T : Set (σ →₀ ℕ)) : Set (σ →₀ ℕ) :=
  {z | ∃ s ∈ S, ∃ t ∈ T, z = s ⊔ t}

/-- The intersection formula for two monomial ideals. -/
theorem monomialIdeal_inf (S T : Set (σ →₀ ℕ)) :
    (monomialIdeal S : Ideal (MvPolynomial σ K)) ⊓ monomialIdeal T =
      monomialIdeal (meetGens S T) := by
  apply le_antisymm
  · intro x hx
    rw [monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image]
    intro e he
    have hxS : x ∈ (monomialIdeal S : Ideal (MvPolynomial σ K)) := by
      exact hx.1
    have hxT : x ∈ (monomialIdeal T : Ideal (MvPolynomial σ K)) := by
      exact hx.2
    rw [monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image] at hxS hxT
    rcases hxS e he with ⟨s, hsS, hse⟩
    rcases hxT e he with ⟨t, htT, hte⟩
    exact ⟨s ⊔ t, ⟨s, hsS, t, htT, rfl⟩, sup_le hse hte⟩
  · rw [monomialIdeal, Ideal.span_le]
    rintro y ⟨z, ⟨s, hsS, t, htT, rfl⟩, rfl⟩
    exact ⟨monomial_mem_monomialIdeal.mpr ⟨s, hsS, le_sup_left⟩,
      monomial_mem_monomialIdeal.mpr ⟨t, htT, le_sup_right⟩⟩

/-- Generators for the product of two monomial ideals. -/
def mulGens (S T : Set (σ →₀ ℕ)) : Set (σ →₀ ℕ) :=
  {z | ∃ s ∈ S, ∃ t ∈ T, z = s + t}

omit [DecidableEq σ] in
/-- The product formula for monomial ideals. -/
theorem monomialIdeal_mul (S T : Set (σ →₀ ℕ)) :
    (monomialIdeal S : Ideal (MvPolynomial σ K)) * monomialIdeal T =
      monomialIdeal (mulGens S T) := by
  rw [monomialIdeal, monomialIdeal, monomialIdeal, Ideal.span_mul_span']
  congr 1
  ext x
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    rcases hp with ⟨s, hsS, rfl⟩
    rcases hq with ⟨t, htT, rfl⟩
    refine ⟨s + t, ⟨s, hsS, t, htT, rfl⟩, ?_⟩
    simp [monomial_mul]
  · rintro ⟨z, ⟨s, hsS, t, htT, rfl⟩, rfl⟩
    refine ⟨monomial s (1 : K), ?_, monomial t (1 : K), ?_, ?_⟩
    · exact ⟨s, hsS, rfl⟩
    · exact ⟨t, htT, rfl⟩
    · simp [monomial_mul]

/-- Iterated generators for ordinary powers of a monomial ideal. -/
def powGens (S : Set (σ →₀ ℕ)) : ℕ → Set (σ →₀ ℕ)
  | 0 => {0}
  | n + 1 => {z | ∃ u ∈ powGens S n, ∃ s ∈ S, z = u + s}

omit [DecidableEq σ] in
/-- Ordinary powers are computed by sums of exponent generators. -/
theorem monomialIdeal_pow (S : Set (σ →₀ ℕ)) (n : ℕ) :
    (monomialIdeal S : Ideal (MvPolynomial σ K)) ^ n = monomialIdeal (powGens S n) := by
  induction n with
  | zero =>
      simp [powGens, monomialIdeal]
  | succ n ih =>
      rw [pow_succ, ih, monomialIdeal_mul]
      rfl

/-- Generators for a finite intersection of monomial ideals. -/
noncomputable def iInfGens {ι : Type*} [Fintype ι] (S : ι → Set (σ →₀ ℕ)) :
    Set (σ →₀ ℕ) :=
  {z | ∃ c : ι → (σ →₀ ℕ), (∀ j, c j ∈ S j) ∧ z = Finset.univ.sup c}

/-- Finite intersections are computed by coordinatewise joins of generators. -/
theorem monomialIdeal_iInf {ι : Type*} [Fintype ι] (S : ι → Set (σ →₀ ℕ)) :
    (⨅ j, (monomialIdeal (S j) : Ideal (MvPolynomial σ K))) =
      monomialIdeal (iInfGens S) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image]
    intro e he
    have hex : ∀ j, ∃ u ∈ S j, u ≤ e := by
      intro j
      have hxj : x ∈ (monomialIdeal (S j) : Ideal (MvPolynomial σ K)) :=
        (iInf_le (fun j => (monomialIdeal (S j) : Ideal (MvPolynomial σ K))) j) hx
      rw [monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image] at hxj
      exact hxj e he
    choose c hcS hc_le using hex
    refine ⟨Finset.univ.sup c, ⟨c, hcS, rfl⟩, ?_⟩
    exact Finset.sup_le fun j _ => hc_le j
  · rw [monomialIdeal, Ideal.span_le]
    rintro y ⟨z, ⟨c, hcS, rfl⟩, rfl⟩
    exact Ideal.mem_iInf.mpr (fun j =>
      monomial_mem_monomialIdeal.mpr
        ⟨c j, hcS j, Finset.le_sup (s := (Finset.univ : Finset ι)) (f := c) (by simp)⟩)

/-- Membership of a monic monomial in a pure-power component. -/
theorem monomial_mem_purePower {A : Finset σ} {a : σ → ℕ} {e : σ →₀ ℕ} :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ purePower A a ↔ ∃ i ∈ A, a i ≤ e i := by
  rw [purePower, monomial_mem_monomialIdeal]
  constructor
  · rintro ⟨u, ⟨i, hiA, rfl⟩, hle⟩
    exact ⟨i, hiA, Finsupp.single_le_iff.mp hle⟩
  · rintro ⟨i, hiA, hle⟩
    exact ⟨Finsupp.single i (a i), ⟨i, hiA, rfl⟩, Finsupp.single_le_iff.mpr hle⟩

/-- Membership of a monic monomial in a variable prime. -/
theorem monomial_mem_primeOf {A : Finset σ} {e : σ →₀ ℕ} :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ primeOf A ↔ ∃ i ∈ A, 1 ≤ e i := by
  simp [primeOf, monomial_mem_purePower]

omit [DecidableEq σ] in
/-- Membership of an arbitrary polynomial in a variable prime, supportwise. -/
theorem mem_primeOf {A : Finset σ} {x : MvPolynomial σ K} :
    x ∈ primeOf A ↔ ∀ e ∈ x.support, ∃ i ∈ A, 1 ≤ e i := by
  rw [primeOf, purePower, mem_monomialIdeal]
  constructor
  · intro h e he
    rcases h e he with ⟨u, ⟨i, hiA, rfl⟩, hue⟩
    exact ⟨i, hiA, Finsupp.single_le_iff.mp hue⟩
  · intro h e he
    rcases h e he with ⟨i, hiA, hie⟩
    exact ⟨Finsupp.single i 1, ⟨i, hiA, rfl⟩, Finsupp.single_le_iff.mpr hie⟩

/-- Kill the variables in a finite set and keep all other variables fixed. -/
noncomputable def killVariablesHom (A : Finset σ) :
    MvPolynomial σ K →+* MvPolynomial σ K :=
  eval₂Hom C (fun i ↦ if i ∈ A then 0 else X i)

/-- A monomial involving a killed variable maps to zero. -/
theorem killVariablesHom_monomial_eq_zero {A : Finset σ} {e : σ →₀ ℕ}
    (he : ∃ i ∈ A, e i ≠ 0) (c : K) :
    killVariablesHom (K := K) A (monomial e c) = 0 := by
  rw [killVariablesHom]
  apply MvPolynomial.eval₂Hom_eq_zero
  intro d hd
  have hde : d = e := by
    by_contra hne
    have hed : e ≠ d := fun h => hne h.symm
    have hzero : coeff d (monomial e c : MvPolynomial σ K) = 0 := by
      rw [MvPolynomial.coeff_monomial]
      simp [hed]
    exact hd hzero
  subst d
  rcases he with ⟨i, hiA, hi⟩
  exact ⟨i, by simpa [Finsupp.mem_support_iff] using hi, by simp [hiA]⟩

/-- A monomial avoiding all killed variables is fixed by the killing map. -/
theorem killVariablesHom_monomial_eq_self {A : Finset σ} {e : σ →₀ ℕ}
    (he : ∀ i ∈ A, e i = 0) (c : K) :
    killVariablesHom (K := K) A (monomial e c) = monomial e c := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  · have hv : ((monomial e c : MvPolynomial σ K).vars : Set σ) ⊆ {i : σ | i ∉ A} := by
      intro i hi
      have his : i ∈ e.support := by
        simpa [MvPolynomial.vars_monomial hc] using hi
      have hie : e i ≠ 0 := by
        simpa [Finsupp.mem_support_iff] using his
      exact fun hiA => hie (he i hiA)
    simpa [killVariablesHom] using
      (MvPolynomial.aeval_ite_mem_eq_self (monomial e c : MvPolynomial σ K)
        (s := {i : σ | i ∉ A}) hv)

/-- The difference between a polynomial and its variable-killing projection lies in `primeOf`. -/
theorem sub_killVariablesHom_mem_primeOf (A : Finset σ) (p : MvPolynomial σ K) :
    p - killVariablesHom (K := K) A p ∈ primeOf A := by
  induction p using MvPolynomial.induction_on' with
  | monomial e c =>
      by_cases he : ∃ i ∈ A, e i ≠ 0
      · have hz := killVariablesHom_monomial_eq_zero (K := K) he c
        rw [hz, sub_zero]
        rw [primeOf, purePower, monomialIdeal,
          MvPolynomial.mem_ideal_span_monomial_image]
        intro xi hxi
        have hxi_eq : xi = e := by
          have hcoeff : coeff xi (monomial e c : MvPolynomial σ K) ≠ 0 := by
            simpa [MvPolynomial.mem_support_iff] using hxi
          by_contra hne
          have hex : e ≠ xi := fun h => hne h.symm
          have hzero : coeff xi (monomial e c : MvPolynomial σ K) = 0 := by
            rw [MvPolynomial.coeff_monomial]
            simp [hex]
          exact hcoeff hzero
        subst xi
        rcases he with ⟨i, hiA, hie⟩
        refine ⟨Finsupp.single i 1, ⟨i, hiA, rfl⟩, ?_⟩
        exact Finsupp.single_le_iff.mpr (Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hie))
      · have he0 : ∀ i ∈ A, e i = 0 := by
          intro i hiA
          by_contra hie
          exact he ⟨i, hiA, hie⟩
        have hz := killVariablesHom_monomial_eq_self (K := K) he0 c
        rw [hz, sub_self]
        exact (primeOf A : Ideal (MvPolynomial σ K)).zero_mem
  | add p q hp hq =>
      have hadd :
          p + q - killVariablesHom (K := K) A (p + q) =
            (p - killVariablesHom (K := K) A p) +
              (q - killVariablesHom (K := K) A q) := by
        simp only [map_add]
        abel
      rw [hadd]
      exact (primeOf A : Ideal (MvPolynomial σ K)).add_mem hp hq

/-- The variable ideal is the kernel of the evident projection. -/
theorem primeOf_eq_ker_killVariablesHom (A : Finset σ) :
    (primeOf A : Ideal (MvPolynomial σ K)) =
      RingHom.ker (killVariablesHom (K := K) A) := by
  apply le_antisymm
  · rw [primeOf, purePower, monomialIdeal, Ideal.span_le]
    rintro y ⟨e, ⟨i, hiA, rfl⟩, rfl⟩
    change killVariablesHom (K := K) A (monomial (Finsupp.single i (1 : ℕ)) (1 : K)) = 0
    exact killVariablesHom_monomial_eq_zero (K := K)
      ⟨i, hiA, by simp⟩ (1 : K)
  · intro p hp
    change killVariablesHom (K := K) A p = 0 at hp
    have h := sub_killVariablesHom_mem_primeOf (K := K) A p
    simpa [hp] using h

/-- The ideal generated by a set of variables is prime. -/
theorem primeOf_isPrime (A : Finset σ) :
    (primeOf A : Ideal (MvPolynomial σ K)).IsPrime := by
  rw [primeOf_eq_ker_killVariablesHom]
  exact RingHom.ker_isPrime (killVariablesHom (K := K) A)

/-- A pure-power component is contained in its variable radical when exponents are positive. -/
theorem purePower_le_primeOf_of_pos {A : Finset σ} {a : σ → ℕ}
    (ha : ∀ i ∈ A, 0 < a i) :
    (purePower A a : Ideal (MvPolynomial σ K)) ≤ primeOf A := by
  change (monomialIdeal {e : σ →₀ ℕ | ∃ i ∈ A, e = Finsupp.single i (a i)} :
        Ideal (MvPolynomial σ K)) ≤
      monomialIdeal {e : σ →₀ ℕ | ∃ i ∈ A, e = Finsupp.single i (1 : ℕ)}
  rw [monomialIdeal_le_iff]
  rintro e ⟨u, ⟨i, hiA, rfl⟩, hue⟩
  refine ⟨Finsupp.single i 1, ⟨i, hiA, rfl⟩, ?_⟩
  have hai : a i ≤ e i := Finsupp.single_le_iff.mp hue
  exact Finsupp.single_le_iff.mpr (le_trans (Nat.succ_le_iff.mpr (ha i hiA)) hai)

/-- The radical of a pure-power component is the corresponding variable prime. -/
theorem purePower_radical_eq_primeOf {A : Finset σ} {a : σ → ℕ}
    (ha : ∀ i ∈ A, 0 < a i) :
    (purePower A a : Ideal (MvPolynomial σ K)).radical = primeOf A := by
  apply le_antisymm
  · exact (primeOf_isPrime (K := K) A).radical_le_iff.mpr
      (purePower_le_primeOf_of_pos (K := K) ha)
  · change (Ideal.span ((fun e : σ →₀ ℕ => (monomial e (1 : K) : MvPolynomial σ K)) ''
        {e : σ →₀ ℕ | ∃ i ∈ A, e = Finsupp.single i (1 : ℕ)}) :
        Ideal (MvPolynomial σ K)) ≤ (purePower A a : Ideal (MvPolynomial σ K)).radical
    rw [Ideal.span_le]
    rintro y ⟨e, ⟨i, hiA, rfl⟩, rfl⟩
    refine ⟨a i, ?_⟩
    have hgen : (monomial (Finsupp.single i (a i)) (1 : K) : MvPolynomial σ K) ∈
        purePower A a :=
      monomial_mem_purePower.mpr ⟨i, hiA, by simp⟩
    simpa [monomial_pow] using hgen

/-- Inclusion of variable primes is detected on their variable sets. -/
theorem primeOf_le_iff_subset {A B : Finset σ} :
    (primeOf A : Ideal (MvPolynomial σ K)) ≤ primeOf B ↔ A ⊆ B := by
  constructor
  · intro h i hi
    have hmem : (monomial (Finsupp.single i (1 : ℕ)) (1 : K) : MvPolynomial σ K) ∈
        primeOf A :=
      monomial_mem_primeOf.mpr ⟨i, hi, by simp⟩
    rcases monomial_mem_primeOf.mp (h hmem) with ⟨j, hjB, hjle⟩
    have hji : j = i := by
      by_contra hne
      simp [hne] at hjle
    simpa [hji] using hjB
  · intro hsub
    change (monomialIdeal {e : σ →₀ ℕ | ∃ i ∈ A, e = Finsupp.single i (1 : ℕ)} :
        Ideal (MvPolynomial σ K)) ≤
      monomialIdeal {e : σ →₀ ℕ | ∃ i ∈ B, e = Finsupp.single i (1 : ℕ)}
    rw [monomialIdeal_le_iff]
    intro e he
    rcases he with ⟨u, ⟨i, hiA, rfl⟩, hue⟩
    exact ⟨Finsupp.single i 1, ⟨i, hsub hiA, rfl⟩, hue⟩

omit [Field K] [DecidableEq σ] in
/-- Ideal height is unchanged by passing to the radical. -/
theorem height_radical {R : Type*} [CommRing R] (I : Ideal R) :
    I.radical.height = I.height := by
  rw [Ideal.height_eq_inf_minimalPrimes, Ideal.height_eq_inf_minimalPrimes]
  rw [Ideal.radical_minimalPrimes]

omit [DecidableEq σ] in
/-- A variable prime is generated by its variables. -/
theorem primeOf_eq_span_X {A : Finset σ} :
    (primeOf A : Ideal (MvPolynomial σ K)) =
      Ideal.span ((fun i : σ => (X i : MvPolynomial σ K)) '' (A : Set σ)) := by
  classical
  let f : σ → MvPolynomial σ K := fun i => X i
  change (primeOf A : Ideal (MvPolynomial σ K)) = Ideal.span (f '' (A : Set σ))
  rw [primeOf, purePower, monomialIdeal]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro y ⟨e, ⟨i, hiA, rfl⟩, rfl⟩
    change (monomial (Finsupp.single i (1 : ℕ)) (1 : K) : MvPolynomial σ K) ∈
      Ideal.span (f '' (A : Set σ))
    have hmem : f i ∈ Ideal.span (f '' (A : Set σ)) :=
      Ideal.subset_span ⟨i, hiA, rfl⟩
    simpa [f, X] using hmem
  · rw [Ideal.span_le]
    rintro y ⟨i, hiA, rfl⟩
    change (monomial (Finsupp.single i (1 : ℕ)) (1 : K) : MvPolynomial σ K) ∈
      monomialIdeal {e : σ →₀ ℕ | ∃ i ∈ A, e = Finsupp.single i (1 : ℕ)}
    exact monomial_mem_monomialIdeal.mpr
      ⟨Finsupp.single i (1 : ℕ), ⟨i, hiA, rfl⟩, le_rfl⟩

omit [DecidableEq σ] in
/-- A variable prime in a finite polynomial ring has height equal to its support cardinality. -/
theorem height_primeOf_eq_card [Fintype σ] (A : Finset σ) :
    (primeOf A : Ideal (MvPolynomial σ K)).height = (A.card : ℕ∞) := by
  classical
  have hlower : (A.card : ℕ∞) ≤ (primeOf A : Ideal (MvPolynomial σ K)).height := by
    induction A using Finset.induction_on with
    | empty =>
        have hbot : (primeOf (∅ : Finset σ) : Ideal (MvPolynomial σ K)) = ⊥ := by
          rw [primeOf, purePower, monomialIdeal]
          simp
        rw [hbot]
        simp
    | insert i A hi ih =>
        have hle : (primeOf A : Ideal (MvPolynomial σ K)) ≤ primeOf (insert i A) :=
          (primeOf_le_iff_subset (K := K)).mpr (by simp)
        have hne : (primeOf A : Ideal (MvPolynomial σ K)) ≠ primeOf (insert i A) := by
          intro hEq
          have hback : (primeOf (insert i A) : Ideal (MvPolynomial σ K)) ≤ primeOf A := by
            rw [hEq]
          have hsub : insert i A ⊆ A := (primeOf_le_iff_subset (K := K)).mp hback
          exact hi (hsub (by simp))
        have hlt : (primeOf A : Ideal (MvPolynomial σ K)) < primeOf (insert i A) :=
          lt_of_le_of_ne hle hne
        have hpA : (primeOf A : Ideal (MvPolynomial σ K)).IsPrime := primeOf_isPrime A
        have hpI : (primeOf (insert i A) : Ideal (MvPolynomial σ K)).IsPrime :=
          primeOf_isPrime (insert i A)
        have hstep : (primeOf A : Ideal (MvPolynomial σ K)).height + 1 ≤
            (primeOf (insert i A) : Ideal (MvPolynomial σ K)).height :=
          @Ideal.height_add_one_le_of_lt_of_isPrime (MvPolynomial σ K) inferInstance
            (primeOf A : Ideal (MvPolynomial σ K))
            (primeOf (insert i A) : Ideal (MvPolynomial σ K)) hpA hpI hlt
        calc
          ((insert i A).card : ℕ∞) = (A.card : ℕ∞) + 1 := by
            simp [Finset.card_insert_of_notMem hi]
          _ ≤ (primeOf A : Ideal (MvPolynomial σ K)).height + 1 := by
            simpa [add_comm] using add_le_add_right ih (1 : ℕ∞)
          _ ≤ (primeOf (insert i A) : Ideal (MvPolynomial σ K)).height := hstep
  let f : σ → MvPolynomial σ K := fun i => X i
  let S : Finset (MvPolynomial σ K) := A.image f
  have hspan : (primeOf A : Ideal (MvPolynomial σ K)) =
      Ideal.span (S : Set (MvPolynomial σ K)) := by
    simpa [S, f] using (primeOf_eq_span_X (K := K) (A := A))
  have hupper : (primeOf A : Ideal (MvPolynomial σ K)).height ≤ (A.card : ℕ∞) := by
    have hne : (primeOf A : Ideal (MvPolynomial σ K)) ≠ ⊤ :=
      (primeOf_isPrime (K := K) A).ne_top
    have hheight : (primeOf A : Ideal (MvPolynomial σ K)).height ≤
        ((Submodule.spanFinrank (primeOf A : Ideal (MvPolynomial σ K))) : ℕ∞) :=
      Ideal.height_le_spanFinrank (primeOf A : Ideal (MvPolynomial σ K)) hne
    have hsf : Submodule.spanFinrank (primeOf A : Ideal (MvPolynomial σ K)) ≤ S.card := by
      rw [hspan]
      simpa using (Submodule.spanFinrank_span_le_ncard_of_finite
        (s := (S : Set (MvPolynomial σ K))) S.finite_toSet)
    have hcardNat : S.card ≤ A.card := by
      dsimp [S]
      exact Finset.card_image_le
    have hsfNat : Submodule.spanFinrank (primeOf A : Ideal (MvPolynomial σ K)) ≤ A.card :=
      hsf.trans hcardNat
    have hsfENat : ((Submodule.spanFinrank (primeOf A : Ideal (MvPolynomial σ K))) : ℕ∞) ≤
        (A.card : ℕ∞) := by
      exact_mod_cast hsfNat
    exact hheight.trans hsfENat
  exact le_antisymm hupper hlower

omit [DecidableEq σ] in
/-- A pure-power component with positive exponents has the same height as its radical. -/
theorem height_purePower_eq_card [Fintype σ] {A : Finset σ} {a : σ → ℕ}
    (ha : ∀ i ∈ A, 0 < a i) :
    (purePower A a : Ideal (MvPolynomial σ K)).height = (A.card : ℕ∞) := by
  classical
  calc
    (purePower A a : Ideal (MvPolynomial σ K)).height =
        (purePower A a : Ideal (MvPolynomial σ K)).radical.height :=
      (height_radical (purePower A a : Ideal (MvPolynomial σ K))).symm
    _ = (primeOf A : Ideal (MvPolynomial σ K)).height := by
      rw [purePower_radical_eq_primeOf (K := K) ha]
    _ = (A.card : ℕ∞) := height_primeOf_eq_card (K := K) A

/-- A lexicographic Finsupp inequality follows from pointwise inequality and one strict
coordinate. The strict coordinate must be the least coordinate at which the two functions
differ. -/
theorem finsupp_lex_lt_of_le_of_exists_lt {α : Type*} [LinearOrder α]
    {a b : α →₀ ℕ} (hle : a ≤ b) (hex : ∃ i, a i < b i) :
    (toLex a : Lex (α →₀ ℕ)) < toLex b := by
  classical
  rcases hex with ⟨i₀, hi₀⟩
  let D : Finset α := (a.support ∪ b.support).filter (fun i => a i ≠ b i)
  have hiD : i₀ ∈ D := by
    have hsupp : i₀ ∈ a.support ∪ b.support := by
      apply Finset.mem_union.mpr
      by_cases hb : b i₀ = 0
      · left
        have ha : a i₀ ≠ 0 := by omega
        simpa [Finsupp.mem_support_iff] using ha
      · right
        simpa [Finsupp.mem_support_iff] using hb
    exact Finset.mem_filter.mpr ⟨hsupp, ne_of_lt hi₀⟩
  obtain ⟨j, hjD, hjmin⟩ := Finset.exists_min_image D (fun i => i) ⟨i₀, hiD⟩
  rw [Finsupp.Lex.lt_iff]
  have hjne : a j ≠ b j := (Finset.mem_filter.mp hjD).2
  refine ⟨j, ?_, ?_⟩
  · intro k hk
    have hEq : a k = b k := by
      by_contra hne
      have hsupp : k ∈ a.support ∪ b.support := by
        apply Finset.mem_union.mpr
        by_cases ha : a k = 0
        · right
          have hb : b k ≠ 0 := by
            intro hb
            exact hne (by omega)
          simpa [Finsupp.mem_support_iff] using hb
        · left
          simpa [Finsupp.mem_support_iff] using ha
      have hkD : k ∈ D := Finset.mem_filter.mpr ⟨hsupp, hne⟩
      exact (not_lt_of_ge (hjmin k hkD)) hk
    simp [hEq]
  · have hlej := hle j
    have hlt : a j < b j := by omega
    simpa using hlt

omit [DecidableEq σ] in
/-- Generators of a power of a monomial ideal have support contained in the union of supports
of the original generators. -/
theorem powGens_support_subset {A : Finset σ} {S : Set (σ →₀ ℕ)}
    (hS : ∀ u ∈ S, u.support ⊆ A) :
    ∀ n e, e ∈ powGens S n → e.support ⊆ A := by
  intro n
  induction n with
  | zero =>
      intro e he
      simp [powGens] at he
      subst e
      simp
  | succ n ih =>
      intro e he i hi
      rcases he with ⟨u, hu, s, hs, rfl⟩
      by_contra hnot
      have hu0 : u i = 0 := by
        by_contra hui
        have huiSupp : i ∈ u.support := by simpa [Finsupp.mem_support_iff] using hui
        exact hnot (ih u hu huiSupp)
      have hs0 : s i = 0 := by
        by_contra hsi
        have hsiSupp : i ∈ s.support := by simpa [Finsupp.mem_support_iff] using hsi
        exact hnot (hS s hs hsiSupp)
      have hsum0 : (u + s) i = 0 := by simp [hu0, hs0]
      have hsumNe : (u + s) i ≠ 0 := by simpa [Finsupp.mem_support_iff] using hi
      exact hsumNe hsum0

/-- If a pure-power component has a zero exponent on its own support, it is the unit ideal. -/
theorem purePower_eq_top_of_zero_on_support {A : Finset σ} {a : σ → ℕ}
    {i : σ} (hi : i ∈ A) (ha : a i = 0) :
    (purePower A a : Ideal (MvPolynomial σ K)) = ⊤ := by
  apply (Ideal.eq_top_iff_one (purePower A a : Ideal (MvPolynomial σ K))).mpr
  have hmem : (monomial (0 : σ →₀ ℕ) (1 : K) : MvPolynomial σ K) ∈ purePower A a := by
    rw [monomial_mem_purePower]
    exact ⟨i, hi, by simp [ha]⟩
  simpa using hmem

omit [DecidableEq σ] in
@[simp]
theorem mem_minGens {I : Ideal (MvPolynomial σ K)} {e : σ →₀ ℕ} :
    e ∈ minGens I ↔ (monomial e (1 : K) : MvPolynomial σ K) ∈ I ∧
      ∀ u, (monomial u (1 : K) : MvPolynomial σ K) ∈ I → u ≤ e → u = e := Iff.rfl

/-- Every monomial of an ideal lies above a minimal monomial generator. -/
theorem exists_minGens_le {I : Ideal (MvPolynomial σ K)} {e : σ →₀ ℕ}
    (he : (monomial e (1 : K) : MvPolynomial σ K) ∈ I) :
    ∃ u ∈ minGens I, u ≤ e := by
  classical
  let T : Finset (σ →₀ ℕ) :=
    (Finset.Iic e).filter fun u ↦ (monomial u (1 : K) : MvPolynomial σ K) ∈ I
  have heT : e ∈ T := by
    simp [T, he]
  obtain ⟨u, huT, hmin⟩ :=
    Finset.exists_min_image T (fun u ↦ (Finset.Iic u).card) ⟨e, heT⟩
  have hue : u ≤ e := by
    have huIic := (Finset.mem_filter.mp huT).1
    simpa using huIic
  have huI : (monomial u (1 : K) : MvPolynomial σ K) ∈ I :=
    (Finset.mem_filter.mp huT).2
  refine ⟨u, ?_, hue⟩
  rw [mem_minGens]
  refine ⟨huI, ?_⟩
  intro v hvI hvu
  by_contra hne
  have hve : v ≤ e := le_trans hvu hue
  have hvT : v ∈ T := by
    simp [T, hve, hvI]
  have hcard : (Finset.Iic u).card ≤ (Finset.Iic v).card := hmin v hvT
  have hsub : Finset.Iic v ⊆ Finset.Iic u := by
    intro w hw
    have hwv : w ≤ v := by simpa using hw
    exact by simpa using le_trans hwv hvu
  have hnot : u ∉ Finset.Iic v := by
    intro huv
    have huv' : u ≤ v := by simpa using huv
    exact hne (le_antisymm hvu huv')
  have hss : Finset.Iic v ⊂ Finset.Iic u :=
    (Finset.ssubset_iff_of_subset hsub).2 ⟨u, by simp, hnot⟩
  have hlt : (Finset.Iic v).card < (Finset.Iic u).card := Finset.card_lt_card hss
  exact (not_lt_of_ge hcard) hlt

omit [DecidableEq σ] in
/-- Coordinate of a diagonally multiplied exponent. -/
@[simp] theorem diagExp_apply (d : σ → ℕ) (e : σ →₀ ℕ) (i : σ) :
    diagExp d e i = e i * d i := by
  simp [diagExp]

omit [DecidableEq σ] in
/-- Coordinate of floor division. -/
@[simp] theorem floorDiv_apply (d : σ → ℕ) (e : σ →₀ ℕ) (i : σ) :
    floorDiv d e i = e i / d i := by
  simp [floorDiv]

omit [DecidableEq σ] in
/-- Divisibility after a positive diagonal map is the same as floor division. -/
theorem diagExp_le_iff_floor {d : σ → ℕ} (hd : ∀ i, 0 < d i) (u β : σ →₀ ℕ) :
    diagExp d u ≤ β ↔ u ≤ floorDiv d β := by
  rw [Finsupp.le_def, Finsupp.le_def]
  constructor
  · intro h i
    have hi := h i
    simp only [diagExp_apply, floorDiv_apply] at hi ⊢
    exact (Nat.le_div_iff_mul_le (hd i)).2 hi
  · intro h i
    have hi := h i
    simp only [diagExp_apply, floorDiv_apply] at hi ⊢
    exact (Nat.le_div_iff_mul_le (hd i)).1 hi

omit [DecidableEq σ] in
/-- Image of a monic monomial under a diagonal endomorphism. -/
theorem diagHom_monomial [Fintype σ] (d : σ → ℕ) (e : σ →₀ ℕ) :
    diagHom d (monomial e (1 : K)) = monomial (diagExp d e) (1 : K) := by
  rw [diagHom, MvPolynomial.eval₂Hom_monomial]
  simp only [map_one, one_mul]
  rw [MvPolynomial.monic_monomial_eq]
  simp [diagExp_apply, Finsupp.prod_pow, pow_mul, Nat.mul_comm]

/-- The diagonal image of a monomial ideal is generated by weighted generators. -/
theorem diagonal_monomialIdeal [Fintype σ] (d : σ → ℕ) (S : Set (σ →₀ ℕ)) :
    diagonal d (monomialIdeal S : Ideal (MvPolynomial σ K)) =
      monomialIdeal (diagExp d '' S) := by
  rw [diagonal]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    rw [monomialIdeal, Ideal.span_le]
    rintro y ⟨e, heS, rfl⟩
    change diagHom (K := K) d (monomial e (1 : K)) ∈
      (monomialIdeal (diagExp d '' S) : Ideal (MvPolynomial σ K))
    rw [diagHom_monomial]
    exact monomial_mem_monomialIdeal.mpr ⟨diagExp d e, ⟨e, heS, rfl⟩, le_rfl⟩
  · rw [monomialIdeal, Ideal.span_le]
    rintro y ⟨z, ⟨e, heS, rfl⟩, rfl⟩
    change (monomial (diagExp d e) (1 : K) : MvPolynomial σ K) ∈
      Ideal.map (diagHom (K := K) d) (monomialIdeal S : Ideal (MvPolynomial σ K))
    rw [← diagHom_monomial]
    exact Ideal.mem_map_of_mem (diagHom (K := K) d)
      (monomial_mem_monomialIdeal.mpr ⟨e, heS, le_rfl⟩)

/-- Eq. (3) for an explicitly generated monomial ideal. -/
theorem monomial_mem_diagonal_monomialIdeal [Fintype σ] {d : σ → ℕ}
    (hd : ∀ i, 0 < d i) (S : Set (σ →₀ ℕ)) {e : σ →₀ ℕ} :
    (monomial e (1 : K) : MvPolynomial σ K) ∈
        diagonal d (monomialIdeal S : Ideal (MvPolynomial σ K)) ↔
      (monomial (floorDiv d e) (1 : K) : MvPolynomial σ K) ∈ monomialIdeal S := by
  rw [diagonal_monomialIdeal]
  constructor
  · intro h
    rcases monomial_mem_monomialIdeal.mp h with ⟨z, ⟨u, huS, rfl⟩, hzle⟩
    exact monomial_mem_monomialIdeal.mpr
      ⟨u, huS, (diagExp_le_iff_floor hd u e).mp hzle⟩
  · intro h
    rcases monomial_mem_monomialIdeal.mp h with ⟨u, huS, hule⟩
    exact monomial_mem_monomialIdeal.mpr
      ⟨diagExp d u, ⟨u, huS, rfl⟩, (diagExp_le_iff_floor hd u e).mpr hule⟩

/-- Eq. (3) for an arbitrary monomial ideal, represented explicitly in the hypothesis. -/
theorem monomial_mem_diagonal [Fintype σ] {I : Ideal (MvPolynomial σ K)}
    (hI : IsMonomialIdeal I) {d : σ → ℕ} (hd : ∀ i, 0 < d i) {e : σ →₀ ℕ} :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ diagonal d I ↔
      (monomial (floorDiv d e) (1 : K) : MvPolynomial σ K) ∈ I := by
  rcases hI with ⟨S, hS⟩
  simpa [hS] using (monomial_mem_diagonal_monomialIdeal (K := K) hd S (e := e))

@[simp] theorem characteristicExp_apply (A : Finset σ) (i : σ) :
    characteristicExp A i = if i ∈ A then 1 else 0 := by
  simp [characteristicExp]

/-- Exponents on a component's own support are positive in an irredundant family. -/
theorem exponents_pos_of_irredundant {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hirr : IsIrredundant (K := K) A a) :
    ∀ j i, i ∈ A j → 0 < a j i := by
  intro j i hi
  by_contra hpos
  have ha0 : a j i = 0 := Nat.eq_zero_of_not_pos hpos
  have htop : (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) = ⊤ :=
    purePower_eq_top_of_zero_on_support (K := K) hi ha0
  exact hirr j (by rw [htop]; exact le_top)

end SimisFormal
end
