import SimisFormal.Defs
import SimisFormal.Basic
import SimisFormal.Prop2_1
import SimisFormal.Eq4_DiagonalSimis
import SimisFormal.MonomialDecompExists

namespace SimisFormal
open MvPolynomial
open scoped BigOperators
variable {σ K ι : Type*} [Field K] [DecidableEq σ] [Fintype σ]
noncomputable section
omit [DecidableEq σ] [Fintype σ] in
/-- The grouped components still intersect to the original ideal. -/
theorem diagAssoc_iInf_groupedComponent {I : Ideal (MvPolynomial σ K)}
    {A : ι → Finset σ} {a : ι → σ → ℕ} (hI : HasComponents I A a) :
    I = ⨅ B : Set.range A, diagAssoc_groupedComponent (K := K) A a B := by
  ext x
  constructor
  · intro hx
    rw [hI] at hx
    refine Ideal.mem_iInf.mpr ?_
    intro B
    change x ∈ (⨅ j : {j : ι // A j = B.1},
      (purePower (A j.1) (a j.1) : Ideal (MvPolynomial σ K)))
    refine Ideal.mem_iInf.mpr ?_
    intro j
    exact Ideal.mem_iInf.mp hx j.1
  · intro hx
    rw [hI]
    refine Ideal.mem_iInf.mpr ?_
    intro j
    let B : Set.range A := ⟨A j, ⟨j, rfl⟩⟩
    have hxB : x ∈ diagAssoc_groupedComponent (K := K) A a B := Ideal.mem_iInf.mp hx B
    have hxB' : x ∈ (⨅ k : {k : ι // A k = B.1},
        (purePower (A k.1) (a k.1) : Ideal (MvPolynomial σ K))) := by
      simpa [diagAssoc_groupedComponent] using hxB
    exact Ideal.mem_iInf.mp hxB' ⟨j, rfl⟩

omit [Fintype σ] in
/-- The radical of a radical class component is the common radical of the class. -/
theorem diagAssoc_groupedComponent_radical [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hirr : IsIrredundant (K := K) A a) (B : Set.range A) :
    (diagAssoc_groupedComponent (K := K) A a B : Ideal (MvPolynomial σ K)).radical =
      primeOf B.1 := by
  classical
  have ha : ∀ j i, i ∈ A j → 0 < a j i :=
    fun j i hi ↦ prop21_componentExponent_pos_of_irredundant (K := K) hirr hi
  rcases B.2 with ⟨j₀, hj₀⟩
  let : Nonempty {j : ι // A j = B.1} := ⟨⟨j₀, hj₀⟩⟩
  calc
    (diagAssoc_groupedComponent (K := K) A a B : Ideal (MvPolynomial σ K)).radical =
        ⨅ j : {j : ι // A j = B.1},
          (purePower (A j.1) (a j.1) : Ideal (MvPolynomial σ K)).radical := by
      rw [diagAssoc_groupedComponent, radical_iInf_fintype]
    _ = ⨅ j : {j : ι // A j = B.1}, (primeOf B.1 : Ideal (MvPolynomial σ K)) := by
      apply iInf_congr
      intro j
      calc
        (purePower (A j.1) (a j.1) : Ideal (MvPolynomial σ K)).radical =
            primeOf (A j.1) :=
          purePower_radical_eq_primeOf (K := K) (a := a j.1)
            (fun i hi ↦ ha j.1 i hi)
        _ = primeOf B.1 := by rw [j.2]
    _ = primeOf B.1 := by simp

/-- A radical class component is primary. -/
theorem diagAssoc_groupedComponent_isPrimary [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hirr : IsIrredundant (K := K) A a) (B : Set.range A) :
    (diagAssoc_groupedComponent (K := K) A a B : Ideal (MvPolynomial σ K)).IsPrimary := by
  classical
  have ha : ∀ j i, i ∈ A j → 0 < a j i :=
    fun j i hi ↦ prop21_componentExponent_pos_of_irredundant (K := K) hirr hi
  rcases B.2 with ⟨j₀, hj₀⟩
  let jB : {j : ι // A j = B.1} := ⟨j₀, hj₀⟩
  let Q : {j : ι // A j = B.1} → Ideal (MvPolynomial σ K) :=
    fun j ↦ purePower (A j.1) (a j.1)
  have hgroup : diagAssoc_groupedComponent (K := K) A a B =
      Finset.univ.inf Q := by
    simp [diagAssoc_groupedComponent, Q, Finset.inf_univ_eq_iInf]
  rw [hgroup]
  refine Ideal.isPrimary_finsetInf (i := jB) (by simp) ?_ ?_
  · intro j hj
    exact prop21_purePower_isPrimary (K := K) (a := a j.1)
      (fun i hi ↦ ha j.1 i hi)
  · intro j hj
    calc
      (Q j : Ideal (MvPolynomial σ K)).radical = primeOf (A j.1) := by
        simpa [Q] using
          (purePower_radical_eq_primeOf (K := K) (a := a j.1)
            (fun i hi ↦ ha j.1 i hi))
      _ = primeOf (A jB.1) := by rw [j.2, jB.2]
      _ = (Q jB : Ideal (MvPolynomial σ K)).radical := by
        symm
        simpa [Q] using
          (purePower_radical_eq_primeOf (K := K) (a := a jB.1)
            (fun i hi ↦ ha jB.1 i hi))

/-- The grouped family is a minimal primary decomposition, retaining embedded components. -/
theorem diagAssoc_groupedComponents_isCanonicalPrimarySet [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hirr : IsIrredundant (K := K) A a) :
    diagAssoc_IsCanonicalPrimarySet I (diagAssoc_groupedComponents (K := K) A a) := by
  classical
  let G : Set.range A → Ideal (MvPolynomial σ K) := diagAssoc_groupedComponent (K := K) A a
  let t : Finset (Ideal (MvPolynomial σ K)) := Finset.univ.image G
  have htInf : t = Finset.univ.image G := rfl
  refine ⟨t, ?_, ?_⟩
  · ext J
    constructor
    · intro hJ
      rcases Finset.mem_image.mp hJ with ⟨B, hB, rfl⟩
      exact ⟨B, rfl⟩
    · rintro ⟨B, rfl⟩
      exact Finset.mem_image.mpr ⟨B, by simp, rfl⟩
  · have htinf : t.inf id = I := by
      calc
        t.inf id = ⨅ B : Set.range A, G B := by
          rw [htInf, Finset.inf_image]
          exact Finset.inf_univ_eq_iInf G
        _ = I := by
          simpa [G] using (diagAssoc_iInf_groupedComponent (K := K) hI).symm
    refine ⟨htinf, ?_, ?_, ?_⟩
    · intro J hJ
      change J ∈ Finset.univ.image G at hJ
      rcases Finset.mem_image.mp hJ with ⟨B, hB, rfl⟩
      exact diagAssoc_groupedComponent_isPrimary (K := K) hirr B
    · intro J hJ K' hK' hne
      dsimp only [Function.onFun]
      change J ∈ Finset.univ.image G at hJ
      change K' ∈ Finset.univ.image G at hK'
      rcases Finset.mem_image.mp hJ with ⟨B, hB, rfl⟩
      rcases Finset.mem_image.mp hK' with ⟨C, hC, rfl⟩
      intro hrad
      have hradB := diagAssoc_groupedComponent_radical (K := K) hirr B
      have hradC := diagAssoc_groupedComponent_radical (K := K) hirr C
      have hP : (primeOf B.1 : Ideal (MvPolynomial σ K)) = primeOf C.1 := by
        simpa [G, Submodule.colon_univ, hradB, hradC] using hrad
      have hBC : B.1 ⊆ C.1 := primeOf_le_iff_subset.mp (le_of_eq hP)
      have hCB : C.1 ⊆ B.1 := primeOf_le_iff_subset.mp (le_of_eq hP.symm)
      have hEq : B = C := Subtype.ext (Finset.Subset.antisymm hBC hCB)
      apply hne
      simp [G, hEq]
    · intro J hJ
      change J ∈ Finset.univ.image G at hJ
      rcases Finset.mem_image.mp hJ with ⟨B, hB, rfl⟩
      intro hle
      rcases B.2 with ⟨j₀, hj₀⟩
      apply hirr j₀
      intro x hxomit
      have hxinf : x ∈ (⨅ k : {k : ι // k ≠ j₀},
          (purePower (A k.1) (a k.1) : Ideal (MvPolynomial σ K))) := by
        simpa [decompOmit] using hxomit
      have hxt : x ∈ (t.erase (G B)).inf id := by
        rw [Submodule.mem_finsetInf]
        intro L hL
        rcases Finset.mem_erase.mp hL with ⟨hLne, hLt⟩
        change L ∈ Finset.univ.image G at hLt
        rcases Finset.mem_image.mp hLt with ⟨C, hC, rfl⟩
        have hCB : C ≠ B := by
          intro hCB
          apply hLne
          simp [hCB]
        have hval : C.1 ≠ B.1 := by
          intro hval
          exact hCB (Subtype.ext hval)
        change x ∈ G C
        refine Ideal.mem_iInf.mpr ?_
        intro k
        have hkj : k.1 ≠ j₀ := by
          intro hkj
          apply hval
          rw [← k.2, hkj, hj₀]
        exact Ideal.mem_iInf.mp hxinf ⟨k.1, hkj⟩
      have hxGB : x ∈ G B := hle hxt
      have hxGB' : x ∈ (⨅ k : {k : ι // A k = B.1},
          (purePower (A k.1) (a k.1) : Ideal (MvPolynomial σ K))) := by
        simpa [G, diagAssoc_groupedComponent] using hxGB
      exact Ideal.mem_iInf.mp hxGB' ⟨j₀, hj₀⟩

/-- For an irredundant monomial decomposition, the associated primes are the displayed
radicals, with repetitions discarded.  Embedded radicals are included. -/
theorem diagAssoc_associatedPrimes_eq_range [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hirr : IsIrredundant (K := K) A a) :
    I.associatedPrimes = Set.range (fun j ↦ (primeOf (A j) : Ideal (MvPolynomial σ K))) := by
  classical
  obtain ⟨t, htSet, ht⟩ :=
    diagAssoc_groupedComponents_isCanonicalPrimarySet (K := K) hI hirr
  have hAss := ht.image_radical_eq_associated_primes
  rw [← hAss]
  ext P
  constructor
  · rintro ⟨J, hJt, rfl⟩
    have hJSet : J ∈ diagAssoc_groupedComponents (K := K) A a := by
      rw [← htSet]
      exact hJt
    rcases hJSet with ⟨B, rfl⟩
    rcases B.2 with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    simpa [Submodule.colon_univ, ← hj] using
      (diagAssoc_groupedComponent_radical (K := K) hirr B).symm
  · rintro ⟨j, rfl⟩
    let B : Set.range A := ⟨A j, ⟨j, rfl⟩⟩
    have hGSet :
        diagAssoc_groupedComponent (K := K) A a B ∈
          diagAssoc_groupedComponents (K := K) A a :=
      ⟨B, rfl⟩
    have hGtSet : diagAssoc_groupedComponent (K := K) A a B ∈
        (t : Set (Ideal (MvPolynomial σ K))) := by
      rw [htSet]
      exact hGSet
    have hGt : diagAssoc_groupedComponent (K := K) A a B ∈ t :=
      Finset.mem_coe.mp hGtSet
    refine ⟨diagAssoc_groupedComponent (K := K) A a B, hGt, ?_⟩
    simpa [Submodule.colon_univ, B] using
      (diagAssoc_groupedComponent_radical (K := K) hirr B)

/-- The quotient-module convention used in the paper. -/
theorem diagAssoc_quotientAssociatedPrimes_eq_range [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hirr : IsIrredundant (K := K) A a) :
    associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) =
      Set.range (fun j ↦ (primeOf (A j) : Ideal (MvPolynomial σ K))) :=
  (prop21_associatedPrimes_quotient_eq_submodule (I := I)).trans
    (diagAssoc_associatedPrimes_eq_range (K := K) hI hirr)

/-- Weighting an irredundant irreducible decomposition produces the expected irredundant
irreducible decomposition. -/
theorem diagAssoc_diagonal_hasComponents [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} {d : σ → ℕ}
    (hd : ∀ i, 0 < d i) (hI : HasComponents I A a) :
    HasComponents (diagonal d I) A (fun j i ↦ a j i * d i) := by
  change diagonal d I = ⨅ j, (purePower (A j) (fun i ↦ a j i * d i) :
    Ideal (MvPolynomial σ K))
  rw [hI]
  rw [eq4_diagonal_iInf
    (Q := fun j ↦ (purePower (A j) (a j) : Ideal (MvPolynomial σ K)))
    (fun j ↦ eq4_isMonomialIdeal_purePower (K := K) (A j) (a j)) hd]
  apply iInf_congr
  intro j
  exact eq4_diagonal_purePower (K := K) d (A j) (a j)

theorem diagAssoc_diagonal_isIrredundant [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ} {d : σ → ℕ}
    (hd : ∀ i, 0 < d i) (hirr : IsIrredundant (K := K) A a) :
    IsIrredundant (K := K) A (fun j i ↦ a j i * d i) := by
  intro j hleD
  have hleDiag : diagonal d (decompOmit A a j : Ideal (MvPolynomial σ K)) ≤
      diagonal d (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) := by
    simpa only [eq4_diagonal_decompOmit hd, eq4_diagonal_purePower] using hleD
  have hleJ : (decompOmit A a j : Ideal (MvPolynomial σ K)) ≤ purePower (A j) (a j) :=
    (eq4_diagonal_le_iff_le (K := K)
      (I := (decompOmit A a j : Ideal (MvPolynomial σ K)))
      (J := (purePower (A j) (a j) : Ideal (MvPolynomial σ K))) hd
      (eq4_isMonomialIdeal_decompOmit (K := K) j)
      (eq4_isMonomialIdeal_purePower (K := K) (A j) (a j))).mp hleDiag
  exact hirr j hleJ

/-- Positive weighting takes each radical class component to the corresponding weighted one. -/
theorem diagAssoc_diagonal_groupedComponent [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ} {d : σ → ℕ}
    (hd : ∀ i, 0 < d i) (B : Set.range A) :
    diagonal d (diagAssoc_groupedComponent (K := K) A a B : Ideal (MvPolynomial σ K)) =
      diagAssoc_groupedComponent (K := K) A (fun j i ↦ a j i * d i) B := by
  rw [diagAssoc_groupedComponent, diagAssoc_groupedComponent]
  rw [eq4_diagonal_iInf
    (Q := fun j : {j : ι // A j = B.1} ↦
      (purePower (A j.1) (a j.1) : Ideal (MvPolynomial σ K)))
    (fun j : {j : ι // A j = B.1} ↦
      eq4_isMonomialIdeal_purePower (K := K) (A j.1) (a j.1)) hd]
  apply iInf_congr
  intro j
  exact eq4_diagonal_purePower (K := K) d (A j.1) (a j.1)

/-- Positive weighting preserves the grouped (canonical) primary components exactly. -/
theorem diagAssoc_diagonal_groupedComponents [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ} {d : σ → ℕ}
    (hd : ∀ i, 0 < d i) :
    diagonal d '' diagAssoc_groupedComponents (K := K) A a =
      diagAssoc_groupedComponents (K := K) A (fun j i ↦ a j i * d i) := by
  ext Q
  constructor
  · rintro ⟨G, ⟨B, rfl⟩, rfl⟩
    refine ⟨B, ?_⟩
    exact (diagAssoc_diagonal_groupedComponent (K := K) (A := A) (a := a) (d := d) hd B).symm
  · rintro ⟨B, rfl⟩
    refine ⟨diagAssoc_groupedComponent (K := K) A a B, ⟨B, rfl⟩, ?_⟩
    exact diagAssoc_diagonal_groupedComponent (K := K) (A := A) (a := a) (d := d) hd B

/-- The cited decomposition and associated-prime preservation theorem, without any
antichain assumption, once an irredundant irreducible monomial decomposition is supplied. -/
theorem diagAssoc_preservesCanonical_and_Ass [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} {d : σ → ℕ}
    (hd : ∀ i, 0 < d i) (hI : HasComponents I A a)
    (hirr : IsIrredundant (K := K) A a) :
    diagonal d '' diagAssoc_groupedComponents (K := K) A a =
        diagAssoc_groupedComponents (K := K) A (fun j i ↦ a j i * d i) ∧
      diagAssoc_IsCanonicalPrimarySet I (diagAssoc_groupedComponents (K := K) A a) ∧
      diagAssoc_IsCanonicalPrimarySet (diagonal d I)
        (diagAssoc_groupedComponents (K := K) A (fun j i ↦ a j i * d i)) ∧
      associatedPrimes (MvPolynomial σ K)
          (MvPolynomial σ K ⧸ diagonal d I) =
        associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) := by
  have hI' := diagAssoc_diagonal_hasComponents (K := K) hd hI
  have hirr' := diagAssoc_diagonal_isIrredundant (K := K) hd hirr
  refine ⟨diagAssoc_diagonal_groupedComponents (K := K) (A := A) (a := a) (d := d) hd,
    diagAssoc_groupedComponents_isCanonicalPrimarySet (K := K) hI hirr,
    diagAssoc_groupedComponents_isCanonicalPrimarySet (K := K) hI' hirr', ?_⟩
  calc
    associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ diagonal d I) =
        Set.range (fun j ↦ (primeOf (A j) : Ideal (MvPolynomial σ K))) :=
      diagAssoc_quotientAssociatedPrimes_eq_range (K := K) hI' hirr'
    _ = associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) :=
      (diagAssoc_quotientAssociatedPrimes_eq_range (K := K) hI hirr).symm

/-- In the antichain case the \(q=1\) assertion follows directly from Proposition 2.1. -/
theorem diagAssoc_associatedPrimes_eq_of_supportsAntichain [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} {d : σ → ℕ}
    (hd : ∀ i, 0 < d i) (hI : HasComponents I A a)
    (hirr : IsIrredundant (K := K) A a) (hanti : SupportsAntichain A a) :
    associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ diagonal d I) =
      associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) := by
  have hI' := diagAssoc_diagonal_hasComponents (K := K) hd hI
  have hirr' := diagAssoc_diagonal_isIrredundant (K := K) hd hirr
  have hanti' : SupportsAntichain A (fun j i ↦ a j i * d i) := by
    intro j k hsub
    exact hanti j k hsub
  calc
    associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ diagonal d I) =
        Set.range (fun j ↦ (primeOf (A j) : Ideal (MvPolynomial σ K))) :=
      prop21_associatedPrimes_eq_range_of_supportsAntichain (K := K) hI' hirr' hanti'
    _ = associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) :=
      (prop21_associatedPrimes_eq_range_of_supportsAntichain (K := K) hI hirr hanti).symm

/-- Existence of a finite irredundant irreducible monomial decomposition. -/
def diagAssoc_HasFiniteIrredundantDecomposition (I : Ideal (MvPolynomial σ K)) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (A : κ → Finset σ) (a : κ → σ → ℕ),
    IsIrredundantDecomp I A a

omit [DecidableEq σ] [Fintype σ] in
/-- Bridge between the shared decomposition predicate and the file-local spelling.  The bodies
are identical, but the local definition is retained so all earlier signatures remain valid. -/
theorem diagAssoc_sharedHasFiniteIrredundantDecomp_iff_local
    {I : Ideal (MvPolynomial σ K)} :
    HasFiniteIrredundantDecomp I ↔ diagAssoc_HasFiniteIrredundantDecomposition I := by
  constructor
  · rintro ⟨κ, instκ, A, a, hIA⟩
    exact ⟨κ, instκ, A, a, hIA⟩
  · rintro ⟨κ, instκ, A, a, hIA⟩
    exact ⟨κ, instκ, A, a, hIA⟩

/-- The minimal external `Ass`-preservation input at exponent one.  Its quantifier is over *all*
monomial ideals, so embedded primes are not excluded. -/
def diagAssoc_PreservesAssociatedPrimes (d : σ → ℕ) : Prop :=
  ∀ L : Ideal (MvPolynomial σ K), IsMonomialIdeal L → (∀ i, 0 < d i) →
    associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ diagonal d L) =
      associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ L)

/-- The narrower input actually needed for a fixed ideal and all its positive powers. -/
def diagAssoc_PreservesAssociatedPrimesOfPowers
    (J : Ideal (MvPolynomial σ K)) (d : σ → ℕ) : Prop :=
  ∀ q : ℕ, 1 ≤ q →
    associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ (diagonal d J) ^ q) =
      associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ J ^ q)

/-- Under the paper's existence theorem for nonzero proper monomial ideals, grouping proves
the external input at exponent one for every monomial ideal.  The zero and unit ideals are
handled directly by extension of the zero and unit ideals. -/
theorem diagAssoc_preservesAssociatedPrimes_of_nontrivialFiniteDecompositions
    {d : σ → ℕ}
    (hdecomp : ∀ L : Ideal (MvPolynomial σ K), IsMonomialIdeal L →
      L ≠ ⊥ → L ≠ ⊤ → diagAssoc_HasFiniteIrredundantDecomposition L) :
    diagAssoc_PreservesAssociatedPrimes (K := K) d := by
  intro L hL hd
  by_cases hbot : L = ⊥
  · subst L
    rw [diagonal, Ideal.map_bot]
  by_cases htop : L = ⊤
  · subst L
    rw [diagonal, Ideal.map_top]
  rcases hdecomp L hL hbot htop with ⟨κ, instκ, A, a, hLA⟩
  let instDecomp : Fintype κ := instκ
  exact (diagAssoc_preservesCanonical_and_Ass (K := K) hd hLA.1 hLA.2).2.2.2

/-- The same reduction using the shared predicate `HasFiniteIrredundantDecomp`. -/
theorem diagAssoc_preservesAssociatedPrimes_of_sharedFiniteDecompositions
    {d : σ → ℕ}
    (hdecomp : ∀ L : Ideal (MvPolynomial σ K), IsMonomialIdeal L →
      L ≠ ⊥ → L ≠ ⊤ → HasFiniteIrredundantDecomp L) :
    diagAssoc_PreservesAssociatedPrimes (K := K) d := by
  apply diagAssoc_preservesAssociatedPrimes_of_nontrivialFiniteDecompositions
  intro L hL hbot htop
  exact (diagAssoc_sharedHasFiniteIrredundantDecomp_iff_local (I := L)).mp
    (hdecomp L hL hbot htop)

/-- Convenience form of the previous theorem when decomposition data is supplied even for the
zero and unit ideals. -/
theorem diagAssoc_preservesAssociatedPrimes_of_allFiniteDecompositions {d : σ → ℕ}
    (hdecomp : ∀ L : Ideal (MvPolynomial σ K), IsMonomialIdeal L →
      diagAssoc_HasFiniteIrredundantDecomposition L) :
    diagAssoc_PreservesAssociatedPrimes (K := K) d := by
  apply diagAssoc_preservesAssociatedPrimes_of_nontrivialFiniteDecompositions
  intro L hL hbot htop
  exact hdecomp L hL

omit [DecidableEq σ] [Fintype σ] in
/-- The \(q=1\) preservation input specializes to every ordinary positive power. -/
theorem diagAssoc_preservesAssociatedPrimesOfPowers_of_preservesAssociatedPrimes
    {I : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hI : IsMonomialIdeal I) (hd : ∀ i, 0 < d i)
    (hpres : diagAssoc_PreservesAssociatedPrimes (K := K) d) :
    diagAssoc_PreservesAssociatedPrimesOfPowers I d := by
  intro q hq
  have hpow : (diagonal d I : Ideal (MvPolynomial σ K)) ^ q = diagonal d (I ^ q) := by
    simpa [diagonal] using (Ideal.map_pow (diagHom (K := K) d) I q).symm
  rw [hpow]
  exact hpres (I ^ q) (eq4_isMonomialIdeal_pow (K := K) hI q) hd

/-- When finite irreducible decompositions exist for all monomial ideals, weighting preserves
associated primes of every positive ordinary power, including embedded primes. -/
theorem diagAssoc_preservesAssociatedPrimesOfPowers_of_allFiniteDecompositions
    {I : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hI : IsMonomialIdeal I) (hd : ∀ i, 0 < d i)
    (hdecomp : ∀ L : Ideal (MvPolynomial σ K), IsMonomialIdeal L →
      diagAssoc_HasFiniteIrredundantDecomposition L) :
    diagAssoc_PreservesAssociatedPrimesOfPowers I d :=
  diagAssoc_preservesAssociatedPrimesOfPowers_of_preservesAssociatedPrimes hI hd
    (diagAssoc_preservesAssociatedPrimes_of_allFiniteDecompositions hdecomp)

omit [DecidableEq σ] [Fintype σ] in
/-- Normal torsion freeness transfers under precisely the needed power-`Ass` input. -/
theorem diagAssoc_normallyTorsionFree_iff_of_powerPreservation
    {J : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hpow : diagAssoc_PreservesAssociatedPrimesOfPowers J d) :
    prop21NormallyTorsionFree (diagonal d J) ↔ prop21NormallyTorsionFree J := by
  constructor
  · intro hNT q hq P hPJq
    have hPIq : P ∈ associatedPrimes (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ (diagonal d J) ^ q) := by
      rw [hpow q hq]
      exact hPJq
    have hPI : P ∈ associatedPrimes (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ diagonal d J) := hNT q hq hPIq
    have h1 := hpow 1 (by omega)
    rw [pow_one] at h1
    rw [pow_one] at h1
    rw [h1] at hPI
    exact hPI
  · intro hNT q hq P hPIq
    have hPJq : P ∈ associatedPrimes (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ J ^ q) := by
      rw [← hpow q hq]
      exact hPIq
    have hPJ : P ∈ associatedPrimes (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ J) := hNT q hq hPJq
    have h1 := hpow 1 (by omega)
    rw [pow_one] at h1
    rw [pow_one] at h1
    rw [← h1] at hPJ
    exact hPJ

omit [Fintype σ] in
/-- In particular, the global \(q=1\) hypothesis gives Proposition 2.1's desired transfer
for a squarefree diagonal root. -/
theorem diagAssoc_normallyTorsionFree_iff_of_associatedPreservation
    {J : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hJ : IsSquarefreeMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hpres : diagAssoc_PreservesAssociatedPrimes (K := K) d) :
    prop21NormallyTorsionFree (diagonal d J) ↔ prop21NormallyTorsionFree J :=
  diagAssoc_normallyTorsionFree_iff_of_powerPreservation
    (diagAssoc_preservesAssociatedPrimesOfPowers_of_preservesAssociatedPrimes
      (by rcases hJ with ⟨H, hH⟩; exact ⟨characteristicExp '' H, hH⟩) hd hpres)

/-- The same transfer under the named irreducible-decomposition existence input. -/
theorem diagAssoc_normallyTorsionFree_iff_of_allFiniteDecompositions
    {J : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hJ : IsSquarefreeMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hdecomp : ∀ L : Ideal (MvPolynomial σ K), IsMonomialIdeal L →
      diagAssoc_HasFiniteIrredundantDecomposition L) :
    prop21NormallyTorsionFree (diagonal d J) ↔ prop21NormallyTorsionFree J :=
  diagAssoc_normallyTorsionFree_iff_of_associatedPreservation hJ hd
    (diagAssoc_preservesAssociatedPrimes_of_allFiniteDecompositions hdecomp)

/-- Unconditional preservation of associated primes at exponent one for monomial ideals,
using the shared finite-decomposition existence theorem. -/
theorem diagAssoc_associatedPrimes_diagonal_eq_of_monomial
    {L : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hL : IsMonomialIdeal L) (hd : ∀ i, 0 < d i) :
    associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ diagonal d L) =
      associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ L) := by
  have hglobal : diagAssoc_PreservesAssociatedPrimes (K := K) d := by
    apply diagAssoc_preservesAssociatedPrimes_of_sharedFiniteDecompositions
    intro M hM hbot htop
    exact hasFiniteIrredundantDecomp_of_isMonomialIdeal (K := K) hM
  exact hglobal L hL hd

/-- Unconditional preservation of associated primes for every positive ordinary power. -/
theorem diagAssoc_associatedPrimes_pow_diagonal_eq_of_monomial
    {J : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hJ : IsMonomialIdeal J) (hd : ∀ i, 0 < d i) (q : ℕ) (hq : 1 ≤ q) :
    associatedPrimes (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ (diagonal d J) ^ q) =
      associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ J ^ q) := by
  have hglobal : diagAssoc_PreservesAssociatedPrimes (K := K) d := by
    intro L hL hd'
    exact diagAssoc_associatedPrimes_diagonal_eq_of_monomial (K := K) hL hd'
  exact diagAssoc_preservesAssociatedPrimesOfPowers_of_preservesAssociatedPrimes
    hJ hd hglobal q hq

/-- Unconditional diagonal invariance of the paper's normally-torsion-free property. -/
theorem diagAssoc_normallyTorsionFree_diagonal_iff_of_monomial
    {J : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hJ : IsMonomialIdeal J) (hd : ∀ i, 0 < d i) :
    prop21NormallyTorsionFree (diagonal d J) ↔ prop21NormallyTorsionFree J := by
  apply diagAssoc_normallyTorsionFree_iff_of_powerPreservation
  intro q hq
  exact diagAssoc_associatedPrimes_pow_diagonal_eq_of_monomial (K := K) hJ hd q hq

end
end SimisFormal
