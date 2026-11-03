/-
Equation (2) for a finite irredundant irreducible monomial decomposition in the general
case. Components with the same radical are grouped by intersecting them, and only the
groups indexed by minimal primes are retained. This permits repeated radicals and nested
(embedded) radicals in the original irreducible decomposition.

The proof retains the intrinsic localization definition of `symbolicPower`. The grouped
components are indexed directly by `I.minimalPrimes`, so no quotient of the indexing type
or reindexing equivalence is needed.
-/
import SimisFormal.Defs
import SimisFormal.Basic
import SimisFormal.Eq2_StandardSymbolic

namespace SimisFormal
open MvPolynomial
open scoped BigOperators
variable {σ K ι : Type*} [Field K] [DecidableEq σ]
/-- A lexicographically minimal exponent is forced to equal any pointwise smaller one. -/
private lemma lex_eq_of_pointwise_le {α : Type*} [LinearOrder α] {e₀ e : α →₀ ℕ}
    (hmin : (toLex e₀ : Lex (α →₀ ℕ)) ≤ toLex e) (hpt : e ≤ e₀) : e = e₀ := by
  by_contra hne
  have hex : ∃ i, e i < e₀ i := by
    by_contra h
    apply hne
    ext i
    exact le_antisymm (hpt i) (not_lt.mp (fun hi ↦ h ⟨i, hi⟩))
  exact (not_lt_of_ge hmin) (finsupp_lex_lt_of_le_of_exists_lt hpt hex)

/-- Lexicographically extremal factors of a fixed sum are unique. -/
private lemma lex_factor_unique {α : Type*} [LinearOrder α] {a₀ a b₀ b : α →₀ ℕ}
    (ha : (toLex a₀ : Lex (α →₀ ℕ)) ≤ toLex a)
    (hb : (toLex b₀ : Lex (α →₀ ℕ)) ≤ toLex b)
    (heq : a + b = a₀ + b₀) : a = a₀ ∧ b = b₀ := by
  constructor
  · rcases lt_or_eq_of_le ha with hlt | hEq
    · have hsum : (toLex (a₀ + b₀) : Lex (α →₀ ℕ)) < toLex (a + b) := by
        simpa [add_comm] using add_lt_add_of_lt_of_le hlt hb
      exact False.elim ((ne_of_lt hsum) heq.symm)
    · change a₀ = a at hEq
      exact hEq.symm
  · rcases lt_or_eq_of_le hb with hlt | hEq
    · have hsum : (toLex (a₀ + b₀) : Lex (α →₀ ℕ)) < toLex (a + b) := by
        simpa [add_comm] using add_lt_add_of_le_of_lt ha hlt
      exact False.elim ((ne_of_lt hsum) heq.symm)
    · change b₀ = b at hEq
      exact hEq.symm

/-- If a product lies in a monomial ideal whose generators are supported in `A`,
while the left factor does not, then the right factor lies in `primeOf A`.

Only variables occurring in `x`, `y`, or `A` are used in the lexicographic choices, so
the ambient variable type needs no global linear order. -/
private theorem mem_primeOf_of_mul_mem_monomialIdeal_of_generators_support
    {A : Finset σ} {S : Set (σ →₀ ℕ)}
    (hS : ∀ u ∈ S, u.support ⊆ A) {x y : MvPolynomial σ K}
    (hxy : x * y ∈ (monomialIdeal S : Ideal (MvPolynomial σ K)))
    (hx : x ∉ (monomialIdeal S : Ideal (MvPolynomial σ K))) :
    y ∈ (primeOf A : Ideal (MvPolynomial σ K)) := by
  classical
  have hxBadExists : ∃ e ∈ x.support, ∀ u ∈ S, ¬ u ≤ e := by
    by_contra h
    apply hx
    rw [mem_monomialIdeal]
    intro e he
    by_contra hgood
    exact h ⟨e, he, fun u hu hule ↦ hgood ⟨u, hu, hule⟩⟩
  by_contra hy
  have hyAvoidExists : ∃ t ∈ y.support, ∀ i ∈ A, t i = 0 := by
    by_contra h
    apply hy
    rw [mem_primeOf]
    intro t ht
    by_contra htp
    apply h
    refine ⟨t, ht, ?_⟩
    intro i hi
    by_contra hti
    exact htp ⟨i, hi, Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hti)⟩
  let U : Finset σ := A ∪ (x.support.biUnion fun e ↦ e.support) ∪
    (y.support.biUnion fun e ↦ e.support)
  have hxU : ∀ {e : σ →₀ ℕ}, e ∈ x.support → e.support ⊆ U := by
    intro e he i hi
    simp only [U, Finset.mem_union]
    exact Or.inl (Or.inr (Finset.mem_biUnion.mpr ⟨e, he, hi⟩))
  have hyU : ∀ {e : σ →₀ ℕ}, e ∈ y.support → e.support ⊆ U := by
    intro e he i hi
    simp only [U, Finset.mem_union]
    exact Or.inr (Finset.mem_biUnion.mpr ⟨e, he, hi⟩)
  let τA := {i : σ // i ∈ U.filter (fun i ↦ i ∈ A)}
  let τC := {i : σ // i ∈ U.filter (fun i ↦ i ∉ A)}
  let fA : Fintype τA := inferInstance
  let fC : Fintype τC := inferInstance
  let oA : LinearOrder τA :=
    LinearOrder.lift' (Fintype.equivFin τA) (Fintype.equivFin τA).injective
  let oC : LinearOrder τC :=
    LinearOrder.lift' (Fintype.equivFin τC) (Fintype.equivFin τC).injective
  let ins : (σ →₀ ℕ) → (τA →₀ ℕ) :=
    fun e ↦ e.subtypeDomain (fun i ↦ i ∈ U.filter (fun j ↦ j ∈ A))
  let out : (σ →₀ ℕ) → (τC →₀ ℕ) :=
    fun e ↦ e.subtypeDomain (fun i ↦ i ∈ U.filter (fun j ↦ j ∉ A))
  have ins_apply (f : σ →₀ ℕ) {i : σ} (hi : i ∈ U.filter (fun j ↦ j ∈ A)) :
      ins f ⟨i, hi⟩ = f i := by
    change f.subtypeDomain (fun j : σ ↦ j ∈ U.filter (fun k ↦ k ∈ A)) ⟨i, hi⟩ = f i
    rw [Finsupp.subtypeDomain_apply]
  have out_apply (f : σ →₀ ℕ) {i : σ} (hi : i ∈ U.filter (fun j ↦ j ∉ A)) :
      out f ⟨i, hi⟩ = f i := by
    change f.subtypeDomain (fun j : σ ↦ j ∈ U.filter (fun k ↦ k ∉ A)) ⟨i, hi⟩ = f i
    rw [Finsupp.subtypeDomain_apply]
  let Bad : Finset (σ →₀ ℕ) :=
    x.support.filter (fun e ↦ ∀ u ∈ S, ¬ u ≤ e)
  rcases hxBadExists with ⟨ew, hewSupp, hewBad⟩
  have hewBadMem : ew ∈ Bad := Finset.mem_filter.mpr ⟨hewSupp, hewBad⟩
  obtain ⟨e₁, he₁Bad, he₁min⟩ :=
    Finset.exists_min_image Bad (fun e ↦ (toLex (ins e) : Lex (τA →₀ ℕ))) ⟨ew, hewBadMem⟩
  let Same : Finset (σ →₀ ℕ) := Bad.filter (fun e ↦ ins e = ins e₁)
  have he₁Same : e₁ ∈ Same := Finset.mem_filter.mpr ⟨he₁Bad, rfl⟩
  obtain ⟨e₀, he₀Same, he₀max⟩ :=
    Finset.exists_max_image Same (fun e ↦ (toLex (out e) : Lex (τC →₀ ℕ))) ⟨e₁, he₁Same⟩
  rcases hyAvoidExists with ⟨tw, htwSupp, htwAvoid⟩
  let Avoid : Finset (σ →₀ ℕ) :=
    y.support.filter (fun t ↦ ∀ i ∈ A, t i = 0)
  have htwAvoidMem : tw ∈ Avoid := Finset.mem_filter.mpr ⟨htwSupp, htwAvoid⟩
  obtain ⟨t₀, ht₀Avoid, ht₀max⟩ :=
    Finset.exists_max_image Avoid (fun t ↦ (toLex (out t) : Lex (τC →₀ ℕ))) ⟨tw, htwAvoidMem⟩
  have he₀Bad : e₀ ∈ Bad := (Finset.mem_filter.mp he₀Same).1
  have he₀SameIns : ins e₀ = ins e₁ := (Finset.mem_filter.mp he₀Same).2
  have he₀Supp : e₀ ∈ x.support := (Finset.mem_filter.mp he₀Bad).1
  have he₀BadProp : ∀ u ∈ S, ¬ u ≤ e₀ := (Finset.mem_filter.mp he₀Bad).2
  have ht₀Supp : t₀ ∈ y.support := (Finset.mem_filter.mp ht₀Avoid).1
  have ht₀AvoidProp : ∀ i ∈ A, t₀ i = 0 := (Finset.mem_filter.mp ht₀Avoid).2
  have unique_factor : ∀ {e t : σ →₀ ℕ}, e ∈ x.support → t ∈ y.support →
      e + t = e₀ + t₀ → e = e₀ ∧ t = t₀ := by
    intro e t heSupp htSupp heqsum
    have heBadProp : ∀ u ∈ S, ¬ u ≤ e := by
      intro u huS hule
      have huSupport : u.support ⊆ A := hS u huS
      have hule₀ : u ≤ e₀ := by
        intro i
        by_cases hiA : i ∈ A
        · by_cases hiU : i ∈ U
          · have ht₀zero : t₀ i = 0 := ht₀AvoidProp i hiA
            have hc : e i + t i = e₀ i + t₀ i := by
              simpa only [Finsupp.add_apply] using
                congrArg (fun v : σ →₀ ℕ ↦ v i) heqsum
            have hei : e i ≤ e₀ i := by omega
            exact (hule i).trans hei
          · have hezero : e i = 0 := by
              by_contra hne
              exact hiU (hxU heSupp (by simpa [Finsupp.mem_support_iff] using hne))
            have := hule i
            omega
        · have hui : u i = 0 := by
            by_contra hne
            exact hiA (huSupport (by simpa [Finsupp.mem_support_iff] using hne))
          omega
      exact he₀BadProp u huS hule₀
    have heBad : e ∈ Bad := Finset.mem_filter.mpr ⟨heSupp, heBadProp⟩
    have hins_min : (toLex (ins e₀) : Lex (τA →₀ ℕ)) ≤ toLex (ins e) := by
      simpa [he₀SameIns] using he₁min e heBad
    have hins_le_point : ins e ≤ ins e₀ := by
      intro k
      have hk := Finset.mem_filter.mp k.2
      have ht₀zero : t₀ k.1 = 0 := ht₀AvoidProp k.1 hk.2
      have hc : e k.1 + t k.1 = e₀ k.1 + t₀ k.1 := by
        simpa only [Finsupp.add_apply] using
          congrArg (fun v : σ →₀ ℕ ↦ v k.1) heqsum
      rw [ins_apply e k.2, ins_apply e₀ k.2]
      omega
    have hins_eq : ins e = ins e₀ :=
      lex_eq_of_pointwise_le hins_min hins_le_point
    have htAvoidProp : ∀ i ∈ A, t i = 0 := by
      intro i hiA
      by_cases hiU : i ∈ U
      · have hiFil : i ∈ U.filter (fun j ↦ j ∈ A) := Finset.mem_filter.mpr ⟨hiU, hiA⟩
        have hinside := congrArg (fun v : τA →₀ ℕ ↦ v ⟨i, hiFil⟩) hins_eq
        rw [ins_apply, ins_apply] at hinside
        have ht₀zero : t₀ i = 0 := ht₀AvoidProp i hiA
        have hc : e i + t i = e₀ i + t₀ i := by
          simpa only [Finsupp.add_apply] using
            congrArg (fun v : σ →₀ ℕ ↦ v i) heqsum
        omega
      · by_contra hti
        exact hiU (hyU htSupp (by simpa [Finsupp.mem_support_iff] using hti))
    have htAvoid : t ∈ Avoid := Finset.mem_filter.mpr ⟨htSupp, htAvoidProp⟩
    have heSame : e ∈ Same :=
      Finset.mem_filter.mpr ⟨heBad, hins_eq.trans he₀SameIns⟩
    have houtE : (toLex (out e) : Lex (τC →₀ ℕ)) ≤ toLex (out e₀) := he₀max e heSame
    have houtT : (toLex (out t) : Lex (τC →₀ ℕ)) ≤ toLex (out t₀) := ht₀max t htAvoid
    have houtsum : out e + out t = out e₀ + out t₀ := by
      ext k
      have hc : e k.1 + t k.1 = e₀ k.1 + t₀ k.1 := by
        simpa only [Finsupp.add_apply] using
          congrArg (fun v : σ →₀ ℕ ↦ v k.1) heqsum
      simp only [Finsupp.add_apply]
      rw [out_apply e k.2, out_apply t k.2, out_apply e₀ k.2, out_apply t₀ k.2]
      exact hc
    rcases lex_factor_unique houtE houtT houtsum.symm with ⟨houtEeq, houtTeq⟩
    have heEq : e = e₀ := by
      ext i
      by_cases hiU : i ∈ U
      · by_cases hiA : i ∈ A
        · have hiFil : i ∈ U.filter (fun j ↦ j ∈ A) := Finset.mem_filter.mpr ⟨hiU, hiA⟩
          have h := congrArg (fun v : τA →₀ ℕ ↦ v ⟨i, hiFil⟩) hins_eq
          rw [ins_apply, ins_apply] at h
          exact h
        · have hiFil : i ∈ U.filter (fun j ↦ j ∉ A) := Finset.mem_filter.mpr ⟨hiU, hiA⟩
          have h := congrArg (fun v : τC →₀ ℕ ↦ v ⟨i, hiFil⟩) houtEeq
          rw [out_apply, out_apply] at h
          exact h.symm
      · have hezero : e i = 0 := by
          by_contra hne
          exact hiU (hxU heSupp (by simpa [Finsupp.mem_support_iff] using hne))
        have he₀zero : e₀ i = 0 := by
          by_contra hne
          exact hiU (hxU he₀Supp (by simpa [Finsupp.mem_support_iff] using hne))
        rw [hezero, he₀zero]
    have htEq : t = t₀ := by
      ext i
      by_cases hiU : i ∈ U
      · by_cases hiA : i ∈ A
        · rw [htAvoidProp i hiA, ht₀AvoidProp i hiA]
        · have hiFil : i ∈ U.filter (fun j ↦ j ∉ A) := Finset.mem_filter.mpr ⟨hiU, hiA⟩
          have h := congrArg (fun v : τC →₀ ℕ ↦ v ⟨i, hiFil⟩) houtTeq
          rw [out_apply, out_apply] at h
          exact h.symm
      · have htzero : t i = 0 := by
          by_contra hne
          exact hiU (hyU htSupp (by simpa [Finsupp.mem_support_iff] using hne))
        have ht₀zero : t₀ i = 0 := by
          by_contra hne
          exact hiU (hyU ht₀Supp (by simpa [Finsupp.mem_support_iff] using hne))
        rw [htzero, ht₀zero]
    exact ⟨heEq, htEq⟩
  let z : σ →₀ ℕ := e₀ + t₀
  have hxe₀ : coeff e₀ x ≠ (0 : K) := by
    simpa [MvPolynomial.mem_support_iff] using he₀Supp
  have hyt₀ : coeff t₀ y ≠ (0 : K) := by
    simpa [MvPolynomial.mem_support_iff] using ht₀Supp
  have hcoeff : coeff z (x * y) = coeff e₀ x * coeff t₀ y := by
    rw [MvPolynomial.coeff_mul]
    refine Finset.sum_eq_single (e₀, t₀) ?_ ?_
    · intro p hp hpne
      have hpadd : p.1 + p.2 = z := by simpa using hp
      by_cases hxp : coeff p.1 x = (0 : K)
      · simp [hxp]
      by_cases hyp : coeff p.2 y = (0 : K)
      · simp [hyp]
      have hpx : p.1 ∈ x.support := by
        simpa [MvPolynomial.mem_support_iff] using hxp
      have hpy : p.2 ∈ y.support := by
        simpa [MvPolynomial.mem_support_iff] using hyp
      rcases unique_factor hpx hpy (by simpa [z] using hpadd) with ⟨heq, hteq⟩
      exact False.elim (hpne (Prod.ext heq hteq))
    · intro hpnot
      exact False.elim (hpnot (by simp [z]))
  have hzsupport : z ∈ (x * y).support := by
    rw [MvPolynomial.mem_support_iff, hcoeff]
    exact mul_ne_zero hxe₀ hyt₀
  rw [mem_monomialIdeal] at hxy
  rcases hxy z hzsupport with ⟨u, huS, huz⟩
  have huSupport : u.support ⊆ A := hS u huS
  have hue₀ : u ≤ e₀ := by
    intro i
    by_cases hiA : i ∈ A
    · by_cases hiU : i ∈ U
      · have ht₀zero : t₀ i = 0 := ht₀AvoidProp i hiA
        simpa [z, ht₀zero] using huz i
      · have he₀zero : e₀ i = 0 := by
          by_contra hne
          exact hiU (hxU he₀Supp (by simpa [Finsupp.mem_support_iff] using hne))
        have ht₀zero : t₀ i = 0 := ht₀AvoidProp i hiA
        simpa [z, he₀zero, ht₀zero] using huz i
    · have hui : u i = 0 := by
        by_contra hne
        exact hiA (huSupport (by simpa [Finsupp.mem_support_iff] using hne))
      omega
  exact he₀BadProp u huS hue₀

/-- A monomial ideal generated inside `A` is saturated with respect to the complement
of the variable prime `primeOf A`. -/
private theorem comap_map_monomialIdeal_eq_of_generators_support
    {A : Finset σ} {S : Set (σ →₀ ℕ)}
    (hS : ∀ u ∈ S, u.support ⊆ A) {P : Ideal (MvPolynomial σ K)}
    [P.IsPrime] (hP : P = (primeOf A : Ideal (MvPolynomial σ K))) :
    Ideal.comap (algebraMap (MvPolynomial σ K) (Localization.AtPrime P))
      (Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P))
        (monomialIdeal S : Ideal (MvPolynomial σ K))) =
          (monomialIdeal S : Ideal (MvPolynomial σ K)) := by
  apply le_antisymm
  · intro x hx
    change algebraMap (MvPolynomial σ K) (Localization.AtPrime P) x ∈
      Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P))
        (monomialIdeal S : Ideal (MvPolynomial σ K)) at hx
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
      (M := P.primeCompl) (S := Localization.AtPrime P)] at hx
    rcases hx with ⟨s, hsM, hsx⟩
    by_contra hxS
    have hsx' : x * s ∈ (monomialIdeal S : Ideal (MvPolynomial σ K)) := by
      simpa [mul_comm] using hsx
    have hsPrime : s ∈ (primeOf A : Ideal (MvPolynomial σ K)) :=
      mem_primeOf_of_mul_mem_monomialIdeal_of_generators_support hS hsx' hxS
    exact (Ideal.mem_primeCompl_iff.mp hsM) (by simpa [hP] using hsPrime)
  · exact Ideal.le_comap_map

omit [DecidableEq σ] in
/-- An ideal that is already recovered by extension and contraction at a prime is
primary, provided its radical is that prime. -/
private theorem isPrimary_of_comap_map_eq_self_atPrime
    {Q P : Ideal (MvPolynomial σ K)} [P.IsPrime]
    (hcontr : Ideal.comap (algebraMap (MvPolynomial σ K) (Localization.AtPrime P))
      (Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P)) Q) = Q)
    (hrad : Q.radical = P) : Q.IsPrimary := by
  rw [Ideal.isPrimary_iff]
  constructor
  · intro htop
    have hPtop : P = ⊤ := by
      calc
        P = Q.radical := hrad.symm
        _ = (⊤ : Ideal (MvPolynomial σ K)).radical := by rw [htop]
        _ = ⊤ := by simp [Ideal.radical_top]
    exact (inferInstance : P.IsPrime).ne_top hPtop
  · intro x y hxy
    by_cases hx : x ∈ Q
    · exact Or.inl hx
    · right
      rw [hrad]
      by_contra hyP
      have hyM : y ∈ P.primeCompl := Ideal.mem_primeCompl_iff.mpr hyP
      apply hx
      have hmap : algebraMap (MvPolynomial σ K) (Localization.AtPrime P) x ∈
          Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P)) Q := by
        rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
          (M := P.primeCompl) (S := Localization.AtPrime P)]
        exact ⟨y, hyM, by simpa [mul_comm] using hxy⟩
      have hx' : x ∈ Ideal.comap (algebraMap (MvPolynomial σ K) (Localization.AtPrime P))
          (Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P)) Q) := hmap
      simpa [hcontr] using hx'

/-- A pure-power component with positive exponents on its support is primary. -/
theorem purePower_isPrimary {A : Finset σ} {a : σ → ℕ}
    (hpos : ∀ i ∈ A, 0 < a i) :
    (purePower A a : Ideal (MvPolynomial σ K)).IsPrimary := by
  let P : Ideal (MvPolynomial σ K) := primeOf A
  let : P.IsPrime := by
    dsimp [P]
    exact primeOf_isPrime (K := K) A
  apply isPrimary_of_comap_map_eq_self_atPrime (P := P)
  · simpa [P, pow_one] using
      (comap_map_pow_purePower_eq_self (K := K) (A := A) (a := a) 1 (P := P) (by rfl))
  · dsimp [P]
    exact purePower_radical_eq_primeOf (K := K) hpos

/-- Every minimal prime of a finite intersection of positive pure powers is one of its
variable radicals. Unlike the antichain result, embedded and repeated radicals are allowed. -/
theorem minimalPrime_eq_primeOf [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    {P : Ideal (MvPolynomial σ K)}
    (hcomp : HasComponents I A a) (hpos : ∀ j i, i ∈ A j → 0 < a j i)
    (hP : I.IsMinimalPrime P) :
    ∃ j, P = (primeOf (A j) : Ideal (MvPolynomial σ K)) := by
  classical
  have hrad : I.radical = ⨅ k, (primeOf (A k) : Ideal (MvPolynomial σ K)) := by
    rw [hcomp]
    exact radical_iInf_purePower_of_pos (K := K) hpos
  have hradP : I.radical ≤ P := hP.isPrime.radical_le_iff.mpr hP.le
  have hInfP : (⨅ k, (primeOf (A k) : Ideal (MvPolynomial σ K))) ≤ P := by
    simpa [hrad] using hradP
  have hFinfP :
      (Finset.univ.inf (fun k ↦ (primeOf (A k) : Ideal (MvPolynomial σ K)))) ≤ P := by
    simpa [Finset.inf_univ_eq_iInf] using hInfP
  rcases (hP.isPrime.inf_le').mp hFinfP with ⟨j, _hj, hjP⟩
  refine ⟨j, le_antisymm ?_ hjP⟩
  have hIle : I ≤ (primeOf (A j) : Ideal (MvPolynomial σ K)) := by
    rw [hcomp]
    exact (iInf_le (fun k ↦ (purePower (A k) (a k) : Ideal (MvPolynomial σ K))) j).trans
      (purePower_le_primeOf_of_pos (K := K) (fun i hi ↦ hpos j i hi))
  exact hP.2 ⟨primeOf_isPrime (K := K) (A j), hIle⟩ hjP

/-- Each grouped component is an intersection of monomial ideals, hence monomial. -/
theorem groupedComponents_isMonomialIdeal [Fintype ι]
    (I : Ideal (MvPolynomial σ K)) (A : ι → Finset σ) (a : ι → σ → ℕ)
    (P : I.minimalPrimes) :
    IsMonomialIdeal (groupedComponents I A a P) := by
  classical
  let J := {j : ι // primeOf (A j) = P.1}
  let gens : J → Set (σ →₀ ℕ) := fun j ↦
    {e | ∃ i ∈ A j.1, e = Finsupp.single i (a j.1 i)}
  refine ⟨iInfGens gens, ?_⟩
  simpa [groupedComponents, J, gens, purePower] using
    (monomialIdeal_iInf (K := K) gens)

/-- Each minimal-radical group has radical the indexing minimal prime. -/
theorem groupedComponents_radical [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hcomp : HasComponents I A a) (hpos : ∀ j i, i ∈ A j → 0 < a j i)
    (P : I.minimalPrimes) :
    (groupedComponents I A a P).radical = P.1 := by
  classical
  obtain ⟨j₀, hj₀⟩ := minimalPrime_eq_primeOf hcomp hpos P.2
  let jP : {j : ι // primeOf (A j) = P.1} := ⟨j₀, hj₀.symm⟩
  rw [groupedComponents]
  calc
    (⨅ j : {j : ι // primeOf (A j) = P.1},
        (purePower (A j.1) (a j.1) : Ideal (MvPolynomial σ K))).radical =
        ⨅ j : {j : ι // primeOf (A j) = P.1},
          (purePower (A j.1) (a j.1) : Ideal (MvPolynomial σ K)).radical :=
      radical_iInf_fintype _
    _ = ⨅ _j : {j : ι // primeOf (A j) = P.1}, P.1 := by
      apply iInf_congr
      intro j
      calc
        (purePower (A j.1) (a j.1) : Ideal (MvPolynomial σ K)).radical =
            primeOf (A j.1) :=
          purePower_radical_eq_primeOf (K := K) (fun i hi ↦ hpos j.1 i hi)
        _ = P.1 := j.2
    _ = P.1 := by
      apply le_antisymm
      · exact iInf_le _ jP
      · exact le_iInf fun _ ↦ le_rfl

/-- Each minimal-radical group is a primary component. -/
theorem groupedComponents_isPrimary [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hcomp : HasComponents I A a) (hpos : ∀ j i, i ∈ A j → 0 < a j i)
    (P : I.minimalPrimes) :
    (groupedComponents I A a P).IsPrimary := by
  classical
  obtain ⟨j₀, hj₀⟩ := minimalPrime_eq_primeOf hcomp hpos P.2
  let jP : {j : ι // primeOf (A j) = P.1} := ⟨j₀, hj₀.symm⟩
  rw [groupedComponents, ← Finset.inf_univ_eq_iInf]
  apply Ideal.isPrimary_finsetInf (i := jP) (by simp)
  · intro j _hj
    exact purePower_isPrimary (K := K) (fun i hi ↦ hpos j.1 i hi)
  · intro j _hj
    calc
      (purePower (A j.1) (a j.1) : Ideal (MvPolynomial σ K)).radical =
          primeOf (A j.1) :=
        purePower_radical_eq_primeOf (K := K) (fun i hi ↦ hpos j.1 i hi)
      _ = P.1 := j.2
      _ = primeOf (A j₀) := hj₀
      _ = (purePower (A jP.1) (a jP.1) : Ideal (MvPolynomial σ K)).radical :=
        (purePower_radical_eq_primeOf (K := K) (fun i hi ↦ hpos jP.1 i hi)).symm

/-- At a minimal prime, localization maps the original intersection to exactly the
group of components whose radical is that prime. All other components map to top. -/
theorem map_iInf_purePower_eq_groupedComponent [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hcomp : HasComponents I A a) (hpos : ∀ j i, i ∈ A j → 0 < a j i)
    (P : I.minimalPrimes) [P.1.IsPrime] (j₀ : ι)
    (hP : P.1 = (primeOf (A j₀) : Ideal (MvPolynomial σ K))) :
    Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1)) I =
      Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1))
        (groupedComponents I A a P) := by
  classical
  let J := {k : ι // primeOf (A k) = P.1}
  let allQ : ι → Ideal (MvPolynomial σ K) := fun k ↦ purePower (A k) (a k)
  let grpQ : J → Ideal (MvPolynomial σ K) := fun j ↦ purePower (A j.1) (a j.1)
  have hmapFinset (s : Finset ι) (B : ι → Ideal (MvPolynomial σ K)) :
      Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1)) (s.inf B) =
        s.inf (fun k ↦ Ideal.map
          (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1)) (B k)) := by
    induction s using Finset.induction with
    | empty =>
        simp [Ideal.map_top]
    | insert k s hks ih =>
        rw [Finset.inf_insert, Finset.inf_insert,
          IsLocalization.map_inf P.1.primeCompl (Localization.AtPrime P.1), ih]
  have hmapFinsetGroup (s : Finset J) (B : J → Ideal (MvPolynomial σ K)) :
      Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1)) (s.inf B) =
        s.inf (fun j ↦ Ideal.map
          (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1)) (B j)) := by
    induction s using Finset.induction with
    | empty =>
        simp [Ideal.map_top]
    | insert j s hjs ih =>
        rw [Finset.inf_insert, Finset.inf_insert,
          IsLocalization.map_inf P.1.primeCompl (Localization.AtPrime P.1), ih]
  have hmapTop : ∀ k, primeOf (A k) ≠ P.1 →
      Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1)) (allQ k) = ⊤ := by
    intro k hk
    have hnotSub : ¬ A k ⊆ A j₀ := by
      intro hsub
      have hk_le_P : (primeOf (A k) : Ideal (MvPolynomial σ K)) ≤ P.1 := by
        calc
          (primeOf (A k) : Ideal (MvPolynomial σ K)) ≤ primeOf (A j₀) :=
            (primeOf_le_iff_subset (K := K) (A := A k) (B := A j₀)).mpr hsub
          _ = P.1 := hP.symm
      have hIlePk : I ≤ (primeOf (A k) : Ideal (MvPolynomial σ K)) := by
        calc
          I = (⨅ l, (purePower (A l) (a l) : Ideal (MvPolynomial σ K))) := hcomp
          _ ≤ purePower (A k) (a k) := iInf_le _ k
          _ ≤ primeOf (A k) :=
            purePower_le_primeOf_of_pos (K := K) (fun i hi ↦ hpos k i hi)
      have hP_le_pk : P.1 ≤ (primeOf (A k) : Ideal (MvPolynomial σ K)) :=
        P.2.2 ⟨primeOf_isPrime (K := K) (A k), hIlePk⟩ hk_le_P
      exact hk (le_antisymm hk_le_P hP_le_pk)
    rw [Finset.not_subset] at hnotSub
    rcases hnotSub with ⟨i, hik, hij⟩
    let g : MvPolynomial σ K := monomial (Finsupp.single i (a k i)) (1 : K)
    have hgQ : g ∈ allQ k := by
      dsimp [allQ]
      exact monomial_mem_purePower.mpr ⟨i, hik, by simp⟩
    have hgPrime : g ∉ (primeOf (A j₀) : Ideal (MvPolynomial σ K)) := by
      rw [monomial_mem_primeOf]
      rintro ⟨l, hlj, hle⟩
      by_cases hli : l = i
      · subst l
        exact hij hlj
      · have hz : (Finsupp.single i (a k i) : σ →₀ ℕ) l = 0 := by
          simp [hli]
        omega
    have hgP : g ∉ P.1 := by simpa [hP] using hgPrime
    have hgM : g ∈ P.1.primeCompl := Ideal.mem_primeCompl_iff.mpr hgP
    apply Ideal.eq_top_of_isUnit_mem
    · exact Ideal.mem_map_of_mem
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1)) hgQ
    · exact IsLocalization.map_units (Localization.AtPrime P.1) ⟨g, hgM⟩
  calc
    Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1)) I =
        Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1))
          (⨅ k, (purePower (A k) (a k) : Ideal (MvPolynomial σ K))) := by
      exact congrArg (fun J : Ideal (MvPolynomial σ K) ↦
        Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1)) J) hcomp
    _ = Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1))
        (groupedComponents I A a P) := by
      change Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1))
          (⨅ k, allQ k) =
        Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1)) (⨅ j : J, grpQ j)
      rw [← Finset.inf_univ_eq_iInf, ← Finset.inf_univ_eq_iInf]
      rw [hmapFinset (Finset.univ : Finset ι) allQ,
          hmapFinsetGroup (Finset.univ : Finset J) grpQ]
      apply le_antisymm
      · refine Finset.le_inf ?_
        intro j _hj
        exact Finset.inf_le (s := Finset.univ)
          (f := fun k ↦ Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1))
            (allQ k)) (b := j.1) (by simp)
      · refine Finset.le_inf ?_
        intro k _hk
        by_cases hk : primeOf (A k) = P.1
        · exact Finset.inf_le (s := Finset.univ)
            (f := fun j : J ↦ Ideal.map (algebraMap (MvPolynomial σ K)
              (Localization.AtPrime P.1)) (grpQ j))
            (b := (⟨k, hk⟩ : J)) (by simp)
        · rw [hmapTop k hk]
          exact le_top

/-- Powers of a grouped component are recovered by extension and contraction at its
radical. The grouped component is represented explicitly as a monomial ideal whose
generators are supported on one representative variable set. -/
theorem comap_map_pow_groupedComponent_eq_self [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (P : I.minimalPrimes) [P.1.IsPrime] (j₀ : ι)
    (hP : P.1 = (primeOf (A j₀) : Ideal (MvPolynomial σ K))) (q : ℕ) :
    Ideal.comap (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1))
      (Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1))
        ((groupedComponents I A a P) ^ q)) = (groupedComponents I A a P) ^ q := by
  classical
  let J := {j : ι // primeOf (A j) = P.1}
  let gens : J → Set (σ →₀ ℕ) := fun j ↦
    {e | ∃ i ∈ A j.1, e = Finsupp.single i (a j.1 i)}
  have hAeq (j : J) : A j.1 = A j₀ := by
    apply le_antisymm
    · have heq : primeOf (A j.1) = (primeOf (A j₀) : Ideal (MvPolynomial σ K)) :=
        j.2.trans hP
      exact (primeOf_le_iff_subset (K := K) (A := A j.1) (B := A j₀)).mp (le_of_eq heq)
    · have heq : primeOf (A j₀) = (primeOf (A j.1) : Ideal (MvPolynomial σ K)) :=
        hP.symm.trans j.2.symm
      exact (primeOf_le_iff_subset (K := K) (A := A j₀) (B := A j.1)).mp (le_of_eq heq)
  have hgrouped :
      groupedComponents I A a P = monomialIdeal (iInfGens gens) := by
    simpa [groupedComponents, J, gens, purePower] using
      (monomialIdeal_iInf (K := K) gens)
  have hgens_base : ∀ j (u : σ →₀ ℕ), u ∈ gens j → u.support ⊆ A j₀ := by
    intro j u hu i hi
    rcases hu with ⟨t, htA, rfl⟩
    have hti : t ∈ A j₀ := by simpa [hAeq j] using htA
    by_cases hit : i = t
    · subst i
      exact hti
    · have hval : (Finsupp.single t (a j.1 t) : σ →₀ ℕ) i ≠ 0 := by
        simpa [Finsupp.mem_support_iff] using hi
      exact False.elim (hval (by simp [hit]))
  have hgens : ∀ u ∈ iInfGens gens, u.support ⊆ A j₀ := by
    intro u hu i hi
    rcases hu with ⟨c, hcMem, rfl⟩
    have hex : ∃ j : J, i ∈ (c j).support := by
      by_contra hno
      have hzero : ∀ j : J, c j i = 0 := by
        intro j
        by_contra hzi
        apply hno
        exact ⟨j, by simpa [Finsupp.mem_support_iff] using hzi⟩
      have heval (s : Finset J) : (s.sup c) i = s.sup (fun j : J ↦ c j i) := by
        induction s using Finset.induction with
        | empty =>
            rfl
        | insert j s hjs ih =>
            simp [Finset.sup_insert, Finsupp.sup_apply, ih]
      have hsupzero : Finset.univ.sup (fun j : J ↦ c j i) = (⊥ : ℕ) := by
        rw [Finset.sup_eq_bot_iff]
        intro j _hj
        exact hzero j
      have hcontr : (Finset.univ.sup c) i = 0 := by
        rw [heval]
        simpa using hsupzero
      have hval : (Finset.univ.sup c) i ≠ 0 := by
        simpa [Finsupp.mem_support_iff] using hi
      exact hval hcontr
    rcases hex with ⟨j, hij⟩
    exact hgens_base j (c j) (hcMem j) hij
  have hpowGens : ∀ u ∈ powGens (iInfGens gens) q, u.support ⊆ A j₀ :=
    powGens_support_subset hgens q
  have hgroupedPow :
      (groupedComponents I A a P) ^ q = monomialIdeal (powGens (iInfGens gens) q) := by
    rw [hgrouped, monomialIdeal_pow]
  rw [hgroupedPow]
  exact comap_map_monomialIdeal_eq_of_generators_support
    (A := A j₀) (S := powGens (iInfGens gens) q) hpowGens (P := P.1) hP

/-- Equation (2) for a finite irredundant irreducible monomial decomposition, allowing
repeated and nested radicals. Each group of components with the same minimal radical is
intersected to obtain a primary component before taking its ordinary power. -/
theorem eq2_groupedSymbolic [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hdecomp : IsIrredundantDecomp I A a) :
    HasStdSymbolicFormula I (groupedComponents I A a) := by
  classical
  rcases hdecomp with ⟨hcomp, hirr⟩
  have hpos : ∀ j i, i ∈ A j → 0 < a j i :=
    exponents_pos_of_irredundant (K := K) hirr
  intro q _hq
  rw [componentSymbolic, symbolicPower]
  apply iInf_congr
  intro P
  let : P.1.IsPrime := P.2.isPrime
  change Ideal.comap (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1))
      (Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1)) (I ^ q)) =
    (groupedComponents I A a P) ^ q
  obtain ⟨j₀, hPj⟩ := minimalPrime_eq_primeOf hcomp hpos P.2
  have hmap :
      Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1)) I =
        Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1))
          (groupedComponents I A a P) :=
    map_iInf_purePower_eq_groupedComponent hcomp hpos P j₀ hPj
  have hmapPow :
      Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1)) (I ^ q) =
        Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1))
          ((groupedComponents I A a P) ^ q) := by
    calc
      Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1)) (I ^ q) =
          (Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1)) I) ^ q :=
        Ideal.map_pow _ _ _
      _ = (Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1))
            (groupedComponents I A a P)) ^ q := by rw [hmap]
      _ = Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1))
            ((groupedComponents I A a P) ^ q) :=
        (Ideal.map_pow _ _ _).symm
  have hcontract :
      Ideal.comap (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1))
        (Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1))
          ((groupedComponents I A a P) ^ q)) = (groupedComponents I A a P) ^ q :=
    comap_map_pow_groupedComponent_eq_self P j₀ hPj q
  calc
    Ideal.comap (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1))
        (Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1)) (I ^ q)) =
      Ideal.comap (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1))
        (Ideal.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime P.1))
          ((groupedComponents I A a P) ^ q)) := by rw [hmapPow]
    _ = (groupedComponents I A a P) ^ q := hcontract

end SimisFormal
