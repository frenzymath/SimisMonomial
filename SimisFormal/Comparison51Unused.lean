import SimisFormal.Defs
import SimisFormal.Basic
import SimisFormal.Prop2_1
import SimisFormal.Thm5_2
import SimisFormal.Eq2_StandardSymbolic
import SimisFormal.Eq4_DiagonalSimis

namespace SimisFormal
open MvPolynomial
open scoped BigOperators
noncomputable section
variable {σ K ι : Type*} [Field K] [DecidableEq σ]
/-- Inclusion of the variables selected by a finite ambient set. -/
def comparison51_subtypeEmbedding (U : Finset σ) : {x : σ // x ∈ U} ↪ σ :=
  ⟨fun x ↦ x.1, by intro x y h; exact Subtype.ext h⟩

omit [DecidableEq σ] in
/-- The selected-variable embedding sends a subtype element to its underlying variable. -/
@[simp] theorem comparison51_subtypeEmbedding_apply {U : Finset σ} (x : {x : σ // x ∈ U}) :
    comparison51_subtypeEmbedding U x = x.1 := rfl

/-- Membership in a restricted support is detected on the underlying ambient variable. -/
@[simp] theorem comparison51_mem_restrictFinset {U : Finset σ} {A : ι → Finset σ}
    {j : ι} (x : {x : σ // x ∈ U}) :
    x ∈ comparison51_restrictFinset U A j ↔ x.1 ∈ A j := by
  simp [comparison51_restrictFinset]

/-- Every displayed support is contained in the union of all displayed supports. -/
theorem comparison51_supports_subset_usedVariables [Fintype ι] (A : ι → Finset σ) (j : ι) :
    A j ⊆ comparison51_usedVariables A := by
  intro i hi
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hi⟩

/-- After restriction to the used variables, every subtype variable remains used. -/
theorem comparison51_restrictFinset_biUnion [Fintype ι] (A : ι → Finset σ) :
    Finset.univ.biUnion
        (comparison51_restrictFinset (comparison51_usedVariables A) A) = Finset.univ := by
  classical
  ext x
  constructor
  · intro _
    exact Finset.mem_univ x
  · intro _
    rcases Finset.mem_biUnion.mp x.2 with ⟨j, -, hj⟩
    exact Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ j,
        (comparison51_mem_restrictFinset (U := _) (A := A) (j := j) x).2 hj⟩

omit [DecidableEq σ] in
/-- Restriction commutes with addition of exponent vectors. -/
@[simp] theorem comparison51_restrictExp_add {U : Finset σ} (e f : σ →₀ ℕ) :
    _root_.thm52_restrictExp (comparison51_subtypeEmbedding U) (e + f) =
      _root_.thm52_restrictExp (comparison51_subtypeEmbedding U) e +
        _root_.thm52_restrictExp (comparison51_subtypeEmbedding U) f := by
  ext x
  simp

omit [DecidableEq σ] in
/-- Restriction of the zero exponent vector is zero. -/
@[simp] theorem comparison51_restrictExp_zero {U : Finset σ} :
    _root_.thm52_restrictExp (comparison51_subtypeEmbedding U) (0 : σ →₀ ℕ) = 0 := by
  ext x
  simp

omit [DecidableEq σ] in
/-- Restriction is monotone for coordinatewise divisibility. -/
theorem comparison51_restrictExp_mono {U : Finset σ} {e f : σ →₀ ℕ} (h : e ≤ f) :
    _root_.thm52_restrictExp (comparison51_subtypeEmbedding U) e ≤
      _root_.thm52_restrictExp (comparison51_subtypeEmbedding U) f := by
  intro x
  simpa using h x.1

omit [DecidableEq σ] in
/-- Expansion evaluates at selected ambient variables by the original subtype coordinate. -/
theorem comparison51_expandExp_apply_of_mem {U : Finset σ}
    (e : {x : σ // x ∈ U} →₀ ℕ) {i : σ} (hi : i ∈ U) :
    _root_.thm52_expandExp (comparison51_subtypeEmbedding U) e i = e ⟨i, hi⟩ := by
  change _root_.thm52_expandExp (comparison51_subtypeEmbedding U) e
      ((comparison51_subtypeEmbedding U) ⟨i, hi⟩) = e ⟨i, hi⟩
  exact _root_.thm52_expandExp_apply_of_range (comparison51_subtypeEmbedding U) e ⟨i, hi⟩

omit [DecidableEq σ] in
/-- Expansion evaluates on the image of a subtype variable by that variable's exponent. -/
@[simp] theorem comparison51_expandExp_apply_subtype {U : Finset σ}
    (e : {x : σ // x ∈ U} →₀ ℕ) (x : {x : σ // x ∈ U}) :
    _root_.thm52_expandExp (comparison51_subtypeEmbedding U) e x.1 = e x := by
  exact comparison51_expandExp_apply_of_mem e x.2

omit [DecidableEq σ] in
/-- Expansion preserves zero. -/
@[simp] theorem comparison51_expandExp_zero {U : Finset σ} :
    _root_.thm52_expandExp (comparison51_subtypeEmbedding U) (0 : {x : σ // x ∈ U} →₀ ℕ) =
      0 := by
  ext i
  by_cases hi : i ∈ U
  · rw [comparison51_expandExp_apply_of_mem (U := U) (0 : {x : σ // x ∈ U} →₀ ℕ) hi]
    rfl
  · rw [_root_.thm52_expandExp_apply_of_not_range]
    · rfl
    · rintro ⟨x, hx⟩
      apply hi
      rw [← hx]
      exact x.2

omit [DecidableEq σ] in
/-- Expansion followed by restriction is the identity on the subtype ring exponents. -/
@[simp] theorem comparison51_restrictExp_expandExp {U : Finset σ}
    (e : {x : σ // x ∈ U} →₀ ℕ) :
    _root_.thm52_restrictExp (comparison51_subtypeEmbedding U)
      (_root_.thm52_expandExp (comparison51_subtypeEmbedding U) e) = e := by
  ext x
  rw [_root_.thm52_restrictExp_apply]
  exact _root_.thm52_expandExp_apply_of_range (comparison51_subtypeEmbedding U) e x

/-- Restriction sends an ambient basis vector inside the selected set to its subtype version. -/
theorem comparison51_restrictExp_single_of_mem {U : Finset σ} {i : σ} (hi : i ∈ U) (n : ℕ) :
    _root_.thm52_restrictExp (comparison51_subtypeEmbedding U) (Finsupp.single i n) =
      Finsupp.single (⟨i, hi⟩ : {x : σ // x ∈ U}) n := by
  ext x
  by_cases hx : x.1 = i
  · have hxy : x = (⟨i, hi⟩ : {x : σ // x ∈ U}) := Subtype.ext hx
    subst x
    simp
  · have hxne : x ≠ (⟨i, hi⟩ : {x : σ // x ∈ U}) := by
      intro hxy
      exact hx (congrArg Subtype.val hxy)
    simp [hx, hxne]

/-- Monomial membership is unchanged by restriction of all component supports. -/
theorem comparison51_restrict_monomial_mem_iff
    [Fintype ι] {U : Finset σ} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hU : ∀ j, A j ⊆ U) {I : Ideal (MvPolynomial σ K)}
    (hI : HasComponents I A a) (e : σ →₀ ℕ) :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ I ↔
      (monomial (_root_.thm52_restrictExp (comparison51_subtypeEmbedding U) e) (1 : K) :
        MvPolynomial {x : σ // x ∈ U} K) ∈
        comparison51_restrictIdeal (K := K) U A a := by
  classical
  rw [hI]
  simp only [comparison51_restrictIdeal, Ideal.mem_iInf]
  constructor
  · intro he j
    rcases monomial_mem_purePower.mp (he j) with ⟨i, hi, hai⟩
    refine monomial_mem_purePower.mpr ⟨⟨i, hU j hi⟩, ?_, ?_⟩
    · simpa using (hi : i ∈ A j)
    · simpa [comparison51_restrictWeight] using hai
  · intro he j
    rcases monomial_mem_purePower.mp (he j) with ⟨x, hx, hax⟩
    refine monomial_mem_purePower.mpr ⟨x.1, ?_, ?_⟩
    · simpa using hx
    · simpa [comparison51_restrictWeight] using hax

/-- Monomial membership in one pure-power component is preserved and reflected. -/
theorem comparison51_restrict_component_monomial_mem_iff
    {U : Finset σ} {A : ι → Finset σ} {a : ι → σ → ℕ} {j : ι}
    (hUj : A j ⊆ U) (e : σ →₀ ℕ) :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ purePower (K := K) (A j) (a j) ↔
      (monomial (_root_.thm52_restrictExp (comparison51_subtypeEmbedding U) e) (1 : K) :
        MvPolynomial {x : σ // x ∈ U} K) ∈
        purePower (K := K) (comparison51_restrictFinset U A j)
          (comparison51_restrictWeight U a j) := by
  constructor
  · intro he
    rcases monomial_mem_purePower.mp he with ⟨i, hi, hai⟩
    refine monomial_mem_purePower.mpr ⟨⟨i, hUj hi⟩, ?_, ?_⟩
    · simpa using hi
    · simpa [comparison51_restrictWeight] using hai
  · intro he
    rcases monomial_mem_purePower.mp he with ⟨x, hx, hax⟩
    refine monomial_mem_purePower.mpr ⟨x.1, ?_, ?_⟩
    · simpa using hx
    · simpa [comparison51_restrictWeight] using hax

omit [DecidableEq σ] in
/-- Restriction maps iterated product generators to corresponding restricted generators. -/
theorem comparison51_restrict_powGens_mem {U : Finset σ}
    {S : Set (σ →₀ ℕ)} {S' : Set ({x : σ // x ∈ U} →₀ ℕ)}
    (hS : ∀ u ∈ S, _root_.thm52_restrictExp (comparison51_subtypeEmbedding U) u ∈ S') :
    ∀ (q : ℕ) (z : σ →₀ ℕ), z ∈ powGens S q →
      _root_.thm52_restrictExp (comparison51_subtypeEmbedding U) z ∈ powGens S' q := by
  intro q
  induction q with
  | zero =>
      intro z hz
      simp only [powGens] at hz ⊢
      subst z
      simp
  | succ q ih =>
      intro z hz
      simp only [powGens] at hz ⊢
      rcases hz with ⟨u, hu, s, hs, rfl⟩
      refine ⟨_root_.thm52_restrictExp (comparison51_subtypeEmbedding U) u, ih u hu,
        _root_.thm52_restrictExp (comparison51_subtypeEmbedding U) s, hS s hs, ?_⟩
      exact comparison51_restrictExp_add (U := U) u s

omit [DecidableEq σ] in
/-- Expansion maps iterated product generators back to ambient generators. -/
theorem comparison51_expand_powGens_mem {U : Finset σ}
    {S : Set (σ →₀ ℕ)} {S' : Set ({x : σ // x ∈ U} →₀ ℕ)}
    (hS : ∀ u ∈ S', _root_.thm52_expandExp (comparison51_subtypeEmbedding U) u ∈ S) :
    ∀ (q : ℕ) (z : {x : σ // x ∈ U} →₀ ℕ), z ∈ powGens S' q →
      _root_.thm52_expandExp (comparison51_subtypeEmbedding U) z ∈ powGens S q := by
  intro q
  induction q with
  | zero =>
      intro z hz
      simp only [powGens] at hz ⊢
      subst z
      simp
  | succ q ih =>
      intro z hz
      simp only [powGens] at hz ⊢
      rcases hz with ⟨u, hu, s, hs, rfl⟩
      refine ⟨_root_.thm52_expandExp (comparison51_subtypeEmbedding U) u, ih u hu,
        _root_.thm52_expandExp (comparison51_subtypeEmbedding U) s, hS s hs, ?_⟩
      exact _root_.thm52_expandExp_add (comparison51_subtypeEmbedding U) u s

omit [DecidableEq σ] in
/-- Ordinary-power membership transfers between ambient and selected variables. -/
theorem comparison51_restrict_monomial_pow_mem_iff {U : Finset σ}
    {S : Set (σ →₀ ℕ)} {S' : Set ({x : σ // x ∈ U} →₀ ℕ)}
    (hRS : ∀ u ∈ S, _root_.thm52_restrictExp (comparison51_subtypeEmbedding U) u ∈ S')
    (hES : ∀ u ∈ S', _root_.thm52_expandExp (comparison51_subtypeEmbedding U) u ∈ S)
    (q : ℕ) (e : σ →₀ ℕ) :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ (monomialIdeal (K := K) S) ^ q ↔
      (monomial (_root_.thm52_restrictExp (comparison51_subtypeEmbedding U) e) (1 : K) :
        MvPolynomial {x : σ // x ∈ U} K) ∈ (monomialIdeal (K := K) S') ^ q := by
  classical
  rw [monomialIdeal_pow, monomialIdeal_pow]
  rw [monomial_mem_monomialIdeal, monomial_mem_monomialIdeal]
  constructor
  · rintro ⟨u, hu, hue⟩
    exact ⟨_root_.thm52_restrictExp (comparison51_subtypeEmbedding U) u,
      comparison51_restrict_powGens_mem hRS q u hu,
      comparison51_restrictExp_mono hue⟩
  · rintro ⟨u, hu, hue⟩
    refine ⟨_root_.thm52_expandExp (comparison51_subtypeEmbedding U) u,
      comparison51_expand_powGens_mem hES q u hu, ?_⟩
    intro i
    by_cases hi : i ∈ U
    · have hui : u (⟨i, hi⟩ : {x : σ // x ∈ U}) ≤ e i := by
        simpa using hue (⟨i, hi⟩ : {x : σ // x ∈ U})
      rw [comparison51_expandExp_apply_of_mem (U := U) u hi]
      exact hui
    · rw [_root_.thm52_expandExp_apply_of_not_range]
      · exact Nat.zero_le _
      · rintro ⟨x, hx⟩
        apply hi
        rw [← hx]
        exact x.2

/-- Ordinary-power monomial membership for the whole intersection is unchanged. -/
theorem comparison51_restrict_componentIdeal_pow_monomial_mem_iff
    [Fintype ι] {U : Finset σ} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hU : ∀ j, A j ⊆ U) {I : Ideal (MvPolynomial σ K)}
    (hI : HasComponents I A a) (q : ℕ) (e : σ →₀ ℕ) :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ I ^ q ↔
      (monomial (_root_.thm52_restrictExp (comparison51_subtypeEmbedding U) e) (1 : K) :
        MvPolynomial {x : σ // x ∈ U} K) ∈
        comparison51_restrictIdeal (K := K) U A a ^ q := by
  classical
  have hRS : ∀ u ∈ _root_.thm52_componentGens A a,
      _root_.thm52_restrictExp (comparison51_subtypeEmbedding U) u ∈
        _root_.thm52_componentGens (comparison51_restrictFinset U A)
          (comparison51_restrictWeight U a) := by
    intro u hu
    change ∀ j, ∃ x ∈ comparison51_restrictFinset U A j,
      comparison51_restrictWeight U a j x ≤
        _root_.thm52_restrictExp (comparison51_subtypeEmbedding U) u x
    intro j
    rcases hu j with ⟨i, hi, hai⟩
    refine ⟨⟨i, hU j hi⟩, ?_, ?_⟩
    · simpa using hi
    · simpa [comparison51_restrictWeight] using hai
  have hES : ∀ u ∈ _root_.thm52_componentGens (comparison51_restrictFinset U A)
      (comparison51_restrictWeight U a),
      _root_.thm52_expandExp (comparison51_subtypeEmbedding U) u ∈
        _root_.thm52_componentGens A a := by
    intro u hu
    change ∀ j, ∃ i ∈ A j, a j i ≤
      _root_.thm52_expandExp (comparison51_subtypeEmbedding U) u i
    intro j
    rcases hu j with ⟨x, hx, hax⟩
    refine ⟨x.1, ?_, ?_⟩
    · simpa using hx
    · have hax' : a j x.1 ≤ u x := by
        simpa [comparison51_restrictWeight] using hax
      calc
        a j x.1 ≤ u x := hax'
        _ = _root_.thm52_expandExp (comparison51_subtypeEmbedding U) u x.1 :=
          (comparison51_expandExp_apply_subtype u x).symm
  rw [hI, comparison51_restrictIdeal]
  rw [_root_.thm52_iInf_purePower_eq (K := K) A a,
    _root_.thm52_iInf_purePower_eq (K := K) (comparison51_restrictFinset U A)
      (comparison51_restrictWeight U a)]
  exact comparison51_restrict_monomial_pow_mem_iff hRS hES q e

/-- Ordinary-power monomial membership for one pure-power component is unchanged. -/
theorem comparison51_restrict_component_pow_monomial_mem_iff
    {U : Finset σ} {A : ι → Finset σ} {a : ι → σ → ℕ} {j : ι}
    (hUj : A j ⊆ U) (q : ℕ) (e : σ →₀ ℕ) :
    (monomial e (1 : K) : MvPolynomial σ K) ∈
        (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K)) ^ q ↔
      (monomial (_root_.thm52_restrictExp (comparison51_subtypeEmbedding U) e) (1 : K) :
        MvPolynomial {x : σ // x ∈ U} K) ∈
        (purePower (K := K) (comparison51_restrictFinset U A j)
          (comparison51_restrictWeight U a j) : Ideal (MvPolynomial {x : σ // x ∈ U} K)) ^ q
    := by
  classical
  let S : Set (σ →₀ ℕ) := {z | ∃ i ∈ A j, z = Finsupp.single i (a j i)}
  let S' : Set ({x : σ // x ∈ U} →₀ ℕ) :=
    {z | ∃ x ∈ comparison51_restrictFinset U A j,
      z = Finsupp.single x (comparison51_restrictWeight U a j x)}
  have hRS : ∀ u ∈ S,
      _root_.thm52_restrictExp (comparison51_subtypeEmbedding U) u ∈ S' := by
    intro u hu
    rcases hu with ⟨i, hi, rfl⟩
    refine ⟨⟨i, hUj hi⟩, ?_, ?_⟩
    · simpa using hi
    · simpa [comparison51_restrictWeight] using
        comparison51_restrictExp_single_of_mem (U := U) (hUj hi) (a j i)
  have hES : ∀ u ∈ S',
      _root_.thm52_expandExp (comparison51_subtypeEmbedding U) u ∈ S := by
    intro u hu
    rcases hu with ⟨x, hx, rfl⟩
    refine ⟨x.1, ?_, ?_⟩
    · simpa using hx
    · simp [comparison51_restrictWeight]
  simpa only [purePower, S, S'] using
    (comparison51_restrict_monomial_pow_mem_iff (K := K) hRS hES q e)

/-- The displayed restricted intersection has the displayed restricted components. -/
theorem comparison51_restrict_hasComponents [Fintype ι] (U : Finset σ)
    (A : ι → Finset σ) (a : ι → σ → ℕ) :
    HasComponents (comparison51_restrictIdeal (K := K) U A a)
      (comparison51_restrictFinset U A) (comparison51_restrictWeight U a) := by
  rfl

/-- Restriction also transports membership in the intersection omitting one component. -/
theorem comparison51_restrict_decompOmit_monomial_mem_iff
    [Fintype ι] {U : Finset σ} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hU : ∀ j, A j ⊆ U) (j : ι) (e : σ →₀ ℕ) :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ decompOmit A a j ↔
      (monomial (_root_.thm52_restrictExp (comparison51_subtypeEmbedding U) e) (1 : K) :
        MvPolynomial {x : σ // x ∈ U} K) ∈
        decompOmit (comparison51_restrictFinset U A) (comparison51_restrictWeight U a) j := by
  classical
  simp only [decompOmit, Ideal.mem_iInf]
  constructor
  · intro he k
    exact (comparison51_restrict_component_monomial_mem_iff (K := K) (hU k.1) e).mp (he k)
  · intro he k
    exact (comparison51_restrict_component_monomial_mem_iff (K := K) (hU k.1) e).mpr (he k)

/-- An irredundant pure-power decomposition stays irredundant after restriction. -/
theorem comparison51_restrict_irredundant
    [Fintype ι] {U : Finset σ} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hU : ∀ j, A j ⊆ U) (hirr : IsIrredundant (K := K) A a) :
    IsIrredundant (K := K) (comparison51_restrictFinset U A)
      (comparison51_restrictWeight U a) := by
  classical
  intro j hle'
  rcases SetLike.not_le_iff_exists.mp (hirr j) with ⟨x, hxD, hxQ⟩
  rcases prop21_exists_monomial_not_mem_of_not_mem_purePower hxQ with ⟨e, he, heQ⟩
  have hcompD : HasComponents (decompOmit (K := K) A a j)
      (fun k : {k : ι // k ≠ j} ↦ A k.1) (fun k : {k : ι // k ≠ j} ↦ a k.1) := by
    rfl
  have heD : (monomial e (1 : K) : MvPolynomial σ K) ∈ decompOmit A a j :=
    prop21_monomial_mem_of_mem_components hcompD hxD he
  have heD' := (comparison51_restrict_decompOmit_monomial_mem_iff (K := K) hU j e).mp heD
  have heQ' := hle' heD'
  exact heQ ((comparison51_restrict_component_monomial_mem_iff (K := K) (hU j) e).mpr heQ')

/-- Restriction turns an irredundant decomposition into an irredundant one. -/
theorem comparison51_restrict_irredundantDecomp
    [Fintype ι] {U : Finset σ} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hU : ∀ j, A j ⊆ U) {I : Ideal (MvPolynomial σ K)}
    (hdec : IsIrredundantDecomp I A a) :
    IsIrredundantDecomp (comparison51_restrictIdeal (K := K) U A a)
      (comparison51_restrictFinset U A) (comparison51_restrictWeight U a) :=
  ⟨comparison51_restrict_hasComponents (K := K) U A a,
    comparison51_restrict_irredundant (K := K) hU hdec.2⟩

/-- Componentwise Simisness is invariant under discarding unused variables. -/
theorem comparison51_restrict_componentSimis_iff
    [Fintype ι] {U : Finset σ} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hU : ∀ j, A j ⊆ U) {I : Ideal (MvPolynomial σ K)}
    (hdec : IsIrredundantDecomp I A a) (hanti : SupportsAntichain A a)
    (hdec' : IsIrredundantDecomp (comparison51_restrictIdeal (K := K) U A a)
      (comparison51_restrictFinset U A) (comparison51_restrictWeight U a))
    (hanti' : SupportsAntichain (comparison51_restrictFinset U A)
      (comparison51_restrictWeight U a)) :
    ComponentSimis I (fun j ↦ purePower (K := K) (A j) (a j)) ↔
      ComponentSimis (comparison51_restrictIdeal (K := K) U A a)
        (fun j ↦ purePower (K := K) (comparison51_restrictFinset U A j)
          (comparison51_restrictWeight U a j)) := by
  classical
  let A' := comparison51_restrictFinset U A
  let a' := comparison51_restrictWeight U a
  let I' := comparison51_restrictIdeal (K := K) U A a
  let Q : ι → Ideal (MvPolynomial σ K) := fun j ↦ purePower (K := K) (A j) (a j)
  let Q' : ι → Ideal (MvPolynomial {x : σ // x ∈ U} K) :=
    fun j ↦ purePower (K := K) (A' j) (a' j)
  change ComponentSimis I Q ↔ ComponentSimis I' Q'
  change SupportsAntichain A a at hanti
  change IsIrredundantDecomp I' A' a' at hdec'
  change SupportsAntichain A' a' at hanti'
  have _hstd := eq2_standardSymbolic hdec hanti
  have _hstd' := eq2_standardSymbolic hdec' hanti'
  have hmonI : IsMonomialIdeal I := by
    rw [hdec.1, _root_.thm52_iInf_purePower_eq (K := K)]
    exact ⟨_, rfl⟩
  have hmonI' : IsMonomialIdeal I' := by
    rw [hdec'.1, _root_.thm52_iInf_purePower_eq (K := K)]
    exact ⟨_, rfl⟩
  have hmonC (q : ℕ) : IsMonomialIdeal (componentSymbolic Q q) := by
    change IsMonomialIdeal (⨅ j, Q j ^ q)
    exact eq4_isMonomialIdeal_iInf (K := K) (fun j ↦
      eq4_isMonomialIdeal_pow (K := K)
        (eq4_isMonomialIdeal_purePower (K := K) (A j) (a j)) q)
  have hmonC' (q : ℕ) : IsMonomialIdeal (componentSymbolic Q' q) := by
    change IsMonomialIdeal (⨅ j, Q' j ^ q)
    exact eq4_isMonomialIdeal_iInf (K := K) (fun j ↦
      eq4_isMonomialIdeal_pow (K := K)
        (eq4_isMonomialIdeal_purePower (K := K) (A' j) (a' j)) q)
  have hpow := comparison51_restrict_componentIdeal_pow_monomial_mem_iff
    (K := K) hU hdec.1
  have hcompPow (j : ι) := comparison51_restrict_component_pow_monomial_mem_iff
    (K := K) (A := A) (a := a) (j := j) (hU j)
  have hmemComp (q : ℕ) (e : σ →₀ ℕ) :
      (monomial e (1 : K) : MvPolynomial σ K) ∈ componentSymbolic Q q ↔
        (monomial (_root_.thm52_restrictExp (comparison51_subtypeEmbedding U) e) (1 : K) :
          MvPolynomial {x : σ // x ∈ U} K) ∈ componentSymbolic Q' q := by
    simp only [componentSymbolic, Ideal.mem_iInf]
    constructor
    · intro he j
      exact (hcompPow j q e).mp (he j)
    · intro he j
      exact (hcompPow j q e).mpr (he j)
  have hmemCompExpand (q : ℕ) (e' : {x : σ // x ∈ U} →₀ ℕ) :
      (monomial (_root_.thm52_expandExp (comparison51_subtypeEmbedding U) e') (1 : K) :
          MvPolynomial σ K) ∈ componentSymbolic Q q ↔
        (monomial e' (1 : K) : MvPolynomial {x : σ // x ∈ U} K) ∈
          componentSymbolic Q' q := by
    simp only [componentSymbolic, Ideal.mem_iInf]
    constructor
    · intro he j
      have hj := (hcompPow j q
        (_root_.thm52_expandExp (comparison51_subtypeEmbedding U) e')).mp (he j)
      simpa using hj
    · intro he j
      exact (hcompPow j q
        (_root_.thm52_expandExp (comparison51_subtypeEmbedding U) e')).mpr
          (by simpa using he j)
  constructor
  · intro hamb q hq
    apply eq4_eq_of_monomial_mem
      (eq4_isMonomialIdeal_pow hmonI' q) (hmonC' q)
    intro e'
    let E := _root_.thm52_expandExp (comparison51_subtypeEmbedding U) e'
    have hEq := hamb q hq
    constructor
    · intro hI'
      have hIA : (monomial E (1 : K) : MvPolynomial σ K) ∈ I ^ q :=
        (hpow q E).mpr (by simpa [E] using hI')
      rw [hEq] at hIA
      have hCR := (hmemComp q E).mp hIA
      simpa [E] using hCR
    · intro hC'
      have hCA : (monomial E (1 : K) : MvPolynomial σ K) ∈ componentSymbolic Q q :=
        (hmemCompExpand q e').mpr hC'
      rw [← hEq] at hCA
      have hIR := (hpow q E).mp hCA
      simpa [E] using hIR
  · intro hres q hq
    apply eq4_eq_of_monomial_mem
      (eq4_isMonomialIdeal_pow hmonI q) (hmonC q)
    intro e
    have hEq := hres q hq
    constructor
    · intro hI
      have hIR := (hpow q e).mp hI
      rw [hEq] at hIR
      exact (hmemComp q e).mpr hIR
    · intro hC
      have hCR := (hmemComp q e).mp hC
      rw [← hEq] at hCR
      exact (hpow q e).mpr hCR

/-- The diagonal-root criterion is unchanged when only used variables are retained. -/
theorem comparison51_restrict_hasSqRoot_iff
    [Fintype σ] [Fintype ι] [LinearOrder ι] {U : Finset σ}
    {A : ι → Finset σ} {a : ι → σ → ℕ} (hU : ∀ j, A j ⊆ U)
    {I : Ideal (MvPolynomial σ K)} (hdec : IsIrredundantDecomp I A a) :
    HasSqRoot I ↔ HasSqRoot (comparison51_restrictIdeal (K := K) U A a) := by
  classical
  let A' := comparison51_restrictFinset U A
  let a' := comparison51_restrictWeight U a
  let I' := comparison51_restrictIdeal (K := K) U A a
  change HasSqRoot I ↔ HasSqRoot I'
  have hdec' : IsIrredundantDecomp I' A' a' :=
    comparison51_restrict_irredundantDecomp (K := K) hU hdec
  have hXI : prop21_XI A a = ∅ ↔ prop21_XI A' a' = ∅ := by
    constructor
    · intro h
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨j, k⟩ hp
      rcases hp with ⟨hlt, x, hxj, hxk, hne⟩
      have hpA : (j, k) ∈ prop21_XI A a := by
        refine ⟨hlt, x.1, ?_, ?_, ?_⟩
        · simpa [A'] using hxj
        · simpa [A'] using hxk
        · intro heq
          apply hne
          simpa only [a', comparison51_restrictWeight] using heq
      exact (Set.eq_empty_iff_forall_notMem.mp h (j, k)) hpA
    · intro h
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨j, k⟩ hp
      rcases hp with ⟨hlt, i, hij, hik, hne⟩
      have hpR : (j, k) ∈ prop21_XI A' a' := by
        refine ⟨hlt, ⟨i, hU j hij⟩, ?_, ?_, ?_⟩
        · simpa [A'] using hij
        · simpa [A'] using hik
        · intro heq
          apply hne
          simpa only [a', comparison51_restrictWeight] using heq
      exact (Set.eq_empty_iff_forall_notMem.mp h (j, k)) hpR
  exact (prop21_hasSqRoot_iff_XI_eq_empty (K := K) hdec.1 hdec.2).trans
    (hXI.trans (prop21_hasSqRoot_iff_XI_eq_empty (K := K) hdec'.1 hdec'.2).symm)

/-- Simisness after restriction to any finite set containing every displayed support. -/
theorem comparison51_restrict_isSimis_iff_of_supports_subset
    [Fintype σ] [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    {U : Finset σ} {A : ι → Finset σ} {a : ι → σ → ℕ} (hU : ∀ j, A j ⊆ U)
    {I : Ideal (MvPolynomial σ K)} (hdec : IsIrredundantDecomp I A a)
    (hroot : HasSqRoot I) :
    IsSimis I ↔ IsSimis (comparison51_restrictIdeal (K := K) U A a) := by
  classical
  let A' := comparison51_restrictFinset U A
  let a' := comparison51_restrictWeight U a
  let I' := comparison51_restrictIdeal (K := K) U A a
  change IsSimis I ↔ IsSimis I'
  have hdec' : IsIrredundantDecomp I' A' a' :=
    comparison51_restrict_irredundantDecomp (K := K) hU hdec
  have hroot' : HasSqRoot I' :=
    (comparison51_restrict_hasSqRoot_iff (K := K) hU hdec).mp hroot
  have hanti : SupportsAntichain A a :=
    prop21_supportsAntichain_of_hasSqRoot (K := K) hdec.1 hdec.2 hroot
  have hanti' : SupportsAntichain A' a' :=
    prop21_supportsAntichain_of_hasSqRoot (K := K) hdec'.1 hdec'.2 hroot'
  have hstd := eq2_standardSymbolic hdec hanti
  have hstd' := eq2_standardSymbolic hdec' hanti'
  have hcomp := comparison51_restrict_componentSimis_iff (K := K) hU hdec hanti hdec' hanti'
  change ComponentSimis I (fun j ↦ purePower (K := K) (A j) (a j)) ↔
    ComponentSimis I' (fun j ↦ purePower (K := K) (A' j) (a' j)) at hcomp
  constructor
  · intro h
    exact (isSimis_iff_componentSimis_of_stdSymbolic hstd').mpr
      (hcomp.mp ((isSimis_iff_componentSimis_of_stdSymbolic hstd).mp h))
  · intro h
    exact (isSimis_iff_componentSimis_of_stdSymbolic hstd).mpr
      (hcomp.mpr ((isSimis_iff_componentSimis_of_stdSymbolic hstd').mp h))

/-- A squarefree monomial ideal is, in particular, a monomial ideal. -/
theorem comparison51_isMonomialIdeal_of_squarefree {I : Ideal (MvPolynomial σ K)}
    (hI : IsSquarefreeMonomialIdeal I) : IsMonomialIdeal I := by
  rcases hI with ⟨H, hH⟩
  exact ⟨characteristicExp '' H, hH⟩

/-- For a diagonal ideal, the MPV conclusion is equivalent to Simisness. -/
theorem comparison51_mpvConc_iff_isSimis_of_hasSqRoot [Fintype σ]
    {I : Ideal (MvPolynomial σ K)} (hroot : HasSqRoot I) :
    MPVConc I ↔ IsSimis I := by
  constructor
  · rintro ⟨J, d, hJ, hJs, hd, hdiag⟩
    have hJm := comparison51_isMonomialIdeal_of_squarefree (K := K) hJ
    have hiff := eq4_isSimis_diagonal_iff_of_isMonomialIdeal (K := K) hJm hd
    rw [hdiag] at hiff
    exact hiff.mp hJs
  · intro hs
    rcases hroot with ⟨J, d, hJ, hd, hdiag⟩
    have hJm := comparison51_isMonomialIdeal_of_squarefree (K := K) hJ
    have hiff := eq4_isSimis_diagonal_iff_of_isMonomialIdeal (K := K) hJm hd
    rw [hdiag] at hiff
    exact ⟨J, d, hJ, hiff.mpr hs, hd, hdiag⟩

/-- Restriction to the union of all supports preserves the complete diagonal package. -/
theorem comparison51_restrict_package
    [Fintype σ] [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hdec : IsIrredundantDecomp I A a)
    (hroot : HasSqRoot I) :
    let U := comparison51_usedVariables A
    let A' := comparison51_restrictFinset U A
    let a' := comparison51_restrictWeight U a
    let I' := comparison51_restrictIdeal (K := K) U A a
    IsIrredundantDecomp I' A' a' ∧
      HasSqRoot I' ∧
      SupportsAntichain A' a' ∧
      Finset.univ.biUnion A' = Finset.univ ∧
      (IsSimis I ↔ IsSimis I') ∧
      (MPVConc I ↔ MPVConc I') := by
  classical
  let U := comparison51_usedVariables A
  let A' := comparison51_restrictFinset U A
  let a' := comparison51_restrictWeight U a
  let I' := comparison51_restrictIdeal (K := K) U A a
  change IsIrredundantDecomp I' A' a' ∧
    HasSqRoot I' ∧
    SupportsAntichain A' a' ∧
    Finset.univ.biUnion A' = Finset.univ ∧
    (IsSimis I ↔ IsSimis I') ∧
    (MPVConc I ↔ MPVConc I')
  have hU : ∀ j, A j ⊆ U := fun j ↦ comparison51_supports_subset_usedVariables A j
  have hdec' : IsIrredundantDecomp I' A' a' :=
    comparison51_restrict_irredundantDecomp (K := K) hU hdec
  have hroot' : HasSqRoot I' :=
    (comparison51_restrict_hasSqRoot_iff (K := K) hU hdec).mp hroot
  have hanti' : SupportsAntichain A' a' :=
    prop21_supportsAntichain_of_hasSqRoot (K := K) hdec'.1 hdec'.2 hroot'
  have hUsed : Finset.univ.biUnion A' = Finset.univ := by
    simpa [A', U] using comparison51_restrictFinset_biUnion A
  have hsimis : IsSimis I ↔ IsSimis I' :=
    comparison51_restrict_isSimis_iff_of_supports_subset (K := K) hU hdec hroot
  have hmpvI := comparison51_mpvConc_iff_isSimis_of_hasSqRoot (K := K) hroot
  have hmpvI' := comparison51_mpvConc_iff_isSimis_of_hasSqRoot (K := K) hroot'
  refine ⟨hdec', hroot', hanti', hUsed, hsimis, ?_⟩
  constructor
  · intro h
    exact hmpvI'.mpr (hsimis.mp (hmpvI.mp h))
  · intro h
    exact hmpvI.mpr (hsimis.mpr (hmpvI'.mp h))

end
end SimisFormal
