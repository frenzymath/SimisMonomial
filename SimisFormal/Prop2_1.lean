import SimisFormal.Defs
import SimisFormal.Basic

namespace SimisFormal
variable {σ K ι : Type*} [Field K] [DecidableEq σ]
open MvPolynomial
open scoped BigOperators
/-- A monomial occurring in an element of a pure-power component is itself in that component. -/
theorem prop21_monomial_mem_of_mem_purePower
    {A : Finset σ} {a : σ → ℕ} {x : MvPolynomial σ K} {e : σ →₀ ℕ}
    (hx : x ∈ (purePower A a : Ideal (MvPolynomial σ K))) (he : e ∈ x.support) :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ purePower A a := by
  rw [purePower, monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image] at hx
  rcases hx e he with ⟨u, ⟨t, htA, rfl⟩, hut⟩
  exact monomial_mem_purePower.mpr ⟨t, htA, Finsupp.single_le_iff.mp hut⟩

/-- An intersection of pure powers contains every monomial occurring in each of its elements. -/
theorem prop21_monomial_mem_of_mem_components
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) {x : MvPolynomial σ K} {e : σ →₀ ℕ}
    (hx : x ∈ I) (he : e ∈ x.support) :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ I := by
  rw [hI] at hx ⊢
  refine Ideal.mem_iInf.mpr ?_
  intro j
  exact prop21_monomial_mem_of_mem_purePower (Ideal.mem_iInf.mp hx j) he

/-- Irredundance forces every displayed component exponent to be positive. -/
theorem prop21_componentExponent_pos_of_irredundant
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hIrr : IsIrredundant (K := K) A a) {j : ι} {i : σ} (hi : i ∈ A j) :
    0 < a j i := by
  classical
  by_contra hnot
  have hzero : a j i = 0 := by omega
  have hOne : (1 : MvPolynomial σ K) ∈
      (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) := by
    have hm : (monomial (0 : σ →₀ ℕ) (1 : K) : MvPolynomial σ K) ∈
        purePower (A j) (a j) :=
      monomial_mem_purePower.mpr ⟨i, hi, by simp [hzero]⟩
    simpa using hm
  have htop : (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) = ⊤ :=
    (Ideal.eq_top_iff_one _).2 hOne
  apply hIrr j
  rw [htop]
  exact le_top

/-- Intersections of pure powers are upward closed on exponent vectors. -/
theorem prop21_monomial_mem_of_le_mem_components
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) {u e : σ →₀ ℕ}
    (hu : (monomial u (1 : K) : MvPolynomial σ K) ∈ I) (hue : u ≤ e) :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ I := by
  rw [hI] at hu ⊢
  refine Ideal.mem_iInf.mpr ?_
  intro j
  rcases monomial_mem_purePower.mp (Ideal.mem_iInf.mp hu j) with ⟨t, htA, hat⟩
  exact monomial_mem_purePower.mpr ⟨t, htA, le_trans hat (hue t)⟩

/-- Proposition 2.1, easier inclusion \(D_i\subseteq C_i\). -/
theorem prop21_generatorExponents_subset_componentExponents
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (i : σ) :
    generatorExponents I i ⊆ componentExponents A a i := by
  classical
  intro n hn
  rcases hn with ⟨hnpos, α, hαmem, hαi⟩
  rcases hαmem with ⟨hαI, hαmin⟩
  let β : σ →₀ ℕ := α - Finsupp.single i 1
  have hβle : β ≤ α := by
    intro t
    simp only [β]
    exact Nat.sub_le _ _
  have hβnotI : (monomial β (1 : K) : MvPolynomial σ K) ∉ I := by
    intro hβI
    have hβeq : β = α := hαmin β hβI hβle
    have hcoord := congrArg (fun e : σ →₀ ℕ ↦ e i) hβeq
    have hbad : n - 1 = n := by simpa [β, hαi] using hcoord
    omega
  have hαinf : (monomial α (1 : K) : MvPolynomial σ K) ∈
      (⨅ j, (purePower (A j) (a j) : Ideal (MvPolynomial σ K))) := by
    rw [← hI]
    exact hαI
  have hαall : ∀ j, (monomial α (1 : K) : MvPolynomial σ K) ∈
      (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) := by
    intro j
    exact Ideal.mem_iInf.mp hαinf j
  obtain ⟨j, hβnotQ⟩ : ∃ j, (monomial β (1 : K) : MvPolynomial σ K) ∉
      (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) := by
    by_contra h
    push Not at h
    apply hβnotI
    rw [hI]
    exact Ideal.mem_iInf.mpr h
  rcases monomial_mem_purePower.mp (hαall j) with ⟨t, htA, hat⟩
  have hti : t = i := by
    by_contra hne
    have hit : i ≠ t := fun h => hne h.symm
    have hβt : β t = α t := by simp [β, hit]
    apply hβnotQ
    exact monomial_mem_purePower.mpr ⟨t, htA, by simpa [hβt] using hat⟩
  subst t
  have hnot : ¬ a j i ≤ β i := by
    intro hai
    exact hβnotQ (monomial_mem_purePower.mpr ⟨i, htA, hai⟩)
  have hβi : β i = n - 1 := by simp [β, hαi]
  have haji : a j i = n := by omega
  exact ⟨j, htA, haji⟩

/-- Proposition 2.1, irredundance-based inclusion \(C_i\subseteq D_i\). -/
theorem prop21_componentExponents_subset_generatorExponents
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hIrr : IsIrredundant (K := K) A a) (i : σ) :
    componentExponents A a i ⊆ generatorExponents I i := by
  classical
  have ha : ∀ j i, i ∈ A j → 0 < a j i :=
    fun j i hi ↦ prop21_componentExponent_pos_of_irredundant hIrr hi
  intro n hn
  rcases hn with ⟨j, hi, haji⟩
  have hposi : 0 < a j i := ha j i hi
  have hnotle : ¬ (decompOmit A a j : Ideal (MvPolynomial σ K)) ≤
      purePower (A j) (a j) := hIrr j
  obtain ⟨x, hxomit, hxnotQ⟩ :
      ∃ x, x ∈ (decompOmit A a j : Ideal (MvPolynomial σ K)) ∧
        x ∉ (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) := by
    by_contra hNo
    apply hnotle
    intro x hx
    by_contra hxQ
    exact hNo ⟨x, hx, hxQ⟩
  obtain ⟨β, hβin, hβnotQ⟩ :
      ∃ e, e ∈ x.support ∧
        (monomial e (1 : K) : MvPolynomial σ K) ∉ purePower (A j) (a j) := by
    by_contra hNo
    apply hxnotQ
    rw [purePower, monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image]
    intro e he
    have heQ : (monomial e (1 : K) : MvPolynomial σ K) ∈ purePower (A j) (a j) := by
      by_contra henot
      exact hNo ⟨e, he, henot⟩
    rw [purePower, monomial_mem_monomialIdeal] at heQ
    exact heQ
  have hxinf : x ∈
      (⨅ k : {k : ι // k ≠ j}, (purePower (A k.1) (a k.1) : Ideal (MvPolynomial σ K))) := by
    simpa [decompOmit] using hxomit
  have hβother : ∀ h, h ≠ j →
      (monomial β (1 : K) : MvPolynomial σ K) ∈ purePower (A h) (a h) := by
    intro h hh
    exact prop21_monomial_mem_of_mem_purePower
      (Ideal.mem_iInf.mp hxinf ⟨h, hh⟩) hβin
  let γ0 : σ →₀ ℕ := Finsupp.onFinset (A j)
    (fun t ↦ if t ∈ A j then a j t - 1 else 0) (by
      intro t ht
      by_contra hnot
      exact ht (by simp [hnot]))
  let γ : σ →₀ ℕ := β ⊔ γ0
  have hγ0_apply (t : σ) (ht : t ∈ A j) : γ0 t = a j t - 1 := by
    simp [γ0, ht]
  have hβlepred (t : σ) (ht : t ∈ A j) : β t ≤ a j t - 1 := by
    have hnole : ¬ a j t ≤ β t := by
      intro hle
      exact hβnotQ (monomial_mem_purePower.mpr ⟨t, ht, hle⟩)
    omega
  have hy_le_pred (t : σ) (ht : t ∈ A j) : γ t ≤ a j t - 1 := by
    have hm : β t ⊔ γ0 t ≤ a j t - 1 :=
      max_le (hβlepred t ht) (by simp [hγ0_apply t ht])
    simpa [γ] using hm
  have hβleγ : β ≤ γ := by
    intro t
    simp [γ]
  have hγ0leγ : γ0 ≤ γ := by
    intro t
    simp [γ]
  have hyi : γ i = a j i - 1 := by
    apply le_antisymm (hy_le_pred i hi)
    have := hγ0leγ i
    simpa [hγ0_apply i hi] using this
  have hyother : ∀ h, h ≠ j →
      (monomial γ (1 : K) : MvPolynomial σ K) ∈ purePower (A h) (a h) := by
    intro h hh
    rcases monomial_mem_purePower.mp (hβother h hh) with ⟨t, htA, hat⟩
    exact monomial_mem_purePower.mpr ⟨t, htA, le_trans hat (hβleγ t)⟩
  have hynotQ : (monomial γ (1 : K) : MvPolynomial σ K) ∉ purePower (A j) (a j) := by
    intro hyQ
    rcases monomial_mem_purePower.mp hyQ with ⟨t, htA, hat⟩
    have hle := hy_le_pred t htA
    have hpost := ha j t htA
    omega
  let eplus : σ →₀ ℕ := γ + Finsupp.single i 1
  have hepi : eplus i = a j i := by
    have h1 : 1 ≤ a j i := by omega
    calc
      eplus i = γ i + 1 := by simp [eplus]
      _ = (a j i - 1) + 1 := by rw [hyi]
      _ = a j i := Nat.sub_add_cancel h1
  have hγleplus : γ ≤ eplus := by
    intro t
    simp [eplus]
  have heplusQ : ∀ h, (monomial eplus (1 : K) : MvPolynomial σ K) ∈
      (purePower (A h) (a h) : Ideal (MvPolynomial σ K)) := by
    intro h
    by_cases hh : h = j
    · subst h
      exact monomial_mem_purePower.mpr ⟨i, hi, by rw [hepi]⟩
    · rcases monomial_mem_purePower.mp (hyother h hh) with ⟨t, htA, hat⟩
      exact monomial_mem_purePower.mpr ⟨t, htA, le_trans hat (hγleplus t)⟩
  have heplusI : (monomial eplus (1 : K) : MvPolynomial σ K) ∈ I := by
    rw [hI]
    exact Ideal.mem_iInf.mpr heplusQ
  have hynotI : (monomial γ (1 : K) : MvPolynomial σ K) ∉ I := by
    intro hyI
    apply hynotQ
    have hyinf : (monomial γ (1 : K) : MvPolynomial σ K) ∈
        (⨅ h, (purePower (A h) (a h) : Ideal (MvPolynomial σ K))) := by
      rw [← hI]
      exact hyI
    exact Ideal.mem_iInf.mp hyinf j
  obtain ⟨u, humin, hueplus⟩ := exists_minGens_le heplusI
  have huI : (monomial u (1 : K) : MvPolynomial σ K) ∈ I := (mem_minGens.mp humin).1
  have hunotleγ : ¬ u ≤ γ := by
    intro hule
    exact hynotI (prop21_monomial_mem_of_le_mem_components hI huI hule)
  rw [Finsupp.le_def] at hunotleγ
  push Not at hunotleγ
  rcases hunotleγ with ⟨t, ht⟩
  have hti : t = i := by
    by_contra hne
    have hit : i ≠ t := fun h => hne h.symm
    have hutle : u t ≤ γ t := by
      have := hueplus t
      simpa [eplus, hit] using this
    exact (not_lt_of_ge hutle) ht
  subst t
  have hui : u i = n := by
    have hiupper := hueplus i
    omega
  have hnpos : 0 < n := by omega
  exact ⟨hnpos, ⟨u, humin, hui⟩⟩

/-- Proposition 2.1: the positive generator and component occurrence exponents coincide. -/
theorem prop21_generatorExponents_eq_componentExponents
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hIrr : IsIrredundant (K := K) A a) (i : σ) :
    generatorExponents I i = componentExponents A a i :=
  Set.Subset.antisymm
    (prop21_generatorExponents_subset_componentExponents hI i)
    (prop21_componentExponents_subset_generatorExponents hI hIrr i)

omit [DecidableEq σ] in
/-- Empty mismatch-pair set is exactly coherence of all component occurrence exponents. -/
theorem prop21_componentExponents_subsingleton_iff_mismatchPairs_eq_empty
    {A : ι → Finset σ} {a : ι → σ → ℕ} :
    (∀ i, (componentExponents A a i).Subsingleton) ↔ mismatchPairs A a = ∅ := by
  classical
  constructor
  · intro hcoh
    ext p
    constructor
    · rintro ⟨i, hi1, hi2, hne⟩
      exact (hne (hcoh i ⟨p.1, hi1, rfl⟩ ⟨p.2, hi2, rfl⟩)).elim
    · intro hp
      simp at hp
  · intro hempty i m hm n hn
    by_contra hmn
    rcases hm with ⟨j, hji, hajm⟩
    rcases hn with ⟨k, hki, hakn⟩
    have hp : (j, k) ∈ mismatchPairs A a := by
      refine ⟨i, hji, hki, ?_⟩
      intro heq
      exact hmn ((hajm.symm).trans (heq.trans hakn))
    rw [hempty] at hp
    simp at hp

/-- A positive coordinate of a minimal generator of a diagonal root is exactly its weight. -/
theorem prop21_minGen_coordinate_eq_weight [Fintype σ]
    {I J : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hJ : IsSquarefreeMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hdiag : diagonal d J = I) {α : σ →₀ ℕ} (hα : α ∈ minGens I) {i : σ}
    (hi : 0 < α i) : α i = d i := by
  classical
  rcases hJ with ⟨H, hJrep⟩
  have hJmono : IsMonomialIdeal J := ⟨characteristicExp '' H, hJrep⟩
  have hαI : (monomial α (1 : K) : MvPolynomial σ K) ∈ I := (mem_minGens.mp hα).1
  have hαdiag : (monomial α (1 : K) : MvPolynomial σ K) ∈ diagonal d J := by
    rw [hdiag]
    exact hαI
  have hfloorJ : (monomial (floorDiv d α) (1 : K) : MvPolynomial σ K) ∈ J :=
    (monomial_mem_diagonal (K := K) hJmono hd).mp hαdiag
  have hfloorR : (monomial (floorDiv d α) (1 : K) : MvPolynomial σ K) ∈
      (monomialIdeal (characteristicExp '' H) : Ideal (MvPolynomial σ K)) := by
    rw [← hJrep]
    exact hfloorJ
  rcases monomial_mem_monomialIdeal.mp hfloorR with ⟨s, hs, hsfloor⟩
  rcases hs with ⟨B, hBH, rfl⟩
  let w : σ →₀ ℕ := diagExp d (characteristicExp B)
  have hwle : w ≤ α := by
    simpa [w] using (diagExp_le_iff_floor hd (characteristicExp B) α).mpr hsfloor
  have hwDiag : (monomial w (1 : K) : MvPolynomial σ K) ∈ diagonal d J := by
    rw [hJrep, diagonal_monomialIdeal]
    exact monomial_mem_monomialIdeal.mpr
      ⟨w, ⟨characteristicExp B, ⟨B, hBH, rfl⟩, rfl⟩, le_rfl⟩
  have hwI : (monomial w (1 : K) : MvPolynomial σ K) ∈ I := by
    rw [← hdiag]
    exact hwDiag
  have hweq : w = α := (mem_minGens.mp hα).2 w hwI hwle
  have hcoord := congrArg (fun e : σ →₀ ℕ ↦ e i) hweq
  by_cases hiB : i ∈ B
  · have hdα : d i = α i := by simpa [w, hiB] using hcoord
    exact hdα.symm
  · have hz : 0 = α i := by simpa [w, hiB] using hcoord
    omega

/-- Proposition 2.1, direction (i) implies (ii). -/
theorem prop21_generatorExponents_subsingleton_of_hasSqRoot [Fintype σ]
    {I : Ideal (MvPolynomial σ K)} (hroot : HasSqRoot I) :
    ∀ i, (generatorExponents I i).Subsingleton := by
  rcases hroot with ⟨J, d, hJ, hd, hdiag⟩
  intro i m hm n hn
  rcases hm with ⟨hmpos, α, hα, hαi⟩
  rcases hn with ⟨hnpos, β, hβ, hβi⟩
  have hαpos : 0 < α i := by omega
  have hβpos : 0 < β i := by omega
  have hαeq := prop21_minGen_coordinate_eq_weight (K := K) hJ hd hdiag hα hαpos
  have hβeq := prop21_minGen_coordinate_eq_weight (K := K) hJ hd hdiag hβ hβpos
  omega

/-- The canonical squarefree ideal generated by supports of minimal monomial generators. -/
noncomputable def prop21_supportSqRoot (I : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial σ K) :=
  monomialIdeal (characteristicExp '' supportComplex I)

/-- The canonical support ideal is squarefree by construction. -/
theorem prop21_supportSqRoot_isSquarefree {I : Ideal (MvPolynomial σ K)} :
    IsSquarefreeMonomialIdeal (prop21_supportSqRoot I) :=
  ⟨supportComplex I, rfl⟩

/-- Any squarefree diagonal root equals the canonical support ideal; hence the root is unique. -/
theorem prop21_sqRoot_eq_supportSqRoot [Fintype σ]
    {I J : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hJ : IsSquarefreeMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hdiag : diagonal d J = I) : J = prop21_supportSqRoot I := by
  classical
  rcases hJ with ⟨H, hJrep⟩
  have hJmono : IsMonomialIdeal J := ⟨characteristicExp '' H, hJrep⟩
  have hchar_mem {u : σ →₀ ℕ} (hu : u ∈ minGens I) :
      (monomial (characteristicExp u.support) (1 : K) : MvPolynomial σ K) ∈ J := by
    have huI : (monomial u (1 : K) : MvPolynomial σ K) ∈ I := (mem_minGens.mp hu).1
    have hudiag : (monomial u (1 : K) : MvPolynomial σ K) ∈ diagonal d J := by
      rw [hdiag]
      exact huI
    have hfloorJ := (monomial_mem_diagonal (K := K) hJmono hd).mp hudiag
    have hfloorEq : floorDiv d u = characteristicExp u.support := by
      ext i
      by_cases hi : 0 < u i
      · have hisupp : i ∈ u.support := Finsupp.mem_support_iff.mpr (by omega)
        have hui := prop21_minGen_coordinate_eq_weight (K := K)
          ⟨H, hJrep⟩ hd hdiag hu hi
        simp [floorDiv_apply, characteristicExp_apply, hisupp, hui, Nat.div_self (hd i)]
      · have hzero : u i = 0 := by omega
        have hnsupp : i ∉ u.support := by simpa [Finsupp.mem_support_iff] using hi
        simp [floorDiv_apply, characteristicExp_apply, hnsupp, hzero]
    simpa [hfloorEq] using hfloorJ
  apply le_antisymm
  · rw [hJrep, prop21_supportSqRoot]
    refine monomialIdeal_le_iff.mpr ?_
    intro e he
    rcases he with ⟨s, hs, hse⟩
    rcases hs with ⟨B, hBH, rfl⟩
    let z : σ →₀ ℕ := diagExp d (characteristicExp B)
    have hzDiag : (monomial z (1 : K) : MvPolynomial σ K) ∈ diagonal d J := by
      rw [hJrep, diagonal_monomialIdeal]
      exact monomial_mem_monomialIdeal.mpr
        ⟨z, ⟨characteristicExp B, ⟨B, hBH, rfl⟩, rfl⟩, le_rfl⟩
    have hzI : (monomial z (1 : K) : MvPolynomial σ K) ∈ I := by
      rw [← hdiag]
      exact hzDiag
    obtain ⟨u, hu, huz⟩ := exists_minGens_le hzI
    have hsupp : u.support ⊆ B := by
      intro t ht
      have hupos : 0 < u t := by
        have hnz := Finsupp.mem_support_iff.mp ht
        omega
      have hut := prop21_minGen_coordinate_eq_weight (K := K)
        ⟨H, hJrep⟩ hd hdiag hu hupos
      by_contra htB
      have hzt : z t = 0 := by simp [z, characteristicExp_apply, htB]
      have hle := huz t
      omega
    have hcharle : characteristicExp u.support ≤ characteristicExp B := by
      intro t
      by_cases ht : t ∈ u.support
      · have := hsupp ht
        simp [characteristicExp_apply, ht, this]
      · simp [characteristicExp_apply, ht]
    exact ⟨characteristicExp u.support,
      ⟨u.support, ⟨u, hu, rfl⟩, rfl⟩, le_trans hcharle hse⟩
  · rw [hJrep, prop21_supportSqRoot]
    refine monomialIdeal_le_iff.mpr ?_
    intro e he
    rcases he with ⟨s, hs, hse⟩
    rcases hs with ⟨F, hF, rfl⟩
    change ∃ u ∈ minGens I, u.support = F at hF
    rcases hF with ⟨u, hu, hsupp⟩
    subst F
    have hmemR : (monomial (characteristicExp u.support) (1 : K) : MvPolynomial σ K) ∈
        (monomialIdeal (characteristicExp '' H) : Ideal (MvPolynomial σ K)) := by
      rw [← hJrep]
      exact hchar_mem hu
    rcases monomial_mem_monomialIdeal.mp hmemR with ⟨r, hrH, hrle⟩
    exact ⟨r, hrH, le_trans hrle hse⟩

/-- The squarefree diagonal root is unique, even when the displayed squarefree generators are not trimmed. -/
theorem prop21_sqRoot_unique [Fintype σ]
    {I J₁ J₂ : Ideal (MvPolynomial σ K)} {d₁ d₂ : σ → ℕ}
    (hJ₁ : IsSquarefreeMonomialIdeal J₁) (hd₁ : ∀ i, 0 < d₁ i)
    (hdiag₁ : diagonal d₁ J₁ = I)
    (hJ₂ : IsSquarefreeMonomialIdeal J₂) (hd₂ : ∀ i, 0 < d₂ i)
    (hdiag₂ : diagonal d₂ J₂ = I) : J₁ = J₂ :=
  (prop21_sqRoot_eq_supportSqRoot hJ₁ hd₁ hdiag₁).trans
    (prop21_sqRoot_eq_supportSqRoot hJ₂ hd₂ hdiag₂).symm

/-- Proposition 2.1, direction (ii) implies (i), with an explicit decomposition witness. -/
theorem prop21_hasSqRoot_of_generatorExponents_subsingleton [Fintype σ]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hcoh : ∀ i, (generatorExponents I i).Subsingleton) :
    HasSqRoot I := by
  classical
  let d : σ → ℕ := fun i ↦
    if hi : (generatorExponents I i).Nonempty then Classical.choose hi else 1
  have hdmem (i : σ) (hi : (generatorExponents I i).Nonempty) :
      d i ∈ generatorExponents I i := by
    simpa [d, hi] using (Classical.choose_spec hi)
  have hdpos : ∀ i, 0 < d i := by
    intro i
    by_cases hi : (generatorExponents I i).Nonempty
    · exact (hdmem i hi).1
    · simp [d, hi]
  have hdcommon {i : σ} {u : σ →₀ ℕ} (hu : u ∈ minGens I) (hi : 0 < u i) :
      d i = u i := by
    have hnonempty : (generatorExponents I i).Nonempty := ⟨u i, hi, u, hu, rfl⟩
    exact hcoh i (hdmem i hnonempty) ⟨hi, u, hu, rfl⟩
  have hdiagchar {u : σ →₀ ℕ} (hu : u ∈ minGens I) :
      diagExp d (characteristicExp u.support) = u := by
    ext i
    by_cases hisupp : i ∈ u.support
    · have hnz : u i ≠ 0 := Finsupp.mem_support_iff.mp hisupp
      have hi : 0 < u i := by omega
      have hdi := hdcommon hu hi
      simp [diagExp_apply, characteristicExp_apply, hisupp, hdi]
    · have hzero : u i = 0 := by simpa [Finsupp.mem_support_iff] using hisupp
      simp [diagExp_apply, characteristicExp_apply, hisupp, hzero]
  let H : Set (Finset σ) := supportComplex I
  let J : Ideal (MvPolynomial σ K) := monomialIdeal (characteristicExp '' H)
  refine ⟨J, d, ?_, hdpos, ?_⟩
  · exact ⟨H, rfl⟩
  · dsimp [J]
    rw [diagonal_monomialIdeal]
    apply le_antisymm
    · rw [monomialIdeal, Ideal.span_le]
      rintro y ⟨z, hz, rfl⟩
      rcases hz with ⟨s, hs, rfl⟩
      rcases hs with ⟨F, hF, rfl⟩
      dsimp [H, supportComplex] at hF
      rcases hF with ⟨u, hu, hsupp⟩
      subst F
      rw [hdiagchar hu]
      exact (mem_minGens.mp hu).1
    · intro x hxI
      rw [monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image]
      intro e he
      have heI := prop21_monomial_mem_of_mem_components hI hxI he
      obtain ⟨u, hu, hue⟩ := exists_minGens_le heI
      refine ⟨diagExp d (characteristicExp u.support), ?_, ?_⟩
      · refine ⟨characteristicExp u.support, ⟨u.support, ?_, rfl⟩, rfl⟩
        change ∃ v ∈ minGens I, v.support = u.support
        exact ⟨u, hu, rfl⟩
      · simpa [hdiagchar hu] using hue

/-- Proposition 2.1, equivalence of (i) and (ii). -/
theorem prop21_hasSqRoot_iff_generatorExponents_subsingleton [Fintype σ]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) :
    HasSqRoot I ↔ ∀ i, (generatorExponents I i).Subsingleton :=
  ⟨prop21_generatorExponents_subsingleton_of_hasSqRoot,
    prop21_hasSqRoot_of_generatorExponents_subsingleton hI⟩

/-- Proposition 2.1, equivalence of (i) and (iii). -/
theorem prop21_hasSqRoot_iff_componentExponents_subsingleton [Fintype σ]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hIrr : IsIrredundant (K := K) A a) :
    HasSqRoot I ↔ ∀ i, (componentExponents A a i).Subsingleton := by
  constructor
  · intro hroot i
    have hgen := (prop21_hasSqRoot_iff_generatorExponents_subsingleton hI).mp hroot i
    rw [← prop21_generatorExponents_eq_componentExponents hI hIrr i]
    exact hgen
  · intro hcoh
    apply (prop21_hasSqRoot_iff_generatorExponents_subsingleton hI).mpr
    intro i
    rw [prop21_generatorExponents_eq_componentExponents hI hIrr i]
    exact hcoh i

/-- Proposition 2.1, equivalence of (i) and (iv). -/
theorem prop21_hasSqRoot_iff_mismatchPairs_eq_empty [Fintype σ]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hIrr : IsIrredundant (K := K) A a) :
    HasSqRoot I ↔ mismatchPairs A a = ∅ :=
  (prop21_hasSqRoot_iff_componentExponents_subsingleton hI hIrr).trans
    prop21_componentExponents_subsingleton_iff_mismatchPairs_eq_empty

/-- Coherent occurrence exponents make an irredundant component family an antichain. -/
theorem prop21_supportsAntichain_of_componentExponents_subsingleton
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hIrr : IsIrredundant (K := K) A a)
    (hcoh : ∀ i, (componentExponents A a i).Subsingleton) :
    SupportsAntichain A a := by
  classical
  intro j k hsubset
  by_contra hjk
  have hQle : (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) ≤
      purePower (A k) (a k) := by
    unfold purePower
    refine monomialIdeal_le_iff.mpr ?_
    intro e he
    rcases he with ⟨u, ⟨t, htA, rfl⟩, hue⟩
    have hak : a j t = a k t := hcoh t ⟨j, htA, rfl⟩ ⟨k, hsubset htA, rfl⟩
    refine ⟨Finsupp.single t (a k t), ⟨t, hsubset htA, rfl⟩, ?_⟩
    apply Finsupp.single_le_iff.mpr
    have := Finsupp.single_le_iff.mp hue
    simpa [← hak] using this
  apply hIrr k
  intro x hxomit
  have hxinf : x ∈
      (⨅ h : {h : ι // h ≠ k},
        (purePower (A h.1) (a h.1) : Ideal (MvPolynomial σ K))) := by
    simpa [decompOmit] using hxomit
  exact hQle (Ideal.mem_iInf.mp hxinf ⟨j, hjk⟩)

/-- An antichain of component supports gives an irredundant intersection of variable primes. -/
theorem prop21_isIrredundant_primeOf_of_supportsAntichain [Fintype ι]
    {A : ι → Finset σ} (hanti : SupportsAntichain A (fun _ _ => 1)) :
    IsIrredundant (K := K) A (fun _ _ => (1 : ℕ)) := by
  classical
  intro j
  have hex : ∀ k, k ≠ j → ∃ i, i ∈ A k ∧ i ∉ A j := by
    intro k hk
    by_contra hno
    push Not at hno
    apply hk
    apply hanti k j
    intro i hi
    exact hno i hi
  choose pick hpick using hex
  let T : Finset σ :=
    Finset.univ.image (fun k : {k : ι // k ≠ j} => pick k.1 k.2)
  have hTdisj : ∀ i ∈ T, i ∉ A j := by
    intro i hiT
    rcases Finset.mem_image.mp hiT with ⟨k, hk, rfl⟩
    exact (hpick k.1 k.2).2
  have heomit : (monomial (characteristicExp T) (1 : K) : MvPolynomial σ K) ∈
      decompOmit A (fun _ _ => (1 : ℕ)) j := by
    rw [decompOmit]
    refine Ideal.mem_iInf.mpr ?_
    intro k
    have hmemT : pick k.1 k.2 ∈ T := by
      exact Finset.mem_image.mpr ⟨k, by simp, rfl⟩
    exact monomial_mem_purePower.mpr ⟨pick k.1 k.2, (hpick k.1 k.2).1,
      by simp [characteristicExp_apply, hmemT]⟩
  have henot : (monomial (characteristicExp T) (1 : K) : MvPolynomial σ K) ∉
      purePower (A j) (fun _ => (1 : ℕ)) := by
    intro he
    rcases monomial_mem_purePower.mp he with ⟨i, hiA, hi⟩
    have hiT : i ∈ T := by
      by_contra hiT
      have hzero : characteristicExp T i = 0 := by simp [characteristicExp_apply, hiT]
      omega
    exact (hTdisj i hiT) hiA
  intro hle
  exact henot (hle heomit)

/-- Under diagonal representability the component radicals are an antichain. -/
theorem prop21_supportsAntichain_of_hasSqRoot [Fintype σ]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hIrr : IsIrredundant (K := K) A a)
    (hroot : HasSqRoot I) : SupportsAntichain A a :=
  prop21_supportsAntichain_of_componentExponents_subsingleton hIrr
    ((prop21_hasSqRoot_iff_componentExponents_subsingleton hI hIrr).mp hroot)

/-- Under diagonal representability the intersection of component radicals is irredundant. -/
theorem prop21_isIrredundant_primeOf_of_hasSqRoot [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hIrr : IsIrredundant (K := K) A a)
    (hroot : HasSqRoot I) : IsIrredundant (K := K) A (fun _ _ => (1 : ℕ)) := by
  apply prop21_isIrredundant_primeOf_of_supportsAntichain
  exact prop21_supportsAntichain_of_hasSqRoot (a := a) hI hIrr hroot

/-- For a finite irredundant decomposition, the canonical support ideal is the prime intersection. -/
theorem prop21_supportSqRoot_eq_iInf_primeOf [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hIrr : IsIrredundant (K := K) A a) :
    prop21_supportSqRoot I = ⨅ j, (primeOf (A j) : Ideal (MvPolynomial σ K)) := by
  classical
  have ha : ∀ j i, i ∈ A j → 0 < a j i :=
    fun j i hi ↦ prop21_componentExponent_pos_of_irredundant hIrr hi
  apply le_antisymm
  · rw [prop21_supportSqRoot, monomialIdeal, Ideal.span_le]
    rintro y ⟨z, hz, rfl⟩
    rcases hz with ⟨F, hF, rfl⟩
    change ∃ u ∈ minGens I, u.support = F at hF
    rcases hF with ⟨u, hu, huF⟩
    subst F
    refine Ideal.mem_iInf.mpr ?_
    intro j
    have huinf : (monomial u (1 : K) : MvPolynomial σ K) ∈
        (⨅ h, (purePower (A h) (a h) : Ideal (MvPolynomial σ K))) := by
      rw [← hI]
      exact (mem_minGens.mp hu).1
    rcases monomial_mem_purePower.mp (Ideal.mem_iInf.mp huinf j) with ⟨t, htA, hat⟩
    have hupos : 0 < u t := by
      have hpost := ha j t htA
      omega
    have hsupp : t ∈ u.support := Finsupp.mem_support_iff.mpr (by omega)
    exact monomial_mem_primeOf.mpr ⟨t, htA, by simp [characteristicExp_apply, hsupp]⟩
  · intro x hxInf
    rw [prop21_supportSqRoot, monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image]
    intro e he
    have heInf : (monomial e (1 : K) : MvPolynomial σ K) ∈
        (⨅ j, (primeOf (A j) : Ideal (MvPolynomial σ K))) := by
      refine Ideal.mem_iInf.mpr ?_
      intro j
      exact prop21_monomial_mem_of_mem_purePower
        (by simpa [primeOf] using (Ideal.mem_iInf.mp hxInf j)) he
    let b : σ →₀ ℕ := Finsupp.onFinset e.support
      (fun t ↦ if e t = 0 then 0 else Finset.univ.sup (fun j ↦ a j t)) (by
        intro t ht
        by_contra hnot
        have hzero : e t = 0 := by simpa [Finsupp.mem_support_iff] using hnot
        exact ht (by simp [hzero]))
    have hbcomponents : ∀ j, (monomial b (1 : K) : MvPolynomial σ K) ∈
        (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) := by
      intro j
      rcases monomial_mem_primeOf.mp (Ideal.mem_iInf.mp heInf j) with ⟨t, htA, hte⟩
      have htsupp : t ∈ e.support := Finsupp.mem_support_iff.mpr (by omega)
      have hat : a j t ≤ b t := by
        have hle : a j t ≤ Finset.univ.sup (fun j ↦ a j t) :=
          Finset.le_sup (s := Finset.univ) (f := fun j ↦ a j t) (by simp)
        have hene : e t ≠ 0 := by omega
        simpa [b, hene] using hle
      exact monomial_mem_purePower.mpr ⟨t, htA, hat⟩
    have hbI : (monomial b (1 : K) : MvPolynomial σ K) ∈ I := by
      rw [hI]
      exact Ideal.mem_iInf.mpr hbcomponents
    obtain ⟨u, hu, hub⟩ := exists_minGens_le hbI
    have hsupp : u.support ⊆ e.support := by
      intro t ht
      have hupos : 0 < u t := by
        have hnz := Finsupp.mem_support_iff.mp ht
        omega
      have hle := hub t
      by_contra hte
      have hzero : e t = 0 := by simpa [Finsupp.mem_support_iff] using hte
      have hbt : b t = 0 := by simp [b, hzero]
      omega
    have hcharle : characteristicExp u.support ≤ e := by
      intro t
      by_cases ht : t ∈ u.support
      · have hte := hsupp ht
        have hone : 1 ≤ e t := by
          have hnz := Finsupp.mem_support_iff.mp hte
          omega
        simpa [characteristicExp_apply, ht] using hone
      · simp [characteristicExp_apply, ht]
    exact ⟨characteristicExp u.support, ⟨u.support, ⟨u, hu, rfl⟩, rfl⟩, hcharle⟩

/-- Weights on unused variables are arbitrary: only positive occurrence exponents are constrained. -/
theorem prop21_diagonal_supportSqRoot_eq_of_forcedWeights [Fintype σ]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} {d : σ → ℕ}
    (hI : HasComponents I A a)
    (hforced : ∀ {u : σ →₀ ℕ} {i : σ}, u ∈ minGens I → 0 < u i → u i = d i) :
    diagonal d (prop21_supportSqRoot I) = I := by
  have hdiagchar {u : σ →₀ ℕ} (hu : u ∈ minGens I) :
      diagExp d (characteristicExp u.support) = u := by
    ext i
    by_cases hisupp : i ∈ u.support
    · have hnz : u i ≠ 0 := Finsupp.mem_support_iff.mp hisupp
      have hi : 0 < u i := by omega
      have hui := hforced hu hi
      simp [diagExp_apply, characteristicExp_apply, hisupp, hui]
    · have hzero : u i = 0 := by simpa [Finsupp.mem_support_iff] using hisupp
      simp [diagExp_apply, characteristicExp_apply, hisupp, hzero]
  rw [prop21_supportSqRoot, diagonal_monomialIdeal]
  apply le_antisymm
  · rw [monomialIdeal, Ideal.span_le]
    rintro y ⟨z, hz, rfl⟩
    rcases hz with ⟨s, hs, rfl⟩
    rcases hs with ⟨F, hF, rfl⟩
    change ∃ u ∈ minGens I, u.support = F at hF
    rcases hF with ⟨u, hu, hsupp⟩
    subst F
    rw [hdiagchar hu]
    exact (mem_minGens.mp hu).1
  · intro x hxI
    rw [monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image]
    intro e he
    have heI := prop21_monomial_mem_of_mem_components hI hxI he
    obtain ⟨u, hu, hue⟩ := exists_minGens_le heI
    refine ⟨diagExp d (characteristicExp u.support), ?_, ?_⟩
    · refine ⟨characteristicExp u.support, ⟨u.support, ?_, rfl⟩, rfl⟩
      change ∃ v ∈ minGens I, v.support = u.support
      exact ⟨u, hu, rfl⟩
    · simpa [hdiagchar hu] using hue

/-- Packaging of the weight freedom: any positive weights agreeing on used variables give a root. -/
theorem prop21_hasSqRoot_of_forcedWeights [Fintype σ]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} {d : σ → ℕ}
    (hI : HasComponents I A a) (hd : ∀ i, 0 < d i)
    (hforced : ∀ {u : σ →₀ ℕ} {i : σ}, u ∈ minGens I → 0 < u i → u i = d i) :
    HasSqRoot I :=
  ⟨prop21_supportSqRoot I, d, prop21_supportSqRoot_isSquarefree, hd,
    prop21_diagonal_supportSqRoot_eq_of_forcedWeights hI hforced⟩

/-- Thus any squarefree diagonal root is the irredundant prime intersection. -/
theorem prop21_sqRoot_eq_iInf_primeOf [Fintype σ] [Fintype ι]
    {I J : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    {d : σ → ℕ} (hI : HasComponents I A a)
    (hIrr : IsIrredundant (K := K) A a)
    (hJ : IsSquarefreeMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hdiag : diagonal d J = I) :
    J = ⨅ j, (primeOf (A j) : Ideal (MvPolynomial σ K)) :=
  (prop21_sqRoot_eq_supportSqRoot hJ hd hdiag).trans
    (prop21_supportSqRoot_eq_iInf_primeOf hI hIrr)

/--
The identification with the radical uses the standard radical formula
\((\bigcap_j Q_j)^{\mathrm{rad}}=\bigcap_j P_j\) as an explicit hypothesis.
The latter is not part of the shared algebra API and is separate from Eq. (2).
-/
theorem prop21_sqRoot_eq_radical_of_componentRadical [Fintype σ] [Fintype ι]
    {I J : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    {d : σ → ℕ} (hI : HasComponents I A a)
    (hIrr : IsIrredundant (K := K) A a)
    (hrad : I.radical = ⨅ j, (primeOf (A j) : Ideal (MvPolynomial σ K)))
    (hJ : IsSquarefreeMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hdiag : diagonal d J = I) : J = I.radical :=
  (prop21_sqRoot_eq_iInf_primeOf hI hIrr hJ hd hdiag).trans hrad.symm

/-- A polynomial outside a monomial ideal has a support monomial outside that ideal. -/
theorem prop21_exists_monomial_not_mem_of_not_mem_purePower
    {A : Finset σ} {a : σ → ℕ} {x : MvPolynomial σ K}
    (hx : x ∉ (purePower A a : Ideal (MvPolynomial σ K))) :
    ∃ e ∈ x.support, (monomial e (1 : K) : MvPolynomial σ K) ∉ purePower A a := by
  classical
  by_contra h
  push Not at h
  apply hx
  rw [purePower] at h
  rw [purePower, mem_monomialIdeal]
  intro e he
  exact monomial_mem_monomialIdeal.mp (h e he)

/-- A pure-power component with positive exponents is primary. -/
theorem prop21_purePower_isPrimary [Fintype σ]
    {A : Finset σ} {a : σ → ℕ} (ha : ∀ i ∈ A, 0 < a i) :
    (purePower A a : Ideal (MvPolynomial σ K)).IsPrimary := by
  classical
  let : LinearOrder σ :=
    LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have hne : (purePower A a : Ideal (MvPolynomial σ K)) ≠ ⊤ := by
    intro htop
    have hone : (1 : MvPolynomial σ K) ∈ purePower A a := by
      rw [htop]
      trivial
    have hm : (monomial (0 : σ →₀ ℕ) (1 : K) : MvPolynomial σ K) ∈ purePower A a := by
      simpa using hone
    rcases monomial_mem_purePower.mp hm with ⟨i, hi, hai⟩
    have hai_zero : a i = 0 := by simpa using hai
    have hai_pos := ha i hi
    omega
  rw [Ideal.isPrimary_iff]
  refine ⟨hne, ?_⟩
  intro x y hxy
  by_cases hx : x ∈ (purePower A a : Ideal (MvPolynomial σ K))
  · exact Or.inl hx
  by_cases hy : y ∈ (purePower A a : Ideal (MvPolynomial σ K)).radical
  · exact Or.inr hy
  exfalso
  have hrad : (purePower A a : Ideal (MvPolynomial σ K)).radical = primeOf A :=
    purePower_radical_eq_primeOf (K := K) ha
  have hyP : y ∉ (primeOf A : Ideal (MvPolynomial σ K)) := by
    intro hy'
    exact hy (by simpa [hrad] using hy')
  have hyPure : y ∉ (purePower A (fun _ => (1 : ℕ)) : Ideal (MvPolynomial σ K)) := by
    simpa [primeOf] using hyP
  obtain ⟨finit, hfinitsupp, hfinitnotPure⟩ :=
    prop21_exists_monomial_not_mem_of_not_mem_purePower hyPure
  obtain ⟨einit, heinitsupp, heinitnot⟩ :=
    prop21_exists_monomial_not_mem_of_not_mem_purePower hx
  let F : Finset (σ →₀ ℕ) := y.support.filter fun e ↦
    (monomial e (1 : K) : MvPolynomial σ K) ∉ primeOf A
  have hFne : F.Nonempty := by
    refine ⟨finit, ?_⟩
    have hfinitnotP : (monomial finit (1 : K) : MvPolynomial σ K) ∉ primeOf A := by
      simpa [primeOf] using hfinitnotPure
    simp [F, hfinitsupp, hfinitnotP]
  obtain ⟨f, hfF, hfLexMin⟩ :=
    Finset.exists_min_image F (fun e ↦ (toLex e : Lex (σ →₀ ℕ))) hFne
  have hfsupp : f ∈ y.support := (Finset.mem_filter.mp hfF).1
  have hfnotP : (monomial f (1 : K) : MvPolynomial σ K) ∉ primeOf A :=
    (Finset.mem_filter.mp hfF).2
  let E : Finset (σ →₀ ℕ) := x.support.filter fun e ↦
    (monomial e (1 : K) : MvPolynomial σ K) ∉ purePower A a
  have hEne : E.Nonempty := ⟨einit, by simp [E, heinitsupp, heinitnot]⟩
  let wt : (σ →₀ ℕ) → ℕ := fun e ↦ ∑ i ∈ A, e i
  obtain ⟨ebase, hbaseE, hbaseMin⟩ := Finset.exists_min_image E wt hEne
  let E₁ : Finset (σ →₀ ℕ) := E.filter fun e ↦ wt e = wt ebase
  have hbaseE₁ : ebase ∈ E₁ := by simp [E₁, hbaseE]
  obtain ⟨e, heE₁, heLexMin⟩ :=
    Finset.exists_min_image E₁ (fun e ↦ (toLex e : Lex (σ →₀ ℕ))) ⟨ebase, hbaseE₁⟩
  have heE : e ∈ E := (Finset.mem_filter.mp heE₁).1
  have hewt : wt e = wt ebase := (Finset.mem_filter.mp heE₁).2
  have hesupp : e ∈ x.support := (Finset.mem_filter.mp heE).1
  have henatQ : (monomial e (1 : K) : MvPolynomial σ K) ∉ purePower A a :=
    (Finset.mem_filter.mp heE).2
  have heA (i : σ) (hi : i ∈ A) : ¬ a i ≤ e i := by
    intro hai
    exact henatQ (monomial_mem_purePower.mpr ⟨i, hi, hai⟩)
  have hfA (i : σ) (hi : i ∈ A) : f i = 0 := by
    by_contra hfi
    apply hfnotP
    exact monomial_mem_primeOf.mpr ⟨i, hi, by omega⟩
  have hunique {u v : σ →₀ ℕ} (husupp : u ∈ x.support) (hvsupp : v ∈ y.support)
      (hadd : u + v = e + f) : u = e ∧ v = f := by
    have huA (i : σ) (hi : i ∈ A) : ¬ a i ≤ u i := by
      intro hau
      have hcoord : u i + v i = e i + f i := by
        simpa using congrArg (fun z : σ →₀ ℕ ↦ z i) hadd
      have : a i ≤ e i + f i := by omega
      exact heA i hi (by simpa [hfA i hi] using this)
    have huE : u ∈ E := by
      have hunotQ : (monomial u (1 : K) : MvPolynomial σ K) ∉ purePower A a := by
        intro huQ
        rcases monomial_mem_purePower.mp huQ with ⟨i, hi, hau⟩
        exact huA i hi hau
      simp [E, husupp, hunotQ]
    have huAe (i : σ) (hi : i ∈ A) : u i ≤ e i := by
      have hcoord : u i + v i = e i + f i := by
        simpa using congrArg (fun z : σ →₀ ℕ ↦ z i) hadd
      have hf0 : f i = 0 := hfA i hi
      omega
    have hwtle : wt u ≤ wt e := by
      unfold wt
      exact Finset.sum_le_sum huAe
    have hwteq : wt u = wt e := by
      have hb := hbaseMin u huE
      omega
    have huAeq (i : σ) (hi : i ∈ A) : u i = e i := by
      by_contra hneCoord
      have hstrict : u i < e i := lt_of_le_of_ne (huAe i hi) hneCoord
      have hlt : wt u < wt e := by
        unfold wt
        exact Finset.sum_lt_sum huAe ⟨i, hi, hstrict⟩
      omega
    have hvA (i : σ) (hi : i ∈ A) : v i = 0 := by
      have hcoord : u i + v i = e i + f i := by
        simpa using congrArg (fun z : σ →₀ ℕ ↦ z i) hadd
      have hf0 : f i = 0 := hfA i hi
      have hue : u i = e i := huAeq i hi
      omega
    have hvnotP : (monomial v (1 : K) : MvPolynomial σ K) ∉ primeOf A := by
      intro hvQ
      rcases monomial_mem_primeOf.mp hvQ with ⟨i, hi, hvi⟩
      have hv0 := hvA i hi
      omega
    have hvF : v ∈ F := by simp [F, hvsupp, hvnotP]
    have huE₁ : u ∈ E₁ := by simp [E₁, huE, hewt, hwteq]
    have hEq : u = e := by
      by_contra hneue
      have hnelex : (toLex u : Lex (σ →₀ ℕ)) ≠ toLex e := by
        intro hlex
        exact hneue (toLex.injective hlex)
      rcases lt_or_gt_of_ne hnelex with hult | heult
      · exact (lt_irrefl (toLex u))
          (lt_of_lt_of_le hult (heLexMin u huE₁))
      · have hlexsum : (toLex u : Lex (σ →₀ ℕ)) + toLex v =
            toLex e + toLex f := by
          change toLex (u + v) = toLex (e + f)
          exact congrArg toLex hadd
        have hsumlt : toLex e + toLex v < toLex u + toLex v := by
          simpa [add_comm] using add_lt_add_right heult (toLex v)
        have hsumlt' : toLex e + toLex v < toLex e + toLex f := by
          simpa [hlexsum] using hsumlt
        have hvltf : toLex v < toLex f :=
          (add_lt_add_iff_left (toLex e : Lex (σ →₀ ℕ))).mp hsumlt'
        exact (lt_irrefl (toLex v)) (lt_of_lt_of_le hvltf (hfLexMin v hvF))
    subst u
    have hvEq : v = f := by
      exact add_left_cancel hadd
    exact ⟨rfl, hvEq⟩
  have hcoeff : coeff (e + f) (x * y) = coeff e x * coeff f y := by
    rw [MvPolynomial.coeff_mul]
    refine Finset.sum_eq_single (e, f) ?_ ?_
    · intro b hb hneb
      have hadd : b.1 + b.2 = e + f :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hb
      by_cases hb1 : b.1 ∈ x.support
      · by_cases hb2 : b.2 ∈ y.support
        · have hbEq := hunique hb1 hb2 hadd
          exact (hneb (Prod.ext hbEq.1 hbEq.2)).elim
        · have hz : coeff b.2 y = 0 := by
            simpa [MvPolynomial.mem_support_iff] using hb2
          simp [hz]
      · have hz : coeff b.1 x = 0 := by
          simpa [MvPolynomial.mem_support_iff] using hb1
        simp [hz]
    · intro hnot
      exact (hnot (by simp)).elim
  have hxcoeff : coeff e x ≠ 0 := by
    simpa [MvPolynomial.mem_support_iff] using hesupp
  have hycoeff : coeff f y ≠ 0 := by
    simpa [MvPolynomial.mem_support_iff] using hfsupp
  have hprodsupp : e + f ∈ (x * y).support := by
    rw [MvPolynomial.mem_support_iff, hcoeff]
    exact mul_ne_zero hxcoeff hycoeff
  have hprodmem := prop21_monomial_mem_of_mem_purePower hxy hprodsupp
  rcases monomial_mem_purePower.mp hprodmem with ⟨i, hi, hai⟩
  exact heA i hi (by simpa [hfA i hi] using hai)

omit [DecidableEq σ] in
/-- Mathlib's submodule and quotient conventions for associated primes agree for ideals. -/
theorem prop21_associatedPrimes_quotient_eq_submodule {I : Ideal (MvPolynomial σ K)} :
    associatedPrimes (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ I) = I.associatedPrimes := by
  ext P
  constructor
  · intro h
    rcases h with ⟨hP, z, hz⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨hP, x, ?_⟩
    have hc : (⊥ : Submodule (MvPolynomial σ K)
          (MvPolynomial σ K ⧸ I)).colon {Ideal.Quotient.mk I x} =
        (I : Submodule (MvPolynomial σ K) (MvPolynomial σ K)).colon {x} := by
      ext r
      rw [Submodule.mem_colon_singleton, Submodule.mem_colon_singleton]
      change Ideal.Quotient.mk I r * Ideal.Quotient.mk I x = 0 ↔ r * x ∈ I
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem
    simpa [hc] using hz
  · intro h
    rcases h with ⟨hP, x, hx⟩
    refine ⟨hP, Ideal.Quotient.mk I x, ?_⟩
    have hc : (⊥ : Submodule (MvPolynomial σ K)
          (MvPolynomial σ K ⧸ I)).colon {Ideal.Quotient.mk I x} =
        (I : Submodule (MvPolynomial σ K) (MvPolynomial σ K)).colon {x} := by
      ext r
      rw [Submodule.mem_colon_singleton, Submodule.mem_colon_singleton]
      change Ideal.Quotient.mk I r * Ideal.Quotient.mk I x = 0 ↔ r * x ∈ I
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem
    simpa [hc] using hx

/-- An irredundant decomposition whose radicals form an antichain has exactly the displayed
associated primes. -/
theorem prop21_submoduleAssociatedPrimes_eq_range_of_supportsAntichain
    [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hIrr : IsIrredundant (K := K) A a)
    (hanti : SupportsAntichain A a) :
    I.associatedPrimes = Set.range (fun j ↦ (primeOf (A j) : Ideal (MvPolynomial σ K))) := by
  classical
  have ha : ∀ j i, i ∈ A j → 0 < a j i := by
    intro j i hi
    exact prop21_componentExponent_pos_of_irredundant hIrr hi
  let Q : ι → Ideal (MvPolynomial σ K) := fun j ↦ purePower (A j) (a j)
  let t : Finset (Ideal (MvPolynomial σ K)) := Finset.univ.image Q
  have htinf : t.inf id = I := by
    calc
      t.inf id = ⨅ j, Q j := by
        rw [show t = Finset.univ.image Q from rfl, Finset.inf_image]
        exact Finset.inf_univ_eq_iInf Q
      _ = I := by simpa [Q] using hI.symm
  have ht : Submodule.IsMinimalPrimaryDecomposition I t := by
    refine ⟨htinf, ?_, ?_, ?_⟩
    · intro J hJ
      change J ∈ Finset.univ.image Q at hJ
      rcases Finset.mem_image.mp hJ with ⟨j, -, rfl⟩
      simpa [Q] using prop21_purePower_isPrimary (K := K) (a := a j) (ha := fun i hi ↦ ha j i hi)
    · intro J hJ K hK hne
      dsimp only [Function.onFun]
      change J ∈ Finset.univ.image Q at hJ
      change K ∈ Finset.univ.image Q at hK
      rcases Finset.mem_image.mp hJ with ⟨j, -, rfl⟩
      rcases Finset.mem_image.mp hK with ⟨k, -, rfl⟩
      intro hrad
      have hjrad := purePower_radical_eq_primeOf (K := K) (a := a j) (fun i hi ↦ ha j i hi)
      have hkrad := purePower_radical_eq_primeOf (K := K) (a := a k) (fun i hi ↦ ha k i hi)
      have hP : (primeOf (A j) : Ideal (MvPolynomial σ K)) = primeOf (A k) := by
        simpa [Q, Submodule.colon_univ, hjrad, hkrad] using hrad
      have hsub : A j ⊆ A k := primeOf_le_iff_subset.mp (le_of_eq hP)
      apply hne
      have hjk : j = k := hanti j k hsub
      simp [Q, hjk]
    · intro J hJ
      change J ∈ Finset.univ.image Q at hJ
      rcases Finset.mem_image.mp hJ with ⟨j, -, rfl⟩
      intro hle
      apply hIrr j
      intro x hxomit
      have hxinf : x ∈
          (⨅ k : {k : ι // k ≠ j}, (purePower (A k.1) (a k.1) :
            Ideal (MvPolynomial σ K))) := by
        simpa [decompOmit] using hxomit
      have hxt : x ∈ (t.erase (Q j)).inf id := by
        rw [Submodule.mem_finsetInf]
        intro L hL
        rcases Finset.mem_erase.mp hL with ⟨hLne, hLt⟩
        change L ∈ Finset.univ.image Q at hLt
        rcases Finset.mem_image.mp hLt with ⟨k, -, hkL⟩
        subst L
        have hkj : k ≠ j := by
          intro hkj
          apply hLne
          simp [Q, hkj]
        simpa [Q] using Ideal.mem_iInf.mp hxinf ⟨k, hkj⟩
      simpa [Q] using hle hxt
  have hAss := ht.image_radical_eq_associated_primes
  rw [← hAss]
  ext P
  constructor
  · rintro ⟨J, hJ, rfl⟩
    change J ∈ Finset.univ.image Q at hJ
    rcases Finset.mem_image.mp hJ with ⟨j, -, rfl⟩
    refine ⟨j, ?_⟩
    simpa [Q, Submodule.colon_univ] using
      (purePower_radical_eq_primeOf (K := K) (a := a j) (fun i hi ↦ ha j i hi)).symm
  · rintro ⟨j, rfl⟩
    refine ⟨Q j, ?_, ?_⟩
    · change Q j ∈ Finset.univ.image Q
      simp
    · simpa [Q, Submodule.colon_univ] using
        (purePower_radical_eq_primeOf (K := K) (a := a j) (fun i hi ↦ ha j i hi))

/-- The paper's quotient convention for associated primes in Proposition 2.1. -/
theorem prop21_associatedPrimes_eq_range_of_supportsAntichain
    [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hIrr : IsIrredundant (K := K) A a)
    (hanti : SupportsAntichain A a) :
    associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) =
      Set.range (fun j ↦ (primeOf (A j) : Ideal (MvPolynomial σ K))) :=
  (prop21_associatedPrimes_quotient_eq_submodule (I := I)).trans
    (prop21_submoduleAssociatedPrimes_eq_range_of_supportsAntichain hI hIrr hanti)

/-- Radical commutation for a finite irredundant pure-power decomposition. -/
theorem prop21_radical_eq_iInf_primeOf [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hIrr : IsIrredundant (K := K) A a) :
    I.radical = ⨅ j, (primeOf (A j) : Ideal (MvPolynomial σ K)) := by
  have ha : ∀ j i, i ∈ A j → 0 < a j i := by
    intro j i hi
    exact prop21_componentExponent_pos_of_irredundant hIrr hi
  rw [hI, radical_iInf_fintype]
  apply iInf_congr
  intro j
  exact purePower_radical_eq_primeOf (K := K) (a := a j) (fun i hi ↦ ha j i hi)

/-- Under an antichain of component radicals, the displayed primes are exactly minimal. -/
theorem prop21_minimalPrimes_eq_range_of_supportsAntichain [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hIrr : IsIrredundant (K := K) A a)
    (hanti : SupportsAntichain A a) :
    I.minimalPrimes = Set.range (fun j ↦ (primeOf (A j) : Ideal (MvPolynomial σ K))) := by
  classical
  have ha : ∀ j i, i ∈ A j → 0 < a j i := by
    intro j i hi
    exact prop21_componentExponent_pos_of_irredundant hIrr hi
  have hrad : I.radical = ⨅ j, (primeOf (A j) : Ideal (MvPolynomial σ K)) :=
    prop21_radical_eq_iInf_primeOf hI hIrr
  have hIleP (j : ι) : I ≤ (primeOf (A j) : Ideal (MvPolynomial σ K)) := by
    rw [hI]
    exact (iInf_le (fun k ↦ (purePower (A k) (a k) : Ideal (MvPolynomial σ K))) j).trans
      (purePower_le_primeOf_of_pos (K := K) (a := a j) (fun i hi ↦ ha j i hi))
  have hEachMin (j : ι) :
      (primeOf (A j) : Ideal (MvPolynomial σ K)) ∈ I.minimalPrimes := by
    change I.IsMinimalPrime (primeOf (A j) : Ideal (MvPolynomial σ K))
    refine ⟨⟨primeOf_isPrime (K := K) (A j), hIleP j⟩, ?_⟩
    intro q hq hqle
    have hradq : I.radical ≤ q := (hq.1.radical_le_iff).2 hq.2
    rw [hrad] at hradq
    have hfin : (Finset.univ.inf fun k ↦ (primeOf (A k) : Ideal (MvPolynomial σ K))) ≤ q := by
      simpa [Finset.inf_univ_eq_iInf] using hradq
    obtain ⟨k, -, hkq⟩ := (Ideal.IsPrime.inf_le' hq.1).mp hfin
    have hsub : A k ⊆ A j := primeOf_le_iff_subset.mp (hkq.trans hqle)
    have hkj : k = j := hanti k j hsub
    simpa [hkj] using hkq
  apply Set.Subset.antisymm
  · intro p hp
    change I.IsMinimalPrime p at hp
    have hpPrime : p.IsPrime := hp.1.1
    have hpI : I ≤ p := hp.1.2
    have hradp : I.radical ≤ p := (hpPrime.radical_le_iff).2 hpI
    rw [hrad] at hradp
    have hfin : (Finset.univ.inf fun k ↦ (primeOf (A k) : Ideal (MvPolynomial σ K))) ≤ p := by
      simpa [Finset.inf_univ_eq_iInf] using hradp
    obtain ⟨j, -, hjp⟩ := (Ideal.IsPrime.inf_le' hpPrime).mp hfin
    refine ⟨j, ?_⟩
    have hj := hEachMin j
    change I.IsMinimalPrime (primeOf (A j) : Ideal (MvPolynomial σ K)) at hj
    exact le_antisymm hjp (hp.2 hj.1 hjp)
  · intro p hp
    rcases hp with ⟨j, rfl⟩
    exact hEachMin j

/-- An antichain of displayed primes excludes embedded associated primes. -/
theorem prop21_associatedPrimes_eq_minimalPrimes_of_supportsAntichain
    [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hIrr : IsIrredundant (K := K) A a)
    (hanti : SupportsAntichain A a) :
    associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) = I.minimalPrimes :=
  (prop21_associatedPrimes_eq_range_of_supportsAntichain hI hIrr hanti).trans
    (prop21_minimalPrimes_eq_range_of_supportsAntichain hI hIrr hanti).symm

/-- Proposition 2.1: a diagonally represented ideal has exactly its displayed component
radicals as associated primes. -/
theorem prop21_associatedPrimes_eq_range_of_hasSqRoot
    [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hIrr : IsIrredundant (K := K) A a)
    (hroot : HasSqRoot I) :
    associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) =
      Set.range (fun j ↦ (primeOf (A j) : Ideal (MvPolynomial σ K))) :=
  prop21_associatedPrimes_eq_range_of_supportsAntichain hI hIrr
    (prop21_supportsAntichain_of_hasSqRoot (K := K) hI hIrr hroot)

/-- Proposition 2.1: a diagonally represented ideal has no embedded primes. -/
theorem prop21_associatedPrimes_eq_minimalPrimes_of_hasSqRoot
    [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hIrr : IsIrredundant (K := K) A a)
    (hroot : HasSqRoot I) :
    associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) = I.minimalPrimes :=
  prop21_associatedPrimes_eq_minimalPrimes_of_supportsAntichain hI hIrr
    (prop21_supportsAntichain_of_hasSqRoot (K := K) hI hIrr hroot)

/-- Proposition 2.1: the unique squarefree root is the radical, unconditionally. -/
theorem prop21_sqRoot_eq_radical [Fintype σ] [Fintype ι]
    {I J : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    {d : σ → ℕ} (hI : HasComponents I A a)
    (hIrr : IsIrredundant (K := K) A a)
    (hJ : IsSquarefreeMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hdiag : diagonal d J = I) : J = I.radical :=
  (prop21_sqRoot_eq_iInf_primeOf hI hIrr hJ hd hdiag).trans
    (prop21_radical_eq_iInf_primeOf hI hIrr).symm

omit [DecidableEq σ] in
/-- Powers of explicitly monomial ideals are monomial. -/
theorem prop21_isMonomialIdeal_pow {I : Ideal (MvPolynomial σ K)}
    (hI : IsMonomialIdeal I) (q : ℕ) : IsMonomialIdeal (I ^ q) := by
  rcases hI with ⟨S, hS⟩
  refine ⟨powGens S q, ?_⟩
  rw [hS, monomialIdeal_pow]

/--
Conditional invariance of normal torsion-freeness under a positive diagonal weighting.
The explicit hypothesis is the standard preservation-of-associated-primes theorem for weighted
monomial ideals, which is not in the shared algebra API.
-/
theorem prop21_NormallyTorsionFree_diagonal_iff
    {J : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hJ : IsSquarefreeMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hAss : ∀ L : Ideal (MvPolynomial σ K), IsMonomialIdeal L →
      (∀ i, 0 < d i) →
      associatedPrimes (MvPolynomial σ K)
          (MvPolynomial σ K ⧸ diagonal d L) =
        associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ L)) :
    prop21NormallyTorsionFree (diagonal d J) ↔ prop21NormallyTorsionFree J := by
  rcases hJ with ⟨H, hJrep⟩
  have hJmono : IsMonomialIdeal J := ⟨characteristicExp '' H, hJrep⟩
  have hpow (q : ℕ) :
      (diagonal d J : Ideal (MvPolynomial σ K)) ^ q = diagonal d (J ^ q) := by
    simpa [diagonal] using (Ideal.map_pow (diagHom (K := K) d) J q).symm
  constructor
  · intro hNT q hq P hPJq
    have hMonoPow : IsMonomialIdeal (J ^ q) := prop21_isMonomialIdeal_pow hJmono q
    have hPAssDiag : P ∈ associatedPrimes (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ diagonal d (J ^ q)) := by
      rw [hAss (J ^ q) hMonoPow hd]
      exact hPJq
    have hPIq : P ∈ associatedPrimes (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ (diagonal d J) ^ q) := by
      rw [hpow q]
      exact hPAssDiag
    have hPI := hNT q hq hPIq
    rw [← hAss J hJmono hd]
    exact hPI
  · intro hNT q hq P hPIq
    have hMonoPow : IsMonomialIdeal (J ^ q) := prop21_isMonomialIdeal_pow hJmono q
    have hPAssDiag : P ∈ associatedPrimes (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ diagonal d (J ^ q)) := by
      rw [hpow q] at hPIq
      exact hPIq
    have hPJq : P ∈ associatedPrimes (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ J ^ q) := by
      rw [← hAss (J ^ q) hMonoPow hd]
      exact hPAssDiag
    have hPJ := hNT q hq hPJq
    rw [hAss J hJmono hd]
    exact hPJ

/-- For a fixed squarefree diagonal root, normal torsion-freeness transfers to and from its
weighted image under the explicit associated-prime preservation hypothesis. Uniqueness of the
root itself is unconditional and is recorded by `prop21_sqRoot_unique`. -/
theorem prop21_NormallyTorsionFree_iff_of_sqRoot
    {I J : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hJ : IsSquarefreeMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hdiag : diagonal d J = I)
    (hAss : ∀ L : Ideal (MvPolynomial σ K), IsMonomialIdeal L →
      (∀ i, 0 < d i) →
      associatedPrimes (MvPolynomial σ K)
          (MvPolynomial σ K ⧸ diagonal d L) =
        associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ L)) :
    prop21NormallyTorsionFree I ↔ prop21NormallyTorsionFree J := by
  rw [← hdiag]
  exact prop21_NormallyTorsionFree_diagonal_iff hJ hd hAss

omit [Field K] [DecidableEq σ] in
/-- Restricting to ordered representatives does not change emptiness of the mismatch pairs. -/
theorem prop21_XI_eq_empty_iff_mismatchPairs_eq_empty [LinearOrder ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ} :
    prop21_XI A a = ∅ ↔ mismatchPairs A a = ∅ := by
  constructor
  · intro hX
    ext p
    constructor
    · intro hp
      rcases p with ⟨k, l⟩
      rcases hp with ⟨i, hki, hli, hne⟩
      by_cases hkl : k = l
      · subst l
        exact (hne rfl).elim
      · rcases lt_or_gt_of_ne hkl with hlt | hgt
        · have hpX : (k, l) ∈ prop21_XI A a :=
            ⟨hlt, ⟨i, hki, hli, hne⟩⟩
          rw [hX] at hpX
          exact hpX
        · have hpX : (l, k) ∈ prop21_XI A a :=
            ⟨hgt, ⟨i, hli, hki, fun heq ↦ hne heq.symm⟩⟩
          rw [hX] at hpX
          exact hpX
    · intro hp
      simp at hp
  · intro hM
    ext p
    constructor
    · intro hp
      rcases hp with ⟨hlt, hpm⟩
      rw [hM] at hpm
      exact hpm
    · intro hp
      simp at hp

/-- Proposition 2.1, equivalence of (i) and the paper's ordered-pair condition (iv). -/
theorem prop21_hasSqRoot_iff_XI_eq_empty [Fintype σ] [LinearOrder ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI : HasComponents I A a) (hIrr : IsIrredundant (K := K) A a) :
    HasSqRoot I ↔ prop21_XI A a = ∅ :=
  (prop21_hasSqRoot_iff_mismatchPairs_eq_empty hI hIrr).trans
    (prop21_XI_eq_empty_iff_mismatchPairs_eq_empty (A := A) (a := a)).symm

/-- In a diagonal representation, a used variable's weight is its component exponent. -/
theorem prop21_weight_eq_componentExponent [Fintype σ]
    {I J : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    {d : σ → ℕ} (hI : HasComponents I A a) (hIrr : IsIrredundant (K := K) A a)
    (hJ : IsSquarefreeMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hdiag : diagonal d J = I) {i : σ} {n : ℕ}
    (hn : n ∈ componentExponents A a i) : n = d i := by
  have hgen : n ∈ generatorExponents I i := by
    rw [prop21_generatorExponents_eq_componentExponents hI hIrr i]
    exact hn
  rcases hgen with ⟨hnpos, u, hu, hui⟩
  have hupos : 0 < u i := by omega
  have hud := prop21_minGen_coordinate_eq_weight (K := K) hJ hd hdiag hu hupos
  omega

/-- Any two diagonal representations have the same weight at each used variable. -/
theorem prop21_weights_eq_on_used [Fintype σ]
    {I J₁ J₂ : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    {d₁ d₂ : σ → ℕ} (hI : HasComponents I A a)
    (hIrr : IsIrredundant (K := K) A a)
    (hJ₁ : IsSquarefreeMonomialIdeal J₁) (hd₁ : ∀ i, 0 < d₁ i)
    (hdiag₁ : diagonal d₁ J₁ = I)
    (hJ₂ : IsSquarefreeMonomialIdeal J₂) (hd₂ : ∀ i, 0 < d₂ i)
    (hdiag₂ : diagonal d₂ J₂ = I) {i : σ}
    (hi : (componentExponents A a i).Nonempty) : d₁ i = d₂ i := by
  rcases hi with ⟨n, hn⟩
  have hnd₁ :=
    prop21_weight_eq_componentExponent (K := K) hI hIrr hJ₁ hd₁ hdiag₁ hn
  have hnd₂ :=
    prop21_weight_eq_componentExponent (K := K) hI hIrr hJ₂ hd₂ hdiag₂ hn
  exact hnd₁.symm.trans hnd₂

/-- Positive weights agreeing with every component occurrence exponent give the radical root;
weights at variables absent from all components are unconstrained. -/
theorem prop21_unusedWeight_diagonal [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    {d : σ → ℕ} (hI : HasComponents I A a)
    (hIrr : IsIrredundant (K := K) A a) (hd : ∀ i, 0 < d i)
    (hforced : ∀ (j : ι) (i : σ), i ∈ A j → a j i = d i) :
    diagonal d (I.radical) = I := by
  have hSupp : diagonal d (prop21_supportSqRoot I) = I := by
    apply prop21_diagonal_supportSqRoot_eq_of_forcedWeights hI
    intro u i hu hui
    rcases prop21_generatorExponents_subset_componentExponents hI i
        ⟨hui, u, hu, rfl⟩ with ⟨j, hji, haji⟩
    exact haji.symm.trans (hforced j i hji)
  have hRad : prop21_supportSqRoot I = I.radical :=
    prop21_sqRoot_eq_radical (I := I) (J := prop21_supportSqRoot I) (A := A)
      (a := a) (d := d) hI hIrr prop21_supportSqRoot_isSquarefree hd hSupp
  rw [← hRad]
  exact hSupp

/-- Proposition 2.1, packaged equality \(D_i=C_i\) and the four criteria. -/
theorem prop21_main_criteria [Fintype σ] [Fintype ι] [LinearOrder ι]
    {I : Ideal (MvPolynomial σ K)} (hBot : I ≠ ⊥) (hTop : I ≠ ⊤)
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hDecomp : IsIrredundantDecomp I A a) :
    (∀ i, generatorExponents I i = componentExponents A a i) ∧
      (HasSqRoot I ↔ ∀ i, (generatorExponents I i).Subsingleton) ∧
        (HasSqRoot I ↔ ∀ i, (componentExponents A a i).Subsingleton) ∧
          (HasSqRoot I ↔ prop21_XI A a = ∅) := by
  rcases hDecomp with ⟨hI, hIrr⟩
  have _hIndex : Nonempty ι := by
    by_contra hne
    have : IsEmpty ι := ⟨fun j ↦ hne ⟨j⟩⟩
    apply hTop
    rw [hI]
    simp
  have _hSupports : ∀ j, (A j).Nonempty := by
    intro j
    by_contra hA
    have hA0 : A j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    apply hBot
    apply le_antisymm ?_ bot_le
    rw [hI]
    calc
      (⨅ k, (purePower (A k) (a k) : Ideal (MvPolynomial σ K))) ≤
          purePower (A j) (a j) := iInf_le _ j
      _ = ⊥ := by simp [hA0, purePower, monomialIdeal]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact prop21_generatorExponents_eq_componentExponents hI hIrr i
  · exact prop21_hasSqRoot_iff_generatorExponents_subsingleton hI
  · exact prop21_hasSqRoot_iff_componentExponents_subsingleton hI hIrr
  · exact prop21_hasSqRoot_iff_XI_eq_empty hI hIrr

/-- Proposition 2.1 in full: the criteria and all their structural and weight consequences. -/
theorem prop21_main [Fintype σ] [Fintype ι] [LinearOrder ι]
    {I : Ideal (MvPolynomial σ K)} (hBot : I ≠ ⊥) (hTop : I ≠ ⊤)
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hDecomp : IsIrredundantDecomp I A a) :
    (∀ i, generatorExponents I i = componentExponents A a i) ∧
      (HasSqRoot I ↔ ∀ i, (generatorExponents I i).Subsingleton) ∧
        (HasSqRoot I ↔ ∀ i, (componentExponents A a i).Subsingleton) ∧
          (HasSqRoot I ↔ prop21_XI A a = ∅) ∧
            (HasSqRoot I →
              IsSquarefreeMonomialIdeal I.radical ∧
                I.radical = ⨅ j, (primeOf (A j) : Ideal (MvPolynomial σ K)) ∧
                  (∀ (J : Ideal (MvPolynomial σ K)) (d : σ → ℕ),
                    IsSquarefreeMonomialIdeal J → (∀ i, 0 < d i) →
                      diagonal d J = I → J = I.radical) ∧
                    (∀ (J₁ J₂ : Ideal (MvPolynomial σ K)) (d₁ d₂ : σ → ℕ),
                      IsSquarefreeMonomialIdeal J₁ → (∀ i, 0 < d₁ i) →
                        diagonal d₁ J₁ = I → IsSquarefreeMonomialIdeal J₂ →
                          (∀ i, 0 < d₂ i) → diagonal d₂ J₂ = I → J₁ = J₂) ∧
                      IsIrredundant (K := K) A (fun _ _ ↦ (1 : ℕ)) ∧
                        Function.Injective
                          (fun j ↦ (primeOf (A j) : Ideal (MvPolynomial σ K))) ∧
                          (∀ j k, j ≠ k → ¬
                            (primeOf (A j) : Ideal (MvPolynomial σ K)) ≤ primeOf (A k)) ∧
                            associatedPrimes (MvPolynomial σ K)
                                (MvPolynomial σ K ⧸ I) = I.minimalPrimes ∧
                              (∀ (J : Ideal (MvPolynomial σ K)) (d : σ → ℕ) (i : σ) (n : ℕ),
                                IsSquarefreeMonomialIdeal J → (∀ t, 0 < d t) →
                                  diagonal d J = I → n ∈ componentExponents A a i →
                                    n = d i) ∧
                                (∀ d : σ → ℕ, (∀ i, 0 < d i) →
                                  (∀ (j : ι) (i : σ), i ∈ A j → a j i = d i) →
                                    diagonal d (I.radical) = I)) := by
  obtain ⟨hEq, hG, hC, hX⟩ :=
    prop21_main_criteria (I := I) (A := A) (a := a) hBot hTop hDecomp
  rcases hDecomp with ⟨hI, hIrr⟩
  refine ⟨hEq, hG, hC, hX, ?_⟩
  intro hroot
  have hRadSqfree : IsSquarefreeMonomialIdeal I.radical := by
    rcases hroot with ⟨J, d, hJ, hd, hdiag⟩
    have hJeq := prop21_sqRoot_eq_radical (K := K) hI hIrr hJ hd hdiag
    rw [← hJeq]
    exact hJ
  have hanti : SupportsAntichain A a :=
    prop21_supportsAntichain_of_hasSqRoot (K := K) hI hIrr hroot
  have hRad : I.radical = ⨅ j, (primeOf (A j) : Ideal (MvPolynomial σ K)) :=
    prop21_radical_eq_iInf_primeOf hI hIrr
  refine ⟨hRadSqfree, hRad, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro J d hJ hd hdiag
    exact prop21_sqRoot_eq_radical (K := K) hI hIrr hJ hd hdiag
  · intro J₁ J₂ d₁ d₂ hJ₁ hd₁ hdiag₁ hJ₂ hd₂ hdiag₂
    exact prop21_sqRoot_unique hJ₁ hd₁ hdiag₁ hJ₂ hd₂ hdiag₂
  · exact prop21_isIrredundant_primeOf_of_hasSqRoot (K := K) hI hIrr hroot
  · intro j k hjk
    exact hanti j k ((primeOf_le_iff_subset (K := K)).mp (le_of_eq hjk))
  · intro j k hjk hle
    exact hjk (hanti j k ((primeOf_le_iff_subset (K := K)).mp hle))
  · exact prop21_associatedPrimes_eq_minimalPrimes_of_hasSqRoot (K := K) hI hIrr hroot
  · intro J d i n hJ hd hdiag hn
    exact prop21_weight_eq_componentExponent (K := K) hI hIrr hJ hd hdiag hn
  · intro d hd hforced
    exact prop21_unusedWeight_diagonal (K := K) hI hIrr hd hforced

end SimisFormal
