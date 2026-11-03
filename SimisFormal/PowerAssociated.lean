import SimisFormal.Defs
import SimisFormal.Basic
import SimisFormal.Eq2_StandardSymbolic
import SimisFormal.Prop2_1

namespace SimisFormal
open MvPolynomial
open scoped BigOperators
variable {σ K ι : Type*} [Field K] [DecidableEq σ]
omit [DecidableEq σ] in
/-- Contraction-extension saturation at a prime, plus the expected radical, gives primary. -/
private theorem powerAssociated_isPrimary_of_comap_map_eq_self_atPrime
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
    right
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

omit [DecidableEq σ] in
/-- Repeating one monomial generator realizes its scalar multiple in `powGens`. -/
private theorem powerAssociated_powGens_nsmul_mem {S : Set (σ →₀ ℕ)} {u : σ →₀ ℕ}
    (hu : u ∈ S) : ∀ q : ℕ, q • u ∈ powGens S q := by
  intro q
  induction q with
  | zero => simp [powGens]
  | succ q ih =>
      exact ⟨q • u, ih, u, hu, succ_nsmul u q⟩

omit [DecidableEq σ] in
/-- A positive-length sum of nonzero exponent generators is nonzero. -/
private theorem powerAssociated_powGens_ne_zero {S : Set (σ →₀ ℕ)}
    (hS : ∀ u ∈ S, u ≠ 0) {q : ℕ} (hq : q ≠ 0) :
    ∀ {z : σ →₀ ℕ}, z ∈ powGens S q → z ≠ 0 := by
  cases q with
  | zero => exact (hq rfl).elim
  | succ q =>
      intro z hz
      rcases hz with ⟨u, hu, s, hs, rfl⟩
      intro hsum
      have hs0 : s = 0 := by
        ext i
        have hi : u i + s i = (0 : ℕ) := by
          simpa only [Finsupp.add_apply, Finsupp.zero_apply] using
            congrArg (fun v : σ →₀ ℕ ↦ v i) hsum
        have his : s i = 0 := by omega
        simpa using his
      exact hS s hs hs0

/-- Simultaneous choices outside a fixed antichain support establish irredundance of the
componentwise positive powers. -/
private theorem powerAssociated_isIrredundant_powers [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (ha : ∀ j i, i ∈ A j → 0 < a j i) (hanti : SupportsAntichain A a)
    {q : ℕ} (hq : 0 < q) :
    ∀ j, ¬ (⨅ k : {k : ι // k ≠ j},
      (purePower (A k.1) (a k.1) : Ideal (MvPolynomial σ K)) ^ q) ≤
        (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) ^ q := by
  classical
  let S : ι → Set (σ →₀ ℕ) := fun j ↦
    {u | ∃ i ∈ A j, u = Finsupp.single i (a j i)}
  have hpure (j : ι) :
      (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) = monomialIdeal (S j) := by
    rfl
  have hSnonzero (j : ι) : ∀ u ∈ S j, u ≠ 0 := by
    intro u hu
    rcases hu with ⟨i, hi, rfl⟩
    intro hzero
    have hcoord := congrArg (fun f : σ →₀ ℕ ↦ f i) hzero
    have hai : a j i = 0 := by simpa using hcoord
    exact (Nat.ne_of_gt (ha j i hi)) hai
  have hSsupport (j : ι) : ∀ u ∈ S j, u.support ⊆ A j := by
    intro u hu x hx
    rcases hu with ⟨i, hi, rfl⟩
    have hxi : x = i := by
      by_contra hne
      exact (Finsupp.mem_support_iff.mp hx) (by simp [hne])
    simpa [hxi] using hi
  intro j hle
  have hchoice : ∀ k : {k : ι // k ≠ j}, ∃ i, i ∈ A k.1 ∧ i ∉ A j := by
    intro k
    rw [← Finset.not_subset]
    intro hsub
    exact k.2 (hanti k.1 j hsub)
  choose z hz using hchoice
  let e : σ →₀ ℕ := ∑ k : {k : ι // k ≠ j},
    q • Finsupp.single (z k) (a k.1 (z k))
  have hterm_le (k : {k : ι // k ≠ j}) :
      q • Finsupp.single (z k) (a k.1 (z k)) ≤ e := by
    dsimp [e]
    exact Finset.single_le_sum
      (N := σ →₀ ℕ)
      (f := fun l : {k : ι // k ≠ j} ↦
        q • Finsupp.single (z l) (a l.1 (z l)))
      (s := (Finset.univ : Finset {k : ι // k ≠ j}))
      (fun l _ ↦ zero_le) (by simp)
  have heomit : (monomial e (1 : K) : MvPolynomial σ K) ∈
      (⨅ k : {k : ι // k ≠ j},
        (purePower (A k.1) (a k.1) : Ideal (MvPolynomial σ K)) ^ q) := by
    refine Ideal.mem_iInf.mpr ?_
    intro k
    have hgen : Finsupp.single (z k) (a k.1 (z k)) ∈ S k.1 :=
      ⟨z k, (hz k).1, rfl⟩
    rw [hpure k, monomialIdeal_pow]
    exact monomial_mem_monomialIdeal.mpr
      ⟨q • Finsupp.single (z k) (a k.1 (z k)),
        powerAssociated_powGens_nsmul_mem hgen q, hterm_le k⟩
  have heoutside : ∀ t ∈ A j, e t = 0 := by
    intro t ht
    dsimp [e]
    have hne : ∀ k : {k : ι // k ≠ j}, z k ≠ t := by
      intro k hkt
      exact (hz k).2 (by simpa [← hkt] using ht)
    simp [hne]
  have heoutsidePower : (monomial e (1 : K) : MvPolynomial σ K) ∉
      (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) ^ q := by
    rw [hpure j, monomialIdeal_pow]
    intro heQ
    rcases monomial_mem_monomialIdeal.mp heQ with ⟨u, huPower, hue⟩
    have husupport : u.support ⊆ A j :=
      powGens_support_subset (hSsupport j) q u huPower
    have hu0 : u = 0 := by
      ext t
      by_cases ht : t ∈ A j
      · have het : e t = 0 := heoutside t ht
        have hle : u t ≤ e t := hue t
        have hut : u t = 0 := by omega
        simpa using hut
      · have hut : u t = 0 := by
          by_contra hne
          exact ht (husupport (by simpa [Finsupp.mem_support_iff] using hne))
        simpa using hut
    exact (powerAssociated_powGens_ne_zero (hSnonzero j) (Nat.ne_of_gt hq) huPower) hu0
  exact heoutsidePower (hle heomit)

/-- Every positive ordinary power of a pure-power component with positive exponents
on its support is primary. -/
theorem purePower_pow_isPrimary [Fintype σ] {A : Finset σ} {a : σ → ℕ}
    (ha : ∀ i ∈ A, 0 < a i) {q : ℕ} (hq : 0 < q) :
    ((purePower A a : Ideal (MvPolynomial σ K)) ^ q).IsPrimary := by
  classical
  let P : Ideal (MvPolynomial σ K) := primeOf A
  let : P.IsPrime := by
    dsimp [P]
    exact primeOf_isPrime (K := K) A
  apply powerAssociated_isPrimary_of_comap_map_eq_self_atPrime (P := P)
  · simpa [P] using
      (comap_map_pow_purePower_eq_self (K := K) (A := A) (a := a) q (P := P) (by rfl))
  · dsimp [P]
    calc
      ((purePower A a : Ideal (MvPolynomial σ K)) ^ q).radical =
          (purePower A a : Ideal (MvPolynomial σ K)).radical :=
        Ideal.radical_pow _ (Nat.ne_of_gt hq)
      _ = primeOf A := purePower_radical_eq_primeOf (K := K) ha

omit [DecidableEq σ] in
/-- The associated primes of a finite minimal primary decomposition indexed by `ι` are its
displayed radicals. -/
private theorem powerAssociated_submoduleAssociatedPrimes_eq_range [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {Q P : ι → Ideal (MvPolynomial σ K)}
    (hI : I = ⨅ j, Q j) (hprimary : ∀ j, (Q j).IsPrimary)
    (hradical : ∀ j, (Q j).radical = P j) (hPinj : Function.Injective P)
    (hirredundant : ∀ j, ¬ (⨅ k : {k : ι // k ≠ j}, Q k.1) ≤ Q j) :
    I.associatedPrimes = Set.range P := by
  classical
  let t : Finset (Ideal (MvPolynomial σ K)) := Finset.univ.image Q
  have htinf : t.inf id = I := by
    calc
      t.inf id = ⨅ j, Q j := by
        rw [show t = Finset.univ.image Q from rfl, Finset.inf_image]
        exact Finset.inf_univ_eq_iInf Q
      _ = I := hI.symm
  have ht : Submodule.IsMinimalPrimaryDecomposition I t := by
    refine ⟨htinf, ?_, ?_, ?_⟩
    · intro J hJ
      change J ∈ Finset.univ.image Q at hJ
      rcases Finset.mem_image.mp hJ with ⟨j, -, rfl⟩
      exact hprimary j
    · intro J hJ K hK hne
      dsimp only [Function.onFun]
      change J ∈ Finset.univ.image Q at hJ
      change K ∈ Finset.univ.image Q at hK
      rcases Finset.mem_image.mp hJ with ⟨j, -, rfl⟩
      rcases Finset.mem_image.mp hK with ⟨k, -, rfl⟩
      intro hrad
      have hP : P j = P k := by
        simpa [Submodule.colon_univ, hradical j, hradical k] using hrad
      apply hne
      have hjk : j = k := hPinj hP
      simp [hjk]
    · intro J hJ
      change J ∈ Finset.univ.image Q at hJ
      rcases Finset.mem_image.mp hJ with ⟨j, -, rfl⟩
      intro hle
      apply hirredundant j
      intro x hxomit
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
          simp [hkj]
        simpa using Ideal.mem_iInf.mp hxomit ⟨k, hkj⟩
      exact hle hxt
  have hAss := ht.image_radical_eq_associated_primes
  rw [← hAss]
  ext R
  constructor
  · rintro ⟨J, hJ, rfl⟩
    change J ∈ Finset.univ.image Q at hJ
    rcases Finset.mem_image.mp hJ with ⟨j, -, rfl⟩
    exact ⟨j, by simp [Submodule.colon_univ, hradical j]⟩
  · rintro ⟨j, rfl⟩
    refine ⟨Q j, ?_, ?_⟩
    · change Q j ∈ Finset.univ.image Q
      simp
    · simp [Submodule.colon_univ, hradical j]

/-- Under componentwise Simis and an irredundant antichain decomposition, every positive
ordinary power has exactly the same associated primes as the original ideal. -/
theorem associatedPrimes_pow_eq_range_of_componentSimis_antichain
    [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hcomp : HasComponents I A a) (hirr : IsIrredundant (K := K) A a)
    (hanti : SupportsAntichain A a)
    (hpow : ComponentSimis I (fun j ↦ (purePower (A j) (a j) : Ideal (MvPolynomial σ K))))
    {q : ℕ} (hq : 0 < q) :
    associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I ^ q) =
      Set.range (fun j ↦ (primeOf (A j) : Ideal (MvPolynomial σ K))) := by
  classical
  have ha : ∀ j i, i ∈ A j → 0 < a j i := exponents_pos_of_irredundant hirr
  let Q : ι → Ideal (MvPolynomial σ K) := fun j ↦ purePower (A j) (a j)
  let Qq : ι → Ideal (MvPolynomial σ K) := fun j ↦ Q j ^ q
  let P : ι → Ideal (MvPolynomial σ K) := fun j ↦ primeOf (A j)
  have hbase : I = ⨅ j, Q j := by
    change I = ⨅ j, (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) at hcomp
    simpa [Q] using hcomp
  have hIpow : I ^ q = ⨅ j, Qq j := by
    calc
      I ^ q = (⨅ j, Q j) ^ q := by rw [hbase]
      _ = ⨅ j, Q j ^ q := by
        have h := hpow q (by omega)
        rw [hbase] at h
        simpa [Q, componentSymbolic] using h
      _ = ⨅ j, Qq j := by simp [Qq]
  have hprimary : ∀ j, (Qq j).IsPrimary := by
    intro j
    simpa [Qq, Q] using
      (purePower_pow_isPrimary (K := K) (A := A j) (a := a j)
        (fun i hi ↦ ha j i hi) (q := q) hq)
  have hradical : ∀ j, (Qq j).radical = P j := by
    intro j
    dsimp [Qq, Q, P]
    calc
      ((purePower (A j) (a j) : Ideal (MvPolynomial σ K)) ^ q).radical =
          (purePower (A j) (a j) : Ideal (MvPolynomial σ K)).radical :=
        Ideal.radical_pow _ (Nat.ne_of_gt hq)
      _ = primeOf (A j) :=
        purePower_radical_eq_primeOf (K := K) (fun i hi ↦ ha j i hi)
  have hPinj : Function.Injective P := by
    intro j k hjk
    have hprime : (primeOf (A j) : Ideal (MvPolynomial σ K)) = primeOf (A k) := by
      simpa [P] using hjk
    exact hanti j k (primeOf_le_iff_subset.mp (le_of_eq hprime))
  have hirrpower : ∀ j, ¬ (⨅ k : {k : ι // k ≠ j}, Qq k.1) ≤ Qq j := by
    simpa [Qq, Q] using
      (powerAssociated_isIrredundant_powers (K := K) (A := A) (a := a) ha hanti (q := q) hq)
  have hass : (I ^ q).associatedPrimes = Set.range P :=
    powerAssociated_submoduleAssociatedPrimes_eq_range
      (I := I ^ q) (Q := Qq) (P := P) hIpow hprimary hradical hPinj hirrpower
  exact (prop21_associatedPrimes_quotient_eq_submodule (I := I ^ q)).trans (by simpa [P] using hass)

omit [DecidableEq σ] in
/-- If all positive powers have the same associated primes as the ideal itself, the paper's
normal-torsion-free condition follows. -/
theorem normallyTorsionFree_of_powerAssociatedPrimes_eq_range
    {I : Ideal (MvPolynomial σ K)} {P : ι → Ideal (MvPolynomial σ K)}
    (hbase : associatedPrimes (MvPolynomial σ K)
        (MvPolynomial σ K ⧸ I) = Set.range P)
    (hpower : ∀ {q : ℕ}, 0 < q →
      associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I ^ q) = Set.range P) :
    prop21NormallyTorsionFree I := by
  intro q hq
  exact le_of_eq ((hpower (by omega)).trans hbase.symm)

end SimisFormal
