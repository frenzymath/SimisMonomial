import SimisFormal.Defs
import SimisFormal.Basic
import SimisFormal.Eq2_StandardSymbolic
import SimisFormal.Eq4_DiagonalSimis
import SimisFormal.Prop2_1
import SimisFormal.PowerAssociated

namespace SimisFormal
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [Field K] [DecidableEq σ]
omit [Field K] [DecidableEq σ] in
/-- The cyclic successor has no fixed point when the cycle length is at least two. -/
theorem finSuccMod_ne_self {q : ℕ} (hq : 2 ≤ q) (i : Fin q) : finSuccMod i ≠ i := by
  intro h
  unfold finSuccMod at h
  split_ifs at h with hlt
  · have hv : i.val + 1 = i.val := by simpa using congrArg Fin.val h
    omega
  · have hv : 0 = i.val := by simpa using congrArg Fin.val h
    omega

omit [Field K] [DecidableEq σ] in
/-- The second cyclic successor has no fixed point when the length is at least three. -/
theorem finSuccMod_succ_ne_self {q : ℕ} (hq : 3 ≤ q) (i : Fin q) :
    finSuccMod (finSuccMod i) ≠ i := by
  classical
  by_cases h₁ : i.val + 1 < q
  · have hs₁ : (finSuccMod i).val = i.val + 1 := by
      rw [finSuccMod]
      rw [dif_pos h₁]
    by_cases h₂ : (finSuccMod i).val + 1 < q
    · have hs₂ : (finSuccMod (finSuccMod i)).val = (finSuccMod i).val + 1 := by
        rw [finSuccMod]
        rw [dif_pos h₂]
      intro h
      have hv := congrArg Fin.val h
      rw [hs₂, hs₁] at hv
      omega
    · have hs₂ : (finSuccMod (finSuccMod i)).val = 0 := by
        rw [finSuccMod]
        rw [dif_neg h₂]
      intro h
      have hv := congrArg Fin.val h
      rw [hs₂] at hv
      omega
  · have hs₁ : (finSuccMod i).val = 0 := by
      rw [finSuccMod]
      rw [dif_neg h₁]
    have h₂ : (finSuccMod i).val + 1 < q := by rw [hs₁]; omega
    have hs₂ : (finSuccMod (finSuccMod i)).val = (finSuccMod i).val + 1 := by
      rw [finSuccMod]
      rw [dif_pos h₂]
    intro h
    have hv := congrArg Fin.val h
    rw [hs₂, hs₁] at hv
    omega

/-- Coning preserves a strong cycle, of the same length. -/
theorem coneClutter_hasStrongCycle {H : Set (Finset σ)} {q : ℕ} :
    HasStrongCycle H q → HasStrongCycle (coneClutter H) q := by
  rintro ⟨hq, v, hv, E, hE, hEH, hInt⟩
  let v' : Fin q → Option σ := fun i => some (v i)
  let E' : Fin q → Finset (Option σ) := fun i => insert none (Finset.image some (E i))
  have hv' : Function.Injective v' := by
    intro i j hij
    apply hv
    exact Option.some.inj hij
  have hE' : Function.Injective E' := by
    intro i j hij
    apply hE
    ext x
    have hm : some x ∈ E' i ↔ some x ∈ E' j := by rw [hij]
    simpa [E'] using hm
  refine ⟨hq, v', hv', E', hE', ?_, ?_⟩
  · intro i
    exact ⟨E i, hEH i, rfl⟩
  · intro i
    ext x
    cases x with
    | none => simp [E', v']
    | some x =>
        have hm : x ∈ E i ∩ Finset.univ.image v ↔
            x ∈ ({v i, v (finSuccMod i)} : Finset σ) := by
          rw [hInt i]
        simpa [E', v'] using hm

/-- Removing the cone point is inverse to coning on strong cycles. -/
theorem coneClutter_hasStrongCycle_iff {H : Set (Finset σ)} {q : ℕ} :
    HasStrongCycle (coneClutter H) q ↔ HasStrongCycle H q := by
  constructor
  · rintro ⟨hq, v, hv, E, hE, hEH, hInt⟩
    choose F hFH hFE using hEH
    have hvne : ∀ i, v i ≠ none := by
      intro i hi
      let k : Fin q := finSuccMod i
      have hki : k ≠ i := by
        dsimp [k]
        exact finSuccMod_ne_self (by omega) i
      have hksi : finSuccMod k ≠ i := by
        dsimp [k]
        exact finSuccMod_succ_ne_self hq i
      have hleft : none ∈ E k ∩ Finset.univ.image v := by
        rw [Finset.mem_inter]
        refine ⟨?_, Finset.mem_image.mpr ⟨i, by simp, hi⟩⟩
        rw [← hFE k]
        simp
      rw [hInt k] at hleft
      have hright : none = v k ∨ none = v (finSuccMod k) := by simpa using hleft
      rcases hright with hright | hright
      · exact hki (hv (hright.symm.trans hi.symm))
      · exact hksi (hv (hright.symm.trans hi.symm))
    let hsome : ∀ i, (v i).isSome = true := fun i =>
      (Option.ne_none_iff_isSome).mp (hvne i)
    let w : Fin q → σ := fun i => (v i).get (hsome i)
    have hw : ∀ i, some (w i) = v i := by
      intro i
      exact Option.some_get (hsome i)
    have hwinj : Function.Injective w := by
      intro i j hij
      apply hv
      calc
        v i = some (w i) := (hw i).symm
        _ = some (w j) := congrArg some hij
        _ = v j := hw j
    have hFinj : Function.Injective F := by
      intro i j hij
      apply hE
      calc
        E i = insert none (Finset.image some (F i)) := (hFE i).symm
        _ = insert none (Finset.image some (F j)) := by rw [hij]
        _ = E j := hFE j
    refine ⟨hq, w, hwinj, F, hFinj, hFH, ?_⟩
    intro i
    ext x
    have hEdge : some x ∈ E i ↔ x ∈ F i := by
      rw [← hFE i]
      simp
    have hVert : some x ∈ Finset.univ.image v ↔ x ∈ Finset.univ.image w := by
      constructor
      · intro hx
        rw [Finset.mem_image] at hx ⊢
        rcases hx with ⟨j, hj, hjx⟩
        refine ⟨j, hj, ?_⟩
        apply Option.some.inj
        exact (hw j).trans hjx
      · intro hx
        rw [Finset.mem_image] at hx ⊢
        rcases hx with ⟨j, hj, hjx⟩
        refine ⟨j, hj, ?_⟩
        exact (hw j).symm.trans (congrArg some hjx)
    have hPair : some x ∈ ({v i, v (finSuccMod i)} : Finset (Option σ)) ↔
        x ∈ ({w i, w (finSuccMod i)} : Finset σ) := by
      rw [← hw i, ← hw (finSuccMod i)]
      simp
    calc
      x ∈ F i ∩ Finset.univ.image w ↔
          some x ∈ E i ∩ Finset.univ.image v := by
            simp only [Finset.mem_inter]
            rw [← hEdge, ← hVert]
      _ ↔ some x ∈ ({v i, v (finSuccMod i)} : Finset (Option σ)) := by rw [hInt i]
      _ ↔ x ∈ ({w i, w (finSuccMod i)} : Finset σ) := hPair
  · exact coneClutter_hasStrongCycle

/-- Coning preserves and reflects balancedness. -/
theorem coneClutter_isBalanced_iff {H : Set (Finset σ)} :
    IsBalanced (coneClutter H) ↔ IsBalanced H := by
  constructor
  · intro hbal q hodd hcycle
    exact hbal q hodd ((coneClutter_hasStrongCycle_iff (H := H)).2 hcycle)
  · intro hbal q hodd hcycle
    exact hbal q hodd ((coneClutter_hasStrongCycle_iff (H := H)).1 hcycle)

omit K in
/-- A strong triangle refutes balancedness. -/
theorem cor33_hasStrongTriangle_not_isBalanced {H : Set (Finset σ)}
    (h : HasStrongTriangle H) : ¬ IsBalanced H := by
  intro hbal
  exact hbal 3 (by norm_num) h

/-- The total capacity of a monomial relative to a pure-power component. -/
def purePowerCapacity (A : Finset σ) (a : σ → ℕ) (e : σ →₀ ℕ) : ℕ :=
  ∑ i ∈ A, e i / a i

omit K in
/-- Adding one allowable pure-power generator increases capacity by exactly one. -/
theorem purePowerCapacity_add_single {A : Finset σ} {a : σ → ℕ}
    (ha : ∀ i ∈ A, 0 < a i) {i : σ} (hi : i ∈ A) (u : σ →₀ ℕ) :
    purePowerCapacity A a (u + Finsupp.single i (a i)) =
      purePowerCapacity A a u + 1 := by
  classical
  unfold purePowerCapacity
  calc
    ∑ j ∈ A, (u + Finsupp.single i (a i)) j / a j =
        ∑ j ∈ A, (u j / a j + if j = i then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          by_cases hji : j = i
          · subst j
            simp [Nat.add_div_right (u i) (ha i hi)]
          · simp [hji]
    _ = (∑ j ∈ A, u j / a j) + ∑ j ∈ A, (if j = i then 1 else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ j ∈ A, u j / a j) + 1 := by
          rw [Finset.sum_ite_eq']
          simp [hi]

omit K in
/-- Subtracting one allowable pure-power generator decreases capacity by exactly one. -/
theorem purePowerCapacity_sub_single {A : Finset σ} {a : σ → ℕ}
    (ha : ∀ i ∈ A, 0 < a i) {i : σ} (hi : i ∈ A) {u : σ →₀ ℕ}
    (hui : a i ≤ u i) :
    purePowerCapacity A a u =
      purePowerCapacity A a (u - Finsupp.single i (a i)) + 1 := by
  classical
  unfold purePowerCapacity
  calc
    ∑ j ∈ A, u j / a j =
        ∑ j ∈ A, ((u - Finsupp.single i (a i)) j / a j + if j = i then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          by_cases hji : j = i
          · subst j
            have hadd : ((u - Finsupp.single i (a i)) i) = u i - a i := by simp
            rw [hadd]
            simpa using (Nat.div_eq_sub_div (ha i hi) hui)
          · simp [hji]
    _ = (∑ j ∈ A, (u - Finsupp.single i (a i)) j / a j) +
          ∑ j ∈ A, (if j = i then 1 else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ j ∈ A, (u - Finsupp.single i (a i)) j / a j) + 1 := by
          rw [Finset.sum_ite_eq']
          simp [hi]

/-- Membership in a power of a pure-power component, in terms of total capacity. -/
theorem monomial_mem_purePower_pow {A : Finset σ} {a : σ → ℕ}
    (ha : ∀ i ∈ A, 0 < a i) (q : ℕ) {e : σ →₀ ℕ} :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ (purePower A a : Ideal (MvPolynomial σ K)) ^ q ↔
      q ≤ purePowerCapacity A a e := by
  constructor
  · intro h
    rw [purePower, monomialIdeal_pow] at h
    rcases monomial_mem_monomialIdeal.mp h with ⟨u, hu, hue⟩
    have hrec : ∀ {q : ℕ} {u : σ →₀ ℕ},
        u ∈ powGens {e : σ →₀ ℕ | ∃ i ∈ A, e = Finsupp.single i (a i)} q →
          q ≤ purePowerCapacity A a u := by
      intro q
      induction q with
      | zero =>
          intro u hu
          simp [powGens] at hu
          subst u
          simp [purePowerCapacity]
      | succ q ih =>
          intro u hu
          simp only [powGens] at hu
          rcases hu with ⟨v, hv, s, hs, hsum⟩
          rcases hs with ⟨i, hi, hs⟩
          subst s
          subst u
          rw [purePowerCapacity_add_single ha hi]
          exact Nat.succ_le_succ (ih hv)
    exact le_trans (hrec hu) (Finset.sum_le_sum fun i hi => Nat.div_le_div_right (hue i))
  · revert e
    induction q with
    | zero =>
        intro e h
        simp
    | succ q ih =>
        intro e he
        have hpos : 0 < purePowerCapacity A a e := by omega
        have hne : purePowerCapacity A a e ≠ 0 := Nat.ne_of_gt hpos
        rcases Finset.exists_ne_zero_of_sum_ne_zero hne with ⟨i, hi, hdiv⟩
        have hdivpos : 0 < e i / a i := Nat.pos_of_ne_zero hdiv
        have hai_le : a i ≤ e i := by
          have := (Nat.le_div_iff_mul_le (ha i hi)).1 hdivpos
          simpa using this
        let d : σ →₀ ℕ := e - Finsupp.single i (a i)
        have hsingle_le : Finsupp.single i (a i) ≤ e := Finsupp.single_le_iff.mpr hai_le
        have hadd : Finsupp.single i (a i) + d = e := add_tsub_cancel_of_le hsingle_le
        have hcap : purePowerCapacity A a e = purePowerCapacity A a d + 1 := by
          dsimp [d]
          exact purePowerCapacity_sub_single ha hi hai_le
        have hdcap : q ≤ purePowerCapacity A a d := by omega
        have hdmem := ih (e := d) hdcap
        have hgmem : (monomial (Finsupp.single i (a i)) (1 : K) : MvPolynomial σ K) ∈
            purePower A a := monomial_mem_purePower.mpr ⟨i, hi, by simp⟩
        rw [pow_succ]
        have hmul : (monomial d (1 : K) : MvPolynomial σ K) *
              monomial (Finsupp.single i (a i)) (1 : K) = monomial e (1 : K) := by
          rw [monomial_mul]
          simpa [hadd] using (show monomial (d + Finsupp.single i (a i)) (1 * (1 : K)) =
            monomial e (1 : K) from by rw [add_comm, hadd]; simp)
        rw [← hmul]
        exact Ideal.mul_mem_mul hdmem hgmem

omit [DecidableEq σ] in
/-- Pure-power components only use exponents on their own supports. -/
theorem cor33_purePower_congr_on_support {A : Finset σ} {a b : σ → ℕ}
    (h : ∀ i ∈ A, a i = b i) :
    (purePower A a : Ideal (MvPolynomial σ K)) = purePower A b := by
  rw [purePower, purePower]
  congr 1
  ext e
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨i, hi, he.trans (by rw [h i hi])⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨i, hi, he.trans (by rw [h i hi])⟩

omit [Field K] [DecidableEq σ] in
/-- Ideal height is unchanged by radical. -/
theorem cor33_height_radical {R : Type*} [CommRing R] (I : Ideal R) :
    I.radical.height = I.height := by
  rw [Ideal.height_eq_inf_minimalPrimes, Ideal.height_eq_inf_minimalPrimes]
  rw [Ideal.radical_minimalPrimes]

omit [DecidableEq σ] in
/-- The variable prime is the ideal spanned by the variables in its support. -/
theorem cor33_primeOf_eq_span_X {A : Finset σ} :
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
/-- A variable prime in a polynomial ring in finitely many variables has height its cardinality. -/
theorem cor33_height_primeOf_eq_card [Fintype σ] (A : Finset σ) :
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
        have hle : (primeOf A : Ideal (MvPolynomial σ K)) ≤
            primeOf (insert i A) :=
          (primeOf_le_iff_subset (K := K)).mpr (by simp)
        have hne : (primeOf A : Ideal (MvPolynomial σ K)) ≠
            primeOf (insert i A) := by
          intro hEq
          have hback : (primeOf (insert i A) : Ideal (MvPolynomial σ K)) ≤
              primeOf A := by
            rw [hEq]
          have hsub : insert i A ⊆ A := (primeOf_le_iff_subset (K := K)).mp hback
          exact hi (hsub (by simp))
        have hlt : (primeOf A : Ideal (MvPolynomial σ K)) <
            primeOf (insert i A) := lt_of_le_of_ne hle hne
        have hpA : (primeOf A : Ideal (MvPolynomial σ K)).IsPrime :=
          primeOf_isPrime A
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
    simpa [S, f] using (cor33_primeOf_eq_span_X (K := K) (A := A))
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
/-- A pure-power component with positive exponents has height its support cardinality. -/
theorem cor33_height_purePower_eq_card [Fintype σ] {A : Finset σ} {a : σ → ℕ}
    (ha : ∀ i ∈ A, 0 < a i) :
    (purePower A a : Ideal (MvPolynomial σ K)).height = (A.card : ℕ∞) := by
  classical
  calc
    (purePower A a : Ideal (MvPolynomial σ K)).height =
        (purePower A a : Ideal (MvPolynomial σ K)).radical.height :=
      (cor33_height_radical (purePower A a : Ideal (MvPolynomial σ K))).symm
    _ = (primeOf A : Ideal (MvPolynomial σ K)).height := by
      rw [purePower_radical_eq_primeOf (K := K) ha]
    _ = (A.card : ℕ∞) := cor33_height_primeOf_eq_card (K := K) A

omit [DecidableEq σ] in
/-- A pure-power component agrees with the variable prime when all exponents are one. -/
theorem cor33_purePower_eq_primeOf_of_one_on_support {A : Finset σ} {a : σ → ℕ}
    (h : ∀ i ∈ A, a i = 1) :
    (purePower A a : Ideal (MvPolynomial σ K)) = primeOf A := by
  rw [primeOf]
  exact cor33_purePower_congr_on_support h

/-- A pure-power component contains every monomial occurring in a member. -/
theorem cor33_monomial_mem_of_mem_purePower {A : Finset σ} {a : σ → ℕ}
    {x : MvPolynomial σ K} {e : σ →₀ ℕ}
    (hx : x ∈ (purePower A a : Ideal (MvPolynomial σ K))) (he : e ∈ x.support) :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ purePower A a := by
  rw [purePower] at hx ⊢
  exact monomial_mem_monomialIdeal.mpr ((mem_monomialIdeal.mp hx) e he)

/-- Recover the exponents on the old variables. -/
noncomputable def optionRestrict (e : Option σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.comapDomain (Option.some : σ → Option σ) e (Option.some_injective σ).injOn

omit [DecidableEq σ] in
@[simp] theorem extendExp_apply_none (e : σ →₀ ℕ) : extendExp e none = 0 := by
  rw [extendExp, Finsupp.mapDomain_of_notMem_range]
  rintro ⟨x, hx⟩
  cases hx

omit [DecidableEq σ] in
@[simp] theorem extendExp_apply_some (e : σ →₀ ℕ) (i : σ) : extendExp e (some i) = e i := by
  exact Finsupp.mapDomain_apply (Option.some_injective σ) e i

omit [DecidableEq σ] in
@[simp] theorem optionRestrict_apply (e : Option σ →₀ ℕ) (i : σ) :
    optionRestrict e i = e (some i) := by
  exact Finsupp.comapDomain_apply (Option.some : σ → Option σ) e
    (Option.some_injective σ).injOn i

omit [DecidableEq σ] in
@[simp] theorem extendExp_zero : extendExp (0 : σ →₀ ℕ) = 0 := by
  ext x
  cases x <;> simp

omit [DecidableEq σ] in
@[simp] theorem optionRestrict_zero :
    optionRestrict (0 : Option σ →₀ ℕ) = 0 := by
  ext i
  simp

omit [DecidableEq σ] in
@[simp] theorem optionRestrict_extendExp (e : σ →₀ ℕ) :
    optionRestrict (extendExp e) = e := by
  ext i
  simp

omit [DecidableEq σ] in
@[simp] theorem optionRestrict_add (e f : Option σ →₀ ℕ) :
    optionRestrict (e + f) = optionRestrict e + optionRestrict f := by
  ext i
  simp

omit [DecidableEq σ] in
@[simp] theorem coneExp_apply_none (e : σ →₀ ℕ) : coneExp e none = 1 := by
  simp [coneExp]

omit [DecidableEq σ] in
@[simp] theorem coneExp_apply_some (e : σ →₀ ℕ) (i : σ) : coneExp e (some i) = e i := by
  simp [coneExp]

omit [DecidableEq σ] in
@[simp] theorem optionRestrict_coneExp (e : σ →₀ ℕ) : optionRestrict (coneExp e) = e := by
  ext i
  simp

omit [DecidableEq σ] in
theorem extendExp_le_iff {e : Option σ →₀ ℕ} {u : σ →₀ ℕ} :
    extendExp u ≤ e ↔ u ≤ optionRestrict e := by
  rw [Finsupp.le_def, Finsupp.le_def]
  constructor
  · intro h i
    simpa using h (some i)
  · intro h x
    cases x with
    | none => simp
    | some i => simpa using h i

omit [DecidableEq σ] in
theorem coneExp_le_iff {e : Option σ →₀ ℕ} {u : σ →₀ ℕ} :
    coneExp u ≤ e ↔ 1 ≤ e none ∧ u ≤ optionRestrict e := by
  rw [Finsupp.le_def]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa using h none
    · rw [Finsupp.le_def]
      intro i
      simpa using h (some i)
  · rintro ⟨ht, hu⟩ x
    cases x with
    | none => simpa using ht
    | some i => simpa using hu i

omit [DecidableEq σ] in
/-- Extension of a represented monomial ideal is represented by extended exponents. -/
theorem cor33_rename_monomialIdeal {τ : Type*} [DecidableEq τ] (f : σ → τ)
    (S : Set (σ →₀ ℕ)) :
    Ideal.map (MvPolynomial.rename (R := K) f) (monomialIdeal S : Ideal (MvPolynomial σ K)) =
      monomialIdeal (Finsupp.mapDomain f '' S) := by
  rw [monomialIdeal, Ideal.map_span, monomialIdeal]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨e, heS, rfl⟩, rfl⟩
    rw [MvPolynomial.rename_monomial]
    exact ⟨Finsupp.mapDomain f e, ⟨e, heS, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨e, heS, rfl⟩, rfl⟩
    refine ⟨monomial e (1 : K), ⟨e, heS, rfl⟩, ?_⟩
    rw [MvPolynomial.rename_monomial]

omit [DecidableEq σ] in
theorem cor33_singleton_primeOf (x : σ) :
    (primeOf ({x} : Finset σ) : Ideal (MvPolynomial σ K)) =
      monomialIdeal ({Finsupp.single x 1} : Set (σ →₀ ℕ)) := by
  rw [primeOf, purePower]
  congr 1
  ext e
  simp

/-- Multiplication by the cone variable shifts every monomial generator. -/
theorem cor33_coneIdeal_monomialIdeal (S : Set (σ →₀ ℕ)) :
    coneIdeal (K := K) (monomialIdeal S : Ideal (MvPolynomial σ K)) =
      monomialIdeal (coneExp '' S) := by
  rw [coneIdeal, cor33_rename_monomialIdeal, cor33_singleton_primeOf]
  rw [monomialIdeal_mul]
  congr 1
  ext z
  constructor
  · rintro ⟨u, ⟨e, he, rfl⟩, t, ht, hz⟩
    have ht' : t = Finsupp.single none 1 := by simpa using ht
    subst t
    exact ⟨e, he, by simpa [extendExp, coneExp] using hz.symm⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨extendExp e, ⟨e, he, rfl⟩, Finsupp.single none 1, by simp, rfl⟩

theorem monomial_mem_coneIdeal {I : Ideal (MvPolynomial σ K)} (hI : IsMonomialIdeal I)
    {e : Option σ →₀ ℕ} :
    (monomial e (1 : K) : MvPolynomial (Option σ) K) ∈ coneIdeal I ↔
      1 ≤ e none ∧ (monomial (optionRestrict e) (1 : K) : MvPolynomial σ K) ∈ I := by
  rcases hI with ⟨S, rfl⟩
  rw [cor33_coneIdeal_monomialIdeal]
  constructor
  · intro he
    rcases monomial_mem_monomialIdeal.mp he with ⟨u, ⟨v, hvS, rfl⟩, hle⟩
    have hcv := coneExp_le_iff.mp hle
    exact ⟨hcv.1, monomial_mem_monomialIdeal.mpr ⟨v, hvS, hcv.2⟩⟩
  · rintro ⟨ht, hrest⟩
    rcases monomial_mem_monomialIdeal.mp hrest with ⟨v, hvS, hvle⟩
    exact monomial_mem_monomialIdeal.mpr
      ⟨coneExp v, ⟨v, hvS, rfl⟩, coneExp_le_iff.mpr ⟨ht, hvle⟩⟩

/-- A represented monomial ideal contains every monomial occurring in a member. -/
theorem cor33_monomial_mem_of_mem_repr {I : Ideal (MvPolynomial σ K)} {S : Set (σ →₀ ℕ)}
    (hI : I = monomialIdeal S) {x : MvPolynomial σ K} {e : σ →₀ ℕ}
    (hx : x ∈ I) (he : e ∈ x.support) :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ I := by
  rw [hI] at hx ⊢
  rw [monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image] at hx
  exact monomial_mem_monomialIdeal.mpr (hx e he)

theorem cor33_monomial_mem_of_mem_purePower_pow {x : MvPolynomial σ K}
    {e : σ →₀ ℕ} {A : Finset σ} {a : σ → ℕ} {q : ℕ}
    (hx : x ∈ (purePower A a : Ideal (MvPolynomial σ K)) ^ q) (he : e ∈ x.support) :
    (monomial e (1 : K) : MvPolynomial σ K) ∈
      (purePower A a : Ideal (MvPolynomial σ K)) ^ q := by
  rw [purePower, monomialIdeal_pow] at hx ⊢
  exact cor33_monomial_mem_of_mem_repr (I := monomialIdeal (powGens
    {e : σ →₀ ℕ | ∃ i ∈ A, e = Finsupp.single i (a i)} q)) rfl hx he

omit [DecidableEq σ] in
theorem cor33_monomial_mem_of_mem_rename_pow {τ : Type*} [DecidableEq τ]
    {I : Ideal (MvPolynomial σ K)} (hI : IsMonomialIdeal I)
    {x : MvPolynomial τ K} {e : τ →₀ ℕ} {q : ℕ} (f : σ → τ)
    (hx : x ∈ (Ideal.map (MvPolynomial.rename (R := K) f) I) ^ q) (he : e ∈ x.support) :
    (monomial e (1 : K) : MvPolynomial τ K) ∈
      (Ideal.map (MvPolynomial.rename (R := K) f) I) ^ q := by
  rcases hI with ⟨S, rfl⟩
  rw [← Ideal.map_pow, monomialIdeal_pow, cor33_rename_monomialIdeal] at hx ⊢
  exact cor33_monomial_mem_of_mem_repr
    (S := Finsupp.mapDomain f '' powGens S q) rfl hx he

theorem cor33_monomial_mem_of_mem_coneIdeal_pow {I : Ideal (MvPolynomial σ K)}
    (hI : IsMonomialIdeal I) {x : MvPolynomial (Option σ) K} {e : Option σ →₀ ℕ}
    {q : ℕ} (hx : x ∈ (coneIdeal I) ^ q) (he : e ∈ x.support) :
    (monomial e (1 : K) : MvPolynomial (Option σ) K) ∈ (coneIdeal I) ^ q := by
  rcases hI with ⟨S, rfl⟩
  rw [cor33_coneIdeal_monomialIdeal, monomialIdeal_pow] at hx ⊢
  exact cor33_monomial_mem_of_mem_repr
    (S := powGens (coneExp '' S) q) rfl hx he

/-- Ordinary powers of a coned monomial ideal separate the cone variable exactly. -/
theorem monomial_mem_coneIdeal_pow {I : Ideal (MvPolynomial σ K)} (hI : IsMonomialIdeal I)
    (q : ℕ) {e : Option σ →₀ ℕ} :
    (monomial e (1 : K) : MvPolynomial (Option σ) K) ∈ (coneIdeal I) ^ q ↔
      q ≤ e none ∧
        (monomial (optionRestrict e) (1 : K) : MvPolynomial σ K) ∈ I ^ q := by
  rcases hI with ⟨S, rfl⟩
  rw [cor33_coneIdeal_monomialIdeal, monomialIdeal_pow, monomialIdeal_pow]
  constructor
  · intro he
    rcases monomial_mem_monomialIdeal.mp he with ⟨u, hu, hue⟩
    have hforward : ∀ {q : ℕ} {u : Option σ →₀ ℕ},
        u ∈ powGens (coneExp '' S) q →
          q ≤ u none ∧ optionRestrict u ∈ powGens S q := by
      intro q
      induction q with
      | zero =>
          intro u hu
          simp only [powGens] at hu
          subst u
          simp [powGens]
      | succ q ih =>
          intro u hu
          simp only [powGens, Set.mem_ofPred_eq] at hu
          rcases hu with ⟨v, hv, s, hs, hadd⟩
          rcases hs with ⟨w, hw, hws⟩
          subst s
          subst u
          have hv' := ih hv
          refine ⟨?_, ?_⟩
          · simp
            omega
          · simp only [powGens, Set.mem_ofPred_eq]
            refine ⟨optionRestrict v, hv'.2, w, hw, ?_⟩
            ext i
            simp
    have hu' := hforward hu
    refine ⟨le_trans hu'.1 (hue none), ?_⟩
    have hrestle : optionRestrict u ≤ optionRestrict e := by
      rw [Finsupp.le_def]
      intro i
      simpa using hue (some i)
    exact monomial_mem_monomialIdeal.mpr ⟨optionRestrict u, hu'.2, hrestle⟩
  · rintro ⟨ht, hbase⟩
    rcases monomial_mem_monomialIdeal.mp hbase with ⟨v, hv, hvle⟩
    have hconstruct : ∀ {q : ℕ} {v : σ →₀ ℕ}, v ∈ powGens S q →
        extendExp v + Finsupp.single none q ∈ powGens (coneExp '' S) q := by
      intro q
      induction q with
      | zero =>
          intro v hv
          simp only [powGens] at hv ⊢
          subst v
          simp
      | succ q ih =>
          intro v hv
          simp only [powGens, Set.mem_ofPred_eq] at hv
          rcases hv with ⟨w, hw, s, hs, hadd⟩
          subst v
          simp only [powGens, Set.mem_ofPred_eq]
          refine ⟨extendExp w + Finsupp.single none q, ih hw, coneExp s,
            ⟨s, hs, rfl⟩, ?_⟩
          ext x
          cases x with
          | none => simp
          | some i => simp
    refine monomial_mem_monomialIdeal.mpr
      ⟨extendExp v + Finsupp.single none q, hconstruct hv, ?_⟩
    rw [Finsupp.le_def]
    intro x
    cases x with
    | none => simpa using ht
    | some i => simpa using hvle i

/-- Minimal generators of a represented ideal are its divisibility-minimal generators. -/
theorem cor33_minGens_monomialIdeal_eq {S : Set (σ →₀ ℕ)}
    (hanti : ∀ e ∈ S, ∀ u ∈ S, u ≤ e → u = e) :
    minGens (monomialIdeal S : Ideal (MvPolynomial σ K)) = S := by
  ext e
  constructor
  · intro he
    rw [mem_minGens] at he
    rcases monomial_mem_monomialIdeal.mp he.1 with ⟨u, huS, hue⟩
    have huI : (monomial u (1 : K) : MvPolynomial σ K) ∈ monomialIdeal S :=
      monomial_mem_monomialIdeal.mpr ⟨u, huS, le_rfl⟩
    have hueq := he.2 u huI hue
    simpa [hueq] using huS
  · intro heS
    rw [mem_minGens]
    refine ⟨monomial_mem_monomialIdeal.mpr ⟨e, heS, le_rfl⟩, ?_⟩
    intro u huI hue
    rcases monomial_mem_monomialIdeal.mp huI with ⟨v, hvS, hvu⟩
    have hve : v = e := hanti e heS v hvS (le_trans hvu hue)
    rw [hve] at hvu
    exact le_antisymm hue hvu

/-- The support of a characteristic exponent is the defining finite set. -/
theorem cor33_characteristicExp_support (A : Finset σ) :
    (characteristicExp A).support = A := by
  ext i
  simp [Finsupp.mem_support_iff, characteristicExp_apply]

/-- The squarefree monomial on the support of a generator lies in the radical. -/
theorem cor33_characteristicExp_mem_radical {S : Set (σ →₀ ℕ)} {u : σ →₀ ℕ} (hu : u ∈ S) :
    (monomial (characteristicExp u.support) (1 : K) : MvPolynomial σ K) ∈
      (monomialIdeal S : Ideal (MvPolynomial σ K)).radical := by
  rw [Ideal.mem_radical_iff]
  let N : ℕ := u.support.sup u + 1
  refine ⟨N, ?_⟩
  rw [monomial_pow, one_pow]
  apply monomial_mem_monomialIdeal.mpr
  refine ⟨u, hu, ?_⟩
  rw [Finsupp.le_def]
  intro i
  by_cases hi : u i = 0
  · simp [hi]
  · have his : i ∈ u.support := by simpa [Finsupp.mem_support_iff] using hi
    have himax : u i ≤ u.support.sup u := Finset.le_sup his
    have hiN : u i ≤ N := le_trans himax (Nat.le_succ _)
    have hichar : characteristicExp u.support i = 1 := by
      simp [characteristicExp_apply, his]
    simp [Finsupp.nsmul_apply, hichar, hiN, N]

/-- For an antichain of generators with antichain supports, taking the radical preserves
their support complex. This isolates the support-comparison part of Corollary 3.3. -/
theorem cor33_supportPreserving_monomialIdeal_of_antichain {S : Set (σ →₀ ℕ)}
    (hanti : ∀ e ∈ S, ∀ u ∈ S, u ≤ e → u = e)
    (hsupp : ∀ e ∈ S, ∀ u ∈ S, u.support ⊆ e.support → u = e) :
    SupportPreserving (monomialIdeal S : Ideal (MvPolynomial σ K)) := by
  rw [SupportPreserving, supportComplex, supportComplex]
  ext A
  constructor
  · rintro ⟨e, hemin, rfl⟩
    have heS : e ∈ S := by
      simpa [cor33_minGens_monomialIdeal_eq hanti] using hemin
    let f : σ →₀ ℕ := characteristicExp e.support
    have hfmem : (monomial f (1 : K) : MvPolynomial σ K) ∈
        (monomialIdeal S : Ideal (MvPolynomial σ K)).radical :=
      cor33_characteristicExp_mem_radical (S := S) heS
    have hfmin : f ∈ minGens (monomialIdeal S : Ideal (MvPolynomial σ K)).radical := by
      rw [mem_minGens]
      refine ⟨hfmem, ?_⟩
      intro u huI huf
      rw [Ideal.mem_radical_iff] at huI
      rcases huI with ⟨N, hNI⟩
      rw [monomial_pow, one_pow] at hNI
      rcases monomial_mem_monomialIdeal.mp hNI with ⟨v, hvS, hvle⟩
      have hvsupp : v.support ⊆ u.support := by
        intro i hi
        by_contra hnot
        have hui : u i = 0 := by
          by_contra hui
          exact hnot (by simpa [Finsupp.mem_support_iff] using hui)
        have hni : (N • u) i = 0 := by simp [hui]
        have hvi : v i ≠ 0 := by simpa [Finsupp.mem_support_iff] using hi
        have hvlei := hvle i
        exact hvi (by simpa [hni] using hvlei)
      have husupp : u.support ⊆ e.support := by
        intro i hiu
        by_contra hnot
        have hfi : f i = 0 := by simp [f, characteristicExp_apply, hnot]
        have hui : u i ≠ 0 := by simpa [Finsupp.mem_support_iff] using hiu
        have hufi := huf i
        exact hui (by omega)
      have hve : v = e := hsupp e heS v hvS (hvsupp.trans husupp)
      have ehusupp : e.support ⊆ u.support := by
        intro i hi
        apply hvsupp
        simpa [hve] using hi
      have hsuppeq : u.support = e.support := le_antisymm husupp ehusupp
      ext i
      by_cases hi : i ∈ e.support
      · have hfi : f i = 1 := by simp [f, characteristicExp_apply, hi]
        have hiu : i ∈ u.support := by simpa [hsuppeq] using hi
        have hui : u i ≠ 0 := by simpa [Finsupp.mem_support_iff] using hiu
        have hufi := huf i
        omega
      · have hfi : f i = 0 := by simp [f, characteristicExp_apply, hi]
        have hufi := huf i
        omega
    refine ⟨f, hfmin, ?_⟩
    simp [f, cor33_characteristicExp_support]
  · rintro ⟨e, hemin, rfl⟩
    rw [mem_minGens] at hemin
    rcases (Ideal.mem_radical_iff.mp hemin.1) with ⟨N, hNI⟩
    rw [monomial_pow, one_pow] at hNI
    rcases monomial_mem_monomialIdeal.mp hNI with ⟨v, hvS, hvle⟩
    have hvsupp : v.support ⊆ e.support := by
      intro i hi
      by_contra hnot
      have hei : e i = 0 := by
        by_contra hei
        exact hnot (by simpa [Finsupp.mem_support_iff] using hei)
      have hni : (N • e) i = 0 := by simp [hei]
      have hvi : v i ≠ 0 := by simpa [Finsupp.mem_support_iff] using hi
      have hvlei := hvle i
      exact hvi (by simpa [hni] using hvlei)
    let f : σ →₀ ℕ := characteristicExp v.support
    have hfmem : (monomial f (1 : K) : MvPolynomial σ K) ∈
        (monomialIdeal S : Ideal (MvPolynomial σ K)).radical :=
      cor33_characteristicExp_mem_radical (S := S) hvS
    have hfle : f ≤ e := by
      rw [Finsupp.le_def]
      intro i
      by_cases hi : i ∈ v.support
      · have hie := hvsupp hi
        have heipos : 0 < e i := Nat.pos_of_ne_zero
          (by simpa [Finsupp.mem_support_iff] using hie)
        have heione : 1 ≤ e i := Nat.succ_le_iff.mpr heipos
        simpa [f, characteristicExp_apply, hi] using heione
      · simp [f, characteristicExp_apply, hi]
    have hfe : f = e := hemin.2 f hfmem hfle
    have hvmin : v ∈ minGens (monomialIdeal S : Ideal (MvPolynomial σ K)) := by
      simpa [cor33_minGens_monomialIdeal_eq hanti] using hvS
    refine ⟨v, hvmin, ?_⟩
    calc
      v.support = (characteristicExp v.support).support :=
        (cor33_characteristicExp_support v.support).symm
      _ = e.support := congrArg Finsupp.support hfe

/-- Membership of an arbitrary polynomial in a cone is tested supportwise. -/
theorem cor33_mem_coneIdeal_iff_support {I : Ideal (MvPolynomial σ K)}
    (hI : IsMonomialIdeal I) {x : MvPolynomial (Option σ) K} :
    x ∈ coneIdeal I ↔ ∀ e ∈ x.support,
      1 ≤ e none ∧ (monomial (optionRestrict e) (1 : K) : MvPolynomial σ K) ∈ I := by
  rcases hI with ⟨S, rfl⟩
  rw [cor33_coneIdeal_monomialIdeal, mem_monomialIdeal]
  constructor
  · intro hx e he
    rcases hx e he with ⟨z, ⟨u, huS, rfl⟩, hzle⟩
    have hcv := coneExp_le_iff.mp hzle
    exact ⟨hcv.1, monomial_mem_monomialIdeal.mpr ⟨u, huS, hcv.2⟩⟩
  · intro hx e he
    rcases monomial_mem_monomialIdeal.mp (hx e he).2 with ⟨u, huS, hule⟩
    exact ⟨coneExp u, ⟨u, huS, rfl⟩,
      coneExp_le_iff.mpr ⟨(hx e he).1, hule⟩⟩

/-- Coning sends minimal monomial generators to minimal monomial generators. -/
theorem cor33_minGens_coneIdeal {I : Ideal (MvPolynomial σ K)} (hI : IsMonomialIdeal I) :
    minGens (coneIdeal I) = coneExp '' minGens I := by
  ext e
  constructor
  · intro he
    rw [mem_minGens] at he
    have hcone := (monomial_mem_coneIdeal hI).mp he.1
    rcases exists_minGens_le hcone.2 with ⟨u, hu, hule⟩
    have hucone : (monomial (coneExp u) (1 : K) : MvPolynomial (Option σ) K) ∈ coneIdeal I :=
      (monomial_mem_coneIdeal hI).mpr ⟨by simp, by simpa using (mem_minGens.mp hu).1⟩
    have hcule : coneExp u ≤ e := coneExp_le_iff.mpr ⟨hcone.1, hule⟩
    exact ⟨u, hu, he.2 (coneExp u) hucone hcule⟩
  · rintro ⟨u, hu, rfl⟩
    rw [mem_minGens] at hu ⊢
    refine ⟨(monomial_mem_coneIdeal hI).mpr ⟨by simp, by simpa using hu.1⟩, ?_⟩
    intro e heI hele
    have hecone := (monomial_mem_coneIdeal hI).mp heI
    have hrestle : optionRestrict e ≤ u := by
      rw [Finsupp.le_def]
      intro i
      simpa using hele (some i)
    have hrest : optionRestrict e = u := hu.2 (optionRestrict e) hecone.2 hrestle
    have hnone : e none = 1 := le_antisymm (by simpa using hele none) hecone.1
    ext x
    cases x with
    | none => simp [hnone]
    | some i =>
        have hi := congrArg (fun f : σ →₀ ℕ => f i) hrest
        simpa [optionRestrict_apply, coneExp_apply_some] using hi

/-- The cone exponent has the expected support. -/
theorem cor33_coneExp_support (e : σ →₀ ℕ) :
    (coneExp e).support = insert none (Finset.image some e.support) := by
  ext x
  cases x <;> simp [Finsupp.mem_support_iff]

/-- Coning a monomial ideal cones its support complex. -/
theorem cor33_supportComplex_coneIdeal {I : Ideal (MvPolynomial σ K)}
    (hI : IsMonomialIdeal I) :
    supportComplex (coneIdeal I) = coneClutter (supportComplex I) := by
  rw [supportComplex, coneClutter, cor33_minGens_coneIdeal hI]
  ext A
  constructor
  · rintro ⟨e, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨u.support, ?_, ?_⟩
    · exact ⟨u, hu, rfl⟩
    · exact (cor33_coneExp_support u).symm
  · rintro ⟨A, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨coneExp u, ?_, ?_⟩
    · exact ⟨u, hu, rfl⟩
    · rw [cor33_coneExp_support]

/-- Coning a squarefree monomial gives the characteristic exponent of the coned support. -/
theorem cor33_coneExp_characteristicExp (A : Finset σ) :
    coneExp (characteristicExp A) =
      characteristicExp (insert none (Finset.image some A)) := by
  ext x
  cases x <;> simp [coneExp_apply_none, coneExp_apply_some, characteristicExp_apply]

omit [DecidableEq σ] in
/-- A diagonal map fixing the cone variable commutes with exponent coning. -/
theorem cor33_diagExp_coneExp (d : Option σ → ℕ) (hdn : d none = 1) (e : σ →₀ ℕ) :
    diagExp d (coneExp e) = coneExp (diagExp (fun i => d (some i)) e) := by
  ext x
  cases x <;> simp [diagExp_apply, hdn]

/-- Coning preserves squarefreeness of a represented squarefree monomial ideal. -/
theorem cor33_coneIdeal_isSquarefree {I : Ideal (MvPolynomial σ K)}
    (hI : IsSquarefreeMonomialIdeal I) :
    IsSquarefreeMonomialIdeal (coneIdeal I) := by
  rcases hI with ⟨H, hI⟩
  have himage : coneExp '' (characteristicExp '' H) =
      characteristicExp '' coneClutter H := by
    ext e
    constructor
    · rintro ⟨_, ⟨A, hA, rfl⟩, rfl⟩
      refine ⟨insert none (Finset.image some A), ?_, ?_⟩
      · exact ⟨A, hA, rfl⟩
      · exact (cor33_coneExp_characteristicExp A).symm
    · rintro ⟨B, ⟨A, hA, hB⟩, hBe⟩
      subst B
      rw [← cor33_coneExp_characteristicExp A] at hBe
      exact ⟨characteristicExp A, ⟨A, hA, rfl⟩, hBe⟩
  refine ⟨coneClutter H, ?_⟩
  rw [hI, cor33_coneIdeal_monomialIdeal, himage]

/-- Diagonal maps fixing the cone variable commute with coning monomial ideals. -/
theorem cor33_diagonal_coneIdeal [Fintype σ] {I : Ideal (MvPolynomial σ K)}
    (hI : IsMonomialIdeal I) {D : Option σ → ℕ} (hD : D none = 1) :
    diagonal D (coneIdeal I) = coneIdeal (diagonal (fun i => D (some i)) I) := by
  rcases hI with ⟨S, rfl⟩
  let d : σ → ℕ := fun i => D (some i)
  have himage : diagExp D '' (coneExp '' S) = coneExp '' (diagExp d '' S) := by
    ext e
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨diagExp d u, ⟨u, hu, rfl⟩, ?_⟩
      exact (cor33_diagExp_coneExp D hD u).symm
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨coneExp u, ⟨u, hu, rfl⟩, ?_⟩
      exact cor33_diagExp_coneExp D hD u
  calc
    diagonal D (coneIdeal (monomialIdeal S : Ideal (MvPolynomial σ K))) =
        diagonal D (monomialIdeal (coneExp '' S) : Ideal (MvPolynomial (Option σ) K)) := by
      rw [cor33_coneIdeal_monomialIdeal]
    _ = monomialIdeal (diagExp D '' (coneExp '' S)) := by
      rw [diagonal_monomialIdeal]
    _ = monomialIdeal (coneExp '' (diagExp d '' S)) := by rw [himage]
    _ = coneIdeal (monomialIdeal (diagExp d '' S) : Ideal (MvPolynomial σ K)) := by
      rw [cor33_coneIdeal_monomialIdeal]
    _ = coneIdeal (diagonal d (monomialIdeal S : Ideal (MvPolynomial σ K))) := by
      rw [diagonal_monomialIdeal]

/-- Minimal generators of a positive diagonal image of a squarefree monomial ideal have
only zero or the common weight in each coordinate. -/
theorem cor33_sqRoot_minGen_coordinate [Fintype σ]
    {I J : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hJ : IsSquarefreeMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hdiag : diagonal d J = I) {e : σ →₀ ℕ} (he : e ∈ minGens I) (i : σ) :
    e i = 0 ∨ e i = d i := by
  rcases hJ with ⟨H, hJ⟩
  have hJmon : IsMonomialIdeal J := ⟨characteristicExp '' H, hJ⟩
  rw [mem_minGens] at he
  let u : σ →₀ ℕ := floorDiv d e
  have heD : (monomial e (1 : K) : MvPolynomial σ K) ∈ diagonal d J := by
    simpa [hdiag] using he.1
  have huJ : (monomial u (1 : K) : MvPolynomial σ K) ∈ J := by
    simpa [u] using (monomial_mem_diagonal (K := K) hJmon hd (e := e)).mp heD
  have hdiagU_D : (monomial (diagExp d u) (1 : K) : MvPolynomial σ K) ∈ diagonal d J := by
    apply (monomial_mem_diagonal (K := K) hJmon hd (e := diagExp d u)).mpr
    simpa [eq4_floorDiv_diagExp hd u] using huJ
  have hdiagU_I : (monomial (diagExp d u) (1 : K) : MvPolynomial σ K) ∈ I := by
    simpa [hdiag] using hdiagU_D
  have hdiagU_le : diagExp d u ≤ e := by
    apply (diagExp_le_iff_floor hd u e).2
    simp [u]
  have hdiagU_eq : diagExp d u = e := he.2 (diagExp d u) hdiagU_I hdiagU_le
  rw [hJ] at huJ
  rcases monomial_mem_monomialIdeal.mp huJ with ⟨v, hv, hvu⟩
  rcases hv with ⟨A, hA, rfl⟩
  have hcharJ : (monomial (characteristicExp A) (1 : K) : MvPolynomial σ K) ∈ J := by
    rw [hJ]
    exact monomial_mem_monomialIdeal.mpr ⟨characteristicExp A, ⟨A, hA, rfl⟩, le_rfl⟩
  have hdiagChar_D : (monomial (diagExp d (characteristicExp A)) (1 : K) :
      MvPolynomial σ K) ∈ diagonal d J := by
    apply (monomial_mem_diagonal (K := K) hJmon hd
      (e := diagExp d (characteristicExp A))).mpr
    simpa [eq4_floorDiv_diagExp hd (characteristicExp A)] using hcharJ
  have hdiagChar_I : (monomial (diagExp d (characteristicExp A)) (1 : K) :
      MvPolynomial σ K) ∈ I := by
    simpa [hdiag] using hdiagChar_D
  have hdiagChar_le : diagExp d (characteristicExp A) ≤ e := by
    calc
      diagExp d (characteristicExp A) ≤ diagExp d u := by
        rw [Finsupp.le_def]
        intro j
        simpa [diagExp_apply] using Nat.mul_le_mul_right (d j) (hvu j)
      _ = e := hdiagU_eq
  have hdiagChar_eq : diagExp d (characteristicExp A) = e :=
    he.2 (diagExp d (characteristicExp A)) hdiagChar_I hdiagChar_le
  have hchar_eq : characteristicExp A = u := by
    have hEq : diagExp d (characteristicExp A) = diagExp d u :=
      hdiagChar_eq.trans hdiagU_eq.symm
    ext j
    have hj := congrArg (fun f : σ →₀ ℕ => f j) hEq
    simp only [diagExp_apply] at hj
    exact Nat.mul_right_cancel (hd j) hj
  have hecoord : e i = characteristicExp A i * d i := by
    have hi := congrArg (fun f : σ →₀ ℕ => f i) hdiagU_eq
    simp only [diagExp_apply] at hi
    rw [← hchar_eq] at hi
    exact hi.symm
  by_cases hi : i ∈ A
  · right
    simpa [characteristicExp_apply, hi] using hecoord
  · left
    simpa [characteristicExp_apply, hi] using hecoord

instance : Fintype Cor33Comp where
  elems := {Cor33Comp.q1, Cor33Comp.q2, Cor33Comp.q3, Cor33Comp.q4}
  complete := by intro x; cases x <;> simp

@[simp] theorem cor33Exp_apply (a b c d z : ℕ) (i : Cor33Var) :
    cor33Exp a b c d z i =
      match i with
      | Cor33Var.a => a
      | Cor33Var.b => b
      | Cor33Var.c => c
      | Cor33Var.d => d
      | Cor33Var.z => z := by
  cases i <;> simp [cor33Exp]

@[simp] theorem cor33ConeWeight_none (rho : ℕ) :
    cor33ConeWeight rho none = 1 := rfl

theorem cor33BaseWeight_pos {rho : ℕ} (hr : 0 < rho) :
    ∀ i, 0 < cor33BaseWeight rho i := by
  intro i
  cases i <;> simp [cor33BaseWeight, hr]

theorem cor33ConeWeight_pos {rho : ℕ} (hr : 0 < rho) :
    ∀ i, 0 < cor33ConeWeight rho i := by
  intro i
  cases i with
  | none => simp [cor33ConeWeight]
  | some i =>
      cases i <;> simp [cor33ConeWeight, cor33BaseWeight, hr]

@[simp] theorem cor33_diagExp_cor33Exp (w : Cor33Var → ℕ) (a b c d z : ℕ) :
    diagExp w (cor33Exp a b c d z) =
      cor33Exp (a * w Cor33Var.a) (b * w Cor33Var.b) (c * w Cor33Var.c)
        (d * w Cor33Var.d) (z * w Cor33Var.z) := by
  ext i
  cases i <;> simp [diagExp_apply, cor33Exp_apply]

/-- The generator clutter \(ac,bd,abz,cdz\) contains the displayed strong triangle. -/
theorem cor33_baseClutter_hasStrongTriangle : HasStrongTriangle cor33BaseClutter := by
  rw [HasStrongTriangle, HasStrongCycle]
  let v : Fin 3 → Cor33Var := ![Cor33Var.a, Cor33Var.c, Cor33Var.z]
  let E : Fin 3 → Finset Cor33Var :=
    ![{Cor33Var.a, Cor33Var.c}, {Cor33Var.c, Cor33Var.d, Cor33Var.z},
      {Cor33Var.a, Cor33Var.b, Cor33Var.z}]
  refine ⟨by omega, v, ?_, E, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [v] at hij ⊢
  · intro i j hij
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals
      exfalso
      have ha := congrArg (fun F : Finset Cor33Var => Cor33Var.a ∈ F) hij
      have hb := congrArg (fun F : Finset Cor33Var => Cor33Var.b ∈ F) hij
      have hc := congrArg (fun F : Finset Cor33Var => Cor33Var.c ∈ F) hij
      have hd := congrArg (fun F : Finset Cor33Var => Cor33Var.d ∈ F) hij
      have hz := congrArg (fun F : Finset Cor33Var => Cor33Var.z ∈ F) hij
      simp [E] at ha hb hc hd hz
  · intro i
    fin_cases i <;> simp [E, cor33BaseClutter]
  · have huniv :
        Finset.univ.image v =
          ({Cor33Var.a, Cor33Var.c, Cor33Var.z} : Finset Cor33Var) := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨i, _, hi⟩
        fin_cases i
        · have hi' : x = Cor33Var.a := by simpa [v] using hi.symm
          simp [hi']
        · have hi' : x = Cor33Var.c := by simpa [v] using hi.symm
          simp [hi']
        · have hi' : x = Cor33Var.z := by simpa [v] using hi.symm
          simp [hi']
      · intro hx
        have hx' : x = Cor33Var.a ∨ x = Cor33Var.c ∨ x = Cor33Var.z := by simpa using hx
        rcases hx' with hxa | hxc | hxz
        · exact Finset.mem_image.mpr ⟨0, by simp, by simp [v, hxa]⟩
        · exact Finset.mem_image.mpr ⟨1, by simp, by simp [v, hxc]⟩
        · exact Finset.mem_image.mpr ⟨2, by simp, by simp [v, hxz]⟩
    intro i
    rw [huniv]
    fin_cases i
    · ext x
      simp [E, v, finSuccMod]
    · ext x
      simp [E, v, finSuccMod]
    · ext x
      simp [E, v, finSuccMod]
      tauto

/-- Its coned generator clutter contains a strong triangle as well. -/
theorem cor33_coneBaseClutter_hasStrongTriangle :
    HasStrongTriangle (coneClutter cor33BaseClutter) :=
  coneClutter_hasStrongCycle cor33_baseClutter_hasStrongTriangle

/-- The generator clutter is not balanced. -/
theorem cor33_baseClutter_not_isBalanced : ¬ IsBalanced cor33BaseClutter :=
  cor33_hasStrongTriangle_not_isBalanced cor33_baseClutter_hasStrongTriangle

/-- Coning preserves this failure of balancedness for the generator clutter. -/
theorem cor33_coneBaseClutter_not_isBalanced : ¬ IsBalanced (coneClutter cor33BaseClutter) :=
  cor33_hasStrongTriangle_not_isBalanced cor33_coneBaseClutter_hasStrongTriangle

@[simp] theorem cor33Exp_support_ac :
    (cor33Exp 1 0 1 0 0).support = {Cor33Var.a, Cor33Var.c} := by
  ext i
  cases i <;> simp [Finsupp.mem_support_iff, cor33Exp_apply]

@[simp] theorem cor33Exp_support_bd :
    (cor33Exp 0 1 0 1 0).support = {Cor33Var.b, Cor33Var.d} := by
  ext i
  cases i <;> simp [Finsupp.mem_support_iff, cor33Exp_apply]

theorem cor33Exp_support_abz_of_pos {r : ℕ} (hr : 0 < r) :
    (cor33Exp 1 1 0 0 r).support = {Cor33Var.a, Cor33Var.b, Cor33Var.z} := by
  ext i
  cases i <;> simp [Finsupp.mem_support_iff, cor33Exp_apply, Nat.ne_of_gt hr]

theorem cor33Exp_support_cdz_of_pos {s : ℕ} (hs : 0 < s) :
    (cor33Exp 0 0 1 1 s).support = {Cor33Var.c, Cor33Var.d, Cor33Var.z} := by
  ext i
  cases i <;> simp [Finsupp.mem_support_iff, cor33Exp_apply, Nat.ne_of_gt hs]

@[simp] theorem cor33_characteristicExp_eq_ac :
    characteristicExp ({Cor33Var.a, Cor33Var.c} : Finset Cor33Var) =
      cor33Exp 1 0 1 0 0 := by
  ext i
  cases i <;> simp [characteristicExp_apply, cor33Exp_apply]

@[simp] theorem cor33_characteristicExp_eq_bd :
    characteristicExp ({Cor33Var.b, Cor33Var.d} : Finset Cor33Var) =
      cor33Exp 0 1 0 1 0 := by
  ext i
  cases i <;> simp [characteristicExp_apply, cor33Exp_apply]

@[simp] theorem cor33_characteristicExp_eq_abz :
    characteristicExp ({Cor33Var.a, Cor33Var.b, Cor33Var.z} : Finset Cor33Var) =
      cor33Exp 1 1 0 0 1 := by
  ext i
  cases i <;> simp [characteristicExp_apply, cor33Exp_apply]

@[simp] theorem cor33_characteristicExp_eq_cdz :
    characteristicExp ({Cor33Var.c, Cor33Var.d, Cor33Var.z} : Finset Cor33Var) =
      cor33Exp 0 0 1 1 1 := by
  ext i
  cases i <;> simp [characteristicExp_apply, cor33Exp_apply]

/-- The exponent set of the squarefree root is the characteristic image of its clutter. -/
theorem cor33_baseGens_one_eq_characteristic :
    (cor33BaseGens 1 1 : Set (Cor33Var →₀ ℕ)) =
      characteristicExp '' cor33BaseClutter := by
  ext e
  constructor
  · intro he
    simp [cor33BaseGens] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨{Cor33Var.a, Cor33Var.c}, by simp [cor33BaseClutter], by simp⟩
    · exact ⟨{Cor33Var.b, Cor33Var.d}, by simp [cor33BaseClutter], by simp⟩
    · exact ⟨{Cor33Var.a, Cor33Var.b, Cor33Var.z}, by simp [cor33BaseClutter], by simp⟩
    · exact ⟨{Cor33Var.c, Cor33Var.d, Cor33Var.z}, by simp [cor33BaseClutter], by simp⟩
  · rintro ⟨A, hA, rfl⟩
    simp [cor33BaseClutter] at hA
    rcases hA with rfl | rfl | rfl | rfl <;> simp [cor33BaseGens]

/-- The displayed squarefree ideal is indeed squarefree. -/
theorem cor33_radicalIdeal_isSquarefree :
    IsSquarefreeMonomialIdeal (cor33RadicalIdeal (K := K)) := by
  rw [IsSquarefreeMonomialIdeal, cor33RadicalIdeal, cor33BaseIdeal]
  exact ⟨cor33BaseClutter, congrArg monomialIdeal cor33_baseGens_one_eq_characteristic⟩

/-- The diagonal weighting of the squarefree root with equal parameters \(\rho\). -/
theorem cor33_diagonal_radicalIdeal_base (rho : ℕ) :
    diagonal (cor33BaseWeight rho) (cor33RadicalIdeal (K := K)) =
      cor33BaseIdeal (K := K) rho rho := by
  rw [cor33RadicalIdeal, cor33BaseIdeal, diagonal_monomialIdeal]
  congr 1
  ext e
  constructor
  · rintro ⟨u, hu, rfl⟩
    simp [cor33BaseGens] at hu
    rcases hu with rfl | rfl | rfl | rfl
    all_goals simp [cor33BaseGens, cor33BaseWeight]
  · intro he
    simp [cor33BaseGens] at he
    rcases he with rfl | rfl | rfl | rfl
    · refine ⟨cor33Exp 1 0 1 0 0, by simp [cor33BaseGens], ?_⟩
      simp [cor33BaseWeight]
    · refine ⟨cor33Exp 0 1 0 1 0, by simp [cor33BaseGens], ?_⟩
      simp [cor33BaseWeight]
    · refine ⟨cor33Exp 1 1 0 0 1, by simp [cor33BaseGens], ?_⟩
      simp [cor33BaseWeight]
    · refine ⟨cor33Exp 0 0 1 1 1, by simp [cor33BaseGens], ?_⟩
      simp [cor33BaseWeight]

/-- The four displayed generators form a divisibility antichain. -/
theorem cor33_baseGens_antichain {r s : ℕ} :
    ∀ e ∈ (cor33BaseGens r s : Set (Cor33Var →₀ ℕ)),
      ∀ u ∈ (cor33BaseGens r s : Set (Cor33Var →₀ ℕ)), u ≤ e → u = e := by
  intro e he u hu hle
  simp [cor33BaseGens] at he hu
  rcases he with rfl | rfl | rfl | rfl <;>
    rcases hu with rfl | rfl | rfl | rfl <;> try rfl
  all_goals
    exfalso
    have hla := hle Cor33Var.a
    have hlb := hle Cor33Var.b
    have hlc := hle Cor33Var.c
    have hld := hle Cor33Var.d
    have hlz := hle Cor33Var.z
    simp [cor33Exp_apply] at hla hlb hlc hld hlz

/-- The supports of the displayed generators also form an antichain. -/
theorem cor33_baseGens_support_antichain {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ∀ e ∈ (cor33BaseGens r s : Set (Cor33Var →₀ ℕ)),
      ∀ u ∈ (cor33BaseGens r s : Set (Cor33Var →₀ ℕ)),
        u.support ⊆ e.support → u = e := by
  intro e he u hu hsub
  simp [cor33BaseGens] at he hu
  rcases he with rfl | rfl | rfl | rfl <;>
    rcases hu with rfl | rfl | rfl | rfl <;> try rfl
  all_goals
    exfalso
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff,
      cor33Exp_support_ac, cor33Exp_support_bd,
      cor33Exp_support_abz_of_pos hr, cor33Exp_support_cdz_of_pos hs] at hsub

/-- The support complex of the base ideal is the clutter displayed in the paper. -/
theorem cor33_base_supportComplex {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    supportComplex (cor33BaseIdeal (K := K) r s) = cor33BaseClutter := by
  rw [cor33BaseIdeal, supportComplex, cor33_minGens_monomialIdeal_eq]
  ext A
  change (∃ e ∈ (cor33BaseGens r s : Set (Cor33Var →₀ ℕ)), e.support = A) ↔
    A ∈ cor33BaseClutter
  constructor
  · rintro ⟨e, he, rfl⟩
    simp [cor33BaseGens] at he
    rcases he with rfl | rfl | rfl | rfl
    · simp [cor33BaseClutter, cor33Exp_support_ac]
    · simp [cor33BaseClutter, cor33Exp_support_bd]
    · have hmem : (cor33Exp 1 1 0 0 r).support ∈ cor33BaseClutter := by
        simp [cor33BaseClutter, cor33Exp_support_abz_of_pos hr]
      simpa using hmem
    · have hmem : (cor33Exp 0 0 1 1 s).support ∈ cor33BaseClutter := by
        simp [cor33BaseClutter, cor33Exp_support_cdz_of_pos hs]
      simpa using hmem
  · intro hA
    simp [cor33BaseClutter] at hA
    rcases hA with rfl | rfl | rfl | rfl
    · exact ⟨cor33Exp 1 0 1 0 0, by simp [cor33BaseGens], cor33Exp_support_ac⟩
    · exact ⟨cor33Exp 0 1 0 1 0, by simp [cor33BaseGens], cor33Exp_support_bd⟩
    · exact ⟨cor33Exp 1 1 0 0 r, by simp [cor33BaseGens],
        cor33Exp_support_abz_of_pos hr⟩
    · exact ⟨cor33Exp 0 0 1 1 s, by simp [cor33BaseGens],
        cor33Exp_support_cdz_of_pos hs⟩
  · exact cor33_baseGens_antichain

/-- The base support complex contains a strong triangle. -/
theorem cor33_base_supportComplex_hasStrongTriangle {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    HasStrongTriangle (supportComplex (cor33BaseIdeal (K := K) r s)) := by
  rw [cor33_base_supportComplex (K := K) hr hs]
  exact cor33_baseClutter_hasStrongTriangle

/-- The base support complex is not balanced. -/
theorem cor33_base_supportComplex_not_isBalanced {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ¬ IsBalanced (supportComplex (cor33BaseIdeal (K := K) r s)) :=
  cor33_hasStrongTriangle_not_isBalanced
    (cor33_base_supportComplex_hasStrongTriangle (K := K) hr hs)

/-- The base example preserves supports. -/
theorem cor33_base_supportPreserving {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    SupportPreserving (cor33BaseIdeal (K := K) r s) := by
  rw [cor33BaseIdeal]
  exact cor33_supportPreserving_monomialIdeal_of_antichain cor33_baseGens_antichain
    (cor33_baseGens_support_antichain hr hs)

/-- The component clutter \(abz,ad,bc,cdz\) of the base decomposition. -/
def cor33ComponentClutter : Set (Finset Cor33Var) :=
  {A | A = {Cor33Var.a, Cor33Var.b, Cor33Var.z} ∨ A = {Cor33Var.a, Cor33Var.d} ∨
    A = {Cor33Var.b, Cor33Var.c} ∨ A = {Cor33Var.c, Cor33Var.d, Cor33Var.z}}

/-- The displayed component clutter is exactly the range of component supports. -/
theorem cor33_componentClutter_eq_range :
    cor33ComponentClutter = Set.range cor33ComponentSupport := by
  ext A
  constructor
  · intro hA
    change A = {Cor33Var.a, Cor33Var.b, Cor33Var.z} ∨ A = {Cor33Var.a, Cor33Var.d} ∨
      A = {Cor33Var.b, Cor33Var.c} ∨ A = {Cor33Var.c, Cor33Var.d, Cor33Var.z} at hA
    rcases hA with hA | hA | hA | hA
    · exact ⟨Cor33Comp.q1, by simp [hA, cor33ComponentSupport]⟩
    · exact ⟨Cor33Comp.q2, by simp [hA, cor33ComponentSupport]⟩
    · exact ⟨Cor33Comp.q3, by simp [hA, cor33ComponentSupport]⟩
    · exact ⟨Cor33Comp.q4, by simp [hA, cor33ComponentSupport]⟩
  · rintro ⟨j, rfl⟩
    cases j <;> simp [cor33ComponentSupport, cor33ComponentClutter]

/-- The component clutter \(abz,ad,bc,cdz\) contains the second displayed triangle. -/
theorem cor33_componentClutter_hasStrongTriangle : HasStrongTriangle cor33ComponentClutter := by
  rw [HasStrongTriangle, HasStrongCycle]
  let v : Fin 3 → Cor33Var := ![Cor33Var.a, Cor33Var.d, Cor33Var.z]
  let E : Fin 3 → Finset Cor33Var :=
    ![{Cor33Var.a, Cor33Var.d}, {Cor33Var.c, Cor33Var.d, Cor33Var.z},
      {Cor33Var.a, Cor33Var.b, Cor33Var.z}]
  refine ⟨by omega, v, ?_, E, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [v] at hij ⊢
  · intro i j hij
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals
      exfalso
      have ha := congrArg (fun F : Finset Cor33Var => Cor33Var.a ∈ F) hij
      have hb := congrArg (fun F : Finset Cor33Var => Cor33Var.b ∈ F) hij
      have hc := congrArg (fun F : Finset Cor33Var => Cor33Var.c ∈ F) hij
      have hd := congrArg (fun F : Finset Cor33Var => Cor33Var.d ∈ F) hij
      have hz := congrArg (fun F : Finset Cor33Var => Cor33Var.z ∈ F) hij
      simp [E] at ha hb hc hd hz
  · intro i
    fin_cases i <;> simp [E, cor33ComponentClutter]
  · have huniv :
        Finset.univ.image v =
          ({Cor33Var.a, Cor33Var.d, Cor33Var.z} : Finset Cor33Var) := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨i, _, hi⟩
        fin_cases i
        · have hi' : x = Cor33Var.a := by simpa [v] using hi.symm
          simp [hi']
        · have hi' : x = Cor33Var.d := by simpa [v] using hi.symm
          simp [hi']
        · have hi' : x = Cor33Var.z := by simpa [v] using hi.symm
          simp [hi']
      · intro hx
        have hx' : x = Cor33Var.a ∨ x = Cor33Var.d ∨ x = Cor33Var.z := by simpa using hx
        rcases hx' with hxa | hxd | hxz
        · exact Finset.mem_image.mpr ⟨0, by simp, by simp [v, hxa]⟩
        · exact Finset.mem_image.mpr ⟨1, by simp, by simp [v, hxd]⟩
        · exact Finset.mem_image.mpr ⟨2, by simp, by simp [v, hxz]⟩
    intro i
    rw [huniv]
    fin_cases i
    · ext x
      simp [E, v, finSuccMod]
    · ext x
      simp [E, v, finSuccMod]
    · ext x
      simp [E, v, finSuccMod]
      tauto

/-- The component clutter is not balanced. -/
theorem cor33_componentClutter_not_isBalanced : ¬ IsBalanced cor33ComponentClutter :=
  cor33_hasStrongTriangle_not_isBalanced cor33_componentClutter_hasStrongTriangle

theorem cor33_componentExp_pos {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ∀ j i, i ∈ cor33ComponentSupport j → 0 < cor33ComponentExp r s j i := by
  intro j i hi
  cases j with
  | q1 =>
      simp [cor33ComponentSupport] at hi
      rcases hi with rfl | rfl | rfl <;> simp [cor33ComponentExp, cor33Exp_apply, hs]
  | q2 =>
      simp [cor33ComponentSupport] at hi
      rcases hi with rfl | rfl <;> simp [cor33ComponentExp, cor33Exp_apply]
  | q3 =>
      simp [cor33ComponentSupport] at hi
      rcases hi with rfl | rfl <;> simp [cor33ComponentExp, cor33Exp_apply]
  | q4 =>
      simp [cor33ComponentSupport] at hi
      rcases hi with rfl | rfl | rfl <;> simp [cor33ComponentExp, cor33Exp_apply, hr]

/-- At weight one, component exponents are exactly one on their supports. -/
theorem cor33_componentExp_one (j : Cor33Comp) {i : Cor33Var}
    (hi : i ∈ cor33ComponentSupport j) : cor33ComponentExp 1 1 j i = 1 := by
  cases j with
  | q1 =>
      simp [cor33ComponentSupport] at hi
      rcases hi with rfl | rfl | rfl <;> simp [cor33ComponentExp, cor33Exp_apply]
  | q2 =>
      simp [cor33ComponentSupport] at hi
      rcases hi with rfl | rfl <;> simp [cor33ComponentExp, cor33Exp_apply]
  | q3 =>
      simp [cor33ComponentSupport] at hi
      rcases hi with rfl | rfl <;> simp [cor33ComponentExp, cor33Exp_apply]
  | q4 =>
      simp [cor33ComponentSupport] at hi
      rcases hi with rfl | rfl | rfl <;> simp [cor33ComponentExp, cor33Exp_apply]

/-- At weight one a displayed component is its variable prime. -/
theorem cor33_component_one_eq_prime (j : Cor33Comp) :
    cor33Component (K := K) 1 1 j = primeOf (cor33ComponentSupport j) := by
  rw [cor33Component]
  exact cor33_purePower_eq_primeOf_of_one_on_support (K := K)
    (fun i hi => cor33_componentExp_one j hi)

/-- Each displayed component support is nonempty. -/
theorem cor33_componentSupport_nonempty (j : Cor33Comp) :
    (cor33ComponentSupport j).Nonempty := by
  cases j <;> simp [cor33ComponentSupport]

/-- The four displayed component supports are pairwise incomparable. -/
theorem cor33_componentSupports_antichain :
    SupportsAntichain cor33ComponentSupport (cor33ComponentExp r s) := by
  intro j k h
  cases j <;> cases k <;> try rfl
  all_goals
    exfalso
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff,
      cor33ComponentSupport] at h

/-- The four irredundance witnesses displayed in Theorem 3.1. -/
noncomputable def cor33IrredWitness (r s : ℕ) : Cor33Comp → Cor33Var →₀ ℕ
  | Cor33Comp.q1 => cor33Exp 0 0 1 1 (s - 1)
  | Cor33Comp.q2 => cor33Exp 0 1 1 0 0
  | Cor33Comp.q3 => cor33Exp 1 0 0 1 0
  | Cor33Comp.q4 => cor33Exp 1 1 0 0 (r - 1)

theorem cor33_irredWitness_mem_component {r s : ℕ} {j k : Cor33Comp} (hkj : k ≠ j) :
    (monomial (cor33IrredWitness r s j) (1 : K) : MvPolynomial Cor33Var K) ∈
      cor33Component r s k := by
  cases j <;> cases k <;> simp at hkj
  all_goals
    apply monomial_mem_purePower.mpr
    simp [cor33ComponentSupport, cor33ComponentExp, cor33IrredWitness, cor33Exp_apply]

theorem cor33_irredWitness_not_mem_component {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (j : Cor33Comp) :
    (monomial (cor33IrredWitness r s j) (1 : K) : MvPolynomial Cor33Var K) ∉
      cor33Component r s j := by
  cases j <;>
    rw [cor33Component, monomial_mem_purePower] <;>
      simp [cor33ComponentSupport, cor33ComponentExp, cor33IrredWitness, cor33Exp_apply] <;>
      omega

/-- The displayed four-component intersection is irredundant. -/
theorem cor33_base_isIrredundant {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    IsIrredundant (K := K) cor33ComponentSupport (cor33ComponentExp r s) := by
  intro j hle
  apply cor33_irredWitness_not_mem_component (K := K) hr hs j
  apply hle
  rw [decompOmit]
  exact Ideal.mem_iInf.mpr (fun k => by
    simpa [cor33Component] using
      (cor33_irredWitness_mem_component (r := r) (s := s) (K := K) k.2))

theorem cor33_base_nsmul_generator_mem {r s : ℕ} {g : Cor33Var →₀ ℕ}
    (hg : g ∈ cor33BaseGens r s) :
    ∀ q : ℕ, q • g ∈ powGens (cor33BaseGens r s : Set (Cor33Var →₀ ℕ)) q := by
  intro q
  induction q with
  | zero => simp [powGens]
  | succ q ih =>
      simp only [powGens, Set.mem_ofPred_eq]
      exact ⟨q • g, ih, g, hg, by simp [succ_nsmul]⟩

theorem cor33_base_monomial_mem_pow_of_capacities {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ∀ (q : ℕ) (e : Cor33Var →₀ ℕ),
      q ≤ e Cor33Var.a + e Cor33Var.b + e Cor33Var.z / s →
      q ≤ e Cor33Var.a + e Cor33Var.d →
      q ≤ e Cor33Var.b + e Cor33Var.c →
      q ≤ e Cor33Var.c + e Cor33Var.d + e Cor33Var.z / r →
      (monomial e (1 : K) : MvPolynomial Cor33Var K) ∈ (cor33BaseIdeal r s) ^ q := by
  intro q
  induction q with
  | zero =>
      intro e
      simp
  | succ n ih =>
      intro e h1 h2 h3 h4
      let gac : Cor33Var →₀ ℕ := cor33Exp 1 0 1 0 0
      let gbd : Cor33Var →₀ ℕ := cor33Exp 0 1 0 1 0
      have hgac : gac ∈ cor33BaseGens r s := by simp [gac, cor33BaseGens]
      have hgbd : gbd ∈ cor33BaseGens r s := by simp [gbd, cor33BaseGens]
      have hgacI : (monomial gac (1 : K) : MvPolynomial Cor33Var K) ∈ cor33BaseIdeal r s := by
        rw [cor33BaseIdeal]
        exact monomial_mem_monomialIdeal.mpr ⟨gac, hgac, le_rfl⟩
      have hgbdI : (monomial gbd (1 : K) : MvPolynomial Cor33Var K) ∈ cor33BaseIdeal r s := by
        rw [cor33BaseIdeal]
        exact monomial_mem_monomialIdeal.mpr ⟨gbd, hgbd, le_rfl⟩
      by_cases hac : 1 ≤ e Cor33Var.a ∧ 1 ≤ e Cor33Var.c
      · let d : Cor33Var →₀ ℕ := e - gac
        have hgle : gac ≤ e := by
          rw [Finsupp.le_def]
          intro x
          cases x <;> simp [gac, cor33Exp_apply, hac.1, hac.2]
        have hadd : gac + d = e := add_tsub_cancel_of_le hgle
        have hd1 : n ≤ d Cor33Var.a + d Cor33Var.b + d Cor33Var.z / s := by
          dsimp [d]
          simp [gac, cor33Exp_apply]
          omega
        have hd2 : n ≤ d Cor33Var.a + d Cor33Var.d := by
          dsimp [d]
          simp [gac, cor33Exp_apply]
          omega
        have hd3 : n ≤ d Cor33Var.b + d Cor33Var.c := by
          dsimp [d]
          simp [gac, cor33Exp_apply]
          omega
        have hd4 : n ≤ d Cor33Var.c + d Cor33Var.d + d Cor33Var.z / r := by
          dsimp [d]
          simp [gac, cor33Exp_apply]
          omega
        have hdmem := ih d hd1 hd2 hd3 hd4
        rw [pow_succ]
        have hmul : (monomial d (1 : K) : MvPolynomial Cor33Var K) *
              monomial gac (1 : K) = monomial e (1 : K) := by
          rw [monomial_mul]
          rw [show d + gac = e by rw [add_comm]; exact hadd]
          simp
        rw [← hmul]
        exact Ideal.mul_mem_mul hdmem hgacI
      · by_cases hbd : 1 ≤ e Cor33Var.b ∧ 1 ≤ e Cor33Var.d
        · let d : Cor33Var →₀ ℕ := e - gbd
          have hgle : gbd ≤ e := by
            rw [Finsupp.le_def]
            intro x
            cases x <;> simp [gbd, cor33Exp_apply, hbd.1, hbd.2]
          have hadd : gbd + d = e := add_tsub_cancel_of_le hgle
          have hd1 : n ≤ d Cor33Var.a + d Cor33Var.b + d Cor33Var.z / s := by
            dsimp [d]
            simp [gbd, cor33Exp_apply]
            omega
          have hd2 : n ≤ d Cor33Var.a + d Cor33Var.d := by
            dsimp [d]
            simp [gbd, cor33Exp_apply]
            omega
          have hd3 : n ≤ d Cor33Var.b + d Cor33Var.c := by
            dsimp [d]
            simp [gbd, cor33Exp_apply]
            omega
          have hd4 : n ≤ d Cor33Var.c + d Cor33Var.d + d Cor33Var.z / r := by
            dsimp [d]
            simp [gbd, cor33Exp_apply]
            omega
          have hdmem := ih d hd1 hd2 hd3 hd4
          rw [pow_succ]
          have hmul : (monomial d (1 : K) : MvPolynomial Cor33Var K) *
                monomial gbd (1 : K) = monomial e (1 : K) := by
            rw [monomial_mul]
            rw [show d + gbd = e by rw [add_comm]; exact hadd]
            simp
          rw [← hmul]
          exact Ideal.mul_mem_mul hdmem hgbdI
        · by_cases ha0 : e Cor33Var.a = 0
          · have hdelta : n + 1 ≤ e Cor33Var.d := by omega
            have hbeta0 : e Cor33Var.b = 0 := by
              by_contra hbne
              have hbpos : 1 ≤ e Cor33Var.b := Nat.one_le_iff_ne_zero.mpr hbne
              exact hbd ⟨hbpos, by omega⟩
            have hgamma : n + 1 ≤ e Cor33Var.c := by omega
            have hfloorS : n + 1 ≤ e Cor33Var.z / s := by omega
            have hzeta : s * (n + 1) ≤ e Cor33Var.z := by
              have := (Nat.le_div_iff_mul_le hs).1 hfloorS
              simpa [Nat.mul_comm] using this
            let gcdz : Cor33Var →₀ ℕ := cor33Exp 0 0 1 1 s
            have hgcdz : gcdz ∈ cor33BaseGens r s := by simp [gcdz, cor33BaseGens]
            have hle : (n + 1) • gcdz ≤ e := by
              rw [Finsupp.le_def]
              intro x
              cases x with
              | a => simp [gcdz, cor33Exp_apply]
              | b => simp [gcdz, cor33Exp_apply]
              | c => simpa [gcdz, cor33Exp_apply] using hgamma
              | d => simpa [gcdz, cor33Exp_apply] using hdelta
              | z => simpa [gcdz, cor33Exp_apply, Nat.mul_comm] using hzeta
            rw [cor33BaseIdeal, monomialIdeal_pow]
            exact monomial_mem_monomialIdeal.mpr
              ⟨(n + 1) • gcdz, cor33_base_nsmul_generator_mem hgcdz (n + 1), hle⟩
          · have hapos : 1 ≤ e Cor33Var.a := Nat.one_le_iff_ne_zero.mpr ha0
            have hgamma0 : e Cor33Var.c = 0 := by
              by_contra hcne
              have hcpos : 1 ≤ e Cor33Var.c := Nat.one_le_iff_ne_zero.mpr hcne
              exact hac ⟨hapos, hcpos⟩
            have hbeta : n + 1 ≤ e Cor33Var.b := by omega
            have hdelta0 : e Cor33Var.d = 0 := by
              by_contra hdne
              have hdpos : 1 ≤ e Cor33Var.d := Nat.one_le_iff_ne_zero.mpr hdne
              exact hbd ⟨by omega, hdpos⟩
            have halpha : n + 1 ≤ e Cor33Var.a := by omega
            have hfloorR : n + 1 ≤ e Cor33Var.z / r := by omega
            have hzeta : r * (n + 1) ≤ e Cor33Var.z := by
              have := (Nat.le_div_iff_mul_le hr).1 hfloorR
              simpa [Nat.mul_comm] using this
            let gabz : Cor33Var →₀ ℕ := cor33Exp 1 1 0 0 r
            have hgabz : gabz ∈ cor33BaseGens r s := by simp [gabz, cor33BaseGens]
            have hle : (n + 1) • gabz ≤ e := by
              rw [Finsupp.le_def]
              intro x
              cases x with
              | a => simpa [gabz, cor33Exp_apply] using halpha
              | b => simpa [gabz, cor33Exp_apply] using hbeta
              | c => simp [gabz, cor33Exp_apply]
              | d => simp [gabz, cor33Exp_apply]
              | z => simpa [gabz, cor33Exp_apply, Nat.mul_comm] using hzeta
            rw [cor33BaseIdeal, monomialIdeal_pow]
            exact monomial_mem_monomialIdeal.mpr
              ⟨(n + 1) • gabz, cor33_base_nsmul_generator_mem hgabz (n + 1), hle⟩

theorem cor33_base_generator_mem_component (r s : ℕ) (j : Cor33Comp)
    {g : Cor33Var →₀ ℕ} (hg : g ∈ cor33BaseGens r s) :
    (monomial g (1 : K) : MvPolynomial Cor33Var K) ∈ cor33Component r s j := by
  cases j <;> simp [cor33BaseGens] at hg <;>
    rcases hg with rfl | rfl | rfl | rfl <;>
      apply monomial_mem_purePower.mpr <;>
        simp [cor33ComponentSupport, cor33ComponentExp, cor33Exp_apply]

theorem cor33_base_componentSimis {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ComponentSimis (cor33BaseIdeal (K := K) r s) (cor33Component (K := K) r s) := by
  intro q _hq
  apply le_antisymm
  · rw [componentSymbolic]
    refine le_iInf (fun j => ?_)
    apply pow_le_pow_left'
    rw [cor33BaseIdeal]
    apply monomialIdeal_le_iff.mpr
    intro e he
    rcases he with ⟨g, hg, hge⟩
    have hgmem := cor33_base_generator_mem_component (K := K) r s j hg
    have hgPure : (monomial g (1 : K) : MvPolynomial Cor33Var K) ∈
        purePower (cor33ComponentSupport j) (cor33ComponentExp r s j) := by
      simpa [cor33Component] using hgmem
    rcases monomial_mem_purePower.mp hgPure with ⟨i, hiA, hgi⟩
    exact ⟨Finsupp.single i (cor33ComponentExp r s j i), ⟨i, hiA, rfl⟩,
      Finsupp.single_le_iff.mpr (le_trans hgi (hge i))⟩
  · intro x hx
    rw [cor33BaseIdeal, monomialIdeal_pow, monomialIdeal,
      MvPolynomial.mem_ideal_span_monomial_image]
    intro e he
    have hmem (j : Cor33Comp) :
        (monomial e (1 : K) : MvPolynomial Cor33Var K) ∈
          (cor33Component (K := K) r s j) ^ q := by
      have hxj : x ∈ (cor33Component (K := K) r s j) ^ q := Ideal.mem_iInf.mp hx j
      exact cor33_monomial_mem_of_mem_purePower_pow hxj he
    have hcap (j : Cor33Comp) :=
      (monomial_mem_purePower_pow (K := K)
        (A := cor33ComponentSupport j) (a := cor33ComponentExp r s j)
        (cor33_componentExp_pos hr hs j) q (e := e)).mp (hmem j)
    have h1 : q ≤ e Cor33Var.a + e Cor33Var.b + e Cor33Var.z / s := by
      simpa [purePowerCapacity, cor33ComponentSupport, cor33ComponentExp, cor33Exp_apply,
        Nat.add_assoc] using hcap Cor33Comp.q1
    have h2 : q ≤ e Cor33Var.a + e Cor33Var.d := by
      simpa [purePowerCapacity, cor33ComponentSupport, cor33ComponentExp, cor33Exp_apply] using
        hcap Cor33Comp.q2
    have h3 : q ≤ e Cor33Var.b + e Cor33Var.c := by
      simpa [purePowerCapacity, cor33ComponentSupport, cor33ComponentExp, cor33Exp_apply] using
        hcap Cor33Comp.q3
    have h4 : q ≤ e Cor33Var.c + e Cor33Var.d + e Cor33Var.z / r := by
      simpa [purePowerCapacity, cor33ComponentSupport, cor33ComponentExp, cor33Exp_apply,
        Nat.add_assoc] using hcap Cor33Comp.q4
    have hbase := cor33_base_monomial_mem_pow_of_capacities (K := K) hr hs q e h1 h2 h3 h4
    have hbaseRep : (monomial e (1 : K) : MvPolynomial Cor33Var K) ∈
        monomialIdeal (powGens (cor33BaseGens r s : Set (Cor33Var →₀ ℕ)) q) := by
      simpa [cor33BaseIdeal, monomialIdeal_pow] using hbase
    exact monomial_mem_monomialIdeal.mp hbaseRep

/-- The four components really intersect in the base ideal. -/
theorem cor33_base_hasComponents {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    HasComponents (cor33BaseIdeal (K := K) r s) cor33ComponentSupport
      (cor33ComponentExp r s) := by
  unfold HasComponents
  have h := cor33_base_componentSimis (K := K) hr hs 1 (by omega)
  simpa [componentSymbolic, cor33Component] using h

/-- The displayed base decomposition is irredundant. -/
theorem cor33_base_irredundantDecomp {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    IsIrredundantDecomp (cor33BaseIdeal (K := K) r s) cor33ComponentSupport
      (cor33ComponentExp r s) :=
  ⟨cor33_base_hasComponents (K := K) hr hs, cor33_base_isIrredundant (K := K) hr hs⟩

/-- Equation (2) for the displayed base decomposition. -/
theorem cor33_base_hasStdSymbolic {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    HasStdSymbolicFormula (cor33BaseIdeal (K := K) r s) (cor33Component (K := K) r s) := by
  intro q hq
  simpa [componentSymbolic, cor33Component] using
    (eq2_standardSymbolic (K := K)
      (cor33_base_irredundantDecomp (K := K) hr hs)
      (cor33_componentSupports_antichain (r := r) (s := s)) q hq)

/-- The base family is Simis for all positive parameters. -/
theorem cor33_base_isSimis {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    IsSimis (cor33BaseIdeal (K := K) r s) :=
  (isSimis_iff_componentSimis_of_stdSymbolic
    (cor33_base_hasStdSymbolic (K := K) hr hs)).2
      (cor33_base_componentSimis (K := K) hr hs)

/-- The squarefree root has the expected irredundant prime decomposition. -/
theorem cor33_radicalIdeal_eq_primeInf :
    cor33RadicalIdeal (K := K) = ⨅ j, primeOf (cor33ComponentSupport j) := by
  have h := cor33_base_componentSimis (K := K) (r := 1) (s := 1)
    (by norm_num) (by norm_num) 1 (by norm_num)
  simpa [cor33RadicalIdeal, componentSymbolic, cor33_component_one_eq_prime (K := K)] using h

/-- The coned component clutter still contains the second displayed triangle. -/
theorem cor33_coneComponentClutter_hasStrongTriangle :
    HasStrongTriangle cor33ConeComponentClutter := by
  change HasStrongTriangle (Set.range (conePureSupport cor33ComponentSupport))
  rw [HasStrongTriangle, HasStrongCycle]
  let v : Fin 3 → Option Cor33Var := ![some Cor33Var.a, some Cor33Var.d, some Cor33Var.z]
  let E : Fin 3 → Finset (Option Cor33Var) :=
    ![{some Cor33Var.a, some Cor33Var.d},
      {some Cor33Var.c, some Cor33Var.d, some Cor33Var.z},
      {some Cor33Var.a, some Cor33Var.b, some Cor33Var.z}]
  refine ⟨by omega, v, ?_, E, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [v] at hij ⊢
  · intro i j hij
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals
      exfalso
      have ha := congrArg (fun F : Finset (Option Cor33Var) => some Cor33Var.a ∈ F) hij
      have hb := congrArg (fun F : Finset (Option Cor33Var) => some Cor33Var.b ∈ F) hij
      have hc := congrArg (fun F : Finset (Option Cor33Var) => some Cor33Var.c ∈ F) hij
      have hd := congrArg (fun F : Finset (Option Cor33Var) => some Cor33Var.d ∈ F) hij
      have hz := congrArg (fun F : Finset (Option Cor33Var) => some Cor33Var.z ∈ F) hij
      simp [E] at ha hb hc hd hz
  · intro i
    fin_cases i
    · exact ⟨some Cor33Comp.q2, by simp [E, conePureSupport, cor33ComponentSupport]⟩
    · exact ⟨some Cor33Comp.q4, by simp [E, conePureSupport, cor33ComponentSupport]⟩
    · exact ⟨some Cor33Comp.q1, by simp [E, conePureSupport, cor33ComponentSupport]⟩
  · have huniv : Finset.univ.image v =
        ({some Cor33Var.a, some Cor33Var.d, some Cor33Var.z} : Finset (Option Cor33Var)) := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨i, _, hi⟩
        fin_cases i
        · have hi' : x = some Cor33Var.a := by simpa [v] using hi.symm
          simp [hi']
        · have hi' : x = some Cor33Var.d := by simpa [v] using hi.symm
          simp [hi']
        · have hi' : x = some Cor33Var.z := by simpa [v] using hi.symm
          simp [hi']
      · intro hx
        have hx' : x = some Cor33Var.a ∨ x = some Cor33Var.d ∨ x = some Cor33Var.z := by
          simpa using hx
        rcases hx' with hxa | hxd | hxz
        · exact Finset.mem_image.mpr ⟨0, by simp, by simp [v, hxa]⟩
        · exact Finset.mem_image.mpr ⟨1, by simp, by simp [v, hxd]⟩
        · exact Finset.mem_image.mpr ⟨2, by simp, by simp [v, hxz]⟩
    intro i
    rw [huniv]
    fin_cases i
    · ext x
      simp [E, v, finSuccMod]
    · ext x
      simp [E, v, finSuccMod]
    · ext x
      simp [E, v, finSuccMod]
      tauto

/-- The coned component clutter is not balanced. -/
theorem cor33_coneComponentClutter_not_isBalanced : ¬ IsBalanced cor33ConeComponentClutter :=
  cor33_hasStrongTriangle_not_isBalanced cor33_coneComponentClutter_hasStrongTriangle

theorem cor33_rename_purePower {A : Finset σ} {a : σ → ℕ} :
    Ideal.map (MvPolynomial.rename (R := K) (Option.some : σ → Option σ))
        (purePower A a : Ideal (MvPolynomial σ K)) =
      purePower (Finset.image some A) (fun x => match x with
        | none => 0
        | some i => a i) := by
  rw [purePower, cor33_rename_monomialIdeal, purePower]
  congr 1
  ext e
  constructor
  · rintro ⟨u, ⟨i, hiA, rfl⟩, rfl⟩
    rw [Finsupp.mapDomain_single]
    exact ⟨some i, by simpa, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hx with ⟨i, hiA, rfl⟩
    exact ⟨Finsupp.single i (a i), ⟨i, hiA, rfl⟩, by rw [Finsupp.mapDomain_single]⟩

/-- Membership in the cone component `(t)`. -/
theorem cor33_monomial_mem_conePurePower_none {ι : Type*}
    {A : ι → Finset σ} {a : ι → σ → ℕ} {e : Option σ →₀ ℕ} :
    (monomial e (1 : K) : MvPolynomial (Option σ) K) ∈
        purePower (conePureSupport A none) (conePureExp a none) ↔ 1 ≤ e none := by
  simpa [conePureSupport, conePureExp] using
    (monomial_mem_purePower (K := K) (A := ({none} : Finset (Option σ)))
      (a := fun _ => 1) (e := e))

/-- Membership in an extended old cone component. -/
theorem cor33_monomial_mem_conePurePower_some {ι : Type*}
    {A : ι → Finset σ} {a : ι → σ → ℕ} {j : ι} {e : Option σ →₀ ℕ} :
    (monomial e (1 : K) : MvPolynomial (Option σ) K) ∈
        purePower (conePureSupport A (some j)) (conePureExp a (some j)) ↔
      (monomial (optionRestrict e) (1 : K) : MvPolynomial σ K) ∈
        purePower (A j) (a j) := by
  rw [conePureSupport, conePureExp, monomial_mem_purePower, monomial_mem_purePower]
  constructor
  · rintro ⟨x, hx, hxe⟩
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact ⟨i, hi, by simpa [optionRestrict_apply] using hxe⟩
  · rintro ⟨i, hi, hie⟩
    refine ⟨some i, by simp [hi], ?_⟩
    simpa [optionRestrict_apply] using hie

theorem monomial_mem_extendIdeal_pow {I : Ideal (MvPolynomial σ K)} (hI : IsMonomialIdeal I)
    (q : ℕ) {e : Option σ →₀ ℕ} :
    (monomial e (1 : K) : MvPolynomial (Option σ) K) ∈
        (Ideal.map (MvPolynomial.rename (R := K) (Option.some : σ → Option σ)) I) ^ q ↔
      (monomial (optionRestrict e) (1 : K) : MvPolynomial σ K) ∈ I ^ q := by
  rcases hI with ⟨S, rfl⟩
  rw [← Ideal.map_pow, monomialIdeal_pow, cor33_rename_monomialIdeal]
  constructor
  · intro he
    rcases monomial_mem_monomialIdeal.mp he with ⟨z, ⟨v, hv, rfl⟩, hz⟩
    exact monomial_mem_monomialIdeal.mpr ⟨v, hv, extendExp_le_iff.mp hz⟩
  · intro he
    rcases monomial_mem_monomialIdeal.mp he with ⟨v, hv, hvle⟩
    exact monomial_mem_monomialIdeal.mpr
      ⟨extendExp v, ⟨v, hv, rfl⟩, extendExp_le_iff.mpr hvle⟩

theorem cone_componentSimis_of_componentSimis {ι : Type*}
    {I : Ideal (MvPolynomial σ K)} (hI : IsMonomialIdeal I)
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hbase : ComponentSimis I (fun j => purePower (A j) (a j) : ι → Ideal (MvPolynomial σ K))) :
    ComponentSimis (coneIdeal I)
      (fun j => purePower (conePureSupport A j) (conePureExp a j) :
        Option ι → Ideal (MvPolynomial (Option σ) K)) := by
  have hdec : HasComponents I A a := by
    unfold HasComponents
    have h := hbase 1 (by omega)
    simpa [componentSymbolic] using h
  intro q hq
  apply le_antisymm
  · rw [componentSymbolic]
    refine le_iInf (fun j => ?_)
    cases j with
    | none =>
        apply pow_le_pow_left'
        change coneIdeal I ≤ primeOf ({none} : Finset (Option σ))
        rw [coneIdeal]
        exact Ideal.mul_le_right
    | some j =>
        apply pow_le_pow_left'
        have hIQ : I ≤ purePower (A j) (a j) := by
          rw [show I = ⨅ k, purePower (A k) (a k) from hdec]
          exact iInf_le _ j
        change coneIdeal I ≤ purePower (Finset.image some (A j))
          (fun x => match x with | none => 0 | some i => a j i)
        rw [← cor33_rename_purePower (K := K) (A := A j) (a := a j)]
        rw [coneIdeal]
        exact le_trans Ideal.mul_le_left (Ideal.map_mono hIQ)
  · intro x hx
    have hx' : x ∈ ⨅ j, (purePower (conePureSupport A j) (conePureExp a j) :
        Ideal (MvPolynomial (Option σ) K)) ^ q := by
      simpa [componentSymbolic] using hx
    rcases hI with ⟨S, hS⟩
    have hKrep : coneIdeal I ^ q = monomialIdeal (powGens (coneExp '' S) q) := by
      rw [hS, cor33_coneIdeal_monomialIdeal, monomialIdeal_pow]
    rw [hKrep, monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image]
    intro e he
    have hxNone := Ideal.mem_iInf.mp hx' none
    have heNone := cor33_monomial_mem_of_mem_purePower_pow hxNone he
    have ht : q ≤ e none := by
      have heNone' : (monomial e (1 : K) : MvPolynomial (Option σ) K) ∈
          (purePower ({none} : Finset (Option σ)) (fun _ => 1)) ^ q := by
        simpa [conePureSupport, conePureExp, primeOf] using heNone
      have hcap := (monomial_mem_purePower_pow (K := K)
        (A := ({none} : Finset (Option σ))) (a := fun _ => 1) (by simp) q (e := e)).mp heNone'
      simpa [purePowerCapacity] using hcap
    have hrestComp : ∀ j : ι, (monomial (optionRestrict e) (1 : K) : MvPolynomial σ K) ∈
        (purePower (A j) (a j)) ^ q := by
      intro j
      have hxj := Ideal.mem_iInf.mp hx' (some j)
      have mej := cor33_monomial_mem_of_mem_purePower_pow hxj he
      have hmap : (monomial e (1 : K) : MvPolynomial (Option σ) K) ∈
          (Ideal.map (MvPolynomial.rename (R := K) (Option.some : σ → Option σ))
            (purePower (A j) (a j))) ^ q := by
        rw [show Ideal.map (MvPolynomial.rename (R := K) (Option.some : σ → Option σ))
              (purePower (A j) (a j)) =
            purePower (conePureSupport A (some j)) (conePureExp a (some j)) from
          cor33_rename_purePower (σ := σ) (K := K) (A := A j) (a := a j)]
        exact mej
      exact (monomial_mem_extendIdeal_pow (K := K)
        (I := purePower (A j) (a j)) ⟨_, rfl⟩ q).mp hmap
    have hrest : (monomial (optionRestrict e) (1 : K) : MvPolynomial σ K) ∈ I ^ q := by
      by_cases hq0 : q = 0
      · subst q
        simp
      · rw [hbase q (Nat.one_le_iff_ne_zero.mpr hq0), componentSymbolic]
        exact Ideal.mem_iInf.mpr hrestComp
    have hk := (monomial_mem_coneIdeal_pow ⟨S, hS⟩ q (e := e)).2 ⟨ht, hrest⟩
    have hkRep : (monomial e (1 : K) : MvPolynomial (Option σ) K) ∈
        monomialIdeal (powGens (coneExp '' S) q) := by
      simpa [hKrep] using hk
    exact monomial_mem_monomialIdeal.mp hkRep

/-- All cone-component exponents are positive on their supports. -/
theorem cor33_cone_componentExp_pos {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ∀ j i, i ∈ conePureSupport cor33ComponentSupport j →
      0 < conePureExp (cor33ComponentExp r s) j i := by
  intro j i hi
  cases j with
  | none =>
      simp [conePureSupport, conePureExp] at hi ⊢
  | some j =>
      cases i with
      | none => simp [conePureSupport] at hi
      | some i =>
          simpa [conePureSupport, conePureExp] using
            cor33_componentExp_pos hr hs j i (by simpa [conePureSupport] using hi)

/-- Each pure-power component after coning has height its support cardinality. -/
theorem cor33_cone_component_height {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (j : Option Cor33Comp) :
    (purePower (conePureSupport cor33ComponentSupport j)
      (conePureExp (cor33ComponentExp r s) j) :
        Ideal (MvPolynomial (Option Cor33Var) K)).height =
      ((conePureSupport cor33ComponentSupport j).card : ℕ∞) := by
  exact cor33_height_purePower_eq_card (K := K)
    (A := conePureSupport cor33ComponentSupport j)
    (a := conePureExp (cor33ComponentExp r s) j)
    (cor33_cone_componentExp_pos hr hs j)

/-- The five heights of the coned pure-power components in Corollary 3.3. -/
theorem cor33_cone_componentHeight_values {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    (purePower (conePureSupport cor33ComponentSupport none)
      (conePureExp (cor33ComponentExp r s) none) :
        Ideal (MvPolynomial (Option Cor33Var) K)).height = (1 : ℕ∞) ∧
    (purePower (conePureSupport cor33ComponentSupport (some Cor33Comp.q1))
      (conePureExp (cor33ComponentExp r s) (some Cor33Comp.q1)) :
        Ideal (MvPolynomial (Option Cor33Var) K)).height = (3 : ℕ∞) ∧
    (purePower (conePureSupport cor33ComponentSupport (some Cor33Comp.q2))
      (conePureExp (cor33ComponentExp r s) (some Cor33Comp.q2)) :
        Ideal (MvPolynomial (Option Cor33Var) K)).height = (2 : ℕ∞) ∧
    (purePower (conePureSupport cor33ComponentSupport (some Cor33Comp.q3))
      (conePureExp (cor33ComponentExp r s) (some Cor33Comp.q3)) :
        Ideal (MvPolynomial (Option Cor33Var) K)).height = (2 : ℕ∞) ∧
    (purePower (conePureSupport cor33ComponentSupport (some Cor33Comp.q4))
      (conePureExp (cor33ComponentExp r s) (some Cor33Comp.q4)) :
        Ideal (MvPolynomial (Option Cor33Var) K)).height = (3 : ℕ∞) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [conePureSupport] using
      (cor33_cone_component_height (K := K) hr hs none)
  · simpa [conePureSupport, cor33ComponentSupport] using
      (cor33_cone_component_height (K := K) hr hs (some Cor33Comp.q1))
  · simpa [conePureSupport, cor33ComponentSupport] using
      (cor33_cone_component_height (K := K) hr hs (some Cor33Comp.q2))
  · simpa [conePureSupport, cor33ComponentSupport] using
      (cor33_cone_component_height (K := K) hr hs (some Cor33Comp.q3))
  · simpa [conePureSupport, cor33ComponentSupport] using
      (cor33_cone_component_height (K := K) hr hs (some Cor33Comp.q4))

/-- The five component supports are pairwise incomparable. -/
theorem cor33_cone_componentSupports_antichain {r s : ℕ} :
    SupportsAntichain (conePureSupport cor33ComponentSupport)
      (conePureExp (cor33ComponentExp r s)) := by
  intro j k h
  cases j with
  | none =>
      cases k with
      | none => rfl
      | some k =>
          exfalso
          have hmem := h (show none ∈ conePureSupport cor33ComponentSupport none by
            simp [conePureSupport])
          simp [conePureSupport] at hmem
  | some j =>
      cases k with
      | none =>
          exfalso
          rcases cor33_componentSupport_nonempty j with ⟨i, hi⟩
          have hmem := h (show some i ∈ conePureSupport cor33ComponentSupport (some j) by
            simp [conePureSupport, hi])
          simp [conePureSupport] at hmem
      | some k =>
          have hbase : cor33ComponentSupport j ⊆ cor33ComponentSupport k := by
            intro i hi
            have hmem := h (show some i ∈ conePureSupport cor33ComponentSupport (some j) by
              exact Finset.mem_image.mpr ⟨i, hi, rfl⟩)
            rw [conePureSupport] at hmem
            rcases Finset.mem_image.mp hmem with ⟨i', hi', heq⟩
            simpa [Option.some.inj heq] using hi'
          exact congrArg some
            (cor33_componentSupports_antichain (r := r) (s := s) j k hbase)

/-- Each cone component has the expected radical. -/
theorem cor33_cone_component_radical {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (j : Option Cor33Comp) :
    (purePower (conePureSupport cor33ComponentSupport j)
      (conePureExp (cor33ComponentExp r s) j) :
      Ideal (MvPolynomial (Option Cor33Var) K)).radical =
      purePower (conePureSupport cor33ComponentSupport j) (fun _ => 1) := by
  simpa [primeOf] using
    (purePower_radical_eq_primeOf (K := K)
      (A := conePureSupport cor33ComponentSupport j)
      (a := conePureExp (cor33ComponentExp r s) j)
      (cor33_cone_componentExp_pos hr hs j))

/-- The coned irredundance witnesses: `ac` for `(t)` and `t` times the old witnesses. -/
noncomputable def cor33ConeIrredWitness (r s : ℕ) :
    Option Cor33Comp → Option Cor33Var →₀ ℕ
  | none => extendExp (cor33Exp 1 0 1 0 0)
  | some j => coneExp (cor33IrredWitness r s j)

theorem cor33_cone_irredWitness_mem_component {r s : ℕ} {j k : Option Cor33Comp}
    (hkj : k ≠ j) :
    (monomial (cor33ConeIrredWitness r s j) (1 : K) :
      MvPolynomial (Option Cor33Var) K) ∈
        purePower (conePureSupport cor33ComponentSupport k)
          (conePureExp (cor33ComponentExp r s) k) := by
  cases j with
  | none =>
      cases k with
      | none => exact (hkj rfl).elim
      | some k =>
          rw [cor33_monomial_mem_conePurePower_some]
          have hg : cor33Exp 1 0 1 0 0 ∈ cor33BaseGens r s := by
            simp [cor33BaseGens]
          simpa [cor33ConeIrredWitness, cor33Component] using
            (cor33_base_generator_mem_component (K := K) r s k hg)
  | some j =>
      cases k with
      | none =>
          rw [cor33_monomial_mem_conePurePower_none]
          simp [cor33ConeIrredWitness]
      | some k =>
          have hk : k ≠ j := by
            intro heq
            exact hkj (congrArg some heq)
          rw [cor33_monomial_mem_conePurePower_some]
          simpa [cor33ConeIrredWitness, cor33Component] using
            (cor33_irredWitness_mem_component (K := K) (r := r) (s := s) hk)

theorem cor33_cone_irredWitness_not_mem_component {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (j : Option Cor33Comp) :
    (monomial (cor33ConeIrredWitness r s j) (1 : K) :
      MvPolynomial (Option Cor33Var) K) ∉
        purePower (conePureSupport cor33ComponentSupport j)
          (conePureExp (cor33ComponentExp r s) j) := by
  cases j with
  | none =>
      rw [cor33_monomial_mem_conePurePower_none]
      simp [cor33ConeIrredWitness]
  | some j =>
      rw [cor33_monomial_mem_conePurePower_some]
      simpa [cor33ConeIrredWitness, cor33Component] using
        (cor33_irredWitness_not_mem_component (K := K) hr hs j)

/-- The five-component cone decomposition is irredundant. -/
theorem cor33_cone_isIrredundant {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    IsIrredundant (K := K) (conePureSupport cor33ComponentSupport)
      (conePureExp (cor33ComponentExp r s)) := by
  intro j hle
  apply cor33_cone_irredWitness_not_mem_component (K := K) hr hs j
  apply hle
  rw [decompOmit]
  exact Ideal.mem_iInf.mpr (fun k =>
    cor33_cone_irredWitness_mem_component (K := K) (r := r) (s := s) k.2)

/-- The coned generators form a divisibility antichain. -/
theorem cor33_coneGens_antichain {r s : ℕ} :
    ∀ e ∈ coneExp '' (cor33BaseGens r s : Set (Cor33Var →₀ ℕ)),
      ∀ u ∈ coneExp '' (cor33BaseGens r s : Set (Cor33Var →₀ ℕ)), u ≤ e → u = e := by
  rintro e ⟨e₀, he₀, rfl⟩ u ⟨u₀, hu₀, rfl⟩ hle
  have hle₀ : u₀ ≤ e₀ := by simpa using (coneExp_le_iff.mp hle).2
  have heq : u₀ = e₀ := cor33_baseGens_antichain e₀ he₀ u₀ hu₀ hle₀
  exact congrArg coneExp heq

/-- The coned generator supports form an antichain. -/
theorem cor33_coneGens_support_antichain {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ∀ e ∈ coneExp '' (cor33BaseGens r s : Set (Cor33Var →₀ ℕ)),
      ∀ u ∈ coneExp '' (cor33BaseGens r s : Set (Cor33Var →₀ ℕ)),
        u.support ⊆ e.support → u = e := by
  rintro e ⟨e₀, he₀, rfl⟩ u ⟨u₀, hu₀, rfl⟩ hsub
  have hbase : u₀.support ⊆ e₀.support := by
    intro i hi
    have hsome : some i ∈ (coneExp u₀).support := by
      rw [cor33_coneExp_support]
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    have hsome' := hsub hsome
    rw [cor33_coneExp_support] at hsome'
    rcases Finset.mem_insert.mp hsome' with hnone | himage
    · cases hnone
    · rcases Finset.mem_image.mp himage with ⟨j, hj, hji⟩
      have hji' : j = i := Option.some.inj hji
      simpa [hji'] using hj
  have heq : u₀ = e₀ :=
    cor33_baseGens_support_antichain hr hs e₀ he₀ u₀ hu₀ hbase
  exact congrArg coneExp heq

/-- The coned support complex is literally the cone on the base clutter. -/
theorem cor33_cone_supportComplex {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    supportComplex (cor33ConeIdeal (K := K) r s) = coneClutter cor33BaseClutter := by
  rw [cor33ConeIdeal,
    cor33_supportComplex_coneIdeal (I := cor33BaseIdeal (K := K) r s)
      ⟨cor33BaseGens r s, rfl⟩, cor33_base_supportComplex hr hs]

/-- The coned support complex contains a strong triangle. -/
theorem cor33_cone_supportComplex_hasStrongTriangle {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    HasStrongTriangle (supportComplex (cor33ConeIdeal (K := K) r s)) := by
  rw [cor33_cone_supportComplex (K := K) hr hs]
  exact cor33_coneBaseClutter_hasStrongTriangle

/-- The coned support complex is not balanced. -/
theorem cor33_cone_supportComplex_not_isBalanced {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ¬ IsBalanced (supportComplex (cor33ConeIdeal (K := K) r s)) :=
  cor33_hasStrongTriangle_not_isBalanced
    (cor33_cone_supportComplex_hasStrongTriangle (K := K) hr hs)

/-- Coning the base example preserves supports. -/
theorem cor33_cone_supportPreserving {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    SupportPreserving (cor33ConeIdeal (K := K) r s) := by
  rw [cor33ConeIdeal, cor33BaseIdeal, cor33_coneIdeal_monomialIdeal]
  exact cor33_supportPreserving_monomialIdeal_of_antichain
    cor33_coneGens_antichain (cor33_coneGens_support_antichain hr hs)

theorem cor33_cone_componentSimis {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ComponentSimis (cor33ConeIdeal (K := K) r s)
      (fun j => purePower (conePureSupport cor33ComponentSupport j)
        (conePureExp (cor33ComponentExp r s) j) :
        Option Cor33Comp → Ideal (MvPolynomial (Option Cor33Var) K)) := by
  apply cone_componentSimis_of_componentSimis
  · exact ⟨cor33BaseGens r s, rfl⟩
  · exact cor33_base_componentSimis (K := K) hr hs

theorem cor33_cone_hasComponents {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    HasComponents (cor33ConeIdeal (K := K) r s)
      (conePureSupport cor33ComponentSupport) (conePureExp (cor33ComponentExp r s)) := by
  unfold HasComponents
  have h := cor33_cone_componentSimis (K := K) hr hs 1 (by omega)
  simpa [componentSymbolic] using h

/-- The displayed cone decomposition is irredundant. -/
theorem cor33_cone_irredundantDecomp {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    IsIrredundantDecomp (cor33ConeIdeal (K := K) r s)
      (conePureSupport cor33ComponentSupport)
      (conePureExp (cor33ComponentExp r s)) :=
  ⟨cor33_cone_hasComponents (K := K) hr hs, cor33_cone_isIrredundant (K := K) hr hs⟩

/-- Equation (2) for the displayed cone decomposition. -/
theorem cor33_cone_hasStdSymbolic {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    HasStdSymbolicFormula (cor33ConeIdeal (K := K) r s)
      (fun j => purePower (conePureSupport cor33ComponentSupport j)
        (conePureExp (cor33ComponentExp r s) j) :
        Option Cor33Comp → Ideal (MvPolynomial (Option Cor33Var) K)) := by
  exact eq2_standardSymbolic (K := K)
    (cor33_cone_irredundantDecomp (K := K) hr hs)
    (cor33_cone_componentSupports_antichain (r := r) (s := s))

/-- The coned family is Simis for all positive parameters. -/
theorem cor33_cone_isSimis {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    IsSimis (cor33ConeIdeal (K := K) r s) :=
  (isSimis_iff_componentSimis_of_stdSymbolic
    (cor33_cone_hasStdSymbolic (K := K) hr hs)).2
      (cor33_cone_componentSimis (K := K) hr hs)

/-- The minimal primes of the cone are exactly its five displayed variable primes. -/
theorem cor33_cone_minimalPrime_iff {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {P : Ideal (MvPolynomial (Option Cor33Var) K)} :
    (cor33ConeIdeal (K := K) r s).IsMinimalPrime P ↔
      ∃ j : Option Cor33Comp,
        P = (purePower (conePureSupport cor33ComponentSupport j) (fun _ => 1) :
          Ideal (MvPolynomial (Option Cor33Var) K)) := by
  have hcomp := cor33_cone_hasComponents (K := K) hr hs
  have hpos := cor33_cone_componentExp_pos hr hs
  have hanti := cor33_cone_componentSupports_antichain (r := r) (s := s)
  constructor
  · intro hP
    rcases minimalPrime_eq_primeOf_of_antichain (K := K) hcomp hpos hP with ⟨j, hj⟩
    exact ⟨j, by simpa [primeOf] using hj⟩
  · rintro ⟨j, rfl⟩
    simpa [primeOf] using
      primeOf_mem_minimalPrimes_of_antichain (K := K) hcomp hpos hanti j

/-- The five displayed coned primes are pairwise distinct. -/
theorem cor33_conePrime_injective :
    Function.Injective (fun j : Option Cor33Comp =>
      (primeOf (conePureSupport cor33ComponentSupport j) :
        Ideal (MvPolynomial (Option Cor33Var) K))) := by
  intro j k hjk
  apply cor33_cone_componentSupports_antichain (r := 1) (s := 1) j k
  exact (primeOf_le_iff_subset (K := K)).mp (le_of_eq hjk)

/-- The five displayed coned primes have a five-element range. -/
theorem cor33_conePrime_range_ncard :
    (Set.range (fun j : Option Cor33Comp =>
      (primeOf (conePureSupport cor33ComponentSupport j) :
        Ideal (MvPolynomial (Option Cor33Var) K)))).ncard = 5 := by
  rw [Set.ncard_range_of_injective (cor33_conePrime_injective (K := K))]
  rw [Nat.card_eq_fintype_card]
  have hcomp : Fintype.card Cor33Comp = 4 := by
    change (Finset.univ : Finset Cor33Comp).card = 4
    rw [show (Finset.univ : Finset Cor33Comp) =
        {Cor33Comp.q1, Cor33Comp.q2, Cor33Comp.q3, Cor33Comp.q4} from rfl]
    simp [Finset.card_insert_of_notMem]
  rw [Fintype.card_option, hcomp]

/-- The associated primes of the coned ideal equal its minimal primes. -/
theorem cor33_cone_associatedPrimes_eq_minimalPrimes {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) :
    associatedPrimes (MvPolynomial (Option Cor33Var) K)
        (MvPolynomial (Option Cor33Var) K ⧸ cor33ConeIdeal (K := K) r s) =
      (cor33ConeIdeal (K := K) r s).minimalPrimes := by
  have hdec := cor33_cone_irredundantDecomp (K := K) hr hs
  have hanti := cor33_cone_componentSupports_antichain (r := r) (s := s)
  exact prop21_associatedPrimes_eq_minimalPrimes_of_supportsAntichain
    hdec.1 hdec.2 hanti

/-- The minimal primes of the coned ideal are the five displayed primes. -/
theorem cor33_cone_minimalPrimes_eq_range {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) :
    (cor33ConeIdeal (K := K) r s).minimalPrimes =
      Set.range (fun j : Option Cor33Comp =>
        (primeOf (conePureSupport cor33ComponentSupport j) :
          Ideal (MvPolynomial (Option Cor33Var) K))) := by
  have hdec := cor33_cone_irredundantDecomp (K := K) hr hs
  have hanti := cor33_cone_componentSupports_antichain (r := r) (s := s)
  exact prop21_minimalPrimes_eq_range_of_supportsAntichain hdec.1 hdec.2 hanti

/-- The associated primes of the coned ideal are the five displayed primes. -/
theorem cor33_cone_associatedPrimes_eq_range {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) :
    associatedPrimes (MvPolynomial (Option Cor33Var) K)
        (MvPolynomial (Option Cor33Var) K ⧸ cor33ConeIdeal (K := K) r s) =
      Set.range (fun j : Option Cor33Comp =>
        (primeOf (conePureSupport cor33ComponentSupport j) :
          Ideal (MvPolynomial (Option Cor33Var) K))) := by
  have hdec := cor33_cone_irredundantDecomp (K := K) hr hs
  have hanti := cor33_cone_componentSupports_antichain (r := r) (s := s)
  exact prop21_associatedPrimes_eq_range_of_supportsAntichain hdec.1 hdec.2 hanti

/-- Every positive ordinary power has the same five associated primes. -/
theorem cor33_cone_associatedPrimes_pow_eq_range {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) {q : ℕ} (hq : 0 < q) :
    associatedPrimes (MvPolynomial (Option Cor33Var) K)
        (MvPolynomial (Option Cor33Var) K ⧸
          (cor33ConeIdeal (K := K) r s) ^ q) =
      Set.range (fun j : Option Cor33Comp =>
        (primeOf (conePureSupport cor33ComponentSupport j) :
          Ideal (MvPolynomial (Option Cor33Var) K))) := by
  have hdec := cor33_cone_irredundantDecomp (K := K) hr hs
  have hanti := cor33_cone_componentSupports_antichain (r := r) (s := s)
  exact associatedPrimes_pow_eq_range_of_componentSimis_antichain
    hdec.1 hdec.2 hanti (cor33_cone_componentSimis (K := K) hr hs) hq

/-- The coned ideal is normally torsion free in the paper's sense. -/
theorem cor33_cone_prop21NormallyTorsionFree {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) :
    prop21NormallyTorsionFree (cor33ConeIdeal (K := K) r s) := by
  let P : Option Cor33Comp → Ideal (MvPolynomial (Option Cor33Var) K) := fun j =>
    primeOf (conePureSupport cor33ComponentSupport j)
  exact normallyTorsionFree_of_powerAssociatedPrimes_eq_range
    (I := cor33ConeIdeal (K := K) r s) (P := P)
    (by simpa [P] using (cor33_cone_associatedPrimes_eq_range (K := K) hr hs))
    (fun {q} hq => by
      simpa [P] using
        (cor33_cone_associatedPrimes_pow_eq_range (K := K) hr hs hq))

/-- The radical of the cone is the cone of the squarefree root. -/
theorem cor33_cone_radical {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    (cor33ConeIdeal (K := K) r s).radical = coneIdeal (cor33RadicalIdeal (K := K)) := by
  have hdec := cor33_cone_hasComponents (K := K) hr hs
  unfold HasComponents at hdec
  have hMmon : IsMonomialIdeal (cor33RadicalIdeal (K := K)) := by
    refine ⟨(cor33BaseGens 1 1 : Set (Cor33Var →₀ ℕ)), ?_⟩
    rw [cor33RadicalIdeal, cor33BaseIdeal]
  calc
    (cor33ConeIdeal (K := K) r s).radical =
        (⨅ j, (purePower (conePureSupport cor33ComponentSupport j)
          (conePureExp (cor33ComponentExp r s) j) :
          Ideal (MvPolynomial (Option Cor33Var) K))).radical := by rw [hdec]
    _ = ⨅ j, (purePower (conePureSupport cor33ComponentSupport j)
          (conePureExp (cor33ComponentExp r s) j) :
          Ideal (MvPolynomial (Option Cor33Var) K)).radical :=
      radical_iInf_fintype _
    _ = ⨅ j, (purePower (conePureSupport cor33ComponentSupport j) (fun _ => 1) :
          Ideal (MvPolynomial (Option Cor33Var) K)) := by
      apply iInf_congr
      intro j
      exact cor33_cone_component_radical (K := K) hr hs j
    _ = coneIdeal (cor33RadicalIdeal (K := K)) := by
      apply le_antisymm
      · intro x hx
        apply (cor33_mem_coneIdeal_iff_support hMmon).2
        intro e he
        have hxNone := Ideal.mem_iInf.mp hx none
        change x ∈ primeOf ({none} : Finset (Option Cor33Var)) at hxNone
        rcases (mem_primeOf.mp hxNone) e he with ⟨t, ht, hte⟩
        have ht' : t = none := by simpa using ht
        subst t
        have hnone : 1 ≤ e none := by simpa using hte
        have hrest : (monomial (optionRestrict e) (1 : K) : MvPolynomial Cor33Var K) ∈
            cor33RadicalIdeal (K := K) := by
          rw [cor33_radicalIdeal_eq_primeInf]
          apply Ideal.mem_iInf.mpr
          intro j
          have hxj := Ideal.mem_iInf.mp hx (some j)
          change x ∈ primeOf (Finset.image some (cor33ComponentSupport j)) at hxj
          rcases (mem_primeOf.mp hxj) e he with ⟨t, htSupp, htLe⟩
          rcases Finset.mem_image.mp htSupp with ⟨i, hi, rfl⟩
          rw [monomial_mem_primeOf]
          exact ⟨i, hi, by simpa [optionRestrict_apply] using htLe⟩
        exact ⟨hnone, hrest⟩
      · intro x hx
        have hxSupp := (cor33_mem_coneIdeal_iff_support hMmon).1 hx
        apply Ideal.mem_iInf.mpr
        intro j
        cases j with
        | none =>
            change x ∈ primeOf ({none} : Finset (Option Cor33Var))
            rw [mem_primeOf]
            intro e he
            exact ⟨none, by simp, (hxSupp e he).1⟩
        | some j =>
            change x ∈ primeOf (Finset.image some (cor33ComponentSupport j))
            rw [mem_primeOf]
            intro e he
            have hrest := (hxSupp e he).2
            rw [cor33_radicalIdeal_eq_primeInf] at hrest
            have hrestj := Ideal.mem_iInf.mp hrest j
            rw [monomial_mem_primeOf] at hrestj
            rcases hrestj with ⟨i, hi, hle⟩
            exact ⟨some i, by simpa using hi, by simpa [optionRestrict_apply] using hle⟩

theorem cor33_cone_isSimis_ofStdSymbolic {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hsym : HasStdSymbolicFormula (cor33ConeIdeal (K := K) r s)
      (fun j => purePower (conePureSupport cor33ComponentSupport j)
        (conePureExp (cor33ComponentExp r s) j) :
        Option Cor33Comp → Ideal (MvPolynomial (Option Cor33Var) K))) :
    IsSimis (cor33ConeIdeal (K := K) r s) := by
  exact (isSimis_iff_componentSimis_of_stdSymbolic hsym).2 (cor33_cone_componentSimis hr hs)

/-- The cone of the squarefree root is squarefree. -/
theorem cor33ConeRadicalIdeal_isSquarefree :
    IsSquarefreeMonomialIdeal (cor33ConeRadicalIdeal (K := K)) := by
  rw [cor33ConeRadicalIdeal]
  exact cor33_coneIdeal_isSquarefree (cor33_radicalIdeal_isSquarefree (K := K))

/-- The explicit diagonal representation when the two parameters agree. -/
theorem cor33_diagonal_coneRadicalIdeal (rho : ℕ) :
    diagonal (cor33ConeWeight rho) (cor33ConeRadicalIdeal (K := K)) =
      cor33ConeIdeal (K := K) rho rho := by
  have hMmon : IsMonomialIdeal (cor33RadicalIdeal (K := K)) := by
    refine ⟨(cor33BaseGens 1 1 : Set (Cor33Var →₀ ℕ)), ?_⟩
    rw [cor33RadicalIdeal, cor33BaseIdeal]
  calc
    diagonal (cor33ConeWeight rho) (cor33ConeRadicalIdeal (K := K)) =
        coneIdeal (diagonal (fun i => cor33ConeWeight rho (some i))
          (cor33RadicalIdeal (K := K))) := by
      rw [cor33ConeRadicalIdeal]
      exact cor33_diagonal_coneIdeal hMmon (by rfl)
    _ = coneIdeal (diagonal (cor33BaseWeight rho) (cor33RadicalIdeal (K := K))) := by
      rfl
    _ = coneIdeal (cor33BaseIdeal (K := K) rho rho) := by
      rw [cor33_diagonal_radicalIdeal_base]
    _ = cor33ConeIdeal (K := K) rho rho := by
      rfl

/-- Minimal generators of the coned ideal are exactly the coned displayed generators. -/
theorem cor33_cone_minGens {r s : ℕ} :
    minGens (cor33ConeIdeal (K := K) r s) =
      coneExp '' (cor33BaseGens r s : Set (Cor33Var →₀ ℕ)) := by
  have hI : IsMonomialIdeal (cor33BaseIdeal (K := K) r s) := by
    refine ⟨(cor33BaseGens r s : Set (Cor33Var →₀ ℕ)), ?_⟩
    rw [cor33BaseIdeal]
  have hbase : minGens (cor33BaseIdeal (K := K) r s) =
      (cor33BaseGens r s : Set (Cor33Var →₀ ℕ)) := by
    rw [cor33BaseIdeal]
    exact cor33_minGens_monomialIdeal_eq cor33_baseGens_antichain
  rw [cor33ConeIdeal, cor33_minGens_coneIdeal hI, hbase]

theorem cor33_cone_generator_mem_minGens {r s : ℕ} {g : Cor33Var →₀ ℕ}
    (hg : g ∈ cor33BaseGens r s) :
    coneExp g ∈ minGens (cor33ConeIdeal (K := K) r s) := by
  rw [cor33_cone_minGens]
  exact ⟨g, hg, rfl⟩

/-- A squarefree diagonal root exists exactly when the two parameters agree. -/
theorem cor33_cone_hasSqRoot_iff {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    HasSqRoot (cor33ConeIdeal (K := K) r s) ↔ r = s := by
  constructor
  · rintro ⟨J, d, hJ, hd, hdiag⟩
    have habz : coneExp (cor33Exp 1 1 0 0 r) ∈
        minGens (cor33ConeIdeal (K := K) r s) :=
      cor33_cone_generator_mem_minGens (r := r) (s := s)
        (by simp [cor33BaseGens])
    have hcdz : coneExp (cor33Exp 0 0 1 1 s) ∈
        minGens (cor33ConeIdeal (K := K) r s) :=
      cor33_cone_generator_mem_minGens (r := r) (s := s)
        (by simp [cor33BaseGens])
    have hrz := cor33_sqRoot_minGen_coordinate (K := K)
      (I := cor33ConeIdeal (K := K) r s) (J := J) (d := d) hJ hd hdiag
      (e := coneExp (cor33Exp 1 1 0 0 r)) habz (some Cor33Var.z)
    have hsz := cor33_sqRoot_minGen_coordinate (K := K)
      (I := cor33ConeIdeal (K := K) r s) (J := J) (d := d) hJ hd hdiag
      (e := coneExp (cor33Exp 0 0 1 1 s)) hcdz (some Cor33Var.z)
    have hrEq : r = d (some Cor33Var.z) := by
      rcases hrz with hzero | hweight
      · have hz : r = 0 := by
          simpa [coneExp_apply_some, cor33Exp_apply] using hzero
        omega
      · simpa [coneExp_apply_some, cor33Exp_apply] using hweight
    have hsEq : s = d (some Cor33Var.z) := by
      rcases hsz with hzero | hweight
      · have hz : s = 0 := by
          simpa [coneExp_apply_some, cor33Exp_apply] using hzero
        omega
      · simpa [coneExp_apply_some, cor33Exp_apply] using hweight
    exact hrEq.trans hsEq.symm
  · intro hrs
    subst s
    refine ⟨cor33ConeRadicalIdeal (K := K), cor33ConeWeight r, ?_, ?_, ?_⟩
    · exact cor33ConeRadicalIdeal_isSquarefree (K := K)
    · exact cor33ConeWeight_pos hr
    · exact cor33_diagonal_coneRadicalIdeal (K := K) r

/-- The squarefree cone is itself Simis. -/
theorem cor33ConeRadicalIdeal_isSimis : IsSimis (cor33ConeRadicalIdeal (K := K)) := by
  simpa [cor33ConeRadicalIdeal, cor33RadicalIdeal, cor33ConeIdeal] using
    (cor33_cone_isSimis (K := K) (r := 1) (s := 1) (by omega) (by omega))

/-- When \(r=s\), the displayed squarefree cone realizes the MPV conclusion. -/
theorem cor33_cone_MPVConc_of_eq {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hrs : r = s) :
    MPVConc (cor33ConeIdeal (K := K) r s) := by
  subst s
  have hdecomp : IsIrredundantDecomp (cor33ConeRadicalIdeal (K := K))
      (conePureSupport cor33ComponentSupport) (conePureExp (cor33ComponentExp 1 1)) := by
    simpa [cor33ConeRadicalIdeal, cor33RadicalIdeal, cor33ConeIdeal] using
      (cor33_cone_irredundantDecomp (K := K) (r := 1) (s := 1) (by omega) (by omega))
  have hanti : SupportsAntichain (conePureSupport cor33ComponentSupport)
      (conePureExp (cor33ComponentExp 1 1)) :=
    cor33_cone_componentSupports_antichain (r := 1) (s := 1)
  have hd : ∀ i, 0 < cor33ConeWeight r i := cor33ConeWeight_pos hr
  have hiff := eq4_isSimis_diagonal_iff_of_irredundantDecomp
      (σ := Option Cor33Var) (K := K) (ι := Option Cor33Comp)
      (J := cor33ConeRadicalIdeal (K := K))
      (A := conePureSupport cor33ComponentSupport)
      (a := conePureExp (cor33ComponentExp 1 1))
      (d := cor33ConeWeight r) hd hdecomp hanti
  have hdiagSim : IsSimis (diagonal (cor33ConeWeight r) (cor33ConeRadicalIdeal (K := K))) := by
    rw [cor33_diagonal_coneRadicalIdeal (K := K) r]
    exact cor33_cone_isSimis (K := K) (r := r) (s := r) hr hr
  have hrootSim : IsSimis (cor33ConeRadicalIdeal (K := K)) := hiff.mpr hdiagSim
  refine ⟨cor33ConeRadicalIdeal (K := K), cor33ConeWeight r, ?_, hrootSim, hd, ?_⟩
  · exact cor33ConeRadicalIdeal_isSquarefree (K := K)
  · exact cor33_diagonal_coneRadicalIdeal (K := K) r

/-- `MPVConc` always supplies a squarefree diagonal root. -/
theorem cor33_MPVConc_hasSqRoot {I : Ideal (MvPolynomial σ K)} (h : MPVConc I) : HasSqRoot I := by
  rcases h with ⟨J, d, hJ, _hSimis, hd, hdiag⟩
  exact ⟨J, d, hJ, hd, hdiag⟩

/-- The displayed cone satisfies the MPV hypotheses. -/
theorem cor33_cone_MPVHypotheses {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    MPVHypotheses (cor33ConeIdeal (K := K) r s)
      (conePureSupport cor33ComponentSupport)
      (conePureExp (cor33ComponentExp r s)) :=
  ⟨cor33_cone_irredundantDecomp (K := K) hr hs,
    cor33_cone_componentSupports_antichain (r := r) (s := s),
    cor33_cone_isSimis (K := K) hr hs⟩

/-- For unequal positive parameters the cone supplies the promised counterexample. -/
theorem cor33_contractibleCounterexample {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) :
    MPVHypotheses (cor33ConeIdeal (K := K) r s)
      (conePureSupport cor33ComponentSupport)
      (conePureExp (cor33ComponentExp r s)) ∧
    SupportPreserving (cor33ConeIdeal (K := K) r s) ∧
    supportComplex (cor33ConeIdeal (K := K) r s) = coneClutter cor33BaseClutter ∧
    ¬ MPVConc (cor33ConeIdeal (K := K) r s) := by
  refine ⟨cor33_cone_MPVHypotheses (K := K) hr hs,
    cor33_cone_supportPreserving (K := K) hr hs,
    cor33_cone_supportComplex (K := K) hr hs, ?_⟩
  intro h
  exact hrs ((cor33_cone_hasSqRoot_iff (K := K) hr hs).1
    (cor33_MPVConc_hasSqRoot h))

omit K [Field K] [DecidableEq σ] in
/-- The apex of a cone over a support-clutter. -/
def cor33ConeApex : Option σ → ℝ
  | none => 1
  | some _ => 0

omit K [Field K] in
/-- The cone apex belongs to every nonempty coned geometric realization. -/
theorem cor33ConeApex_mem [Fintype σ] (H : Set (Finset σ)) (hH : H.Nonempty) :
    cor33ConeApex ∈ cor33GeomRealization (coneClutter H) := by
  rcases hH with ⟨E, hE⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    cases i <;> simp [cor33ConeApex]
  · simp [cor33ConeApex]
  · refine ⟨insert none (E.image some), ⟨E, hE, rfl⟩, ?_⟩
    intro i hi
    cases i with
    | none => simp
    | some i => simp [cor33ConeApex] at hi

omit K [Field K] in
/-- The geometric realization of a nonempty cone is contractible by straight-line homotopy
to the apex. -/
theorem cor33GeomRealization_contractible_cone [Fintype σ] (H : Set (Finset σ))
    (hH : H.Nonempty) :
    ContractibleSpace ↥(cor33GeomRealization (coneClutter H)) := by
  let X : Type _ := ↥(cor33GeomRealization (coneClutter H))
  let a : X := ⟨cor33ConeApex, cor33ConeApex_mem H hH⟩
  let Fhom : unitInterval × X → X := fun p =>
    ⟨fun i => (1 - (p.1 : ℝ)) * (p.2.1 i) + (p.1 : ℝ) * cor33ConeApex i, by
      rcases p.2.2 with ⟨hnonneg, hsum, Fc, hFc, hsupp⟩
      refine ⟨?_, ?_, Fc, hFc, ?_⟩
      · intro i
        cases i with
        | none =>
            have hx0 : 0 ≤ p.2.1 none := hnonneg none
            have ht0 : 0 ≤ (p.1 : ℝ) := p.1.2.1
            have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
            have hmul : 0 ≤ (1 - (p.1 : ℝ)) * p.2.1 none :=
              mul_nonneg (sub_nonneg.mpr ht1) hx0
            simp [cor33ConeApex]
            nlinarith
        | some i =>
            have hx0 : 0 ≤ p.2.1 (some i) := hnonneg (some i)
            have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
            simp [cor33ConeApex]
            exact mul_nonneg (sub_nonneg.mpr ht1) hx0
      · rw [Finset.sum_add_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        rw [hsum]
        have hapex : ∑ i : Option σ, cor33ConeApex i = 1 := by
          simp [cor33ConeApex]
        rw [hapex]
        ring
      · intro i hi
        by_cases hin : i = none
        · subst i
          rcases hFc with ⟨E, hE, rfl⟩
          simp
        · have hap : cor33ConeApex i = 0 := by
            cases i with
            | none => exact (hin rfl).elim
            | some j => rfl
          have hm : 0 < (1 - (p.1 : ℝ)) * p.2.1 i := by
            simpa [hap] using hi
          have hxpos : 0 < p.2.1 i := by
            by_contra hx
            have hxle : p.2.1 i ≤ 0 := le_of_not_gt hx
            have hxnonneg : 0 ≤ p.2.1 i := hnonneg i
            have hxzero : p.2.1 i = 0 := le_antisymm hxle hxnonneg
            rw [hxzero, mul_zero] at hm
            exact (lt_irrefl 0 hm)
          exact hsupp i hxpos⟩
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨a, ?_⟩
  refine ⟨{
    toFun := Fhom
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro i
      have ht : Continuous fun p : unitInterval × X => (p.1 : ℝ) :=
        continuous_subtype_val.comp continuous_fst
      have hx : Continuous fun p : unitInterval × X => p.2.1 i :=
        (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
      exact ((continuous_const.sub ht).mul hx).add (ht.mul continuous_const)
    map_zero_left := by
      intro x
      ext i
      simp [Fhom]
    map_one_left := by
      intro x
      ext i
      simp [Fhom, a, cor33ConeApex]
  }⟩

/-- The support complex of the coned ideal has contractible geometric realization. -/
theorem cor33_cone_supportComplex_contractible {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ContractibleSpace ↥(cor33GeomRealization
      (supportComplex (cor33ConeIdeal (K := K) r s))) := by
  have hne : cor33BaseClutter.Nonempty := by
    refine ⟨{Cor33Var.a, Cor33Var.c}, ?_⟩
    simp [cor33BaseClutter]
  rw [cor33_cone_supportComplex (K := K) hr hs]
  exact cor33GeomRealization_contractible_cone (H := cor33BaseClutter) hne

omit K [Field K] in
/-- The edge from a non-apex vertex to the cone apex. -/
noncomputable def cor33ConeEdgeOfVertex [Fintype σ] [LT σ] (H : Set (Finset σ))
    (v : cor33ChainVertex (coneClutter H)) (hv : v.1 ≠ none) :
    cor33ChainEdge (coneClutter H) := by
  let Fc : Finset (Option σ) := Classical.choose v.2
  have hFc : Fc ∈ coneClutter H ∧ v.1 ∈ Fc := Classical.choose_spec v.2
  have hnoneFc : none ∈ Fc := by
    rcases hFc.1 with ⟨E, hE, hEq⟩
    rw [← hEq]
    simp
  have hlt : none < v.1 := by
    cases hvi : v.1 with
    | none => exact (hv hvi).elim
    | some i => simp
  exact ⟨(none, v.1), hlt, Fc, hFc.1, hnoneFc, hFc.2⟩

omit K [Field K] in
/-- The triangle obtained by coning an edge not already incident to the apex. -/
noncomputable def cor33ConeTriangleOfEdge [Fintype σ] [LT σ] (H : Set (Finset σ))
    (e : cor33ChainEdge (coneClutter H)) (hu : e.1.1 ≠ none) :
    cor33ChainTriangle (coneClutter H) := by
  let Fc : Finset (Option σ) := Classical.choose e.2.2
  have hFc : Fc ∈ coneClutter H ∧ e.1.1 ∈ Fc ∧ e.1.2 ∈ Fc :=
    Classical.choose_spec e.2.2
  have hnoneFc : none ∈ Fc := by
    rcases hFc.1 with ⟨E, hE, hEq⟩
    rw [← hEq]
    simp
  have hvne : e.1.2 ≠ none := by
    intro hv
    cases hui : e.1.1 with
    | none => exact (hu hui).elim
    | some i => simpa [hui, hv] using e.2.1
  have hnoneu : none < e.1.1 := by
    cases hui : e.1.1 with
    | none => exact (hu hui).elim
    | some i => simp
  have hnonev : none < e.1.2 := by
    cases hvi : e.1.2 with
    | none => exact (hvne hvi).elim
    | some j => simp
  exact ⟨(none, e.1.1, e.1.2), hnoneu, e.2.1, hnonev,
    Fc, hFc.1, hnoneFc, hFc.2.1, hFc.2.2⟩

omit K [Field K] in
/-- The degree-zero part of the cone chain contraction. -/
noncomputable def cor33ConeHomotopyZero [Fintype σ] [LT σ] (L : Type*) [Field L]
    (H : Set (Finset σ)) :
    (cor33ChainVertex (coneClutter H) →₀ L) →ₗ[L]
      (cor33ChainEdge (coneClutter H) →₀ L) := by
  classical
  exact Finsupp.linearCombination L (fun v : cor33ChainVertex (coneClutter H) =>
    if hv : v.1 = none then 0 else
      Finsupp.single (cor33ConeEdgeOfVertex H v hv) (1 : L))

omit K [Field K] in
/-- The degree-one part of the cone chain contraction. -/
noncomputable def cor33ConeHomotopyOne [Fintype σ] [LT σ] (L : Type*) [Field L]
    (H : Set (Finset σ)) :
    (cor33ChainEdge (coneClutter H) →₀ L) →ₗ[L]
      (cor33ChainTriangle (coneClutter H) →₀ L) := by
  classical
  exact Finsupp.linearCombination L (fun e : cor33ChainEdge (coneClutter H) =>
    if hu : e.1.1 = none then 0 else
      Finsupp.single (cor33ConeTriangleOfEdge H e hu) (1 : L))

omit K [Field K] in
theorem cor33ConeHomotopyZero_single [Fintype σ] [LT σ] {L : Type*} [Field L]
    (H : Set (Finset σ)) (v : cor33ChainVertex (coneClutter H)) (c : L) :
    cor33ConeHomotopyZero L H (Finsupp.single v c) =
      if hv : v.1 = none then 0 else
        c • Finsupp.single (cor33ConeEdgeOfVertex H v hv) (1 : L) := by
  classical
  by_cases hv : v.1 = none
  · simp [cor33ConeHomotopyZero, Finsupp.linearCombination_apply, hv]
  · simp [cor33ConeHomotopyZero, Finsupp.linearCombination_apply, hv]

omit K [Field K] in
theorem cor33ConeHomotopyOne_single [Fintype σ] [LT σ] {L : Type*} [Field L]
    (H : Set (Finset σ)) (e : cor33ChainEdge (coneClutter H)) (c : L) :
    cor33ConeHomotopyOne L H (Finsupp.single e c) =
      if hu : e.1.1 = none then 0 else
        c • Finsupp.single (cor33ConeTriangleOfEdge H e hu) (1 : L) := by
  classical
  by_cases hu : e.1.1 = none
  · simp [cor33ConeHomotopyOne, Finsupp.linearCombination_apply, hu]
  · simp [cor33ConeHomotopyOne, Finsupp.linearCombination_apply, hu]

omit K [Field K] in
/-- The chain homotopy furnished by coning off an apex. -/
theorem cor33ConeContraction [Fintype σ] [LT σ] {L : Type*} [Field L]
    (H : Set (Finset σ)) :
    (cor33BoundaryTwo L (coneClutter H)).comp (cor33ConeHomotopyOne L H) +
        (cor33ConeHomotopyZero L H).comp (cor33BoundaryOne L (coneClutter H)) =
      LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  refine Finsupp.induction_linear x ?hzero ?hadd ?hsingle
  · simp
  · intro f g hf hg
    simp [map_add, hf, hg]
  · intro e c
    rcases e with ⟨⟨u, v⟩, he⟩
    cases u with
    | none =>
        have hvne : v ≠ none := by
          intro hv
          subst v
          simpa using he.1
        let ee : cor33ChainEdge (coneClutter H) := ⟨(none, v), he⟩
        have heq0 : ee.1.1 = none := rfl
        have hvhi : (cor33EdgeHigh (coneClutter H) ee).1 ≠ none := by
          change v ≠ none
          exact hvne
        have hlo : (cor33EdgeLow (coneClutter H) ee).1 = none := rfl
        have heq : cor33ConeEdgeOfVertex H (cor33EdgeHigh (coneClutter H) ee) hvhi =
            ee := by
          apply Subtype.ext
          rfl
        change
          (cor33BoundaryTwo L (coneClutter H))
              (cor33ConeHomotopyOne L H (Finsupp.single ee c)) +
            (cor33ConeHomotopyZero L H)
              (cor33BoundaryOne L (coneClutter H) (Finsupp.single ee c)) =
              Finsupp.single ee c
        rw [cor33ConeHomotopyOne_single, cor33BoundaryOne_single]
        rw [dif_pos heq0]
        simp only [map_zero, zero_add, map_smul, map_sub]
        rw [cor33ConeHomotopyZero_single, cor33ConeHomotopyZero_single]
        rw [dif_neg hvhi, dif_pos hlo]
        rw [heq]
        simp
    | some x =>
        cases v with
        | none =>
            exfalso
            simpa using he.1
        | some y =>
            let ee : cor33ChainEdge (coneClutter H) := ⟨(some x, some y), he⟩
            have hune : (some x : Option σ) ≠ none := by simp
            have hvne : (some y : Option σ) ≠ none := by simp
            have hu : ee.1.1 ≠ none := by
              change (some x : Option σ) ≠ none
              exact hune
            have hvhi : (cor33EdgeHigh (coneClutter H) ee).1 ≠ none := by
              change (some y : Option σ) ≠ none
              exact hvne
            have hvlo : (cor33EdgeLow (coneClutter H) ee).1 ≠ none := by
              change (some x : Option σ) ≠ none
              exact hune
            let tt : cor33ChainTriangle (coneClutter H) :=
              cor33ConeTriangleOfEdge H ee hu
            have ht12 : cor33Triangle12 (coneClutter H) tt = ee := by
              apply Subtype.ext
              rfl
            have ht02 : cor33Triangle02 (coneClutter H) tt =
                cor33ConeEdgeOfVertex H (cor33EdgeHigh (coneClutter H) ee) hvhi := by
              apply Subtype.ext
              rfl
            have ht01 : cor33Triangle01 (coneClutter H) tt =
                cor33ConeEdgeOfVertex H (cor33EdgeLow (coneClutter H) ee) hvlo := by
              apply Subtype.ext
              rfl
            change
              (cor33BoundaryTwo L (coneClutter H))
                  (cor33ConeHomotopyOne L H (Finsupp.single ee c)) +
                (cor33ConeHomotopyZero L H)
                  (cor33BoundaryOne L (coneClutter H) (Finsupp.single ee c)) =
                  Finsupp.single ee c
            rw [cor33ConeHomotopyOne_single, cor33BoundaryOne_single]
            rw [dif_neg hu]
            simp only [map_smul, map_sub]
            rw [cor33BoundaryTwo_single, cor33ConeHomotopyZero_single,
              cor33ConeHomotopyZero_single]
            rw [dif_neg hvhi, dif_neg hvlo]
            rw [ht12, ht02, ht01]
            simp [Finsupp.smul_single, smul_add, smul_neg, sub_eq_add_neg]
            abel

set_option linter.style.haveILetI false in
omit K [Field K] in
/-- A cone has vanishing first Betti number in the local chain model. -/
theorem cor33_coneBettiOne_eq_zero [Fintype σ] [LinearOrder σ]
    (L : Type*) [Field L] (H : Set (Finset σ)) :
    cor33BettiOne L (coneClutter H) = 0 := by
  letI : AddCommGroup
      ↥(LinearMap.ker (cor33BoundaryOne L (coneClutter H))) := inferInstance
  letI : Module L
      ↥(LinearMap.ker (cor33BoundaryOne L (coneClutter H))) := inferInstance
  have htop : cor33Boundaries L (coneClutter H) = ⊤ := by
    rw [cor33Boundaries, LinearMap.range_eq_top]
    intro z
    rcases z with ⟨z, hz⟩
    refine ⟨cor33ConeHomotopyOne L H z, ?_⟩
    apply Subtype.ext
    have hc := congrArg (fun f : (cor33ChainEdge (coneClutter H) →₀ L) →ₗ[L]
        (cor33ChainEdge (coneClutter H) →₀ L) => f z)
      (cor33ConeContraction (L := L) H)
    have hz0 : cor33BoundaryOne L (coneClutter H) z = 0 := by
      simpa using hz
    simpa [LinearMap.comp_apply, hz0] using hc
  change Module.finrank L
      (↥(LinearMap.ker (cor33BoundaryOne L (coneClutter H))) ⧸
        cor33Boundaries L (coneClutter H)) = 0
  rw [htop]
  exact Module.finrank_eq_zero_of_subsingleton L _

@[simp] theorem cor33VarRank_a : cor33VarRank Cor33Var.a = 0 := rfl
@[simp] theorem cor33VarRank_b : cor33VarRank Cor33Var.b = 1 := rfl
@[simp] theorem cor33VarRank_c : cor33VarRank Cor33Var.c = 2 := rfl
@[simp] theorem cor33VarRank_d : cor33VarRank Cor33Var.d = 3 := rfl
@[simp] theorem cor33VarRank_z : cor33VarRank Cor33Var.z = 4 := rfl

@[simp] theorem cor33Var_lt_iff_rank (x y : Cor33Var) :
    x < y ↔ cor33VarRank x < cor33VarRank y := by
  rfl

/-- The support complex of the coned ideal has vanishing first Betti number over every
field, using a fresh coefficient field independent of the ideal's base field. -/
theorem cor33_cone_supportComplex_bettiOne_eq_zero {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {F : Type*} [Field F] :
    cor33BettiOne F (supportComplex (cor33ConeIdeal (K := K) r s)) = 0 := by
  rw [cor33_cone_supportComplex (K := K) hr hs]
  exact cor33_coneBettiOne_eq_zero (L := F) (H := cor33BaseClutter)

omit [DecidableEq σ] in
/-- The written ideal \((t^q)\) is the \(q\)-th ideal power of \((t)\). -/
theorem cor33ConeTPow_eq_nonePrimeOf_pow (q : ℕ) :
    cor33ConeTPow (K := K) q =
      (primeOf ({none} : Finset (Option Cor33Var)) :
        Ideal (MvPolynomial (Option Cor33Var) K)) ^ q := by
  have hspan :
      (primeOf ({none} : Finset (Option Cor33Var)) :
        Ideal (MvPolynomial (Option Cor33Var) K)) =
        Ideal.span ({X none} : Set (MvPolynomial (Option Cor33Var) K)) := by
    simpa using (cor33_primeOf_eq_span_X (K := K)
      (A := ({none} : Finset (Option Cor33Var))))
  rw [cor33ConeTPow, hspan]
  exact (Ideal.span_singleton_pow
    (X none : MvPolynomial (Option Cor33Var) K) q).symm

omit [DecidableEq σ] in
/-- The \(none\)-component power is exactly \((t^q)\). -/
theorem cor33ConeTPow_eq_component_none_pow {r s q : ℕ} :
    (purePower (conePureSupport cor33ComponentSupport none)
      (conePureExp (cor33ComponentExp r s) none) :
        Ideal (MvPolynomial (Option Cor33Var) K)) ^ q =
      cor33ConeTPow (K := K) q := by
  rw [cor33ConeTPow_eq_nonePrimeOf_pow, primeOf]
  simp [conePureSupport, conePureExp]

omit [DecidableEq σ] in
/-- A \(some\)-component power is the extension of the base component power. -/
theorem cor33ConedComponentPower_eq_component_some_pow {r s q : ℕ} (j : Cor33Comp) :
    (purePower (conePureSupport cor33ComponentSupport (some j))
      (conePureExp (cor33ComponentExp r s) (some j)) :
        Ideal (MvPolynomial (Option Cor33Var) K)) ^ q =
      cor33ConedComponentPower (K := K) r s q j := by
  unfold cor33ConedComponentPower
  rw [cor33Component]
  rw [← (show Ideal.map (MvPolynomial.rename (R := K) (Option.some : Cor33Var → Option Cor33Var))
            (purePower (cor33ComponentSupport j) (cor33ComponentExp r s j)) =
          purePower (conePureSupport cor33ComponentSupport (some j))
            (conePureExp (cor33ComponentExp r s) (some j)) from
        cor33_rename_purePower (σ := Cor33Var) (K := K)
          (A := cor33ComponentSupport j) (a := cor33ComponentExp r s j)), Ideal.map_pow]

omit [DecidableEq σ] in
/-- Split the componentwise symbolic expression into \((t^q)\) and old component powers. -/
theorem cor33_cone_componentSymbolic_eq_displayed {r s q : ℕ} :
    componentSymbolic
      ((fun j => purePower (conePureSupport cor33ComponentSupport j)
        (conePureExp (cor33ComponentExp r s) j)) :
        Option Cor33Comp → Ideal (MvPolynomial (Option Cor33Var) K)) q =
      cor33ConeTPow (K := K) q ⊓
        ⨅ j : Cor33Comp, cor33ConedComponentPower (K := K) r s q j := by
  let C : Option Cor33Comp →
      Ideal (MvPolynomial (Option Cor33Var) K) := fun j =>
    purePower (conePureSupport cor33ComponentSupport j)
      (conePureExp (cor33ComponentExp r s) j)
  change componentSymbolic C q =
    cor33ConeTPow (K := K) q ⊓
      ⨅ j : Cor33Comp, cor33ConedComponentPower (K := K) r s q j
  calc
    componentSymbolic C q = (C none) ^ q ⊓ ⨅ j : Cor33Comp, (C (some j)) ^ q := by
      rw [componentSymbolic, iInf_option]
    _ = cor33ConeTPow (K := K) q ⊓ ⨅ j : Cor33Comp, (C (some j)) ^ q := by
      have hnone : (C none) ^ q = cor33ConeTPow (K := K) q := by
        simpa [C] using (cor33ConeTPow_eq_component_none_pow
          (K := K) (r := r) (s := s) (q := q))
      rw [hnone]
    _ = cor33ConeTPow (K := K) q ⊓
        ⨅ j : Cor33Comp, cor33ConedComponentPower (K := K) r s q j := by
      apply congrArg (fun Z : Ideal (MvPolynomial (Option Cor33Var) K) =>
        cor33ConeTPow (K := K) q ⊓ Z)
      apply iInf_congr
      intro j
      simpa [C] using (cor33ConedComponentPower_eq_component_some_pow
        (K := K) (r := r) (s := s) (q := q) j)

omit [DecidableEq σ] in
/-- The monomial identity \(t^q I_{r,s}^qR = K_{r,s}^q\). -/
theorem cor33_coneTPow_mul_conedBasePower {r s q : ℕ} :
    cor33ConeTPow (K := K) q * cor33ConedBasePower (K := K) r s q =
      (cor33ConeIdeal (K := K) r s) ^ q := by
  unfold cor33ConedBasePower cor33ConeIdeal
  rw [cor33ConeTPow_eq_nonePrimeOf_pow]
  rw [coneIdeal, Ideal.map_pow, mul_pow]
  exact mul_comm _ _

/-- The displayed symbolic-power formula from Corollary 3.3, for every positive \(q\). -/
theorem cor33_cone_symbolicPower_displayedFormula {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {q : ℕ} (hq : 0 < q) :
    (symbolicPower (cor33ConeIdeal (K := K) r s) q =
      cor33ConeTPow (K := K) q ⊓
        ⨅ j : Cor33Comp, cor33ConedComponentPower (K := K) r s q j) ∧
    (cor33ConeTPow (K := K) q ⊓
        ⨅ j : Cor33Comp, cor33ConedComponentPower (K := K) r s q j =
      cor33ConeTPow (K := K) q * cor33ConedBasePower (K := K) r s q) ∧
    (cor33ConeTPow (K := K) q * cor33ConedBasePower (K := K) r s q =
      (cor33ConeIdeal (K := K) r s) ^ q) ∧
    symbolicPower (cor33ConeIdeal (K := K) r s) q =
      (cor33ConeIdeal (K := K) r s) ^ q := by
  have hq1 : 1 ≤ q := by omega
  have hstd := (cor33_cone_hasStdSymbolic (K := K) hr hs) q hq1
  have hcomp := (cor33_cone_componentSimis (K := K) hr hs) q hq1
  have hsimis := (cor33_cone_isSimis (K := K) hr hs) q hq1
  have hsplit := cor33_cone_componentSymbolic_eq_displayed
    (K := K) (r := r) (s := s) (q := q)
  have hprod := cor33_coneTPow_mul_conedBasePower
    (K := K) (r := r) (s := s) (q := q)
  have hsymInt :
      symbolicPower (cor33ConeIdeal (K := K) r s) q =
        cor33ConeTPow (K := K) q ⊓
          ⨅ j : Cor33Comp, cor33ConedComponentPower (K := K) r s q j :=
    hstd.trans hsplit
  have hKInt :
      (cor33ConeIdeal (K := K) r s) ^ q =
        cor33ConeTPow (K := K) q ⊓
          ⨅ j : Cor33Comp, cor33ConedComponentPower (K := K) r s q j :=
    hcomp.trans hsplit
  exact ⟨hsymInt, hKInt.symm.trans hprod.symm, hprod, hsimis⟩

/-- For \(r=s=\rho\), the squarefree diagonal root and its positive weights are unique. -/
theorem cor33_cone_sqRootWeight_unique {rho : ℕ} (hrho : 0 < rho)
    {J : Ideal (MvPolynomial (Option Cor33Var) K)} {d : Option Cor33Var → ℕ}
    (hJ : IsSquarefreeMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hdiag : diagonal d J = cor33ConeIdeal (K := K) rho rho) :
    J = cor33ConeRadicalIdeal (K := K) ∧ d = cor33ConeWeight rho := by
  have hgac : cor33Exp 1 0 1 0 0 ∈ cor33BaseGens rho rho := by
    simp [cor33BaseGens]
  have hgbd : cor33Exp 0 1 0 1 0 ∈ cor33BaseGens rho rho := by
    simp [cor33BaseGens]
  have hgabz : cor33Exp 1 1 0 0 rho ∈ cor33BaseGens rho rho := by
    simp [cor33BaseGens]
  have hd_of_exp {g : Cor33Var →₀ ℕ} (hg : g ∈ cor33BaseGens rho rho)
      {i : Option Cor33Var} {n : ℕ} (hn : 0 < n)
      (hi : coneExp g i = n) : d i = n := by
    have hmin : coneExp g ∈ minGens (cor33ConeIdeal (K := K) rho rho) :=
      cor33_cone_generator_mem_minGens (K := K) hg
    have hcoord := cor33_sqRoot_minGen_coordinate (K := K)
      (I := cor33ConeIdeal (K := K) rho rho) (J := J) (d := d)
      hJ hd hdiag (e := coneExp g) hmin i
    rcases hcoord with hzero | hweight
    · have hnzero : n = 0 := by simpa [hi] using hzero
      omega
    · exact hweight.symm.trans hi
  have hd_none : d none = 1 :=
    hd_of_exp hgac (by omega) (by simp)
  have hd_a : d (some Cor33Var.a) = 1 :=
    hd_of_exp hgac (by omega) (by simp [coneExp_apply_some, cor33Exp_apply])
  have hd_c : d (some Cor33Var.c) = 1 :=
    hd_of_exp hgac (by omega) (by simp [coneExp_apply_some, cor33Exp_apply])
  have hd_b : d (some Cor33Var.b) = 1 :=
    hd_of_exp hgbd (by omega) (by simp [coneExp_apply_some, cor33Exp_apply])
  have hd_d : d (some Cor33Var.d) = 1 :=
    hd_of_exp hgbd (by omega) (by simp [coneExp_apply_some, cor33Exp_apply])
  have hd_z : d (some Cor33Var.z) = rho :=
    hd_of_exp hgabz hrho (by simp [coneExp_apply_some, cor33Exp_apply])
  have hd_weight : d = cor33ConeWeight rho := by
    funext i
    cases i with
    | none => simpa [cor33ConeWeight] using hd_none
    | some i =>
        cases i <;> simp [cor33ConeWeight, cor33BaseWeight,
          hd_a, hd_b, hd_c, hd_d, hd_z]
  have hJmon : IsMonomialIdeal J := by
    rcases hJ with ⟨H, hH⟩
    exact ⟨characteristicExp '' H, hH⟩
  have hRmon : IsMonomialIdeal (cor33ConeRadicalIdeal (K := K)) := by
    refine ⟨coneExp '' (cor33BaseGens 1 1 : Set (Cor33Var →₀ ℕ)), ?_⟩
    rw [cor33ConeRadicalIdeal, cor33RadicalIdeal, cor33BaseIdeal,
      cor33_coneIdeal_monomialIdeal]
  have hdiagW : diagonal (cor33ConeWeight rho) J =
      cor33ConeIdeal (K := K) rho rho := by
    simpa [hd_weight] using hdiag
  have hrootDiag : diagonal (cor33ConeWeight rho) (cor33ConeRadicalIdeal (K := K)) =
      cor33ConeIdeal (K := K) rho rho :=
    cor33_diagonal_coneRadicalIdeal (K := K) rho
  have hroot : J = cor33ConeRadicalIdeal (K := K) :=
    eq4_diagonal_injective (d := cor33ConeWeight rho)
      (cor33ConeWeight_pos hrho) hJmon hRmon (hdiagW.trans hrootDiag.symm)
  exact ⟨hroot, hd_weight⟩

/-- One theorem containing the promised counterexample for unequal positive parameters. -/
theorem cor33_counterexample_full {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s)
    {F : Type*} [Field F] :
    MPVHypotheses (cor33ConeIdeal (K := K) r s)
      (conePureSupport cor33ComponentSupport)
      (conePureExp (cor33ComponentExp r s)) ∧
    SupportPreserving (cor33ConeIdeal (K := K) r s) ∧
    supportComplex (cor33ConeIdeal (K := K) r s) = coneClutter cor33BaseClutter ∧
    ContractibleSpace ↥(cor33GeomRealization
      (supportComplex (cor33ConeIdeal (K := K) r s))) ∧
    cor33BettiOne F (supportComplex (cor33ConeIdeal (K := K) r s)) = 0 ∧
    cor33BettiOne F (supportComplex (cor33ConeIdeal (K := K) r s)) ≤ 1 ∧
    ¬ MPVConc (cor33ConeIdeal (K := K) r s) := by
  have h := cor33_contractibleCounterexample (K := K) hr hs hrs
  rcases h with ⟨hmpv, hsupp, hcomplex, hnot⟩
  have hcontr := cor33_cone_supportComplex_contractible (K := K) hr hs
  have hbetti := cor33_cone_supportComplex_bettiOne_eq_zero (K := K) hr hs (F := F)
  refine ⟨hmpv, hsupp, hcomplex, hcontr, hbetti, ?_, hnot⟩
  rw [hbetti]
  exact Nat.zero_le 1

/-- Corollary 3.3, packaged in one declaration. -/
theorem cor33_main {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    Cor33Conclusion (K := K) (r := r) (s := s) hr hs := by
  refine
    { decomposition := cor33_cone_irredundantDecomp (K := K) hr hs
      componentHeight := cor33_cone_component_height (K := K) hr hs
      componentHeightValues := cor33_cone_componentHeight_values (K := K) hr hs
      primeInjective := cor33_conePrime_injective (K := K)
      primeRangeCard := cor33_conePrime_range_ncard (K := K)
      associatedEqMinimal :=
        cor33_cone_associatedPrimes_eq_minimalPrimes (K := K) hr hs
      minimalEqRange := cor33_cone_minimalPrimes_eq_range (K := K) hr hs
      associatedEqRange := cor33_cone_associatedPrimes_eq_range (K := K) hr hs
      associatedPowerEqRange := by
        intro q hq
        exact cor33_cone_associatedPrimes_pow_eq_range (K := K) hr hs hq
      normallyTorsionFree := cor33_cone_prop21NormallyTorsionFree (K := K) hr hs
      symbolicPowerFormula := by
        intro q hq
        exact cor33_cone_symbolicPower_displayedFormula (K := K) hr hs hq
      radical := cor33_cone_radical (K := K) hr hs
      supportPreserving := cor33_cone_supportPreserving (K := K) hr hs
      supportComplexEqCone := cor33_cone_supportComplex (K := K) hr hs
      contractible := cor33_cone_supportComplex_contractible (K := K) hr hs
      bettiOne := by
        intro F _
        exact cor33_cone_supportComplex_bettiOne_eq_zero (K := K) hr hs (F := F)
      squarefreeRootCriterion := cor33_cone_hasSqRoot_iff (K := K) hr hs
      equalRoot := by
        intro hrs
        subst s
        exact ⟨cor33ConeRadicalIdeal_isSquarefree (K := K),
          cor33ConeWeight_pos hr, cor33_diagonal_coneRadicalIdeal (K := K) r⟩
      equalRootSimis := by
        intro hrs
        exact cor33_cone_MPVConc_of_eq (K := K) hr hs hrs
      equalRootUnique := by
        intro hrs J d hJ hd hdiag
        subst s
        exact cor33_cone_sqRootWeight_unique (K := K) (rho := r) hr hJ hd hdiag
      counterexample := by
        intro F _ hrs
        exact cor33_counterexample_full (K := K) hr hs hrs (F := F) }

end SimisFormal
