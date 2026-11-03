import SimisFormal.Defs
import SimisFormal.Basic

namespace SimisFormal
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [Field K] [DecidableEq σ]
omit [DecidableEq σ] in
/-- Every monomial ideal in finitely many variables has a finite monomial generating set. -/
private theorem exists_finset_monomial_generators [Fintype σ]
    {I : Ideal (MvPolynomial σ K)} (hI : IsMonomialIdeal I) :
    ∃ S : Finset (σ →₀ ℕ), I = monomialIdeal (S : Set (σ →₀ ℕ)) := by
  classical
  obtain ⟨G, hG⟩ := Ideal.FG.of_isNoetherianRing I
  rcases hI with ⟨T, hIT⟩
  let S : Finset (σ →₀ ℕ) := G.biUnion fun p ↦ p.support
  refine ⟨S, le_antisymm ?_ ?_⟩
  · rw [← hG]
    refine Ideal.span_le.mpr ?_
    intro p hpG
    apply mem_monomialIdeal.mpr
    intro e he
    have heS : e ∈ S := by
      exact Finset.mem_biUnion.mpr ⟨p, hpG, he⟩
    exact ⟨e, heS, le_rfl⟩
  · rw [monomialIdeal, Ideal.span_le]
    rintro y ⟨e, heS, rfl⟩
    change e ∈ G.biUnion (fun p ↦ p.support) at heS
    rcases Finset.mem_biUnion.mp heS with ⟨p, hpG, heSupp⟩
    have hpI : p ∈ I := by
      rw [← hG]
      exact Ideal.subset_span hpG
    have heI : (monomial e (1 : K) : MvPolynomial σ K) ∈ I := by
      rw [hIT] at hpI ⊢
      exact monomial_mem_monomialIdeal.mpr ((mem_monomialIdeal.mp hpI) e heSupp)
    exact heI

omit [DecidableEq σ] in
/-- The standard choice-function decomposition of a finitely generated monomial ideal. -/
private theorem exists_choice_decomposition (S : Finset (σ →₀ ℕ)) :
    ∃ (n : ℕ) (A : Fin n → Finset σ) (a : Fin n → σ → ℕ),
      HasComponents (K := K) (monomialIdeal (S : Set (σ →₀ ℕ))) A a := by
  classical
  let C : Type _ :=
    (u : {e : σ →₀ ℕ // e ∈ S}) → {i : σ // i ∈ u.1.support}
  let A : C → Finset σ := fun c ↦
    Finset.univ.image fun u : {e : σ →₀ ℕ // e ∈ S} ↦ (c u).1
  let U : C → σ → Finset {e : σ →₀ ℕ // e ∈ S} := fun c i ↦
    Finset.univ.filter fun u ↦ (c u).1 = i
  let a : C → σ → ℕ := fun c i ↦
    if h : (U c i).Nonempty then (U c i).inf' h (fun u ↦ u.1 i) else 1
  have : Fintype C := inferInstance
  let e : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  refine ⟨Fintype.card C, (fun j ↦ A (e.symm j)), (fun j ↦ a (e.symm j)), ?_⟩
  change monomialIdeal (S : Set (σ →₀ ℕ)) =
    ⨅ j : Fin (Fintype.card C),
      (purePower (A (e.symm j)) (a (e.symm j)) : Ideal (MvPolynomial σ K))
  rw [Equiv.iInf_comp
    (g := fun c : C ↦ (purePower (A c) (a c) : Ideal (MvPolynomial σ K))) e.symm]
  apply le_antisymm
  · intro x hx
    have hxSupp := mem_monomialIdeal.mp hx
    refine Ideal.mem_iInf.mpr ?_
    intro c
    change x ∈ monomialIdeal {z : σ →₀ ℕ | ∃ i ∈ A c, z = Finsupp.single i (a c i)}
    apply mem_monomialIdeal.mpr
    intro e he
    rcases hxSupp e he with ⟨u, huS, hue⟩
    let us : {v : σ →₀ ℕ // v ∈ S} := ⟨u, huS⟩
    let i : σ := (c us).1
    have hiA : i ∈ A c := by
      change (c us).1 ∈ Finset.univ.image fun v : {v : σ →₀ ℕ // v ∈ S} ↦ (c v).1
      exact Finset.mem_image.mpr ⟨us, Finset.mem_univ _, rfl⟩
    have huU : us ∈ U c i := by
      change us ∈ Finset.univ.filter (fun v : {v : σ →₀ ℕ // v ∈ S} ↦ (c v).1 = i)
      simp [i]
    have hmin : a c i ≤ u i := by
      have hnon : (U c i).Nonempty := ⟨us, huU⟩
      dsimp [a]
      rw [dif_pos hnon]
      exact Finset.inf'_le (fun v : {v : σ →₀ ℕ // v ∈ S} ↦ v.1 i) huU
    refine ⟨Finsupp.single i (a c i), ⟨i, hiA, rfl⟩, ?_⟩
    rw [Finsupp.single_le_iff]
    exact hmin.trans (hue i)
  · intro x hx
    apply mem_monomialIdeal.mpr
    intro e he
    by_contra heI
    have hchoose : ∀ u : {v : σ →₀ ℕ // v ∈ S},
        ∃ i : {i : σ // i ∈ u.1.support}, e i.1 < u.1 i.1 := by
      intro u
      have hnle : ¬ u.1 ≤ e := fun hle ↦ heI ⟨u.1, u.2, hle⟩
      rw [Finsupp.le_def] at hnle
      push Not at hnle
      rcases hnle with ⟨i, hlt⟩
      have hiSupp : i ∈ u.1.support := by
        rw [Finsupp.mem_support_iff]
        exact ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hlt)
      exact ⟨⟨i, hiSupp⟩, hlt⟩
    choose c hc using hchoose
    have hxc : x ∈ (purePower (A c) (a c) : Ideal (MvPolynomial σ K)) :=
      Ideal.mem_iInf.mp hx c
    have hxcSupp : ∀ d ∈ x.support, ∃ z,
        (∃ i ∈ A c, z = Finsupp.single i (a c i)) ∧ z ≤ d := by
      change x ∈ monomialIdeal {z : σ →₀ ℕ | ∃ i ∈ A c, z = Finsupp.single i (a c i)} at hxc
      exact mem_monomialIdeal.mp hxc
    rcases hxcSupp e he with ⟨z, ⟨i, hiA, hz⟩, hze⟩
    subst z
    have hai : a c i ≤ e i := Finsupp.single_le_iff.mp hze
    change i ∈ Finset.univ.image (fun u : {v : σ →₀ ℕ // v ∈ S} ↦ (c u).1) at hiA
    rcases Finset.mem_image.mp hiA with ⟨u, _, hcu⟩
    have huU : u ∈ U c i := by
      change u ∈ Finset.univ.filter (fun v : {v : σ →₀ ℕ // v ∈ S} ↦ (c v).1 = i)
      simp [hcu]
    have hsucc : e i + 1 ≤ a c i := by
      have hnon : (U c i).Nonempty := ⟨u, huU⟩
      dsimp [a]
      rw [dif_pos hnon]
      refine Finset.le_inf' hnon (fun v : {v : σ →₀ ℕ // v ∈ S} ↦ v.1 i) ?_
      intro v hv
      have hcv : (c v).1 = i := by
        change v ∈ Finset.univ.filter (fun w : {w : σ →₀ ℕ // w ∈ S} ↦ (c w).1 = i) at hv
        exact (Finset.mem_filter.mp hv).2
      exact Nat.succ_le_of_lt (by simpa [hcv] using hc v)
    exact (Nat.not_succ_le_self (e i)) (hsucc.trans hai)

omit [DecidableEq σ] in
/-- Any finite component family contains a minimum-cardinality irredundant subfamily. -/
private theorem exists_irredundant_subfamily
    {κ : Type*} [Fintype κ] {I : Ideal (MvPolynomial σ K)}
    {A : κ → Finset σ} {a : κ → σ → ℕ}
    (hI : HasComponents (K := K) I A a) :
    ∃ s : Finset κ,
      IsIrredundantDecomp (K := K) I
        (fun j : {k : κ // k ∈ s} ↦ A j.1)
        (fun j : {k : κ // k ∈ s} ↦ a j.1) := by
  classical
  let Q : κ → Ideal (MvPolynomial σ K) := fun k ↦ purePower (A k) (a k)
  let P : Finset (Finset κ) :=
    (Finset.univ : Finset κ).powerset.filter fun s ↦ s.inf Q = I
  have huniv : (Finset.univ : Finset κ).inf Q = I := by
    rw [Finset.inf_univ_eq_iInf]
    exact hI.symm
  have hPne : P.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    change (Finset.univ : Finset κ) ∈
      (Finset.univ : Finset κ).powerset.filter fun s ↦ s.inf Q = I
    rw [Finset.mem_filter]
    exact ⟨by simp, huniv⟩
  obtain ⟨s, hsP, hsmin⟩ := Finset.exists_min_image P (fun t ↦ t.card) hPne
  refine ⟨s, ?_⟩
  let As : {k : κ // k ∈ s} → Finset σ := fun j ↦ A j.1
  let as : {k : κ // k ∈ s} → σ → ℕ := fun j ↦ a j.1
  change IsIrredundantDecomp (K := K) I As as
  have hsEq : s.inf Q = I := by
    change s ∈ (Finset.univ : Finset κ).powerset.filter (fun t ↦ t.inf Q = I) at hsP
    exact (Finset.mem_filter.mp hsP).2
  have hsiInf : (⨅ j : {k : κ // k ∈ s}, Q j.1) = s.inf Q := by
    rw [Finset.inf_eq_iInf]
    exact iInf_subtype'' (s := (s : Set κ)) Q
  have hcomp : HasComponents (K := K) I As as := by
    change I = ⨅ j : {k : κ // k ∈ s}, Q j.1
    exact hsEq.symm.trans hsiInf.symm
  refine ⟨hcomp, ?_⟩
  intro j hred
  have homit_eq :
      (decompOmit As as j : Ideal (MvPolynomial σ K)) = (s.erase j.1).inf Q := by
    apply le_antisymm
    · rw [decompOmit, Finset.le_inf_iff]
      intro k hk
      rcases Finset.mem_erase.mp hk with ⟨hkne, hkS⟩
      have hne : (⟨k, hkS⟩ : {x : κ // x ∈ s}) ≠ j := by
        intro h
        exact hkne (congrArg Subtype.val h)
      have hle := iInf_le
        (fun t : {t : {x : κ // x ∈ s} // t ≠ j} ↦
          (purePower (As t.1) (as t.1) : Ideal (MvPolynomial σ K)))
        ⟨⟨k, hkS⟩, hne⟩
      simpa [As, as, Q] using hle
    · rw [decompOmit]
      refine le_iInf fun k ↦ ?_
      have hne : k.1.1 ≠ j.1 := by
        intro h
        exact k.2 (Subtype.ext h)
      apply Finset.inf_le
      simp [hne, k.1.2]
  have hleErase : (s.erase j.1).inf Q ≤ Q j.1 := by
    rw [← homit_eq]
    simpa [As, as, Q] using hred
  have hfactor : s.inf Q = Q j.1 ⊓ (s.erase j.1).inf Q := by
    calc
      s.inf Q = (insert j.1 (s.erase j.1)).inf Q := by
        rw [Finset.insert_erase j.2]
      _ = Q j.1 ⊓ (s.erase j.1).inf Q := Finset.inf_insert
  have heraseEq : (s.erase j.1).inf Q = I := by
    exact (hfactor.trans (inf_eq_right.mpr hleErase)).symm.trans hsEq
  have heraseP : s.erase j.1 ∈ P := by
    change s.erase j.1 ∈
      (Finset.univ : Finset κ).powerset.filter fun t ↦ t.inf Q = I
    rw [Finset.mem_filter]
    exact ⟨by simp, heraseEq⟩
  exact (not_lt_of_ge (hsmin (s.erase j.1) heraseP))
    (Finset.card_lt_card (Finset.erase_ssubset j.2))

omit [DecidableEq σ] in
/-- Irredundant decompositions are invariant under reindexing by an equivalence. -/
private theorem reindex_irredundantDecomp
    {κ : Type*} [Fintype κ] {I : Ideal (MvPolynomial σ K)}
    {A : κ → Finset σ} {a : κ → σ → ℕ}
    (h : IsIrredundantDecomp (K := K) I A a) :
    IsIrredundantDecomp (K := K) I
      (fun j : Fin (Fintype.card κ) ↦ A ((Fintype.equivFin κ).symm j))
      (fun j : Fin (Fintype.card κ) ↦ a ((Fintype.equivFin κ).symm j)) := by
  classical
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  change IsIrredundantDecomp (K := K) I
    (fun j ↦ A (e.symm j)) (fun j ↦ a (e.symm j))
  rcases h with ⟨hc, hi⟩
  have hEq : I = ⨅ k : κ, (purePower (A k) (a k) : Ideal (MvPolynomial σ K)) := hc
  refine ⟨?_, ?_⟩
  · change I = ⨅ j : Fin (Fintype.card κ),
      (purePower (A (e.symm j)) (a (e.symm j)) : Ideal (MvPolynomial σ K))
    rw [hEq]
    exact (Equiv.iInf_comp
      (g := fun k : κ ↦ (purePower (A k) (a k) : Ideal (MvPolynomial σ K))) e.symm).symm
  · intro j hred
    apply hi (e.symm j)
    intro x hxold
    apply hred
    rw [decompOmit] at hxold ⊢
    have hxoldAll := Ideal.mem_iInf.mp hxold
    refine Ideal.mem_iInf.mpr ?_
    intro k
    have hne : e.symm k.1 ≠ e.symm j := by
      intro heq
      exact k.2 (e.symm.injective heq)
    exact hxoldAll ⟨e.symm k.1, hne⟩

omit [DecidableEq σ] in
/-- Every monomial ideal in finitely many variables has a finite irredundant
irreducible decomposition. -/
theorem hasFiniteIrredundantDecomp_of_isMonomialIdeal [Fintype σ]
    {I : Ideal (MvPolynomial σ K)} (hI : IsMonomialIdeal I) :
    HasFiniteIrredundantDecomp I := by
  obtain ⟨S, hS⟩ := exists_finset_monomial_generators (K := K) hI
  obtain ⟨n, A, a, hcomp⟩ := exists_choice_decomposition (K := K) S
  have hcompI : HasComponents (K := K) I A a := by
    rw [hS]
    exact hcomp
  obtain ⟨s, hsub⟩ := exists_irredundant_subfamily (K := K) hcompI
  let e : {k : Fin n // k ∈ s} ≃ Fin (Fintype.card {k : Fin n // k ∈ s}) :=
    Fintype.equivFin {k : Fin n // k ∈ s}
  refine ⟨Fin (Fintype.card {k : Fin n // k ∈ s}), inferInstance,
    (fun j ↦ A (e.symm j).1), (fun j ↦ a (e.symm j).1), ?_⟩
  simpa [e] using (reindex_irredundantDecomp (K := K) hsub)

end SimisFormal
