import SimisFormal.Defs
import SimisFormal.Basic

namespace SimisFormal
variable {σ Λ : Type*} [DecidableEq σ]
/-- A third edge inside `A ∪ B`, together with a point of `A ∩ B` missing it,
    gives an explicit strong triangle. -/
theorem lem43_strongTriangle_of_third
    {H : Set (Finset σ)} {A B C : Finset σ} {d p q : σ}
    (hAH : A ∈ H) (hCH : C ∈ H) (hBH : B ∈ H)
    (hdA : d ∈ A) (hdB : d ∈ B) (hdC : d ∉ C)
    (hpA : p ∈ A) (hpB : p ∉ B) (hpC : p ∈ C)
    (hqA : q ∉ A) (hqB : q ∈ B) (hqC : q ∈ C)
    (hAC : A ≠ C) (hCB : C ≠ B) (hAB : A ≠ B) :
    HasStrongTriangle H := by
  let v : Fin 3 → σ := ![d, p, q]
  let E : Fin 3 → Finset σ := ![A, C, B]
  have hdp : d ≠ p := by
    intro h
    exact hpB (h ▸ hdB)
  have hdq : d ≠ q := by
    intro h
    exact hqA (h ▸ hdA)
  have hpq : p ≠ q := by
    intro h
    exact hqA (h ▸ hpA)
  have hv : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [v, hdp, hdp.symm, hdq, hdq.symm, hpq, hpq.symm] at hij ⊢
  have hE : Function.Injective E := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [E, hAC, hAC.symm, hCB, hCB.symm, hAB, hAB.symm] at hij ⊢
  have hv_image : Finset.univ.image v = {d, p, q} := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, _, hiv⟩
      fin_cases i <;> simp [v] at hiv ⊢
      all_goals simp [hiv]
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Finset.mem_image.mpr ⟨0, by simp, by simp [v]⟩
      · exact Finset.mem_image.mpr ⟨1, by simp, by simp [v]⟩
      · exact Finset.mem_image.mpr ⟨2, by simp, by simp [v]⟩
  refine ⟨by norm_num, v, hv, E, hE, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [E, hAH, hCH, hBH]
  · intro i
    fin_cases i
    · change A ∩ Finset.univ.image v = {d, p}
      rw [hv_image]
      ext x
      simp [hdA, hpA, hqA]
    · change C ∩ Finset.univ.image v = {p, q}
      rw [hv_image]
      ext x
      simp [hdC, hpC, hqC]
    · change B ∩ Finset.univ.image v = {q, d}
      rw [Finset.pair_comm q d, hv_image]
      ext x
      simp [hdB, hpB, hqB]

/-- Lemma 4.3 (isolation of an unequal incidence).  Choose an unequal-label pair
    whose union has least cardinality; a third edge would either give a strong
    triangle or allow that union to be shrunk. -/
theorem lem43_isolation_of_nonconstant
    {H : Set (Finset σ)} {z : σ}
    (hcl : IsClutter H) (htri : ¬ HasStrongTriangle H)
    (lab : lem43_facetsThrough H z → Λ)
    (hnc : ∃ A B, lab A ≠ lab B) :
    ∃ A B : lem43_facetsThrough H z, lab A ≠ lab B ∧
      {E : Finset σ | E ∈ H ∧ E ⊆ A.1 ∪ B.1} = {A.1, B.1} := by
  classical
  let good : ℕ → Prop := fun n ↦ ∃ A B : lem43_facetsThrough H z,
    lab A ≠ lab B ∧ (A.1 ∪ B.1).card = n
  rcases hnc with ⟨A₀, B₀, h₀⟩
  have hgood : ∃ n, good n :=
    ⟨(A₀.1 ∪ B₀.1).card, A₀, B₀, h₀, rfl⟩
  have hspec : good (Nat.find hgood) := Nat.find_spec hgood
  rcases hspec with ⟨A, B, hAB, hcard⟩
  have hmin : ∀ X Y : lem43_facetsThrough H z, lab X ≠ lab Y →
      (A.1 ∪ B.1).card ≤ (X.1 ∪ Y.1).card := by
    intro X Y hXY
    have hle : Nat.find hgood ≤ (X.1 ∪ Y.1).card :=
      Nat.find_min' hgood ⟨X, Y, hXY, rfl⟩
    simpa [← hcard] using hle
  have hAH : A.1 ∈ H := A.2.1
  have hBH : B.1 ∈ H := B.2.1
  have hABne : A.1 ≠ B.1 := by
    intro h
    apply hAB
    exact congrArg lab (Subtype.ext h)
  have hnoThird : ∀ C : Finset σ, C ∈ H → C ⊆ A.1 ∪ B.1 → C = A.1 ∨ C = B.1 := by
    intro C hCH hCsub
    by_cases hCA : C = A.1
    · exact Or.inl hCA
    · by_cases hCB : C = B.1
      · exact Or.inr hCB
      · exfalso
        have hCnotSubB : ¬ C ⊆ B.1 := by
          intro hsub
          exact hCB (hcl C hCH B.1 hBH hsub)
        rcases Finset.not_subset.mp hCnotSubB with ⟨p, hpC, hpB⟩
        have hpA : p ∈ A.1 := by
          rcases Finset.mem_union.mp (hCsub hpC) with hpA | hpB'
          · exact hpA
          · exact (hpB hpB').elim
        have hCnotSubA : ¬ C ⊆ A.1 := by
          intro hsub
          exact hCA (hcl C hCH A.1 hAH hsub)
        rcases Finset.not_subset.mp hCnotSubA with ⟨q, hqC, hqA⟩
        have hqB : q ∈ B.1 := by
          rcases Finset.mem_union.mp (hCsub hqC) with hqA' | hqB
          · exact (hqA hqA').elim
          · exact hqB
        have hDsub : A.1 ∩ B.1 ⊆ C := by
          intro d hdD
          have hdA : d ∈ A.1 := (Finset.mem_inter.mp hdD).1
          have hdB : d ∈ B.1 := (Finset.mem_inter.mp hdD).2
          by_contra hdC
          apply htri
          exact lem43_strongTriangle_of_third
            (hAH := hAH) (hCH := hCH) (hBH := hBH)
            (hdA := hdA) (hdB := hdB) (hdC := hdC)
            (hpA := hpA) (hpB := hpB) (hpC := hpC)
            (hqA := hqA) (hqB := hqB) (hqC := hqC)
            (hAC := Ne.symm hCA) (hCB := hCB) (hAB := hABne)
        have hzC : z ∈ C := hDsub (Finset.mem_inter.mpr ⟨A.2.2, B.2.2⟩)
        let Cz : lem43_facetsThrough H z := ⟨C, hCH, hzC⟩
        have hAnotSubC : ¬ A.1 ⊆ C := by
          intro hsub
          exact hCA (hcl A.1 hAH C hCH hsub).symm
        rcases Finset.not_subset.mp hAnotSubC with ⟨a, haA, haC⟩
        have haB : a ∉ B.1 := by
          intro haB
          exact haC (hDsub (Finset.mem_inter.mpr ⟨haA, haB⟩))
        have hBnotSubC : ¬ B.1 ⊆ C := by
          intro hsub
          exact hCB (hcl B.1 hBH C hCH hsub).symm
        rcases Finset.not_subset.mp hBnotSubC with ⟨b, hbB, hbC⟩
        have hbA : b ∉ A.1 := by
          intro hbA
          exact hbC (hDsub (Finset.mem_inter.mpr ⟨hbA, hbB⟩))
        have hACsub : A.1 ∪ C ⊆ A.1 ∪ B.1 := by
          intro x hx
          rcases Finset.mem_union.mp hx with hxA | hxC
          · exact Finset.mem_union.mpr (Or.inl hxA)
          · exact hCsub hxC
        have hACssub : A.1 ∪ C ⊂ A.1 ∪ B.1 :=
          (Finset.ssubset_iff_of_subset hACsub).2
            ⟨b, Finset.mem_union.mpr (Or.inr hbB), by
              intro hb
              rcases Finset.mem_union.mp hb with hbA' | hbC'
              · exact hbA hbA'
              · exact hbC hbC'⟩
        have hBCsub : B.1 ∪ C ⊆ A.1 ∪ B.1 := by
          intro x hx
          rcases Finset.mem_union.mp hx with hxB | hxC
          · exact Finset.mem_union.mpr (Or.inr hxB)
          · exact hCsub hxC
        have hBCssub : B.1 ∪ C ⊂ A.1 ∪ B.1 :=
          (Finset.ssubset_iff_of_subset hBCsub).2
            ⟨a, Finset.mem_union.mpr (Or.inl haA), by
              intro ha
              rcases Finset.mem_union.mp ha with haB' | haC'
              · exact haB haB'
              · exact haC haC'⟩
        have hcardAC : (A.1 ∪ C).card < (A.1 ∪ B.1).card :=
          Finset.card_lt_card hACssub
        have hcardBC : (B.1 ∪ C).card < (A.1 ∪ B.1).card :=
          Finset.card_lt_card hBCssub
        have hlabAC : lab A = lab Cz := by
          by_contra hne
          have hle := hmin A Cz hne
          exact (Nat.not_lt_of_ge hle) (by simpa [Cz] using hcardAC)
        have hlabBC : lab B = lab Cz := by
          by_contra hne
          have hle := hmin B Cz hne
          exact (Nat.not_lt_of_ge hle) (by simpa [Cz] using hcardBC)
        exact hAB (hlabAC.trans hlabBC.symm)
  refine ⟨A, B, hAB, ?_⟩
  ext C
  constructor
  · intro hC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hnoThird C hC.1 hC.2
  · intro hC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
    rcases hC with rfl | rfl
    · exact ⟨hAH, Finset.subset_union_left⟩
    · exact ⟨hBH, Finset.subset_union_right⟩

end SimisFormal
