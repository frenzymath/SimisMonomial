/-
Example 6.3: four disjoint blocks of cardinalities \(3,2,2,2\), with every
diagonal weight equal to two.

The file deliberately avoids importing the concurrent formalization of
Proposition 6.2.  It uses the monomial API in `SimisFormal` and the stable
standard-symbolic-power helper `Eq2_StandardSymbolic`.
-/
import SimisFormal.Defs
import SimisFormal.Basic
import SimisFormal.Eq2_StandardSymbolic
import SimisFormal.Thm5_2

open MvPolynomial
open SimisFormal
open scoped BigOperators
abbrev ex63_v1 : ex63_var := ex63_in1 (1 : Fin 3)
abbrev ex63_w1 : ex63_var := ex63_in1 (2 : Fin 3)
abbrev ex63_v2 : ex63_var := ex63_in2 (1 : Fin 2)
abbrev ex63_v3 : ex63_var := ex63_in3 (1 : Fin 2)
abbrev ex63_u4 : ex63_var := ex63_in4 (0 : Fin 2)
abbrev ex63_v4 : ex63_var := ex63_in4 (1 : Fin 2)

/-- The displayed selection with all four indices zero. -/
abbrev ex63_choice0 : ex63_choice := (0, 0, 0, 0)

/-- Recover the chosen variable from a block index. -/
def ex63_chosen (c : ex63_choice) (j : Fin 4) : ex63_var :=
  match j.val with
  | 0 => ex63_in1 c.1
  | 1 => ex63_in2 c.2.1
  | 2 => ex63_in3 c.2.2.1
  | _ => ex63_in4 c.2.2.2

variable {K : Type*} [Field K]
@[simp] theorem ex63_transExpWeight_at_B1 (w : ℕ) (c : ex63_choice) (x : Fin 3) :
    ex63_transExpWeight w c (ex63_in1 x) = if x = c.1 then w else 0 := by
  simp [ex63_transExpWeight, Finsupp.single_apply, ex63_in1, ex63_in2, ex63_in3,
    ex63_in4, eq_comm]

@[simp] theorem ex63_transExpWeight_at_B2 (w : ℕ) (c : ex63_choice) (x : Fin 2) :
    ex63_transExpWeight w c (ex63_in2 x) = if x = c.2.1 then w else 0 := by
  simp [ex63_transExpWeight, Finsupp.single_apply, ex63_in1, ex63_in2, ex63_in3,
    ex63_in4, eq_comm]

@[simp] theorem ex63_transExpWeight_at_B3 (w : ℕ) (c : ex63_choice) (x : Fin 2) :
    ex63_transExpWeight w c (ex63_in3 x) = if x = c.2.2.1 then w else 0 := by
  simp [ex63_transExpWeight, Finsupp.single_apply, ex63_in1, ex63_in2, ex63_in3,
    ex63_in4, eq_comm]

@[simp] theorem ex63_transExpWeight_at_B4 (w : ℕ) (c : ex63_choice) (x : Fin 2) :
    ex63_transExpWeight w c (ex63_in4 x) = if x = c.2.2.2 then w else 0 := by
  simp [ex63_transExpWeight, Finsupp.single_apply, ex63_in1, ex63_in2, ex63_in3,
    ex63_in4, eq_comm]

@[simp] theorem ex63_transExpWeight_at_chosen (w : ℕ) (c : ex63_choice) (j : Fin 4) :
    ex63_transExpWeight w c (ex63_chosen c j) = w := by
  fin_cases j <;> simp [ex63_chosen]

@[simp] theorem ex63_chosen_mem_block (c : ex63_choice) (j : Fin 4) :
    ex63_chosen c j ∈ ex63_block j := by
  fin_cases j <;> simp [ex63_chosen, ex63_block, ex63_B1, ex63_B2, ex63_B3, ex63_B4]

theorem ex63_transExpWeight_le_iff (w : ℕ) (c : ex63_choice) (e : ex63_var →₀ ℕ) :
    ex63_transExpWeight w c ≤ e ↔
      w ≤ e (ex63_in1 c.1) ∧ w ≤ e (ex63_in2 c.2.1) ∧
        w ≤ e (ex63_in3 c.2.2.1) ∧ w ≤ e (ex63_in4 c.2.2.2) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h (ex63_in1 c.1)
    · simpa using h (ex63_in2 c.2.1)
    · simpa using h (ex63_in3 c.2.2.1)
    · simpa using h (ex63_in4 c.2.2.2)
  · rintro ⟨h1, h2, h3, h4⟩ z
    rcases z with (x1 | x2) | (x3 | x4)
    · change ex63_transExpWeight w c (ex63_in1 x1) ≤ e (ex63_in1 x1)
      by_cases hx : x1 = c.1
      · subst x1
        simpa using h1
      · simp [hx]
    · change ex63_transExpWeight w c (ex63_in2 x2) ≤ e (ex63_in2 x2)
      by_cases hx : x2 = c.2.1
      · subst x2
        simpa using h2
      · simp [hx]
    · change ex63_transExpWeight w c (ex63_in3 x3) ≤ e (ex63_in3 x3)
      by_cases hx : x3 = c.2.2.1
      · subst x3
        simpa using h3
      · simp [hx]
    · change ex63_transExpWeight w c (ex63_in4 x4) ≤ e (ex63_in4 x4)
      by_cases hx : x4 = c.2.2.2
      · subst x4
        simpa using h4
      · simp [hx]

theorem ex63_transExpWeight_injective (w : ℕ) (hw : w ≠ 0) :
    Function.Injective (ex63_transExpWeight w) := by
  intro c d hcd
  have h1 : c.1 = d.1 := by
    by_contra hne
    have hv := DFunLike.congr_fun hcd (ex63_in1 c.1)
    have hw0 : w = 0 := by
      simpa [hne, eq_comm] using hv
    exact hw hw0
  have h2 : c.2.1 = d.2.1 := by
    by_contra hne
    have hv := DFunLike.congr_fun hcd (ex63_in2 c.2.1)
    have hw0 : w = 0 := by
      simpa [hne, eq_comm] using hv
    exact hw hw0
  have h3 : c.2.2.1 = d.2.2.1 := by
    by_contra hne
    have hv := DFunLike.congr_fun hcd (ex63_in3 c.2.2.1)
    have hw0 : w = 0 := by
      simpa [hne, eq_comm] using hv
    exact hw hw0
  have h4 : c.2.2.2 = d.2.2.2 := by
    by_contra hne
    have hv := DFunLike.congr_fun hcd (ex63_in4 c.2.2.2)
    have hw0 : w = 0 := by
      simpa [hne, eq_comm] using hv
    exact hw hw0
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))

theorem ex63_transExpWeight_antichain (w : ℕ) (hw : 0 < w)
    {c d : ex63_choice} (hcd : ex63_transExpWeight w c ≤ ex63_transExpWeight w d) :
    c = d := by
  have h1 : c.1 = d.1 := by
    by_contra hne
    have hv := hcd (ex63_in1 c.1)
    have hw0 : w ≤ 0 := by
      simpa [hne, eq_comm] using hv
    exact (not_le_of_gt hw) hw0
  have h2 : c.2.1 = d.2.1 := by
    by_contra hne
    have hv := hcd (ex63_in2 c.2.1)
    have hw0 : w ≤ 0 := by
      simpa [hne, eq_comm] using hv
    exact (not_le_of_gt hw) hw0
  have h3 : c.2.2.1 = d.2.2.1 := by
    by_contra hne
    have hv := hcd (ex63_in3 c.2.2.1)
    have hw0 : w ≤ 0 := by
      simpa [hne, eq_comm] using hv
    exact (not_le_of_gt hw) hw0
  have h4 : c.2.2.2 = d.2.2.2 := by
    by_contra hne
    have hv := hcd (ex63_in4 c.2.2.2)
    have hw0 : w ≤ 0 := by
      simpa [hne, eq_comm] using hv
    exact (not_le_of_gt hw) hw0
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))

theorem ex63_transExpWeight_support (w : ℕ) (hw : w ≠ 0) (c : ex63_choice) :
    (ex63_transExpWeight w c).support = ex63_facet c := by
  ext z
  rcases z with (x1 | x2) | (x3 | x4)
  · rw [Finsupp.mem_support_iff]
    change ex63_transExpWeight w c (ex63_in1 x1) ≠ 0 ↔ ex63_in1 x1 ∈ ex63_facet c
    rw [ex63_transExpWeight_at_B1]
    split_ifs with hx
    · subst x1
      simp [ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4, hw]
    · simp [ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4, hx]
  · rw [Finsupp.mem_support_iff]
    change ex63_transExpWeight w c (ex63_in2 x2) ≠ 0 ↔ ex63_in2 x2 ∈ ex63_facet c
    rw [ex63_transExpWeight_at_B2]
    split_ifs with hx
    · subst x2
      simp [ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4, hw]
    · simp [ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4, hx]
  · rw [Finsupp.mem_support_iff]
    change ex63_transExpWeight w c (ex63_in3 x3) ≠ 0 ↔ ex63_in3 x3 ∈ ex63_facet c
    rw [ex63_transExpWeight_at_B3]
    split_ifs with hx
    · subst x3
      simp [ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4, hw]
    · simp [ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4, hx]
  · rw [Finsupp.mem_support_iff]
    change ex63_transExpWeight w c (ex63_in4 x4) ≠ 0 ↔ ex63_in4 x4 ∈ ex63_facet c
    rw [ex63_transExpWeight_at_B4]
    split_ifs with hx
    · subst x4
      simp [ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4, hw]
    · simp [ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4, hx]

/-- Expanding the displayed product gives exactly the transversal products. -/
theorem ex63_blockProduct_eq_monomialIdeal (w : ℕ) :
    ex63_blockProduct (K := K) w =
      monomialIdeal (K := K) (Set.range (ex63_transExpWeight w)) := by
  classical
  unfold ex63_blockProduct purePower
  rw [monomialIdeal_mul, monomialIdeal_mul, monomialIdeal_mul]
  congr 1
  ext z
  constructor
  · rintro ⟨u123, hu123, s4, hs4, rfl⟩
    rcases hu123 with ⟨u12, hu12, s3, hs3, rfl⟩
    rcases hu12 with ⟨s1, hs1, s2, hs2, rfl⟩
    rcases hs1 with ⟨i1, hi1, rfl⟩
    rcases hs2 with ⟨i2, hi2, rfl⟩
    rcases hs3 with ⟨i3, hi3, rfl⟩
    rcases hs4 with ⟨i4, hi4, rfl⟩
    rcases Finset.mem_image.mp hi1 with ⟨a, -, ha1⟩
    rcases Finset.mem_image.mp hi2 with ⟨b, -, hb2⟩
    rcases Finset.mem_image.mp hi3 with ⟨c, -, hc3⟩
    rcases Finset.mem_image.mp hi4 with ⟨d, -, hd4⟩
    refine ⟨(a, b, c, d), ?_⟩
    simp [ex63_transExpWeight, ha1, hb2, hc3, hd4]
  · rintro ⟨c, rfl⟩
    refine ⟨_, ?_, Finsupp.single (ex63_in4 c.2.2.2) w, ?_, rfl⟩
    · refine ⟨_, ?_, Finsupp.single (ex63_in3 c.2.2.1) w, ?_, rfl⟩
      · refine ⟨Finsupp.single (ex63_in1 c.1) w, ?_,
            Finsupp.single (ex63_in2 c.2.1) w, ?_, rfl⟩
        · exact ⟨ex63_in1 c.1, by simp [ex63_B1], rfl⟩
        · exact ⟨ex63_in2 c.2.1, by simp [ex63_B2], rfl⟩
      · exact ⟨ex63_in3 c.2.2.1, by simp [ex63_B3], rfl⟩
    · exact ⟨ex63_in4 c.2.2.2, by simp [ex63_B4], rfl⟩

/-- The root is generated by the squarefree transversals. -/
theorem ex63_J_eq_monomialIdeal :
    ex63_J (K := K) =
      monomialIdeal (K := K) (Set.range (ex63_transExpWeight 1)) := by
  simpa [ex63_J, ex63_blockProduct, primeOf] using
    (ex63_blockProduct_eq_monomialIdeal (K := K) 1)

theorem ex63_diagExp_transExp (c : ex63_choice) :
    diagExp ex63_weight (ex63_transExpWeight 1 c) = ex63_transExpWeight 2 c := by
  ext z
  rcases z with (x1 | x2) | (x3 | x4)
  · change diagExp ex63_weight (ex63_transExpWeight 1 c) (ex63_in1 x1) =
        ex63_transExpWeight 2 c (ex63_in1 x1)
    simp [diagExp_apply, ex63_weight]
  · change diagExp ex63_weight (ex63_transExpWeight 1 c) (ex63_in2 x2) =
        ex63_transExpWeight 2 c (ex63_in2 x2)
    simp [diagExp_apply, ex63_weight]
  · change diagExp ex63_weight (ex63_transExpWeight 1 c) (ex63_in3 x3) =
        ex63_transExpWeight 2 c (ex63_in3 x3)
    simp [diagExp_apply, ex63_weight]
  · change diagExp ex63_weight (ex63_transExpWeight 1 c) (ex63_in4 x4) =
        ex63_transExpWeight 2 c (ex63_in4 x4)
    simp [diagExp_apply, ex63_weight]

/-- The diagonal image is generated by the transversals with exponent two. -/
theorem ex63_I_eq_monomialIdeal :
    ex63_I (K := K) =
      monomialIdeal (K := K) (Set.range (ex63_transExpWeight 2)) := by
  classical
  rw [ex63_I, ex63_J_eq_monomialIdeal, diagonal_monomialIdeal]
  congr 1
  ext e
  constructor
  · rintro ⟨u, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, (ex63_diagExp_transExp c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨ex63_transExpWeight 1 c, ⟨c, rfl⟩, ex63_diagExp_transExp c⟩

/-- The displayed product formula for \(I_a\). -/
theorem ex63_I_eq_blockProduct : ex63_I (K := K) = ex63_blockProduct (K := K) 2 :=
  ex63_I_eq_monomialIdeal.trans (ex63_blockProduct_eq_monomialIdeal (K := K) 2).symm

/-- An antichain of exponent vectors is precisely its ideal's minimal generating set. -/
theorem ex63_minGens_monomialIdeal_of_antichain (S : Set (ex63_var →₀ ℕ))
    (hanti : ∀ a ∈ S, ∀ b ∈ S, a ≤ b → a = b) :
    minGens (K := K) (monomialIdeal (K := K) S) = S := by
  ext e
  rw [mem_minGens]
  constructor
  · rintro ⟨he, hmin⟩
    rcases monomial_mem_monomialIdeal.mp he with ⟨u, huS, hue⟩
    have hueq := hmin u (monomial_mem_monomialIdeal.mpr ⟨u, huS, le_rfl⟩) hue
    simpa [hueq] using huS
  · intro heS
    refine ⟨monomial_mem_monomialIdeal.mpr ⟨e, heS, le_rfl⟩, ?_⟩
    intro u huI hue
    rcases monomial_mem_monomialIdeal.mp huI with ⟨v, hvS, hvu⟩
    have hveq := hanti v hvS e heS (le_trans hvu hue)
    exact le_antisymm hue (by simpa [hveq] using hvu)

theorem ex63_minGens_weightIdeal (w : ℕ) (hw : w ≠ 0) :
    minGens (K := K) (monomialIdeal (K := K) (Set.range (ex63_transExpWeight w))) =
      Set.range (ex63_transExpWeight w) := by
  apply ex63_minGens_monomialIdeal_of_antichain
  rintro a ⟨c, rfl⟩ b ⟨d, rfl⟩ hab
  exact congrArg (ex63_transExpWeight w)
    (ex63_transExpWeight_antichain w (Nat.pos_of_ne_zero hw) hab)

/-- The 24 minimal generators of \(J\). -/
theorem ex63_minGens_J :
    minGens (K := K) (ex63_J (K := K)) =
      (ex63_transversalGens 1 : Set (ex63_var →₀ ℕ)) := by
  calc
    minGens (K := K) (ex63_J (K := K)) = Set.range (ex63_transExpWeight 1) := by
      rw [ex63_J_eq_monomialIdeal]
      exact ex63_minGens_weightIdeal (K := K) 1 (by decide)
    _ = (ex63_transversalGens 1 : Set (ex63_var →₀ ℕ)) := by
      ext e
      simp [ex63_transversalGens]

/-- The 24 minimal generators of \(I_a\). -/
theorem ex63_minGens_I :
    minGens (K := K) (ex63_I (K := K)) =
      (ex63_transversalGens 2 : Set (ex63_var →₀ ℕ)) := by
  calc
    minGens (K := K) (ex63_I (K := K)) = Set.range (ex63_transExpWeight 2) := by
      rw [ex63_I_eq_monomialIdeal]
      exact ex63_minGens_weightIdeal (K := K) 2 (by decide)
    _ = (ex63_transversalGens 2 : Set (ex63_var →₀ ℕ)) := by
      ext e
      simp [ex63_transversalGens]

/-- Every nonzero uniform weighting gives 24 distinct transversals. -/
theorem ex63_transversalGens_card (w : ℕ) (hw : w ≠ 0) :
    (ex63_transversalGens w).card = 24 := by
  calc
    (ex63_transversalGens w).card =
        (Finset.univ : Finset ex63_choice).card := by
      rw [ex63_transversalGens]
      exact Finset.card_image_of_injective _
        (ex63_transExpWeight_injective w hw)
    _ = 24 := by decide

theorem ex63_minGens_J_ncard : (minGens (K := K) (ex63_J (K := K))).ncard = 24 := by
  rw [ex63_minGens_J]
  exact Set.ncard_coe_finset _ |>.trans (ex63_transversalGens_card 1 (by decide))

theorem ex63_minGens_I_ncard : (minGens (K := K) (ex63_I (K := K))).ncard = 24 := by
  rw [ex63_minGens_I]
  exact Set.ncard_coe_finset _ |>.trans (ex63_transversalGens_card 2 (by decide))

/-- The intersection of the four displayed pure-power components. -/
theorem ex63_intersection_eq_monomialIdeal (w : ℕ) :
    (⨅ j : Fin 4,
        (purePower (K := K) (ex63_block j) (fun _ => w) : Ideal (MvPolynomial ex63_var K))) =
      monomialIdeal (K := K) (Set.range (ex63_transExpWeight w)) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image]
    intro e he
    have threshold (j : Fin 4) : ∃ i ∈ ex63_block j, w ≤ e i := by
      have hxj := (Ideal.mem_iInf.mp hx j)
      rw [purePower, monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image] at hxj
      rcases hxj e he with ⟨u, ⟨i, hi, rfl⟩, hue⟩
      exact ⟨i, hi, Finsupp.single_le_iff.mp hue⟩
    rcases threshold 0 with ⟨i1, hi1, hle1⟩
    rcases threshold 1 with ⟨i2, hi2, hle2⟩
    rcases threshold 2 with ⟨i3, hi3, hle3⟩
    rcases threshold 3 with ⟨i4, hi4, hle4⟩
    have hi1' : i1 ∈ ex63_B1 := by simpa [ex63_block] using hi1
    have hi2' : i2 ∈ ex63_B2 := by simpa [ex63_block] using hi2
    have hi3' : i3 ∈ ex63_B3 := by simpa [ex63_block] using hi3
    have hi4' : i4 ∈ ex63_B4 := by simpa [ex63_block] using hi4
    rcases Finset.mem_image.mp hi1' with ⟨a, -, ha1⟩
    rcases Finset.mem_image.mp hi2' with ⟨b, -, hb2⟩
    rcases Finset.mem_image.mp hi3' with ⟨c, -, hc3⟩
    rcases Finset.mem_image.mp hi4' with ⟨d, -, hd4⟩
    refine ⟨ex63_transExpWeight w (a, b, c, d), ⟨(a, b, c, d), rfl⟩, ?_⟩
    exact (ex63_transExpWeight_le_iff w (a, b, c, d) e).2
      ⟨by simpa [ha1] using hle1, by simpa [hb2] using hle2,
        by simpa [hc3] using hle3, by simpa [hd4] using hle4⟩
  · intro x hx
    rw [Ideal.mem_iInf]
    intro j
    rw [monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image] at hx
    rw [purePower, monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image]
    intro z hz
    rcases hx z hz with ⟨u, ⟨c, rfl⟩, hue⟩
    refine ⟨Finsupp.single (ex63_chosen c j) w,
      ⟨ex63_chosen c j, ex63_chosen_mem_block c j, rfl⟩, ?_⟩
    exact Finsupp.single_le_iff.mpr (by simpa using hue (ex63_chosen c j))

theorem ex63_hasComponents_weightIdeal (w : ℕ) :
    HasComponents (monomialIdeal (K := K) (Set.range (ex63_transExpWeight w)))
      ex63_block (fun _ _ => w) := by
  rw [HasComponents]
  exact (ex63_intersection_eq_monomialIdeal (K := K) w).symm

theorem ex63_hasComponents_J :
    HasComponents (ex63_J (K := K)) ex63_block (fun _ _ => 1) := by
  rw [HasComponents, ex63_J_eq_monomialIdeal]
  exact (ex63_intersection_eq_monomialIdeal (K := K) 1).symm

theorem ex63_hasComponents_I :
    HasComponents (ex63_I (K := K)) ex63_block (fun _ _ => 2) := by
  rw [HasComponents, ex63_I_eq_monomialIdeal]
  exact (ex63_intersection_eq_monomialIdeal (K := K) 2).symm

theorem ex63_supportComplex_weightIdeal (w : ℕ) (hw : w ≠ 0) :
    supportComplex (monomialIdeal (K := K) (Set.range (ex63_transExpWeight w))) =
      (ex63_facets : Set (Finset ex63_var)) := by
  ext F
  change (∃ e ∈ minGens (K := K)
      (monomialIdeal (K := K) (Set.range (ex63_transExpWeight w))), e.support = F) ↔
    F ∈ (ex63_facets : Set (Finset ex63_var))
  constructor
  · rintro ⟨e, he, hF⟩
    rw [ex63_minGens_weightIdeal (K := K) w hw] at he
    rcases he with ⟨c, rfl⟩
    rw [← hF, ex63_transExpWeight_support w hw]
    exact Finset.mem_image.mpr ⟨c, by simp, rfl⟩
  · intro hF
    rcases Finset.mem_image.mp hF with ⟨c, -, hcF⟩
    refine ⟨ex63_transExpWeight w c, ?_, ?_⟩
    · rw [ex63_minGens_weightIdeal (K := K) w hw]
      exact ⟨c, rfl⟩
    · exact (ex63_transExpWeight_support w hw c).trans hcF

theorem ex63_supportComplex_J :
    supportComplex (ex63_J (K := K)) = (ex63_facets : Set (Finset ex63_var)) := by
  rw [ex63_J_eq_monomialIdeal]
  exact ex63_supportComplex_weightIdeal (K := K) 1 (by decide)

theorem ex63_supportComplex_I :
    supportComplex (ex63_I (K := K)) = (ex63_facets : Set (Finset ex63_var)) := by
  rw [ex63_I_eq_monomialIdeal]
  exact ex63_supportComplex_weightIdeal (K := K) 2 (by decide)

theorem ex63_triangleVertices_injective : Function.Injective ex63_triangleVertices := by
  decide

theorem ex63_triangleEdges_injective : Function.Injective ex63_triangleEdges := by
  decide

theorem ex63_triangleEdges_mem_facets (i : Fin 3) :
    ex63_triangleEdges i ∈ (ex63_facets : Set (Finset ex63_var)) := by
  fin_cases i <;> simp [ex63_triangleEdges, ex63_facets]

theorem ex63_triangle_incidence (i : Fin 3) :
    ex63_triangleEdges i ∩ (Finset.univ.image ex63_triangleVertices) =
      {ex63_triangleVertices i, ex63_triangleVertices (finSuccMod i)} := by
  fin_cases i <;> decide

theorem ex63_strongTriangle_facets :
    HasStrongTriangle (ex63_facets : Set (Finset ex63_var)) := by
  rw [HasStrongTriangle, HasStrongCycle]
  refine ⟨by decide, ex63_triangleVertices, ex63_triangleVertices_injective,
    ex63_triangleEdges, ex63_triangleEdges_injective, ?_, ?_⟩
  · exact ex63_triangleEdges_mem_facets
  · exact ex63_triangle_incidence

theorem ex63_strongTriangle_J : HasStrongTriangle (supportComplex (ex63_J (K := K))) := by
  rw [ex63_supportComplex_J]
  exact ex63_strongTriangle_facets

theorem ex63_strongTriangle_I : HasStrongTriangle (supportComplex (ex63_I (K := K))) := by
  rw [ex63_supportComplex_I]
  exact ex63_strongTriangle_facets

/-- Fixed-point-free successor in the three-element block. -/
def ex63_other3 (i : Fin 3) : Fin 3 :=
  match i.val with
  | 0 => 1
  | 1 => 2
  | _ => 0

/-- Fixed-point-free successor in a two-element block. -/
def ex63_other2 (i : Fin 2) : Fin 2 :=
  match i.val with
  | 0 => 1
  | _ => 0

theorem ex63_other3_ne (i : Fin 3) : ex63_other3 i ≠ i := by
  fin_cases i <;> decide

theorem ex63_other2_ne (i : Fin 2) : ex63_other2 i ≠ i := by
  fin_cases i <;> decide

/-- Change the selected variable in block `j` and leave the other blocks fixed. -/
def ex63_alter (c : ex63_choice) (j : Fin 4) : ex63_choice :=
  match j.val with
  | 0 => (ex63_other3 c.1, c.2.1, c.2.2.1, c.2.2.2)
  | 1 => (c.1, ex63_other2 c.2.1, c.2.2.1, c.2.2.2)
  | 2 => (c.1, c.2.1, ex63_other2 c.2.2.1, c.2.2.2)
  | _ => (c.1, c.2.1, c.2.2.1, ex63_other2 c.2.2.2)

theorem ex63_alter_ne (c : ex63_choice) (j : Fin 4) : ex63_alter c j ≠ c := by
  fin_cases j
  · intro h
    exact ex63_other3_ne c.1 (by simpa [ex63_alter] using congrArg Prod.fst h)
  · intro h
    exact ex63_other2_ne c.2.1
      (by simpa [ex63_alter] using congrArg (fun p : ex63_choice => p.2.1) h)
  · intro h
    exact ex63_other2_ne c.2.2.1
      (by simpa [ex63_alter] using congrArg (fun p : ex63_choice => p.2.2.1) h)
  · intro h
    exact ex63_other2_ne c.2.2.2
      (by simpa [ex63_alter] using congrArg (fun p : ex63_choice => p.2.2.2) h)

@[simp] theorem ex63_chosen_mem_facet (c : ex63_choice) (j : Fin 4) :
    ex63_chosen c j ∈ ex63_facet c := by
  fin_cases j <;> simp [ex63_chosen, ex63_facet]

theorem ex63_chosen_not_mem_alterFacet (c : ex63_choice) (j : Fin 4) :
    ex63_chosen c j ∉ ex63_facet (ex63_alter c j) := by
  fin_cases j
  · simpa [ex63_chosen, ex63_alter, ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4] using
      Ne.symm (ex63_other3_ne c.1)
  · simpa [ex63_chosen, ex63_alter, ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4] using
      Ne.symm (ex63_other2_ne c.2.1)
  · simpa [ex63_chosen, ex63_alter, ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4] using
      Ne.symm (ex63_other2_ne c.2.2.1)
  · simpa [ex63_chosen, ex63_alter, ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4] using
      Ne.symm (ex63_other2_ne c.2.2.2)

theorem ex63_chosen_mem_alterFacet (c : ex63_choice) {j k : Fin 4} (hjk : j ≠ k) :
    ex63_chosen c j ∈ ex63_facet (ex63_alter c k) := by
  fin_cases j <;> fin_cases k <;>
    simp [ex63_chosen, ex63_alter, ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4] at hjk ⊢

theorem ex63_alterFacet_ne (c : ex63_choice) (j : Fin 4) :
    ex63_facet (ex63_alter c j) ≠ ex63_facet c := by
  intro h
  exact ex63_chosen_not_mem_alterFacet c j
    (by simpa [← h] using ex63_chosen_mem_facet c j)

theorem ex63_chosen_not_mem_facet_of_ne {c d : ex63_choice} {j : Fin 4}
    (h : ex63_chosen c j ≠ ex63_chosen d j) : ex63_chosen c j ∉ ex63_facet d := by
  fin_cases j <;>
    simp [ex63_chosen, ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4] at h ⊢ <;>
    assumption

/-- The paper's alteration argument: a facet different from `F` cannot be a joint. -/
theorem ex63_not_joint (c d : ex63_choice) (j k : Fin 4) (hjk : j ≠ k)
    (hdiff : ex63_chosen c j ≠ ex63_chosen d j) :
    ¬ (∀ H' ∈ (ex63_facets : Set (Finset ex63_var)), H' ≠ ex63_facet c →
        H' ∩ ex63_facet c ⊆ ex63_facet c ∩ ex63_facet d) := by
  intro hjoint
  have hH : ex63_facet (ex63_alter c k) ∈ (ex63_facets : Set (Finset ex63_var)) :=
    Finset.mem_image.mpr ⟨ex63_alter c k, by simp, rfl⟩
  have hsub := hjoint _ hH (ex63_alterFacet_ne c k)
  have hx : ex63_chosen c j ∈ ex63_facet (ex63_alter c k) ∩ ex63_facet c :=
    Finset.mem_inter.mpr ⟨ex63_chosen_mem_alterFacet c hjk, ex63_chosen_mem_facet c j⟩
  exact ex63_chosen_not_mem_facet_of_ne hdiff ((Finset.mem_inter.mp (hsub hx)).2)

theorem ex63_noLeaves_facets :
    ∀ F ∈ (ex63_facets : Set (Finset ex63_var)),
      ¬ IsLeaf (ex63_facets : Set (Finset ex63_var)) F := by
  intro F hF
  rcases Finset.mem_image.mp hF with ⟨c, -, rfl⟩
  intro hleaf
  rcases hleaf.2 with hOnly | hJoint
  · have hH : ex63_facet (ex63_alter c 0) ∈ (ex63_facets : Set (Finset ex63_var)) :=
      Finset.mem_image.mpr ⟨ex63_alter c 0, by simp, rfl⟩
    exact (ex63_alterFacet_ne c 0) (hOnly _ hH)
  · rcases hJoint with ⟨G, hG, hGF, hj⟩
    rcases Finset.mem_image.mp hG with ⟨d, -, hGd⟩
    subst G
    by_cases hd1 : d.1 = c.1
    · by_cases hd2 : d.2.1 = c.2.1
      · by_cases hd3 : d.2.2.1 = c.2.2.1
        · by_cases hd4 : d.2.2.2 = c.2.2.2
          · exact hGF (congrArg ex63_facet
              (Prod.ext hd1 (Prod.ext hd2 (Prod.ext hd3 hd4))))
          · apply ex63_not_joint c d (3 : Fin 4) (0 : Fin 4) (by decide)
            · simpa [ex63_chosen, ex63_in1, ex63_in2, ex63_in3, ex63_in4] using Ne.symm hd4
            · exact hj
        · apply ex63_not_joint c d (2 : Fin 4) (0 : Fin 4) (by decide)
          · simpa [ex63_chosen, ex63_in1, ex63_in2, ex63_in3, ex63_in4] using Ne.symm hd3
          · exact hj
      · apply ex63_not_joint c d (1 : Fin 4) (0 : Fin 4) (by decide)
        · simpa [ex63_chosen, ex63_in1, ex63_in2, ex63_in3, ex63_in4] using Ne.symm hd2
        · exact hj
    · apply ex63_not_joint c d (0 : Fin 4) (1 : Fin 4) (by decide)
      · simpa [ex63_chosen, ex63_in1, ex63_in2, ex63_in3, ex63_in4] using Ne.symm hd1
      · exact hj

theorem ex63_noLeaves_J :
    ∀ F ∈ supportComplex (ex63_J (K := K)), ¬ IsLeaf (supportComplex (ex63_J (K := K))) F := by
  rw [ex63_supportComplex_J]
  exact ex63_noLeaves_facets

theorem ex63_noLeaves_I :
    ∀ F ∈ supportComplex (ex63_I (K := K)), ¬ IsLeaf (supportComplex (ex63_I (K := K))) F := by
  rw [ex63_supportComplex_I]
  exact ex63_noLeaves_facets

theorem ex63_facets_nonempty : (ex63_facets : Set (Finset ex63_var)).Nonempty := by
  exact ⟨ex63_facet ex63_choice0,
    Finset.mem_image.mpr ⟨ex63_choice0, by simp, rfl⟩⟩

theorem ex63_notSimplicialForest_J :
    ¬ IsSimplicialForest (supportComplex (ex63_J (K := K))) := by
  intro hforest
  have hnonempty : (supportComplex (ex63_J (K := K))).Nonempty := by
    simpa [ex63_supportComplex_J] using ex63_facets_nonempty
  obtain ⟨F, hF, hleaf⟩ :=
    hforest (supportComplex (ex63_J (K := K))) (by intro G hG; exact hG) hnonempty
  exact ex63_noLeaves_J F hF hleaf

theorem ex63_notSimplicialForest_I :
    ¬ IsSimplicialForest (supportComplex (ex63_I (K := K))) := by
  intro hforest
  have hnonempty : (supportComplex (ex63_I (K := K))).Nonempty := by
    simpa [ex63_supportComplex_I] using ex63_facets_nonempty
  obtain ⟨F, hF, hleaf⟩ :=
    hforest (supportComplex (ex63_I (K := K))) (by intro G hG; exact hG) hnonempty
  exact ex63_noLeaves_I F hF hleaf

theorem ex63_notBalanced_J : ¬ IsBalanced (supportComplex (ex63_J (K := K))) := by
  intro hbal
  exact hbal 3 (by decide) ex63_strongTriangle_J

theorem ex63_notBalanced_I : ¬ IsBalanced (supportComplex (ex63_I (K := K))) := by
  intro hbal
  exact hbal 3 (by decide) ex63_strongTriangle_I

theorem ex63_facet0_card : (ex63_facet ex63_choice0).card = 4 := by
  decide

theorem ex63_facets_notAtMostThree :
    ¬ ∀ F ∈ (ex63_facets : Set (Finset ex63_var)), F.card ≤ 3 := by
  intro h
  have hF : ex63_facet ex63_choice0 ∈ (ex63_facets : Set (Finset ex63_var)) :=
    Finset.mem_image.mpr ⟨ex63_choice0, by simp, rfl⟩
  have hle := h _ hF
  have hcard := ex63_facet0_card
  omega

theorem ex63_notSupportAtMostThree_J :
    ¬ ∀ F ∈ supportComplex (ex63_J (K := K)), F.card ≤ 3 := by
  rw [ex63_supportComplex_J]
  exact ex63_facets_notAtMostThree

theorem ex63_notSupportAtMostThree_I :
    ¬ ∀ F ∈ supportComplex (ex63_I (K := K)), F.card ≤ 3 := by
  rw [ex63_supportComplex_I]
  exact ex63_facets_notAtMostThree

/-- The component supports, in the order displayed in Example 6.3. -/
theorem ex63_componentFacets_explicit :
    ex63_componentFacets = {ex63_B1, ex63_B2, ex63_B3, ex63_B4} := by
  decide

theorem ex63_componentHeights :
    (ex63_B1.card, ex63_B2.card, ex63_B3.card, ex63_B4.card) = (3, 2, 2, 2) := by
  decide

theorem ex63_notComponentHeightAtMostTwo :
    ¬ ∀ j : Fin 4, (ex63_block j).card ≤ 2 := by
  intro h
  have hle : ex63_B1.card ≤ 2 := by simpa [ex63_block] using h (0 : Fin 4)
  have hcard : ex63_B1.card = 3 :=
    congrArg (fun p : ℕ × ℕ × ℕ × ℕ => p.1) ex63_componentHeights
  omega

theorem ex63_XI_eq_empty : ex63_XI = ∅ := by
  ext p
  simp [ex63_XI, mismatchPairs]

theorem ex63_mismatchPairs_eq_empty :
    mismatchPairs ex63_block (fun _ _ => 2) = ∅ := by
  ext p
  simp [mismatchPairs]

theorem ex63_intervenors_empty (k l : Fin 4) : ex63_intervenors k l = ∅ := by
  fin_cases k <;> fin_cases l <;> decide

theorem ex63_atMostOneIntervenor :
    ∀ k l : Fin 4, (ex63_block k ∩ ex63_block l).Nonempty →
      (ex63_intervenors k l).card ≤ 1 := by
  intro k l _
  simp [ex63_intervenors_empty]

/-- Every transversal of Example 6.3 has support cardinality four. -/
theorem ex63_facet_card (c : ex63_choice) : (ex63_facet c).card = 4 := by
  rcases c with ⟨i1, i2, i3, i4⟩
  simp [ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4]

theorem ex63_facets_all_card_four :
    ∀ F ∈ (ex63_facets : Set (Finset ex63_var)), F.card = 4 := by
  intro F hF
  rcases Finset.mem_image.mp hF with ⟨c, -, rfl⟩
  exact ex63_facet_card c

theorem ex63_allSupportCards_J :
    ∀ F ∈ supportComplex (ex63_J (K := K)), F.card = 4 := by
  rw [ex63_supportComplex_J]
  exact ex63_facets_all_card_four

theorem ex63_allSupportCards_I :
    ∀ F ∈ supportComplex (ex63_I (K := K)), F.card = 4 := by
  rw [ex63_supportComplex_I]
  exact ex63_facets_all_card_four

/-- The actual height of the first variable-prime component. -/
theorem ex63_height_primeOf_B1 :
    (primeOf (K := K) ex63_B1 : Ideal (MvPolynomial ex63_var K)).height = (3 : ℕ∞) := by
  calc
    (primeOf (K := K) ex63_B1 : Ideal (MvPolynomial ex63_var K)).height =
        (ex63_B1.card : ℕ∞) := height_primeOf_eq_card (K := K) ex63_B1
    _ = (3 : ℕ∞) := by decide

/-- The actual height of the second variable-prime component. -/
theorem ex63_height_primeOf_B2 :
    (primeOf (K := K) ex63_B2 : Ideal (MvPolynomial ex63_var K)).height = (2 : ℕ∞) := by
  calc
    (primeOf (K := K) ex63_B2 : Ideal (MvPolynomial ex63_var K)).height =
        (ex63_B2.card : ℕ∞) := height_primeOf_eq_card (K := K) ex63_B2
    _ = (2 : ℕ∞) := by decide

/-- The actual height of the third variable-prime component. -/
theorem ex63_height_primeOf_B3 :
    (primeOf (K := K) ex63_B3 : Ideal (MvPolynomial ex63_var K)).height = (2 : ℕ∞) := by
  calc
    (primeOf (K := K) ex63_B3 : Ideal (MvPolynomial ex63_var K)).height =
        (ex63_B3.card : ℕ∞) := height_primeOf_eq_card (K := K) ex63_B3
    _ = (2 : ℕ∞) := by decide

/-- The actual height of the fourth variable-prime component. -/
theorem ex63_height_primeOf_B4 :
    (primeOf (K := K) ex63_B4 : Ideal (MvPolynomial ex63_var K)).height = (2 : ℕ∞) := by
  calc
    (primeOf (K := K) ex63_B4 : Ideal (MvPolynomial ex63_var K)).height =
        (ex63_B4.card : ℕ∞) := height_primeOf_eq_card (K := K) ex63_B4
    _ = (2 : ℕ∞) := by decide

theorem ex63_primeHeights :
    ((primeOf (K := K) ex63_B1 : Ideal (MvPolynomial ex63_var K)).height,
      (primeOf (K := K) ex63_B2 : Ideal (MvPolynomial ex63_var K)).height,
      (primeOf (K := K) ex63_B3 : Ideal (MvPolynomial ex63_var K)).height,
      (primeOf (K := K) ex63_B4 : Ideal (MvPolynomial ex63_var K)).height) =
        ((3 : ℕ∞), (2 : ℕ∞), (2 : ℕ∞), (2 : ℕ∞)) := by
  simp [ex63_height_primeOf_B1, ex63_height_primeOf_B2, ex63_height_primeOf_B3,
    ex63_height_primeOf_B4]

/-- The actual height of the first exponent-two component. -/
theorem ex63_height_purePower_B1_two :
    (purePower (K := K) ex63_B1 (fun _ ↦ 2) :
      Ideal (MvPolynomial ex63_var K)).height = (3 : ℕ∞) := by
  calc
    (purePower (K := K) ex63_B1 (fun _ ↦ 2) : Ideal (MvPolynomial ex63_var K)).height =
        (ex63_B1.card : ℕ∞) :=
      height_purePower_eq_card (K := K) (A := ex63_B1) (a := fun _ ↦ 2) (by
        intro i hi
        norm_num)
    _ = (3 : ℕ∞) := by decide

/-- The actual height of the second exponent-two component. -/
theorem ex63_height_purePower_B2_two :
    (purePower (K := K) ex63_B2 (fun _ ↦ 2) :
      Ideal (MvPolynomial ex63_var K)).height = (2 : ℕ∞) := by
  calc
    (purePower (K := K) ex63_B2 (fun _ ↦ 2) : Ideal (MvPolynomial ex63_var K)).height =
        (ex63_B2.card : ℕ∞) :=
      height_purePower_eq_card (K := K) (A := ex63_B2) (a := fun _ ↦ 2) (by
        intro i hi
        norm_num)
    _ = (2 : ℕ∞) := by decide

/-- The actual height of the third exponent-two component. -/
theorem ex63_height_purePower_B3_two :
    (purePower (K := K) ex63_B3 (fun _ ↦ 2) :
      Ideal (MvPolynomial ex63_var K)).height = (2 : ℕ∞) := by
  calc
    (purePower (K := K) ex63_B3 (fun _ ↦ 2) : Ideal (MvPolynomial ex63_var K)).height =
        (ex63_B3.card : ℕ∞) :=
      height_purePower_eq_card (K := K) (A := ex63_B3) (a := fun _ ↦ 2) (by
        intro i hi
        norm_num)
    _ = (2 : ℕ∞) := by decide

/-- The actual height of the fourth exponent-two component. -/
theorem ex63_height_purePower_B4_two :
    (purePower (K := K) ex63_B4 (fun _ ↦ 2) :
      Ideal (MvPolynomial ex63_var K)).height = (2 : ℕ∞) := by
  calc
    (purePower (K := K) ex63_B4 (fun _ ↦ 2) : Ideal (MvPolynomial ex63_var K)).height =
        (ex63_B4.card : ℕ∞) :=
      height_purePower_eq_card (K := K) (A := ex63_B4) (a := fun _ ↦ 2) (by
        intro i hi
        norm_num)
    _ = (2 : ℕ∞) := by decide

theorem ex63_purePowerHeights :
    ((purePower (K := K) ex63_B1 (fun _ ↦ 2) : Ideal (MvPolynomial ex63_var K)).height,
      (purePower (K := K) ex63_B2 (fun _ ↦ 2) : Ideal (MvPolynomial ex63_var K)).height,
      (purePower (K := K) ex63_B3 (fun _ ↦ 2) : Ideal (MvPolynomial ex63_var K)).height,
      (purePower (K := K) ex63_B4 (fun _ ↦ 2) : Ideal (MvPolynomial ex63_var K)).height) =
        ((3 : ℕ∞), (2 : ℕ∞), (2 : ℕ∞), (2 : ℕ∞)) := by
  simp [ex63_height_purePower_B1_two, ex63_height_purePower_B2_two,
    ex63_height_purePower_B3_two, ex63_height_purePower_B4_two]

/-- Squarefree characteristic vectors are exactly the exponent-one transversals. -/
theorem ex63_characteristicExp_facet (c : ex63_choice) :
    characteristicExp (ex63_facet c) = ex63_transExpWeight 1 c := by
  ext z
  rcases z with (x1 | x2) | (x3 | x4)
  · rw [characteristicExp_apply]
    change (if ex63_in1 x1 ∈ ex63_facet c then 1 else 0) =
      ex63_transExpWeight 1 c (ex63_in1 x1)
    rw [ex63_transExpWeight_at_B1]
    by_cases hx : x1 = c.1
    · subst x1
      simp [ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4]
    · simp [ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4, hx]
  · rw [characteristicExp_apply]
    change (if ex63_in2 x2 ∈ ex63_facet c then 1 else 0) =
      ex63_transExpWeight 1 c (ex63_in2 x2)
    rw [ex63_transExpWeight_at_B2]
    by_cases hx : x2 = c.2.1
    · subst x2
      simp [ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4]
    · simp [ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4, hx]
  · rw [characteristicExp_apply]
    change (if ex63_in3 x3 ∈ ex63_facet c then 1 else 0) =
      ex63_transExpWeight 1 c (ex63_in3 x3)
    rw [ex63_transExpWeight_at_B3]
    by_cases hx : x3 = c.2.2.1
    · subst x3
      simp [ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4]
    · simp [ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4, hx]
  · rw [characteristicExp_apply]
    change (if ex63_in4 x4 ∈ ex63_facet c then 1 else 0) =
      ex63_transExpWeight 1 c (ex63_in4 x4)
    rw [ex63_transExpWeight_at_B4]
    by_cases hx : x4 = c.2.2.2
    · subst x4
      simp [ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4]
    · simp [ex63_facet, ex63_in1, ex63_in2, ex63_in3, ex63_in4, hx]

/-- The root \(J\) is squarefree. -/
theorem ex63_isSquarefree_J : IsSquarefreeMonomialIdeal (ex63_J (K := K)) := by
  refine ⟨Set.range ex63_facet, ?_⟩
  rw [ex63_J_eq_monomialIdeal]
  congr 1
  ext e
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨ex63_facet c, ⟨c, rfl⟩, ex63_characteristicExp_facet c⟩
  · intro he
    rcases he with ⟨F, hFH, hFe⟩
    rcases hFH with ⟨c, hcF⟩
    refine ⟨c, ?_⟩
    calc
      ex63_transExpWeight 1 c = characteristicExp (ex63_facet c) :=
        (ex63_characteristicExp_facet c).symm
      _ = characteristicExp F := by rw [hcF]
      _ = e := hFe

/-- A weight-two minimal generator cannot be divisible by a squarefree generator. -/
theorem ex63_not_isSquarefree_I : ¬ IsSquarefreeMonomialIdeal (ex63_I (K := K)) := by
  rintro ⟨H, hI⟩
  let g : ex63_var →₀ ℕ := ex63_transExpWeight 2 ex63_choice0
  have hgmem : (monomial g (1 : K) : MvPolynomial ex63_var K) ∈ ex63_I (K := K) := by
    rw [ex63_I_eq_monomialIdeal]
    exact monomial_mem_monomialIdeal.mpr ⟨g, Set.mem_range_self ex63_choice0, le_rfl⟩
  have hgmin : g ∈ minGens (K := K) (ex63_I (K := K)) := by
    rw [ex63_minGens_I]
    simp [g, ex63_transversalGens]
  have hgmem' : (monomial g (1 : K) : MvPolynomial ex63_var K) ∈
      monomialIdeal (K := K) (characteristicExp '' H) := by
    simpa [hI] using hgmem
  rcases monomial_mem_monomialIdeal.mp hgmem' with ⟨u, ⟨F, hFH, rfl⟩, hug⟩
  have huI : (monomial (characteristicExp F) (1 : K) : MvPolynomial ex63_var K) ∈
      ex63_I (K := K) := by
    rw [hI]
    exact monomial_mem_monomialIdeal.mpr
      ⟨characteristicExp F, ⟨F, hFH, rfl⟩, le_rfl⟩
  have heq : characteristicExp F = g :=
    (mem_minGens.mp hgmin).2 (characteristicExp F) huI hug
  have hval := congrArg (fun e : ex63_var →₀ ℕ ↦ e (ex63_in1 (0 : Fin 3))) heq
  rw [characteristicExp_apply, ex63_transExpWeight_at_B1] at hval
  by_cases hm : ex63_in1 (0 : Fin 3) ∈ F
  · simp [hm] at hval
  · simp [hm] at hval

/-- The four displayed blocks are nonempty, pairwise disjoint, and cover all variables. -/
theorem ex63_blockFamily : ex63_BlockFamily := by
  constructor
  · intro j
    exact ⟨ex63_chosen ex63_choice0 j, ex63_chosen_mem_block ex63_choice0 j⟩
  constructor
  · intro j k x hxj hxk
    rcases x with (x1 | x2) | (x3 | x4) <;>
      fin_cases j <;> fin_cases k <;>
        simp [ex63_block, ex63_B1, ex63_B2, ex63_B3, ex63_B4,
          ex63_in1, ex63_in2, ex63_in3, ex63_in4] at hxj hxk ⊢
  · intro x
    rcases x with (x1 | x2) | (x3 | x4)
    · refine ⟨0, ?_⟩
      fin_cases x1 <;> simp [ex63_block, ex63_B1, ex63_in1]
    · refine ⟨1, ?_⟩
      fin_cases x2 <;> simp [ex63_block, ex63_B2, ex63_in2]
    · refine ⟨2, ?_⟩
      fin_cases x3 <;> simp [ex63_block, ex63_B3, ex63_in3]
    · refine ⟨3, ?_⟩
      fin_cases x4 <;> simp [ex63_block, ex63_B4, ex63_in4]

theorem ex63_block_injective : Function.Injective ex63_block := by
  intro j k hjk
  rcases ex63_blockFamily.1 j with ⟨x, hx⟩
  exact ex63_blockFamily.2.1 j k x hx (by simpa [hjk] using hx)

theorem ex63_block_inter_eq_empty_of_ne {j k : Fin 4} (hjk : j ≠ k) :
    ex63_block j ∩ ex63_block k = ∅ := by
  ext x
  constructor
  · intro hx
    have hx' := Finset.mem_inter.mp hx
    exact (hjk (ex63_blockFamily.2.1 j k x hx'.1 hx'.2)).elim
  · intro hx
    simp at hx

/-- Any component family on these blocks has pairwise incomparable supports. -/
theorem ex63_supportsAntichain (a : Fin 4 → ex63_var → ℕ) :
    SupportsAntichain ex63_block a := by
  intro j k hsubset
  rcases ex63_blockFamily.1 j with ⟨x, hx⟩
  exact ex63_blockFamily.2.1 j k x hx (hsubset hx)

theorem ex63_supportsAntichain_J :
    SupportsAntichain ex63_block (fun _ _ ↦ (1 : ℕ)) :=
  ex63_supportsAntichain (fun _ _ ↦ (1 : ℕ))

theorem ex63_supportsAntichain_I :
    SupportsAntichain ex63_block (fun _ _ ↦ (2 : ℕ)) :=
  ex63_supportsAntichain (fun _ _ ↦ (2 : ℕ))

/-- A monomial meeting every block except `j`. -/
noncomputable def ex63_omitExp (w : ℕ) (j : Fin 4) : ex63_var →₀ ℕ :=
  match j.val with
  | 0 => ((Finsupp.single ex63_u2 w + Finsupp.single ex63_u3 w) +
      Finsupp.single ex63_u4 w)
  | 1 => ((Finsupp.single ex63_u1 w + Finsupp.single ex63_u3 w) +
      Finsupp.single ex63_u4 w)
  | 2 => ((Finsupp.single ex63_u1 w + Finsupp.single ex63_u2 w) +
      Finsupp.single ex63_u4 w)
  | _ => ((Finsupp.single ex63_u1 w + Finsupp.single ex63_u2 w) +
      Finsupp.single ex63_u3 w)

theorem ex63_omitExp_mem_decompOmit (w : ℕ) (j : Fin 4) :
    (monomial (ex63_omitExp w j) (1 : K) : MvPolynomial ex63_var K) ∈
      decompOmit (K := K) ex63_block (fun _ _ ↦ w) j := by
  classical
  rw [decompOmit, Ideal.mem_iInf]
  intro k
  refine monomial_mem_purePower.mpr
    ⟨ex63_chosen ex63_choice0 k.1, ex63_chosen_mem_block ex63_choice0 k.1, ?_⟩
  rcases k with ⟨k, hk⟩
  fin_cases j <;> fin_cases k <;>
    simp [ex63_omitExp, ex63_chosen, ex63_in1, ex63_in2, ex63_in3, ex63_in4] at hk ⊢

theorem ex63_omitExp_eq_zero_on_block (w : ℕ) (j : Fin 4) {i : ex63_var}
    (hi : i ∈ ex63_block j) : ex63_omitExp w j i = 0 := by
  fin_cases j
  · have hi' : i ∈ ex63_B1 := by simpa [ex63_block] using hi
    rcases Finset.mem_image.mp hi' with ⟨a, -, rfl⟩
    fin_cases a <;>
      simp [ex63_omitExp, ex63_in1, ex63_in2, ex63_in3, ex63_in4]
  · have hi' : i ∈ ex63_B2 := by simpa [ex63_block] using hi
    rcases Finset.mem_image.mp hi' with ⟨a, -, rfl⟩
    fin_cases a <;>
      simp [ex63_omitExp, ex63_in1, ex63_in2, ex63_in3, ex63_in4]
  · have hi' : i ∈ ex63_B3 := by simpa [ex63_block] using hi
    rcases Finset.mem_image.mp hi' with ⟨a, -, rfl⟩
    fin_cases a <;>
      simp [ex63_omitExp, ex63_in1, ex63_in2, ex63_in3, ex63_in4]
  · have hi' : i ∈ ex63_B4 := by simpa [ex63_block] using hi
    rcases Finset.mem_image.mp hi' with ⟨a, -, rfl⟩
    fin_cases a <;>
      simp [ex63_omitExp, ex63_in1, ex63_in2, ex63_in3, ex63_in4]

theorem ex63_omitExp_not_mem_purePower (w : ℕ) (hw : 0 < w) (j : Fin 4) :
    (monomial (ex63_omitExp w j) (1 : K) : MvPolynomial ex63_var K) ∉
      purePower (K := K) (ex63_block j) (fun _ ↦ w) := by
  intro hm
  rcases monomial_mem_purePower.mp hm with ⟨i, hi, hle⟩
  have hzero := ex63_omitExp_eq_zero_on_block w j hi
  omega

/-- Positive uniform weights give an irredundant decomposition. -/
theorem ex63_isIrredundant_weight (w : ℕ) (hw : 0 < w) :
    IsIrredundant (K := K) ex63_block (fun _ _ ↦ w) := by
  intro j hle
  exact ex63_omitExp_not_mem_purePower (K := K) w hw j
    (hle (ex63_omitExp_mem_decompOmit (K := K) w j))

theorem ex63_isIrredundantDecomp_weightIdeal (w : ℕ) (hw : 0 < w) :
    IsIrredundantDecomp (K := K)
      (monomialIdeal (K := K) (Set.range (ex63_transExpWeight w)))
      ex63_block (fun _ _ ↦ w) :=
  ⟨ex63_hasComponents_weightIdeal (K := K) w,
    ex63_isIrredundant_weight (K := K) w hw⟩

theorem ex63_isIrredundantDecomp_J :
    IsIrredundantDecomp (K := K) (ex63_J (K := K)) ex63_block (fun _ _ ↦ (1 : ℕ)) :=
  ⟨ex63_hasComponents_J (K := K), ex63_isIrredundant_weight (K := K) 1 (by norm_num)⟩

theorem ex63_isIrredundantDecomp_I :
    IsIrredundantDecomp (K := K) (ex63_I (K := K)) ex63_block (fun _ _ ↦ (2 : ℕ)) :=
  ⟨ex63_hasComponents_I (K := K), ex63_isIrredundant_weight (K := K) 2 (by norm_num)⟩

/-- Exponent vectors with disjoint support have join equal to their sum. -/
theorem ex63_sup_eq_add_of_disjoint_support {u v : ex63_var →₀ ℕ}
    (huv : Disjoint u.support v.support) : u ⊔ v = u + v := by
  ext x
  rw [Finsupp.sup_apply]
  by_cases hu : u x = 0
  · simp [hu]
  · by_cases hv : v x = 0
    · simp [hv]
    · exfalso
      exact (Finset.disjoint_left.mp huv (by simpa [Finsupp.mem_support_iff] using hu))
        (by simpa [Finsupp.mem_support_iff] using hv)

/-- A finite join of vectors supported in disjoint blocks is their sum. -/
theorem ex63_finset_sup_eq_sum_of_disjoint_support {c : Fin 4 → ex63_var →₀ ℕ}
    (hc : ∀ h, (c h).support ⊆ ex63_block h) :
    Finset.univ.sup c = ∑ h, c h := by
  classical
  have hgen : ∀ s : Finset (Fin 4), s.sup c = ∑ h ∈ s, c h := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        apply le_antisymm
        · exact bot_le
        · rw [Finsupp.le_def]
          intro x
          exact Nat.zero_le _
    | @insert j s hjs ih =>
        rw [Finset.sup_insert, Finset.sum_insert hjs, ih]
        apply ex63_sup_eq_add_of_disjoint_support
        refine Finset.disjoint_left.mpr ?_
        intro x hx hsum
        rcases Finsupp.mem_support_finsetSum x hsum with ⟨k, hks, hxk⟩
        have hjk : j = k := ex63_blockFamily.2.1 j k x (hc j hx) (hc k hxk)
        exact hjs (by simpa [hjk] using hks)
  simpa using hgen (Finset.univ : Finset (Fin 4))

/-- A monomial whose exponent is a finite sum belongs to the corresponding product. -/
theorem ex63_monomial_sum_mem_finsetProd {S : Fin 4 → Set (ex63_var →₀ ℕ)}
    {c : Fin 4 → ex63_var →₀ ℕ} {s : Finset (Fin 4)}
    (hc : ∀ h ∈ s, c h ∈ S h) :
    (monomial (∑ h ∈ s, c h) (1 : K) : MvPolynomial ex63_var K) ∈
      ∏ h ∈ s, (monomialIdeal (K := K) (S h) : Ideal (MvPolynomial ex63_var K)) := by
  classical
  induction s using Finset.induction_on generalizing c with
  | empty => simp
  | @insert j s hjs ih =>
      rw [Finset.prod_insert hjs, Finset.sum_insert hjs]
      have hgenj : (monomial (c j) (1 : K) : MvPolynomial ex63_var K) ∈
          (monomialIdeal (K := K) (S j) : Ideal (MvPolynomial ex63_var K)) :=
        monomial_mem_monomialIdeal.mpr ⟨c j, hc j (by simp), le_rfl⟩
      have hgens : (monomial (∑ h ∈ s, c h) (1 : K) : MvPolynomial ex63_var K) ∈
          ∏ h ∈ s, (monomialIdeal (K := K) (S h) : Ideal (MvPolynomial ex63_var K)) :=
        ih (fun h hh ↦ hc h (by simp [hh]))
      have hmul := Ideal.mul_mem_mul hgenj hgens
      simpa [monomial_mul] using hmul

/-- On these disjoint blocks a finite monomial-ideal intersection is a product. -/
theorem ex63_iInf_eq_finsetProd_monomialIdeal {S : Fin 4 → Set (ex63_var →₀ ℕ)}
    (hsupp : ∀ h e, e ∈ S h → e.support ⊆ ex63_block h) :
    (⨅ h, (monomialIdeal (K := K) (S h) : Ideal (MvPolynomial ex63_var K))) =
      ∏ h, (monomialIdeal (K := K) (S h) : Ideal (MvPolynomial ex63_var K)) := by
  classical
  have hiInf : (⨅ h, (monomialIdeal (K := K) (S h) : Ideal (MvPolynomial ex63_var K))) =
      (monomialIdeal (K := K) (iInfGens S) : Ideal (MvPolynomial ex63_var K)) :=
    monomialIdeal_iInf (K := K) S
  apply le_antisymm
  · rw [hiInf, monomialIdeal, Ideal.span_le]
    rintro y ⟨z, hz, rfl⟩
    rcases hz with ⟨c, hcS, rfl⟩
    have hsup : Finset.univ.sup c = ∑ h, c h :=
      ex63_finset_sup_eq_sum_of_disjoint_support
        (fun h ↦ hsupp h (c h) (hcS h))
    simpa [hsup] using
      (ex63_monomial_sum_mem_finsetProd (K := K) (s := (Finset.univ : Finset (Fin 4)))
        (fun h _ ↦ hcS h))
  · refine le_iInf fun j ↦ ?_
    rw [Finset.prod_eq_mul_prod_sdiff_singleton j
      (fun h ↦ (monomialIdeal (K := K) (S h) : Ideal (MvPolynomial ex63_var K)))
      (by intro hj; exact (hj (by simp)).elim)]
    exact Ideal.mul_le_left

/-- Support bounds propagate from monomial generators to iterated power generators. -/
theorem ex63_powGens_support_subset {A : Finset ex63_var}
    {S : Set (ex63_var →₀ ℕ)} (hsupp : ∀ e ∈ S, e.support ⊆ A) :
    ∀ n e, e ∈ powGens S n → e.support ⊆ A := by
  intro n
  induction n with
  | zero =>
      intro e he
      simp only [powGens] at he
      subst e
      intro x hx
      simp at hx
  | succ n ih =>
      intro e he
      simp only [powGens] at he
      rcases he with ⟨u, hu, v, hv, rfl⟩
      intro x hx
      have hxuv : u x + v x ≠ 0 := by
        simpa [Finsupp.mem_support_iff] using hx
      by_cases hux : u x = 0
      · have hvx : v x ≠ 0 := by
          intro hvx
          exact hxuv (by simp [hux, hvx])
        exact hsupp v hv (by simpa [Finsupp.mem_support_iff] using hvx)
      · exact ih u hu (by simpa [Finsupp.mem_support_iff] using hux)

/-- Every ordinary power of a uniform transversal ideal is componentwise. -/
theorem ex63_weightIdeal_pow_eq_componentSymbolic (w q : ℕ) :
    (monomialIdeal (K := K) (Set.range (ex63_transExpWeight w)) :
        Ideal (MvPolynomial ex63_var K)) ^ q =
      componentSymbolic (fun j ↦ (purePower (K := K) (ex63_block j) (fun _ ↦ w) :
        Ideal (MvPolynomial ex63_var K))) q := by
  classical
  let S : Fin 4 → Set (ex63_var →₀ ℕ) := fun h ↦
    {e | ∃ i ∈ ex63_block h, e = Finsupp.single i w}
  let Q : Fin 4 → Ideal (MvPolynomial ex63_var K) := fun h ↦
    purePower (K := K) (ex63_block h) (fun _ ↦ w)
  change (monomialIdeal (K := K) (Set.range (ex63_transExpWeight w)) :
      Ideal (MvPolynomial ex63_var K)) ^ q = componentSymbolic Q q
  have hsupp : ∀ h e, e ∈ S h → e.support ⊆ ex63_block h := by
    intro h e he x hx
    rcases he with ⟨i, hiB, rfl⟩
    have hxi : x = i := by
      by_contra hnexi
      have hxnonzero : Finsupp.single i w x ≠ 0 := by
        simpa [Finsupp.mem_support_iff] using hx
      exact hxnonzero (by simp [hnexi])
    simpa [hxi] using hiB
  have hsuppPow : ∀ h e, e ∈ powGens (S h) q → e.support ⊆ ex63_block h := by
    intro h
    exact ex63_powGens_support_subset (A := ex63_block h) (S := S h) (hsupp h) q
  have hprod0 : (monomialIdeal (K := K) (Set.range (ex63_transExpWeight w)) :
      Ideal (MvPolynomial ex63_var K)) = ∏ h, Q h := by
    calc
      (monomialIdeal (K := K) (Set.range (ex63_transExpWeight w)) :
          Ideal (MvPolynomial ex63_var K)) = ⨅ h, Q h :=
        (ex63_intersection_eq_monomialIdeal (K := K) w).symm
      _ = ∏ h, Q h := by
        simpa [Q, S, purePower] using
          (ex63_iInf_eq_finsetProd_monomialIdeal (K := K) hsupp)
  have hprodq : (⨅ h, Q h ^ q) = ∏ h, Q h ^ q := by
    simpa [Q, S, purePower, monomialIdeal_pow] using
      (ex63_iInf_eq_finsetProd_monomialIdeal (K := K)
        (S := fun h ↦ powGens (S h) q) hsuppPow)
  calc
    (monomialIdeal (K := K) (Set.range (ex63_transExpWeight w)) :
        Ideal (MvPolynomial ex63_var K)) ^ q = (∏ h, Q h) ^ q := by rw [hprod0]
    _ = ∏ h, Q h ^ q := by
      simpa using (Finset.prod_pow (s := (Finset.univ : Finset (Fin 4))) q
        (fun h ↦ Q h)).symm
    _ = ⨅ h, Q h ^ q := hprodq.symm
    _ = componentSymbolic Q q := rfl

/-- Equation (2) for every positive uniform weighting of Example 6.3. -/
theorem ex63_hasStdSymbolicFormula_weightIdeal (w : ℕ) (hw : 0 < w) :
    HasStdSymbolicFormula
      (monomialIdeal (K := K) (Set.range (ex63_transExpWeight w)))
      (fun j ↦ (purePower (K := K) (ex63_block j) (fun _ ↦ w) :
        Ideal (MvPolynomial ex63_var K))) := by
  exact eq2_standardSymbolic (K := K)
    (ex63_isIrredundantDecomp_weightIdeal (K := K) w hw)
    (ex63_supportsAntichain (fun _ _ ↦ w))

/-- Every positive uniform transversal ideal is Simis. -/
theorem ex63_weightIdeal_isSimis (w : ℕ) (hw : 0 < w) :
    IsSimis (monomialIdeal (K := K) (Set.range (ex63_transExpWeight w))) := by
  intro q hq
  exact (ex63_hasStdSymbolicFormula_weightIdeal (K := K) w hw q hq).trans
    (ex63_weightIdeal_pow_eq_componentSymbolic (K := K) w q).symm

theorem ex63_isSimis_J : IsSimis (ex63_J (K := K)) := by
  rw [ex63_J_eq_monomialIdeal]
  exact ex63_weightIdeal_isSimis (K := K) 1 (by norm_num)

theorem ex63_isSimis_I : IsSimis (ex63_I (K := K)) := by
  rw [ex63_I_eq_monomialIdeal]
  exact ex63_weightIdeal_isSimis (K := K) 2 (by norm_num)

/-- \(I_a\) satisfies the conclusion of the Morey--Villarreal--Vasconcelos conjecture. -/
theorem ex63_MPVConc_I : MPVConc (ex63_I (K := K)) := by
  refine ⟨ex63_J (K := K), ex63_weight, ex63_isSquarefree_J (K := K),
    ex63_isSimis_J (K := K), ?_, rfl⟩
  intro i
  norm_num [ex63_weight]

theorem ex63_I_ne_bot : ex63_I (K := K) ≠ ⊥ := by
  let g : ex63_var →₀ ℕ := ex63_transExpWeight 2 ex63_choice0
  have hgmem : (monomial g (1 : K) : MvPolynomial ex63_var K) ∈ ex63_I (K := K) := by
    rw [ex63_I_eq_monomialIdeal]
    exact monomial_mem_monomialIdeal.mpr ⟨g, Set.mem_range_self ex63_choice0, le_rfl⟩
  intro hbot
  simp [hbot] at hgmem

theorem ex63_I_ne_top : ex63_I (K := K) ≠ ⊤ := by
  have hnotone : (1 : MvPolynomial ex63_var K) ∉ ex63_I (K := K) := by
    have hnot : (monomial (0 : ex63_var →₀ ℕ) (1 : K) : MvPolynomial ex63_var K) ∉
        monomialIdeal (K := K) (Set.range (ex63_transExpWeight 2)) := by
      rw [monomial_mem_monomialIdeal]
      rintro ⟨u, ⟨c, rfl⟩, hu0⟩
      have hle := hu0 (ex63_in1 c.1)
      simp at hle
    rw [ex63_I_eq_monomialIdeal]
    simpa using hnot
  intro htop
  exact hnotone (by simp [htop])

theorem ex63_incidenceBound : ex63_IncidenceBound := by
  intro k l _ _ j₁ j₂ hj₁ _
  have hjmem : j₁ ∈ ex63_intervenors k l := by
    simpa [ex63_intervenors, ex63_isIntervenor, and_assoc] using hj₁
  rw [ex63_intervenors_empty k l] at hjmem
  simp at hjmem

/-- The hypotheses of Theorem 5.2, specialized to \(I_a\), with the local incidence bound. -/
theorem ex63_ComponentCriterion :
    ex63_I (K := K) ≠ ⊥ ∧ ex63_I (K := K) ≠ ⊤ ∧
      IsIrredundantDecomp (K := K) (ex63_I (K := K)) ex63_block (fun _ _ ↦ (2 : ℕ)) ∧
        SupportsAntichain ex63_block (fun _ _ ↦ (2 : ℕ)) ∧
          ex63_IncidenceBound ∧
            symbolicPower (ex63_I (K := K)) 2 = ex63_I (K := K) ^ 2 := by
  refine ⟨ex63_I_ne_bot (K := K), ex63_I_ne_top (K := K),
    ex63_isIrredundantDecomp_I (K := K), ex63_supportsAntichain (fun _ _ ↦ (2 : ℕ)),
      ex63_incidenceBound, ?_⟩
  exact ex63_isSimis_I (K := K) 2 (by norm_num)

theorem ex63_notPrimeComponentHeightAtMostTwo :
    ¬ ∀ j : Fin 4,
      (primeOf (K := K) (ex63_block j) : Ideal (MvPolynomial ex63_var K)).height ≤
        (2 : ℕ∞) := by
  intro h
  have hle := h (0 : Fin 4)
  have heq : (primeOf (K := K) (ex63_block (0 : Fin 4)) :
      Ideal (MvPolynomial ex63_var K)).height = (3 : ℕ∞) := by
    simpa [ex63_block] using ex63_height_primeOf_B1 (K := K)
  rw [heq] at hle
  norm_num at hle

theorem ex63_notPurePowerComponentHeightAtMostTwo :
    ¬ ∀ j : Fin 4,
      (purePower (K := K) (ex63_block j) (fun _ ↦ 2) :
        Ideal (MvPolynomial ex63_var K)).height ≤ (2 : ℕ∞) := by
  intro h
  have hle := h (0 : Fin 4)
  have heq : (purePower (K := K) (ex63_block (0 : Fin 4)) (fun _ ↦ 2) :
      Ideal (MvPolynomial ex63_var K)).height = (3 : ℕ∞) := by
    simpa [ex63_block] using ex63_height_purePower_B1_two (K := K)
  rw [heq] at hle
  norm_num at hle

theorem ex63_failsNoStrongTriangle_J :
    ¬ (¬ HasStrongTriangle (supportComplex (ex63_J (K := K)))) := by
  intro h
  exact h (ex63_strongTriangle_J (K := K))

theorem ex63_failsNoStrongTriangle_I :
    ¬ (¬ HasStrongTriangle (supportComplex (ex63_I (K := K)))) := by
  intro h
  exact h (ex63_strongTriangle_I (K := K))

/-- The mismatch criterion has no ordered pair on which to separate this example. -/
theorem ex63_notSeparatingMismatchCriterion : ¬ ex63_XI.Nonempty := by
  rintro ⟨p, hp⟩
  rw [ex63_XI_eq_empty] at hp
  simp at hp

theorem ex63_main_combinatorics : ex63_MainCombinatorics (K := K) := by
  dsimp [ex63_MainCombinatorics]
  exact ⟨ex63_blockFamily, ex63_componentFacets_explicit, ex63_componentHeights,
    ex63_minGens_J_ncard, ex63_minGens_I_ncard, ex63_allSupportCards_J,
    ex63_allSupportCards_I, ex63_primeHeights, ex63_purePowerHeights,
    ex63_strongTriangle_J, ex63_strongTriangle_I, ex63_notSimplicialForest_J,
    ex63_notSimplicialForest_I, ex63_notBalanced_J, ex63_notBalanced_I,
    ex63_failsNoStrongTriangle_J, ex63_failsNoStrongTriangle_I,
    ex63_notSupportAtMostThree_J, ex63_notSupportAtMostThree_I,
    ex63_notPrimeComponentHeightAtMostTwo, ex63_notPurePowerComponentHeightAtMostTwo,
    ex63_notComponentHeightAtMostTwo, ex63_XI_eq_empty, ex63_mismatchPairs_eq_empty,
    ex63_intervenors_empty, ex63_notSeparatingMismatchCriterion⟩

theorem ex63_main_algebra : ex63_MainAlgebra (K := K) := by
  dsimp [ex63_MainAlgebra]
  exact ⟨ex63_J_eq_monomialIdeal, ex63_I_eq_blockProduct,
    ex63_isSquarefree_J, ex63_not_isSquarefree_I, ex63_isIrredundantDecomp_J,
    ex63_isIrredundantDecomp_I, ex63_supportsAntichain_J, ex63_supportsAntichain_I,
    ex63_isSimis_J, ex63_isSimis_I, ex63_MPVConc_I,
    ex63_I_ne_bot, ex63_I_ne_top, ex63_isIrredundantDecomp_I,
    ex63_supportsAntichain_I, ex63_incidenceBound,
    ex63_isSimis_I (K := K) 2 (by norm_num)⟩

/-- All assertions of Example 6.3, split into combinatorial and algebraic packages. -/
theorem ex63_main : ex63_MainCombinatorics (K := K) ∧ ex63_MainAlgebra (K := K) := by
  exact ⟨ex63_main_combinatorics, ex63_main_algebra⟩

/-- The Example 6.3 blocks satisfy Theorem 5.2's incidence-bound hypothesis. -/
theorem ex63_incidenceBound_thm52 :
    _root_.thm52_IncidenceBound ex63_block := by
  exact ex63_incidenceBound
