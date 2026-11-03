import SimisFormal.Defs
import SimisFormal.Basic
import SimisFormal.Eq2_StandardSymbolic
import SimisFormal.Eq4_DiagonalSimis
import SimisFormal.Thm5_2
import SimisFormal.DiagAssociatedPreserve

namespace SimisFormal
open MvPolynomial
open scoped BigOperators
variable {σ K ι : Type*} [Field K] [DecidableEq σ]
/-- The cardinality and uniqueness formulations of condition (11) agree. -/
theorem cor53_atMostOneIntervenor_iff_thm52 [Fintype ι] {A : ι → Finset σ} :
    cor53_AtMostOneIntervenor A ↔ _root_.thm52_IncidenceBound A := by
  constructor
  · intro h k l hkl hint j₁ j₂ hj₁ hj₂
    have hj₁' : j₁ ∈ cor53_intervenorSet A k l := by
      simpa [cor53_intervenorSet, _root_.thm52_isIntervenor] using hj₁
    have hj₂' : j₂ ∈ cor53_intervenorSet A k l := by
      simpa [cor53_intervenorSet, _root_.thm52_isIntervenor] using hj₂
    exact Finset.card_le_one.mp (h k l hkl hint) j₁ hj₁' j₂ hj₂'
  · intro h k l hkl hint
    rw [Finset.card_le_one]
    intro j₁ hj₁ j₂ hj₂
    apply h hkl hint
    · simpa [cor53_intervenorSet, _root_.thm52_isIntervenor] using hj₁
    · simpa [cor53_intervenorSet, _root_.thm52_isIntervenor] using hj₂

/-- The underlying graph determined by component supports.  When every support has cardinality
two, this is exactly the hypergraph of components regarded as a graph. -/
def cor53_componentGraph (A : ι → Finset σ) : SimpleGraph σ where
  Adj x y := x ≠ y ∧ ∃ j, x ∈ A j ∧ y ∈ A j
  symm := ⟨by
    rintro x y ⟨hxy, j, hx, hy⟩
    exact ⟨hxy.symm, j, hy, hx⟩⟩
  loopless := ⟨by
    rintro x ⟨hxx, _⟩
    exact hxx rfl⟩

/-- The incidence graph on the components: two distinct components are adjacent when their
supports meet. -/
def cor53_intersectionGraph (A : ι → Finset σ) : SimpleGraph ι where
  Adj j k := j ≠ k ∧ (A j ∩ A k).Nonempty
  symm := ⟨by
    rintro j k ⟨hjk, hint⟩
    exact ⟨hjk.symm, by simpa [Finset.inter_comm] using hint⟩⟩
  loopless := ⟨by
    rintro j ⟨hjj, _⟩
    exact hjj rfl⟩

/-- For two-element component supports, adjacency in `cor53_componentGraph` is exactly being one
of the component edges. -/
theorem cor53_componentGraph_adj_iff_eq_pair {A : ι → Finset σ}
    (hcard : ∀ j, (A j).card = 2) {x y : σ} :
    (cor53_componentGraph A).Adj x y ↔ ∃ j, A j = {x, y} := by
  constructor
  · rintro ⟨hxy, j, hx, hy⟩
    refine ⟨j, ?_⟩
    have hsub : ({x, y} : Finset σ) ⊆ A j := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    have hpaircard : ({x, y} : Finset σ).card = 2 := Finset.card_pair hxy
    symm
    exact Finset.eq_of_subset_of_card_le hsub (by simp [hcard j, hpaircard])
  · rintro ⟨j, hj⟩
    have hpaircard : ({x, y} : Finset σ).card = 2 := by simpa [hj] using hcard j
    have hxy : x ≠ y := Finset.card_pair_eq_two_iff.mp hpaircard
    exact ⟨hxy, j, by simp [hj], by simp [hj]⟩

/-- An intervenor must meet the first support, since otherwise irredundance would identify it
with the second component. -/
theorem cor53_intervenor_meets_left [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ} (hanti : SupportsAntichain A a)
    {k l j : ι} (hj : j ∈ cor53_intervenorSet A k l) :
    (A j ∩ A k).Nonempty := by
  classical
  have hjdata : j ≠ k ∧ j ≠ l ∧ A j ⊆ A k ∪ A l := by
    simpa [cor53_intervenorSet] using hj
  rcases hjdata with ⟨hjk, hjl, hjsub⟩
  by_contra hdisjoint
  apply hjl
  apply hanti j l
  intro x hx
  rcases Finset.mem_union.mp (hjsub hx) with hxK | hxL
  · exact (hdisjoint ⟨x, Finset.mem_inter.mpr ⟨hx, hxK⟩⟩).elim
  · exact hxL

/-- An intervenor must meet the second support, since otherwise irredundance would identify it
with the first component. -/
theorem cor53_intervenor_meets_right [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ} (hanti : SupportsAntichain A a)
    {k l j : ι} (hj : j ∈ cor53_intervenorSet A k l) :
    (A j ∩ A l).Nonempty := by
  classical
  have hjdata : j ≠ k ∧ j ≠ l ∧ A j ⊆ A k ∪ A l := by
    simpa [cor53_intervenorSet] using hj
  rcases hjdata with ⟨hjk, hjl, hjsub⟩
  by_contra hdisjoint
  apply hjk
  apply hanti j k
  intro x hx
  rcases Finset.mem_union.mp (hjsub hx) with hxK | hxL
  · exact hxK
  · exact (hdisjoint ⟨x, Finset.mem_inter.mpr ⟨hx, hxL⟩⟩).elim

/-- Two distinct two-element finite sets which meet have singleton differences. -/
theorem cor53_card_sdiff_eq_one_of_card_eq_two {S T : Finset σ}
    (hS : S.card = 2) (hT : T.card = 2) (hne : S ≠ T)
    (hint : (S ∩ T).Nonempty) :
    (S \ T).card = 1 ∧ (T \ S).card = 1 := by
  classical
  have hpos : 0 < (S ∩ T).card := Finset.card_pos.mpr hint
  have hle : (S ∩ T).card ≤ 2 := by
    have h := Finset.card_le_card (Finset.inter_subset_left : S ∩ T ⊆ S)
    simpa [hS] using h
  have hne2 : (S ∩ T).card ≠ 2 := by
    intro hc
    have hIS : S ∩ T = S :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by simp [hc, hS])
    have hIT : S ∩ T = T :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by simp [hc, hT])
    exact hne (hIS.symm.trans hIT)
  have hinter : (S ∩ T).card = 1 := by omega
  constructor
  · calc
      (S \ T).card = S.card - (T ∩ S).card := Finset.card_sdiff
      _ = 1 := by rw [Finset.inter_comm, hS, hinter]
  · calc
      (T \ S).card = T.card - (S ∩ T).card := Finset.card_sdiff
      _ = 1 := by rw [hT, hinter]

/-- In the graph case, every intervenor between two intersecting edges is the third edge of the
triangle on their union. -/
theorem cor53_intervenor_support_eq_sdiff [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ} {k l j : ι}
    (hcard : ∀ r, (A r).card = 2) (hanti : SupportsAntichain A a)
    (hkl : k ≠ l) (hint : (A k ∩ A l).Nonempty)
    (hj : j ∈ cor53_intervenorSet A k l) :
    A j = (A k \ A l) ∪ (A l \ A k) := by
  classical
  have hjdata : j ≠ k ∧ j ≠ l ∧ A j ⊆ A k ∪ A l := by
    simpa [cor53_intervenorSet] using hj
  rcases hjdata with ⟨hjk, hjl, hjsub⟩
  have hAk_ne_Al : A k ≠ A l := by
    intro heq
    exact hkl (hanti k l heq.le)
  rcases cor53_card_sdiff_eq_one_of_card_eq_two (hcard k) (hcard l) hAk_ne_Al hint with
    ⟨hKdiff, hLdiff⟩
  have hjnotK : ¬ A j ⊆ A k := by
    intro hs
    exact hjk (hanti j k hs)
  have hjnotL : ¬ A j ⊆ A l := by
    intro hs
    exact hjl (hanti j l hs)
  obtain ⟨p, hp⟩ := Finset.sdiff_nonempty.mpr hjnotK
  obtain ⟨q, hq⟩ := Finset.sdiff_nonempty.mpr hjnotL
  have hpj : p ∈ A j := (Finset.mem_sdiff.mp hp).1
  have hpnotK : p ∉ A k := (Finset.mem_sdiff.mp hp).2
  have hqj : q ∈ A j := (Finset.mem_sdiff.mp hq).1
  have hqnotL : q ∉ A l := (Finset.mem_sdiff.mp hq).2
  have hpL : p ∈ A l := (Finset.mem_union.mp (hjsub hpj)).resolve_left hpnotK
  have hqK : q ∈ A k := (Finset.mem_union.mp (hjsub hqj)).resolve_right hqnotL
  have hpLdiff : p ∈ A l \ A k := Finset.mem_sdiff.mpr ⟨hpL, hpnotK⟩
  have hqKdiff : q ∈ A k \ A l := Finset.mem_sdiff.mpr ⟨hqK, hqnotL⟩
  have hpq : p ≠ q := by
    intro heq
    exact hpnotK (by simpa [heq] using hqK)
  have hpairsub : ({p, q} : Finset σ) ⊆ A j := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hpj
    · exact hqj
  have hpaircard : ({p, q} : Finset σ).card = 2 := Finset.card_pair hpq
  have hAj : A j = {p, q} := by
    symm
    exact Finset.eq_of_subset_of_card_le hpairsub (by simp [hcard j, hpaircard])
  have hKsingleton : A k \ A l = {q} := by
    have hsub : ({q} : Finset σ) ⊆ A k \ A l := by
      intro x hx
      have hxq : x = q := Finset.mem_singleton.mp hx
      simpa [hxq] using hqKdiff
    symm
    exact Finset.eq_of_subset_of_card_le hsub (by simp [hKdiff])
  have hLsingleton : A l \ A k = {p} := by
    have hsub : ({p} : Finset σ) ⊆ A l \ A k := by
      intro x hx
      have hxp : x = p := Finset.mem_singleton.mp hx
      simpa [hxp] using hpLdiff
    symm
    exact Finset.eq_of_subset_of_card_le hsub (by simp [hLdiff])
  rw [hAj, hKsingleton, hLsingleton]
  ext x
  simp [or_comm]

/-- Condition (11) is automatic for graph-sized component supports. -/
theorem cor53_atMostOneIntervenor_of_card_eq_two [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hcard : ∀ j, (A j).card = 2) (hanti : SupportsAntichain A a) :
    cor53_AtMostOneIntervenor A := by
  classical
  have hAinj : Function.Injective A := by
    intro r s hrs
    exact hanti r s hrs.le
  intro k l hkl hint
  rw [Finset.card_le_one]
  intro j hj j' hj'
  apply hAinj
  exact (cor53_intervenor_support_eq_sdiff hcard hanti hkl hint hj).trans
    (cor53_intervenor_support_eq_sdiff hcard hanti hkl hint hj').symm

/-- If the clique-expansion graph of component supports is acyclic, there are no intervenors:
an intervenor and a common vertex always form a triangle. -/
theorem cor53_intervenorSet_eq_empty_of_componentGraph_isAcyclic [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ} {k l : ι}
    (hanti : SupportsAntichain A a) (hacy : (cor53_componentGraph A).IsAcyclic)
    (hint : (A k ∩ A l).Nonempty) :
    cor53_intervenorSet A k l = ∅ := by
  classical
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨j, hj⟩
  rcases hint with ⟨x, hxint⟩
  have hxK : x ∈ A k := (Finset.mem_inter.mp hxint).1
  have hxL : x ∈ A l := (Finset.mem_inter.mp hxint).2
  have hjdata : j ≠ k ∧ j ≠ l ∧ A j ⊆ A k ∪ A l := by
    simpa [cor53_intervenorSet] using hj
  rcases hjdata with ⟨hjk, hjl, hjsub⟩
  have hjnotK : ¬ A j ⊆ A k := by
    intro hs
    exact hjk (hanti j k hs)
  have hjnotL : ¬ A j ⊆ A l := by
    intro hs
    exact hjl (hanti j l hs)
  obtain ⟨p, hp⟩ := Finset.sdiff_nonempty.mpr hjnotK
  obtain ⟨q, hq⟩ := Finset.sdiff_nonempty.mpr hjnotL
  have hpj : p ∈ A j := (Finset.mem_sdiff.mp hp).1
  have hpnotK : p ∉ A k := (Finset.mem_sdiff.mp hp).2
  have hqj : q ∈ A j := (Finset.mem_sdiff.mp hq).1
  have hqnotL : q ∉ A l := (Finset.mem_sdiff.mp hq).2
  have hpL : p ∈ A l := (Finset.mem_union.mp (hjsub hpj)).resolve_left hpnotK
  have hqK : q ∈ A k := (Finset.mem_union.mp (hjsub hqj)).resolve_right hqnotL
  have hxp : x ≠ p := by
    intro heq
    exact hpnotK (by simpa [heq] using hxK)
  have hxq : x ≠ q := by
    intro heq
    exact hqnotL (by simpa [heq] using hxL)
  have hpq : p ≠ q := by
    intro heq
    exact hpnotK (by simpa [heq] using hqK)
  have hadj_xp : (cor53_componentGraph A).Adj x p := ⟨hxp, l, hxL, hpL⟩
  have hadj_xq : (cor53_componentGraph A).Adj x q := ⟨hxq, k, hxK, hqK⟩
  have hadj_pq : (cor53_componentGraph A).Adj p q := ⟨hpq, j, hpj, hqj⟩
  have hadj_px : (cor53_componentGraph A).Adj p x := ⟨hxp.symm, l, hpL, hxL⟩
  have hadj_qx : (cor53_componentGraph A).Adj q x := ⟨hxq.symm, k, hqK, hxK⟩
  have hadj_qp : (cor53_componentGraph A).Adj q p := ⟨hpq.symm, j, hqj, hpj⟩
  have hclique : (cor53_componentGraph A).IsNClique 3 ({x, p, q} : Finset σ) := by
    rw [SimpleGraph.isNClique_iff]
    constructor
    · intro u hu v hv huv
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
      · exact (huv rfl).elim
      · exact hadj_xp
      · exact hadj_xq
      · exact hadj_px
      · exact (huv rfl).elim
      · exact hadj_pq
      · exact hadj_qx
      · exact hadj_qp
      · exact (huv rfl).elim
    · simp [hxp, hxq, hpq]
  exact (hacy.cliqueFree (by norm_num) ({x, p, q} : Finset σ)) hclique

/-- An acyclic clique-expansion graph in particular satisfies condition (11). -/
theorem cor53_atMostOneIntervenor_of_componentGraph_isAcyclic [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hanti : SupportsAntichain A a) (hacy : (cor53_componentGraph A).IsAcyclic) :
    cor53_AtMostOneIntervenor A := by
  intro k l _ hint
  rw [cor53_intervenorSet_eq_empty_of_componentGraph_isAcyclic hanti hacy hint]
  simp

/-- A tree has no intervenors between incident component edges. -/
theorem cor53_intervenorSet_eq_empty_of_componentGraph_isTree [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ} {k l : ι}
    (hanti : SupportsAntichain A a) (htree : (cor53_componentGraph A).IsTree)
    (hint : (A k ∩ A l).Nonempty) :
    cor53_intervenorSet A k l = ∅ :=
  cor53_intervenorSet_eq_empty_of_componentGraph_isAcyclic hanti htree.isAcyclic hint

/-- Component supports whose clique-expansion graph is a tree satisfy condition (11). -/
theorem cor53_atMostOneIntervenor_of_componentGraph_isTree [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hanti : SupportsAntichain A a) (htree : (cor53_componentGraph A).IsTree) :
    cor53_AtMostOneIntervenor A :=
  cor53_atMostOneIntervenor_of_componentGraph_isAcyclic hanti htree.isAcyclic

/-- One intervenor makes the three component indices pairwise adjacent in the incidence graph.
Consequently an acyclic incidence graph has no intervenors. -/
theorem cor53_intervenorSet_eq_empty_of_intersectionGraph_isAcyclic [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ} {k l : ι}
    (hanti : SupportsAntichain A a) (hacy : (cor53_intersectionGraph A).IsAcyclic)
    (hkl : k ≠ l) (hint : (A k ∩ A l).Nonempty) :
    cor53_intervenorSet A k l = ∅ := by
  classical
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨j, hj⟩
  have hjdata : j ≠ k ∧ j ≠ l ∧ A j ⊆ A k ∪ A l := by
    simpa [cor53_intervenorSet] using hj
  rcases hjdata with ⟨hjk, hjl, _⟩
  have hjK := cor53_intervenor_meets_left hanti hj
  have hjL := cor53_intervenor_meets_right hanti hj
  have hadj_kj : (cor53_intersectionGraph A).Adj k j :=
    ⟨hjk.symm, by simpa [Finset.inter_comm] using hjK⟩
  have hadj_kl : (cor53_intersectionGraph A).Adj k l := ⟨hkl, hint⟩
  have hadj_jl : (cor53_intersectionGraph A).Adj j l := ⟨hjl, hjL⟩
  have hadj_jk : (cor53_intersectionGraph A).Adj j k := ⟨hjk, hjK⟩
  have hadj_lk : (cor53_intersectionGraph A).Adj l k :=
    ⟨hkl.symm, by simpa [Finset.inter_comm] using hint⟩
  have hadj_lj : (cor53_intersectionGraph A).Adj l j :=
    ⟨hjl.symm, by simpa [Finset.inter_comm] using hjL⟩
  have hclique : (cor53_intersectionGraph A).IsNClique 3 ({k, j, l} : Finset ι) := by
    rw [SimpleGraph.isNClique_iff]
    constructor
    · intro u hu v hv huv
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
      · exact (huv rfl).elim
      · exact hadj_kj
      · exact hadj_kl
      · exact hadj_jk
      · exact (huv rfl).elim
      · exact hadj_jl
      · exact hadj_lk
      · exact hadj_lj
      · exact (huv rfl).elim
    · simp [hkl, hjk.symm, hjl]
  exact (hacy.cliqueFree (by norm_num) ({k, j, l} : Finset ι)) hclique

/-- An acyclic incidence graph satisfies condition (11). -/
theorem cor53_atMostOneIntervenor_of_intersectionGraph_isAcyclic [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hanti : SupportsAntichain A a) (hacy : (cor53_intersectionGraph A).IsAcyclic) :
    cor53_AtMostOneIntervenor A := by
  intro k l hkl hint
  rw [cor53_intervenorSet_eq_empty_of_intersectionGraph_isAcyclic hanti hacy hkl hint]
  simp

/-- A tree of component incidences has no intervenors. -/
theorem cor53_intervenorSet_eq_empty_of_intersectionGraph_isTree [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ} {k l : ι}
    (hanti : SupportsAntichain A a) (htree : (cor53_intersectionGraph A).IsTree)
    (hkl : k ≠ l) (hint : (A k ∩ A l).Nonempty) :
    cor53_intervenorSet A k l = ∅ :=
  cor53_intervenorSet_eq_empty_of_intersectionGraph_isAcyclic hanti htree.isAcyclic hkl hint

/-- A tree of component incidences satisfies condition (11). -/
theorem cor53_atMostOneIntervenor_of_intersectionGraph_isTree [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hanti : SupportsAntichain A a) (htree : (cor53_intersectionGraph A).IsTree) :
    cor53_AtMostOneIntervenor A :=
  cor53_atMostOneIntervenor_of_intersectionGraph_isAcyclic hanti htree.isAcyclic

/-- A squarefree monomial ideal admits a monomial representation. -/
theorem cor53_isMonomial_of_squarefree {J : Ideal (MvPolynomial σ K)}
    (hJ : IsSquarefreeMonomialIdeal J) : IsMonomialIdeal J := by
  rcases hJ with ⟨H, hJ⟩
  exact ⟨characteristicExp '' H, hJ⟩

/-- Corollary 5.3.  Theorem 5.2 and Eq. (4) are explicit hypotheses here: the former supplies the
forced squarefree diagonal root from equality of second powers, and the latter reflects Simisness
along a positive diagonal weighting. -/
theorem cor53_main [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hstruct : cor53_StructuralHypotheses I A a)
    (hinc : cor53_AtMostOneIntervenor A)
    (thm52 :
      ∀ (L : Ideal (MvPolynomial σ K)) (B : ι → Finset σ) (b : ι → σ → ℕ),
        cor53_StructuralHypotheses L B b → cor53_AtMostOneIntervenor B →
          symbolicPower L 2 = L ^ 2 → HasSqRoot L)
    (eq4 :
      ∀ (J : Ideal (MvPolynomial σ K)) (d : σ → ℕ),
        IsMonomialIdeal J → (∀ i, 0 < d i) →
          (IsSimis J ↔ IsSimis (diagonal d J)))
    (hsimis : IsSimis I) : MPVConc I := by
  classical
  have hsecond : symbolicPower I 2 = I ^ 2 := hsimis 2 (by norm_num)
  rcases thm52 I A a hstruct hinc hsecond with ⟨J, d, hJ, hd, hdiag⟩
  have hJmono : IsMonomialIdeal J := cor53_isMonomial_of_squarefree hJ
  have hdiagSimis : IsSimis (diagonal d J) := by
    simpa [← hdiag] using hsimis
  have hJsimis : IsSimis J := (eq4 J d hJmono hd).mpr hdiagSimis
  exact ⟨J, d, hJ, hJsimis, hd, hdiag⟩

/-- The Theorem 5.2 input used by Corollary 5.3. -/
def cor53_Thm52Input [Fintype ι] : Prop :=
  ∀ (L : Ideal (MvPolynomial σ K)) (B : ι → Finset σ) (b : ι → σ → ℕ),
    cor53_StructuralHypotheses L B b → cor53_AtMostOneIntervenor B →
      symbolicPower L 2 = L ^ 2 → HasSqRoot L

/-- Equation (4) restricted to the form used by Corollary 5.3. -/
def cor53_Eq4Input : Prop :=
  ∀ (J : Ideal (MvPolynomial σ K)) (d : σ → ℕ),
    IsMonomialIdeal J → (∀ i, 0 < d i) →
      (IsSimis J ↔ IsSimis (diagonal d J))

/-- Theorem 5.2, with Equation (2) discharged, as long as the current development still leaves
its localization/contraction form of Lemma 5.1 explicit. -/
theorem cor53_thm52Input_of_thm52Obstruction [Fintype σ] [Fintype ι]
    (hobstruction :
      ∀ (_L : Ideal (MvPolynomial σ K)) (B : ι → Finset σ) (b : ι → σ → ℕ),
        _root_.thm52_lem51Obstruction (K := K) B b) :
    cor53_Thm52Input (σ := σ) (K := K) (ι := ι) := by
  intro L B b hstruct hinc hsecond
  rcases hstruct with ⟨hI0, hItop, _, _, hdec, hanti⟩
  exact _root_.thm52_hasSqRoot_ofStdSymbolic (K := K) (I := L) (A := B) (a := b)
    hI0 hItop hdec hanti (cor53_atMostOneIntervenor_iff_thm52.mp hinc)
    (eq2_standardSymbolic (K := K) hdec hanti) hsecond (hobstruction L B b)

/-- Corollary 5.3 with the completed Eq. (2) and Eq. (4) integrations.  The only residual
Theorem 5.2 ingredient is its currently explicit localization/contraction obstruction. -/
theorem cor53_main_of_thm52Obstruction [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hstruct : cor53_StructuralHypotheses I A a)
    (hinc : cor53_AtMostOneIntervenor A)
    (hobstruction : _root_.thm52_lem51Obstruction (K := K) A a)
    (hsimis : IsSimis I) : MPVConc I := by
  classical
  rcases hstruct with ⟨hI0, hItop, _, _, hdec, hanti⟩
  have hinc52 : _root_.thm52_IncidenceBound A :=
    cor53_atMostOneIntervenor_iff_thm52.mp hinc
  have hstdI : HasStdSymbolicFormula I (fun j ↦ purePower (A j) (a j)) :=
    eq2_standardSymbolic (K := K) hdec hanti
  have hsecond : symbolicPower I 2 = I ^ 2 := hsimis 2 (by norm_num)
  rcases _root_.thm52_ofStdSymbolic (K := K) (I := I) (A := A) (a := a)
      hI0 hItop hdec hanti hinc52 hstdI hsecond hobstruction with
    ⟨_, d, hd, _, hJsq, hJdec, _, hdiag⟩
  have hantiJ : SupportsAntichain A (fun _ _ ↦ (1 : ℕ)) := by
    intro j k hsub
    exact hanti j k hsub
  have hdiagSimis : IsSimis (diagonal d (_root_.thm52_root (K := K) A)) := by
    simpa [← hdiag] using hsimis
  have hJsimis : IsSimis (_root_.thm52_root (K := K) A) :=
    (eq4_isSimis_diagonal_iff_of_irredundantDecomp (K := K)
      (J := _root_.thm52_root (K := K) A) (A := A) (a := fun _ _ ↦ (1 : ℕ))
      hd hJdec hantiJ).mpr hdiagSimis
  exact ⟨_root_.thm52_root (K := K) A, d, hJsq, hJsimis, hd, hdiag⟩

/-- Height-two specialization: condition (11) is automatic. -/
theorem cor53_main_of_card_eq_two [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hstruct : cor53_StructuralHypotheses I A a)
    (hcard : ∀ j, (A j).card = 2)
    (thm52 : cor53_Thm52Input (σ := σ) (K := K) (ι := ι))
    (eq4 : cor53_Eq4Input (σ := σ) (K := K))
    (hsimis : IsSimis I) : MPVConc I := by
  have hanti : SupportsAntichain A a := hstruct.2.2.2.2.2
  exact cor53_main hstruct (cor53_atMostOneIntervenor_of_card_eq_two hcard hanti)
    (by simpa [cor53_Thm52Input] using thm52) (by simpa [cor53_Eq4Input] using eq4) hsimis

/-- Tree specialization for the incidence graph of components. -/
theorem cor53_main_of_intersectionGraph_isTree [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hstruct : cor53_StructuralHypotheses I A a)
    (htree : (cor53_intersectionGraph A).IsTree)
    (thm52 : cor53_Thm52Input (σ := σ) (K := K) (ι := ι))
    (eq4 : cor53_Eq4Input (σ := σ) (K := K))
    (hsimis : IsSimis I) : MPVConc I := by
  have hanti : SupportsAntichain A a := hstruct.2.2.2.2.2
  exact cor53_main hstruct (cor53_atMostOneIntervenor_of_intersectionGraph_isTree hanti htree)
    (by simpa [cor53_Thm52Input] using thm52) (by simpa [cor53_Eq4Input] using eq4) hsimis

/-- Height-two specialization using the verified Eq. (2), Eq. (4), and Theorem 5.2 modules. -/
theorem cor53_main_of_card_eq_two_of_thm52Obstruction [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hstruct : cor53_StructuralHypotheses I A a)
    (hcard : ∀ j, (A j).card = 2)
    (hobstruction : _root_.thm52_lem51Obstruction (K := K) A a)
    (hsimis : IsSimis I) : MPVConc I := by
  have hanti : SupportsAntichain A a := hstruct.2.2.2.2.2
  exact cor53_main_of_thm52Obstruction hstruct
    (cor53_atMostOneIntervenor_of_card_eq_two hcard hanti) hobstruction hsimis

/-- Incidence-tree specialization using the verified Eq. (2), Eq. (4), and Theorem 5.2 modules. -/
theorem cor53_main_of_intersectionGraph_isTree_of_thm52Obstruction [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hstruct : cor53_StructuralHypotheses I A a)
    (htree : (cor53_intersectionGraph A).IsTree)
    (hobstruction : _root_.thm52_lem51Obstruction (K := K) A a)
    (hsimis : IsSimis I) : MPVConc I := by
  have hanti : SupportsAntichain A a := hstruct.2.2.2.2.2
  exact cor53_main_of_thm52Obstruction hstruct
    (cor53_atMostOneIntervenor_of_intersectionGraph_isTree hanti htree) hobstruction hsimis

/-- The final Theorem 5.2 API discharges the packaged `cor53_Thm52Input` hypothesis. -/
theorem cor53_thm52Input_verified [Fintype σ] [Fintype ι] :
    cor53_Thm52Input (σ := σ) (K := K) (ι := ι) := by
  intro L B b hstruct hinc hsecond
  rcases hstruct with ⟨hI0, hItop, _, _, hdec, hanti⟩
  exact _root_.thm52_hasSqRoot (K := K) (I := L) (A := B) (a := b)
    hI0 hItop hdec hanti (cor53_atMostOneIntervenor_iff_thm52.mp hinc) hsecond

/-- Corollary 5.3 with every cross-file ingredient discharged.  Theorem 5.2 supplies the
root together with its irredundant prime decomposition, and Eq. (4) then reflects Simisness. -/
theorem cor53_main_verified [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hstruct : cor53_StructuralHypotheses I A a)
    (hinc : cor53_AtMostOneIntervenor A)
    (hsimis : IsSimis I) : MPVConc I := by
  classical
  rcases hstruct with ⟨hI0, hItop, _, _, hdec, hanti⟩
  have hinc52 : _root_.thm52_IncidenceBound A :=
    cor53_atMostOneIntervenor_iff_thm52.mp hinc
  have hsecond : symbolicPower I 2 = I ^ 2 := hsimis 2 (by norm_num)
  rcases _root_.thm52 (K := K) (I := I) (A := A) (a := a)
      hI0 hItop hdec hanti hinc52 hsecond with
    ⟨_, d, hd, _, hJsq, hJdec, _, hdiag⟩
  have hantiJ : SupportsAntichain A (fun _ _ ↦ (1 : ℕ)) := by
    intro j k hsub
    exact hanti j k hsub
  have hdiagSimis : IsSimis (diagonal d (_root_.thm52_root (K := K) A)) := by
    simpa [← hdiag] using hsimis
  have hJsimis : IsSimis (_root_.thm52_root (K := K) A) :=
    (eq4_isSimis_diagonal_iff_of_irredundantDecomp (K := K)
      (J := _root_.thm52_root (K := K) A) (A := A) (a := fun _ _ ↦ (1 : ℕ))
      hd hJdec hantiJ).mpr hdiagSimis
  exact ⟨_root_.thm52_root (K := K) A, d, hJsq, hJsimis, hd, hdiag⟩

/-- Height-two Corollary 5.3 with no packaged algebraic hypotheses. -/
theorem cor53_main_of_card_eq_two_verified [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hstruct : cor53_StructuralHypotheses I A a)
    (hcard : ∀ j, (A j).card = 2)
    (hsimis : IsSimis I) : MPVConc I := by
  have hanti : SupportsAntichain A a := hstruct.2.2.2.2.2
  exact cor53_main_verified hstruct
    (cor53_atMostOneIntervenor_of_card_eq_two hcard hanti) hsimis

/-- Incidence-tree Corollary 5.3 with no packaged algebraic hypotheses. -/
theorem cor53_main_of_intersectionGraph_isTree_verified [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hstruct : cor53_StructuralHypotheses I A a)
    (htree : (cor53_intersectionGraph A).IsTree)
    (hsimis : IsSimis I) : MPVConc I := by
  have hanti : SupportsAntichain A a := hstruct.2.2.2.2.2
  exact cor53_main_verified hstruct
    (cor53_atMostOneIntervenor_of_intersectionGraph_isTree hanti htree) hsimis

/-- The completed Theorem 5.2 data used by Corollary 5.3, augmented by reflection of Simisness
along the forced positive diagonal weighting. -/
theorem cor53_forcedRootData_verified [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hstruct : cor53_StructuralHypotheses I A a)
    (hinc : cor53_AtMostOneIntervenor A)
    (hsimis : IsSimis I) :
    ∃ d : σ → ℕ,
      (∀ i, 0 < d i) ∧
        IsSquarefreeMonomialIdeal (_root_.thm52_root (K := K) A) ∧
          IsIrredundantDecomp
            (_root_.thm52_root (K := K) A) A (fun _ _ ↦ (1 : ℕ)) ∧
            IsSimis (_root_.thm52_root (K := K) A) ∧
              _root_.thm52_root (K := K) A = I.radical ∧
                diagonal d (_root_.thm52_root (K := K) A) = I := by
  classical
  rcases hstruct with ⟨hI0, hItop, _, _, hdec, hanti⟩
  have hinc52 : _root_.thm52_IncidenceBound A :=
    cor53_atMostOneIntervenor_iff_thm52.mp hinc
  have hsecond : symbolicPower I 2 = I ^ 2 := hsimis 2 (by norm_num)
  rcases _root_.thm52 (K := K) (I := I) (A := A) (a := a)
      hI0 hItop hdec hanti hinc52 hsecond with
    ⟨_, d, hd, _, hJsq, hJdec, hrad, hdiag⟩
  have hantiJ : SupportsAntichain A (fun _ _ ↦ (1 : ℕ)) := by
    intro j k hsub
    exact hanti j k hsub
  have hdiagSimis : IsSimis (diagonal d (_root_.thm52_root (K := K) A)) := by
    simpa [← hdiag] using hsimis
  have hJsimis : IsSimis (_root_.thm52_root (K := K) A) :=
    (eq4_isSimis_diagonal_iff_of_irredundantDecomp (K := K)
      (J := _root_.thm52_root (K := K) A) (A := A) (a := fun _ _ ↦ (1 : ℕ))
      hd hJdec hantiJ).mpr hdiagSimis
  exact ⟨d, hd, hJsq, hJdec, hJsimis, hrad, hdiag⟩

/-- Corollary 5.3: under the structural and incidence hypotheses, the forced squarefree root is
itself Simis. -/
theorem cor53_forcedRoot_isSimis_verified [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hstruct : cor53_StructuralHypotheses I A a)
    (hinc : cor53_AtMostOneIntervenor A)
    (hsimis : IsSimis I) :
    IsSimis (_root_.thm52_root (K := K) A) := by
  rcases cor53_forcedRootData_verified hstruct hinc hsimis with
    ⟨_, _, _, _, hJsimis, _, _⟩
  exact hJsimis

/-- Corollary 5.3: Theorem 5.2 identifies the forced root with the radical, so the radical is also
Simis. -/
theorem cor53_radical_isSimis_verified [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hstruct : cor53_StructuralHypotheses I A a)
    (hinc : cor53_AtMostOneIntervenor A)
    (hsimis : IsSimis I) : IsSimis I.radical := by
  rcases cor53_forcedRootData_verified hstruct hinc hsimis with
    ⟨_, _, _, _, hJsimis, hrad, _⟩
  simpa [hrad] using hJsimis

/-- Corollary 5.3 in full: public Simisness of the forced root, the MPV conclusion, the
radical identification, and the positive diagonal weighting realizing the given ideal. -/
theorem cor53_main_full_verified [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hstruct : cor53_StructuralHypotheses I A a)
    (hinc : cor53_AtMostOneIntervenor A)
    (hsimis : IsSimis I) :
    IsSimis (_root_.thm52_root (K := K) A) ∧
      MPVConc I ∧
        _root_.thm52_root (K := K) A = I.radical ∧
          IsSimis I.radical ∧
            ∃ d : σ → ℕ,
              (∀ i, 0 < d i) ∧
                IsSquarefreeMonomialIdeal (_root_.thm52_root (K := K) A) ∧
                  diagonal d (_root_.thm52_root (K := K) A) = I := by
  rcases cor53_forcedRootData_verified hstruct hinc hsimis with
    ⟨d, hd, hJsq, _, hJsimis, hrad, hdiag⟩
  have hradSimis : IsSimis I.radical := by
    simpa [hrad] using hJsimis
  have hmpv : MPVConc I :=
    ⟨_root_.thm52_root (K := K) A, d, hJsq, hJsimis, hd, hdiag⟩
  refine ⟨hJsimis, ?_⟩
  refine ⟨hmpv, ?_⟩
  refine ⟨hrad, ?_⟩
  refine ⟨hradSimis, ?_⟩
  exact ⟨d, hd, hJsq, hdiag⟩

/-- The paper's irredundance, unmixedness, and pairwise-distinct-radical hypotheses imply the
support antichain used by the internal form of Corollary 5.3. -/
theorem cor53_supportsAntichain_of_paperHypotheses [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hdec : IsIrredundantDecomp I A a)
    (hNoEmb : associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) =
      I.minimalPrimes)
    (hDistinct : ∀ j k, (primeOf (A j) : Ideal (MvPolynomial σ K)) =
      primeOf (A k) → j = k) :
    SupportsAntichain A a := by
  classical
  rcases hdec with ⟨hI, hirr⟩
  have hpos : ∀ j i, i ∈ A j → 0 < a j i :=
    exponents_pos_of_irredundant (K := K) hirr
  have hAssRange :
      associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) =
        Set.range (fun j ↦ (primeOf (A j) : Ideal (MvPolynomial σ K))) :=
    diagAssoc_quotientAssociatedPrimes_eq_range
      (K := K) (I := I) (A := A) (a := a) hI hirr
  have hIleP (j : ι) : I ≤ (primeOf (A j) : Ideal (MvPolynomial σ K)) := by
    rw [hI]
    exact (iInf_le (fun k : ι ↦
      (purePower (K := K) (A k) (a k) : Ideal (MvPolynomial σ K))) j).trans
        (purePower_le_primeOf_of_pos (K := K) (A := A j) (a := a j)
          (fun i hi ↦ hpos j i hi))
  have hMin (j : ι) :
      (primeOf (A j) : Ideal (MvPolynomial σ K)) ∈ I.minimalPrimes := by
    have hjAss : (primeOf (A j) : Ideal (MvPolynomial σ K)) ∈
        associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) := by
      rw [hAssRange]
      exact ⟨j, rfl⟩
    simpa [hNoEmb] using hjAss
  intro j k hsub
  have hPsub : (primeOf (A j) : Ideal (MvPolynomial σ K)) ≤
      (primeOf (A k) : Ideal (MvPolynomial σ K)) := by
    rw [primeOf_eq_span_X (K := K) (A := A j),
      primeOf_eq_span_X (K := K) (A := A k)]
    exact Ideal.span_mono (Set.image_mono hsub)
  have hkMin := hMin k
  change I.IsMinimalPrime (primeOf (A k) : Ideal (MvPolynomial σ K)) at hkMin
  have hPkSubPj : (primeOf (A k) : Ideal (MvPolynomial σ K)) ≤
      (primeOf (A j) : Ideal (MvPolynomial σ K)) :=
    hkMin.2 ⟨primeOf_isPrime (K := K) (A j), hIleP j⟩ hPsub
  have hEq : (primeOf (A j) : Ideal (MvPolynomial σ K)) =
      (primeOf (A k) : Ideal (MvPolynomial σ K)) := le_antisymm hPsub hPkSubPj
  exact hDistinct j k hEq

/-- Corollary 5.3 under exactly the hypotheses stated in the manuscript. -/
theorem cor53_of_paperHypotheses [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤)
    (hdec : IsIrredundantDecomp I A a)
    (hNoEmb : associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) =
      I.minimalPrimes)
    (hDistinct : ∀ j k, (primeOf (A j) : Ideal (MvPolynomial σ K)) =
      primeOf (A k) → j = k)
    (hinc : thm52_IncidenceBound A)
    (hSimis : IsSimis I) :
    IsSimis (_root_.thm52_root (K := K) A) ∧
      MPVConc I ∧
        _root_.thm52_root (K := K) A = I.radical ∧
          IsSimis I.radical ∧
            ∃ d : σ → ℕ,
              (∀ i, 0 < d i) ∧
                IsSquarefreeMonomialIdeal (_root_.thm52_root (K := K) A) ∧
                  diagonal d (_root_.thm52_root (K := K) A) = I := by
  classical
  have hanti : SupportsAntichain A a :=
    cor53_supportsAntichain_of_paperHypotheses (K := K) (I := I) (A := A) (a := a)
      hdec hNoEmb hDistinct
  have hsupp : ∀ j, (A j).Nonempty := by
    intro j
    by_contra hj
    have hAj : A j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hj
    have hPj : (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K)) = ⊥ := by
      rw [hAj]
      simp [purePower, monomialIdeal]
    have hIle : I ≤ (⊥ : Ideal (MvPolynomial σ K)) := by
      rw [hdec.1]
      exact (iInf_le (fun k : ι ↦
        (purePower (K := K) (A k) (a k) : Ideal (MvPolynomial σ K))) j).trans
          (le_of_eq hPj)
    exact hI0 (bot_unique hIle)
  have hpos : ∀ j i, i ∈ A j → 0 < a j i :=
    exponents_pos_of_irredundant (K := K) hdec.2
  have hstruct : cor53_StructuralHypotheses I A a :=
    ⟨hI0, hItop, hsupp, hpos, hdec, hanti⟩
  have hincC : cor53_AtMostOneIntervenor A :=
    cor53_atMostOneIntervenor_iff_thm52.mpr hinc
  exact cor53_main_full_verified (K := K) hstruct hincC hSimis

end SimisFormal
