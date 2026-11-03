import SimisFormal.Defs
import SimisFormal.Basic
import SimisFormal.MonomialDecompExists
import SimisFormal.Prop2_1
import SimisFormal.Eq2_StandardSymbolic
import SimisFormal.Eq4_DiagonalSimis
import SimisFormal.DiagAssociatedPreserve
import SimisFormal.PowerAssociated
import SimisFormal.EvenCycleFlow

namespace SimisFormal
open MvPolynomial
open scoped BigOperators
/-! Even-cycle family from Proposition 6.1.

The file proves the displayed generator, clutter, support and diagonal assertions directly.
Intrinsic symbolic/associated-prime and the nonlocal combinatorial clauses are exposed as explicit
hypotheses in the final suffixed theorem, since Mathlib does not contain the cited FHO/HHTZ
implication, the paper's Eq. (2)/(4), and the blocker decomposition/forest facts used here. -/
/-- Explicit enumeration of the ambient variable type. -/
@[instance_reducible] def prop61_varFintype (m : ℕ) : Fintype (prop61_var m) :=
  ⟨(Finset.univ : Finset (Fin 3)).product (Finset.univ : Finset (Fin (2 * m))), by
    rintro ⟨i, j⟩
    simp⟩

/-- The Proposition 6.1 facets agree with the shared even-cycle flow facets. -/
theorem prop61_H_eq_evenCycleFlow_facets (m : ℕ) :
    prop61_H m = evenCycleFlow_facets m := by
  have hfun (i : Fin (2 * m)) : prop61_edge i = evenCycleFlow_facet i := by
    ext v
    rcases v with ⟨r, j⟩
    fin_cases r <;> simp [prop61_edge, evenCycleFlow_facet, prop61_x, prop61_y, prop61_z]
  ext E
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, hfun i⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, (hfun i).symm⟩

/-- Every variable occurs in the facet indexed by its own cyclic coordinate. -/
theorem prop61_var_mem_own_edge {m : ℕ} (v : prop61_var m) :
    v ∈ prop61_edge v.2 := by
  rcases v with ⟨r, i⟩
  fin_cases r <;> simp [prop61_edge, prop61_x, prop61_y, prop61_z]

theorem prop61_finSuccMod_ne_self_of_one_lt {q : ℕ} (hq : 1 < q) (i : Fin q) :
    finSuccMod i ≠ i := by
  intro h
  unfold finSuccMod at h
  split_ifs at h with hs
  · have hv := congrArg Fin.val h
    simp at hv
  · have hv := congrArg Fin.val h
    simp at hv
    omega

/-- Cyclic predecessor on `Fin q`. -/
def prop61_finPredMod {q : ℕ} (i : Fin q) : Fin q :=
  if h : i.val = 0 then ⟨q - 1, by
    have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    omega⟩
  else ⟨i.val - 1, by omega⟩

@[simp] theorem prop61_finSuccMod_val {q : ℕ} (i : Fin q) :
    (finSuccMod i).val = if i.val + 1 < q then i.val + 1 else 0 := by
  rw [finSuccMod]
  split_ifs <;> rfl

@[simp] theorem prop61_finPredMod_val {q : ℕ} (i : Fin q) :
    (prop61_finPredMod i).val = if i.val = 0 then q - 1 else i.val - 1 := by
  rw [prop61_finPredMod]
  split_ifs <;> rfl

/-- The predecessor used here agrees with the shared even-cycle flow predecessor. -/
theorem prop61_finPredMod_eq_evenCycleFlow_pred {q : ℕ} (i : Fin q) :
    prop61_finPredMod i = evenCycleFlow_pred i := by
  apply Fin.ext
  simp [prop61_finPredMod_val, evenCycleFlow_pred_val]

theorem prop61_finSuccMod_finPredMod {q : ℕ} (i : Fin q) :
    finSuccMod (prop61_finPredMod i) = i := by
  apply Fin.ext
  rw [prop61_finSuccMod_val, prop61_finPredMod_val]
  by_cases hi : i.val = 0
  · rw [if_pos hi]
    have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    have hnot : ¬ q - 1 + 1 < q := by omega
    rw [if_neg hnot]
    omega
  · rw [if_neg hi]
    have hlt : i.val - 1 + 1 < q := by omega
    rw [if_pos hlt]
    omega

theorem prop61_finPredMod_finSuccMod {q : ℕ} (i : Fin q) :
    prop61_finPredMod (finSuccMod i) = i := by
  apply Fin.ext
  rw [prop61_finPredMod_val, prop61_finSuccMod_val]
  by_cases hs : i.val + 1 < q
  · rw [if_pos hs]
    have hnot : ¬ i.val + 1 = 0 := by omega
    rw [if_neg hnot]
    omega
  · rw [if_neg hs, if_pos rfl]
    omega

theorem prop61_finSuccMod_injective {q : ℕ} : Function.Injective (@finSuccMod q) := by
  intro i j hij
  have := congrArg prop61_finPredMod hij
  simpa [prop61_finPredMod_finSuccMod] using this

theorem prop61_finPredMod_injective {q : ℕ} : Function.Injective (@prop61_finPredMod q) := by
  intro i j hij
  have := congrArg finSuccMod hij
  simpa [prop61_finSuccMod_finPredMod] using this

theorem prop61_finPredMod_ne_finSuccMod_of_two_lt {q : ℕ} (hq : 2 < q) (i : Fin q) :
    prop61_finPredMod i ≠ finSuccMod i := by
  intro h
  have hv := congrArg Fin.val h
  rw [prop61_finPredMod_val, prop61_finSuccMod_val] at hv
  by_cases hi : i.val = 0
  · rw [if_pos hi] at hv
    have hs : i.val + 1 < q := by omega
    rw [if_pos hs] at hv
    omega
  · rw [if_neg hi] at hv
    by_cases hs : i.val + 1 < q
    · rw [if_pos hs] at hv
      omega
    · rw [if_neg hs] at hv
      omega

@[simp] theorem prop61_finSuccMod_iterate_val {q : ℕ} (hq : 1 < q) (i : Fin q) (k : ℕ) :
    ((finSuccMod^[k]) i).val = (i.val + k) % q := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
      rw [Function.iterate_succ_apply', prop61_finSuccMod_val, ih]
      by_cases h : (i.val + k) % q + 1 < q
      · rw [if_pos h]
        have hmod : (i.val + k) % q + 1 = (i.val + k + 1) % q := by
          rw [Nat.add_mod]
          simpa [Nat.mod_eq_of_lt hq] using (Nat.mod_eq_of_lt h).symm
        rw [hmod]
        congr 1
      · rw [if_neg h]
        have hle : (i.val + k) % q < q := Nat.mod_lt _ (by omega)
        have heq : (i.val + k) % q + 1 = q := by omega
        calc
          0 = (q : ℕ) % q := (Nat.mod_self q).symm
          _ = ((i.val + k) % q + 1) % q := by rw [heq]
          _ = (i.val + k + 1) % q := by
            rw [Nat.add_mod]
            simp [Nat.mod_eq_of_lt hq]
          _ = (i.val + (k + 1)) % q := rfl

@[simp] theorem prop61_finSuccMod_iterate_of_lt {q : ℕ} (hq : 1 < q)
    {k : ℕ} (hk : k < q) :
    (finSuccMod^[k]) (⟨0, by omega⟩ : Fin q) = ⟨k, hk⟩ := by
  apply Fin.ext
  rw [prop61_finSuccMod_iterate_val hq]
  simpa using Nat.mod_eq_of_lt hk

/-- An injective closed walk on a finite cycle traverses the entire cycle. -/
theorem prop61_cyclicWalk_length_eq {n q : ℕ} (hn : 1 < n) (hq3 : 3 ≤ q)
    {a : Fin q → Fin n} (ha : Function.Injective a)
    (hstep : ∀ i : Fin q,
      a (finSuccMod i) = finSuccMod (a i) ∨
        a (finSuccMod i) = prop61_finPredMod (a i)) : q = n := by
  classical
  let _ : Fintype (Fin q) := inferInstance
  let _ : Fintype (Fin n) := inferInstance
  have hq1 : 1 < q := by omega
  have hqle : q ≤ n := by
    simpa using (Fintype.card_le_of_injective a ha)
  let z : Fin q := ⟨0, by omega⟩
  have hsucc_idx (k : ℕ) (hk : k < q) (hkp : k + 1 < q) :
      finSuccMod (⟨k, hk⟩ : Fin q) = ⟨k + 1, hkp⟩ := by
    apply Fin.ext
    rw [prop61_finSuccMod_val]
    simp [hkp]
  have hlength_of_fixed (hfix : (finSuccMod^[q]) (a z) = a z) : q = n := by
    have hv := congrArg Fin.val hfix
    rw [prop61_finSuccMod_iterate_val hn] at hv
    by_cases hnowrap : (a z).val + q < n
    · rw [Nat.mod_eq_of_lt hnowrap] at hv
      omega
    · have hwrap : n ≤ (a z).val + q := Nat.le_of_not_gt hnowrap
      have hsmall : (a z).val + q - n < n := by omega
      have hmod : ((a z).val + q) % n = (a z).val + q - n := by
        rw [Nat.mod_eq_sub_mod hwrap]
        exact Nat.mod_eq_of_lt hsmall
      rw [hmod] at hv
      omega
  rcases hstep z with hzforward | hzbackward
  · have hforward : ∀ k (hk : k < q) (hkp : k + 1 < q),
        a (⟨k + 1, hkp⟩ : Fin q) = finSuccMod (a (⟨k, hk⟩ : Fin q)) := by
      intro k
      induction k with
      | zero =>
          intro hk hkp
          have hzEq : z = (⟨0, hk⟩ : Fin q) := by
            apply Fin.ext
            simp [z]
          have hs := hsucc_idx 0 hk hkp
          have hst := hzforward
          rw [hzEq, hs] at hst
          simpa using hst
      | succ k ih =>
          intro hkS hkSp
          have hk : k < q := by omega
          have hk1 : k + 1 < q := by omega
          have hprev := ih hk hk1
          have hs := hsucc_idx (k + 1) hk1 hkSp
          have hst := hstep (⟨k + 1, hk1⟩ : Fin q)
          rw [hs] at hst
          rcases hst with hst | hst
          · simpa using hst
          · exfalso
            rw [hprev, prop61_finPredMod_finSuccMod] at hst
            have heq := ha hst
            have hv := congrArg Fin.val heq
            simp at hv
            omega
    have hiterForward : ∀ k (hk : k < q),
        a (⟨k, hk⟩ : Fin q) = (finSuccMod^[k]) (a z) := by
      intro k
      induction k with
      | zero =>
          intro hk
          have hzEq : z = (⟨0, hk⟩ : Fin q) := by
            apply Fin.ext
            simp [z]
          simp [hzEq]
      | succ k ih =>
          intro hkS
          have hk : k < q := by omega
          rw [Function.iterate_succ_apply', hforward k hk hkS, ih hk]
    have hLast : q - 1 < q := by omega
    have hPen : q - 2 < q := by omega
    have hlastIter := hiterForward (q - 1) hLast
    have hpenStep0 := hforward (q - 2) hPen (by omega)
    have hpenStep : a (⟨q - 1, hLast⟩ : Fin q) =
        finSuccMod (a (⟨q - 2, hPen⟩ : Fin q)) := by
      simpa [show q - 2 + 1 = q - 1 by omega] using hpenStep0
    have hsLast : finSuccMod (⟨q - 1, hLast⟩ : Fin q) = z := by
      apply Fin.ext
      rw [prop61_finSuccMod_val]
      have hnot : ¬ q - 1 + 1 < q := by omega
      rw [if_neg hnot]
    have hstepLast := hstep (⟨q - 1, hLast⟩ : Fin q)
    rw [hsLast] at hstepLast
    rcases hstepLast with hclose | hclose
    · have hiterSucc : (finSuccMod^[q]) (a z) =
          finSuccMod ((finSuccMod^[q - 1]) (a z)) := by
        simpa [show q - 1 + 1 = q by omega] using
          (Function.iterate_succ_apply' finSuccMod (q - 1) (a z))
      have hfixed : (finSuccMod^[q]) (a z) = a z := by
        rw [hiterSucc, ← hlastIter]
        exact hclose.symm
      exact hlength_of_fixed hfixed
    · exfalso
      rw [hpenStep, prop61_finPredMod_finSuccMod] at hclose
      have heq := ha hclose
      have hv := congrArg Fin.val heq
      simp [z] at hv
      omega
  · have hbackward : ∀ k (hk : k < q) (hkp : k + 1 < q),
        a (⟨k + 1, hkp⟩ : Fin q) = prop61_finPredMod (a (⟨k, hk⟩ : Fin q)) := by
      intro k
      induction k with
      | zero =>
          intro hk hkp
          have hzEq : z = (⟨0, hk⟩ : Fin q) := by
            apply Fin.ext
            simp [z]
          have hs := hsucc_idx 0 hk hkp
          have hst := hzbackward
          rw [hzEq, hs] at hst
          simpa using hst
      | succ k ih =>
          intro hkS hkSp
          have hk : k < q := by omega
          have hk1 : k + 1 < q := by omega
          have hprev := ih hk hk1
          have hs := hsucc_idx (k + 1) hk1 hkSp
          have hst := hstep (⟨k + 1, hk1⟩ : Fin q)
          rw [hs] at hst
          rcases hst with hst | hst
          · exfalso
            rw [hprev, prop61_finSuccMod_finPredMod] at hst
            have heq := ha hst
            have hv := congrArg Fin.val heq
            simp at hv
            omega
          · simpa using hst
    have hiterBackward : ∀ k (hk : k < q),
        a (⟨k, hk⟩ : Fin q) = (prop61_finPredMod^[k]) (a z) := by
      intro k
      induction k with
      | zero =>
          intro hk
          have hzEq : z = (⟨0, hk⟩ : Fin q) := by
            apply Fin.ext
            simp [z]
          simp [hzEq]
      | succ k ih =>
          intro hkS
          have hk : k < q := by omega
          rw [Function.iterate_succ_apply', hbackward k hk hkS, ih hk]
    have hLast : q - 1 < q := by omega
    have hPen : q - 2 < q := by omega
    have hlastIter := hiterBackward (q - 1) hLast
    have hpenStep0 := hbackward (q - 2) hPen (by omega)
    have hpenStep : a (⟨q - 1, hLast⟩ : Fin q) =
        prop61_finPredMod (a (⟨q - 2, hPen⟩ : Fin q)) := by
      simpa [show q - 2 + 1 = q - 1 by omega] using hpenStep0
    have hsLast : finSuccMod (⟨q - 1, hLast⟩ : Fin q) = z := by
      apply Fin.ext
      rw [prop61_finSuccMod_val]
      have hnot : ¬ q - 1 + 1 < q := by omega
      rw [if_neg hnot]
    have hstepLast := hstep (⟨q - 1, hLast⟩ : Fin q)
    rw [hsLast] at hstepLast
    rcases hstepLast with hclose | hclose
    · exfalso
      rw [hpenStep, prop61_finSuccMod_finPredMod] at hclose
      have heq := ha hclose
      have hv := congrArg Fin.val heq
      simp [z] at hv
      omega
    · have hiterPred : (prop61_finPredMod^[q]) (a z) =
          prop61_finPredMod ((prop61_finPredMod^[q - 1]) (a z)) := by
        simpa [show q - 1 + 1 = q by omega] using
          (Function.iterate_succ_apply' prop61_finPredMod (q - 1) (a z))
      have hfixedPred : (prop61_finPredMod^[q]) (a z) = a z := by
        rw [hiterPred, ← hlastIter]
        exact hclose.symm
      have hleft : Function.LeftInverse (@finSuccMod n) (@prop61_finPredMod n) :=
        prop61_finSuccMod_finPredMod
      have hc := congrArg (fun x : Fin n => (finSuccMod^[q]) x) hfixedPred
      have hfixed : (finSuccMod^[q]) (a z) = a z :=
        hc.symm.trans (hleft.iterate q (a z))
      exact hlength_of_fixed hfixed

theorem prop61_y_mem_edge_iff {m : ℕ} {i j : Fin (2 * m)} :
    prop61_y i ∈ prop61_edge j ↔ i = j := by
  simp [prop61_edge, prop61_x, prop61_y, prop61_z]

theorem prop61_z_mem_edge_iff {m : ℕ} {i j : Fin (2 * m)} :
    prop61_z i ∈ prop61_edge j ↔ i = j := by
  simp [prop61_edge, prop61_x, prop61_y, prop61_z]

theorem prop61_x_mem_edge_iff {m : ℕ} {i j : Fin (2 * m)} :
    prop61_x i ∈ prop61_edge j ↔ i = j ∨ i = finSuccMod j := by
  simp [prop61_edge, prop61_x, prop61_y, prop61_z]

/-- Alternative index form for \(x_i\) membership in \(E_j\). -/
theorem prop61_x_mem_edge_iff_index {m : ℕ} {i j : Fin (2 * m)} :
    prop61_x i ∈ prop61_edge j ↔ j = i ∨ j = prop61_finPredMod i := by
  constructor
  · intro h
    rcases prop61_x_mem_edge_iff.mp h with h₁ | h₂
    · exact Or.inl h₁.symm
    · exact Or.inr (by
        calc
          j = prop61_finPredMod (finSuccMod j) :=
            (prop61_finPredMod_finSuccMod j).symm
          _ = prop61_finPredMod i := by rw [← h₂])
  · intro h
    rcases h with h₁ | h₂
    · exact prop61_x_mem_edge_iff.mpr (Or.inl h₁.symm)
    · exact prop61_x_mem_edge_iff.mpr (Or.inr (by
        rw [h₂, prop61_finSuccMod_finPredMod]))

/-- The displayed facets are pairwise distinct. -/
theorem prop61_edge_injective (m : ℕ) : Function.Injective (@prop61_edge m) := by
  intro i j hij
  have hy : prop61_y i ∈ prop61_edge j := by
    rw [← hij]
    simp [prop61_edge, prop61_y]
  exact prop61_y_mem_edge_iff.mp hy

/-- The displayed facet set is a clutter. -/
theorem prop61_H_isClutter (m : ℕ) : IsClutter (prop61_H m) := by
  intro E hE F hF hEF
  rcases hE with ⟨i, rfl⟩
  rcases hF with ⟨j, rfl⟩
  have hy : prop61_y i ∈ prop61_edge j := hEF (by simp [prop61_edge, prop61_y])
  have hij : i = j := prop61_y_mem_edge_iff.mp hy
  subst j
  rfl

/-- Each facet has cardinality four when \(m\ge 2\). -/
theorem prop61_edge_card {m : ℕ} (hm : 2 ≤ m) (i : Fin (2 * m)) :
    (prop61_edge i).card = 4 := by
  have hn : 1 < 2 * m := by omega
  have hs : finSuccMod i ≠ i := prop61_finSuccMod_ne_self_of_one_lt hn i
  simp [prop61_edge, prop61_x, prop61_y, prop61_z, hs.symm]

theorem prop61_H_four_uniform {m : ℕ} (hm : 2 ≤ m) :
    ∀ E ∈ prop61_H m, E.card = 4 := by
  rintro E ⟨i, rfl⟩
  exact prop61_edge_card hm i

/-- A facet with its predecessor removed can only meet another facet through its successor. -/
theorem prop61_edge_inter_subset_successor {m : ℕ} {i j : Fin (2 * m)}
    (hji : j ≠ i) (hjpred : j ≠ prop61_finPredMod i) :
    prop61_edge j ∩ prop61_edge i ⊆
      prop61_edge i ∩ prop61_edge (finSuccMod i) := by
  intro a ha
  have hai : a ∈ prop61_edge i := (Finset.mem_inter.mp ha).2
  have haj : a ∈ prop61_edge j := (Finset.mem_inter.mp ha).1
  rcases a with ⟨r, k⟩
  fin_cases r
  · have hxi : prop61_x k ∈ prop61_edge i := by simpa [prop61_x] using hai
    have hxj : prop61_x k ∈ prop61_edge j := by simpa [prop61_x] using haj
    have hxs : prop61_x k ∈ prop61_edge (finSuccMod i) := by
      rcases prop61_x_mem_edge_iff.mp hxi with hki | hki
      · subst k
        rcases prop61_x_mem_edge_iff.mp hxj with hij | his
        · exact False.elim (hji hij.symm)
        · have hjp : j = prop61_finPredMod i := by
            calc
              j = prop61_finPredMod (finSuccMod j) :=
                (prop61_finPredMod_finSuccMod j).symm
              _ = prop61_finPredMod i := (congrArg prop61_finPredMod his).symm
          exact False.elim (hjpred hjp)
      · exact prop61_x_mem_edge_iff.mpr (Or.inl hki)
    exact Finset.mem_inter.mpr ⟨hai, by simpa [prop61_x] using hxs⟩
  · have hyi : prop61_y k ∈ prop61_edge i := by simpa [prop61_y] using hai
    have hyj : prop61_y k ∈ prop61_edge j := by simpa [prop61_y] using haj
    exact False.elim (hji ((prop61_y_mem_edge_iff.mp hyj).symm.trans
      (prop61_y_mem_edge_iff.mp hyi)))
  · have hzi : prop61_z k ∈ prop61_edge i := by simpa [prop61_z] using hai
    have hzj : prop61_z k ∈ prop61_edge j := by simpa [prop61_z] using haj
    exact False.elim (hji ((prop61_z_mem_edge_iff.mp hzj).symm.trans
      (prop61_z_mem_edge_iff.mp hzi)))

/-- Two facets without equal, adjacent, or predecessor indices are disjoint. -/
theorem prop61_edge_inter_empty_of_no_neighbors {m : ℕ} {i j : Fin (2 * m)}
    (hji : j ≠ i) (hjsucc : j ≠ finSuccMod i)
    (hjpred : j ≠ prop61_finPredMod i) :
    prop61_edge j ∩ prop61_edge i = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨a, ha⟩
  have hai : a ∈ prop61_edge i := (Finset.mem_inter.mp ha).2
  have haj : a ∈ prop61_edge j := (Finset.mem_inter.mp ha).1
  rcases a with ⟨r, k⟩
  fin_cases r
  · have hxi : prop61_x k ∈ prop61_edge i := by simpa [prop61_x] using hai
    have hxj : prop61_x k ∈ prop61_edge j := by simpa [prop61_x] using haj
    rcases prop61_x_mem_edge_iff.mp hxi with hki | hki
    · subst k
      rcases prop61_x_mem_edge_iff.mp hxj with hij | his
      · exact hji hij.symm
      · have hjp : j = prop61_finPredMod i := by
          calc
            j = prop61_finPredMod (finSuccMod j) :=
              (prop61_finPredMod_finSuccMod j).symm
            _ = prop61_finPredMod i := (congrArg prop61_finPredMod his).symm
        exact hjpred hjp
    · subst k
      rcases prop61_x_mem_edge_iff.mp hxj with hij | his
      · exact hjsucc hij.symm
      · exact hji (prop61_finSuccMod_injective his).symm
  · have hyi : prop61_y k ∈ prop61_edge i := by simpa [prop61_y] using hai
    have hyj : prop61_y k ∈ prop61_edge j := by simpa [prop61_y] using haj
    exact hji ((prop61_y_mem_edge_iff.mp hyj).symm.trans
      (prop61_y_mem_edge_iff.mp hyi))
  · have hzi : prop61_z k ∈ prop61_edge i := by simpa [prop61_z] using hai
    have hzj : prop61_z k ∈ prop61_edge j := by simpa [prop61_z] using haj
    exact hji ((prop61_z_mem_edge_iff.mp hzj).symm.trans
      (prop61_z_mem_edge_iff.mp hzi))

section Prop61BlockerHelpers
variable {σ : Type*} [DecidableEq σ]
/-- Every transversal contains a minimal one. -/
theorem prop61_exists_minimalTransversal_subset (H : Set (Finset σ)) {T : Finset σ}
    (hT : IsTransversal H T) : ∃ C ∈ blocker H, C ⊆ T := by
  classical
  let S : Finset (Finset σ) := T.powerset.filter (fun U ↦ IsTransversal H U)
  have hTS : T ∈ S := by simp [S, hT]
  obtain ⟨C, hCS, hmin⟩ :=
    Finset.exists_min_image S (fun U ↦ U.card) ⟨T, hTS⟩
  have hCS' := Finset.mem_filter.mp hCS
  have hCT : C ⊆ T := by simpa using hCS'.1
  refine ⟨C, ⟨hCS'.2, ?_⟩, hCT⟩
  intro U hUC hUtrans
  have hUT : U ⊆ T := fun i hi ↦ hCT (hUC.1 hi)
  have hUS : U ∈ S := by simp [S, hUT, hUtrans]
  exact (not_lt_of_ge (hmin U hUS)) (Finset.card_lt_card hUC)

/-- If a set meets every minimal transversal, it contains a member of the clutter. -/
theorem prop61_edge_subset_of_meets_blocker [Fintype σ] (H : Set (Finset σ)) (A : Finset σ)
    (hA : ∀ C ∈ blocker H, (C ∩ A).Nonempty) : ∃ E ∈ H, E ⊆ A := by
  classical
  by_contra hcontra
  have hnone : ∀ E ∈ H, ¬ E ⊆ A := by
    intro E hE hEA
    exact hcontra ⟨E, hE, hEA⟩
  let B : Finset σ := Finset.univ.filter (fun i ↦ i ∉ A)
  have hBtrans : IsTransversal H B := by
    intro E hE
    by_contra hEB
    apply hnone E hE
    intro i hiE
    by_contra hiA
    exact hEB ⟨i, Finset.mem_inter.mpr ⟨hiE, by simp [B, hiA]⟩⟩
  rcases prop61_exists_minimalTransversal_subset H hBtrans with ⟨C, hC, hCB⟩
  rcases hA C hC with ⟨i, hiCA⟩
  have hiC : i ∈ C := (Finset.mem_inter.mp hiCA).1
  have hiA : i ∈ A := (Finset.mem_inter.mp hiCA).2
  have hiB : i ∈ B := hCB hiC
  have hinot : i ∉ A := by simpa [B] using hiB
  exact hinot hiA

/-- Minimal transversals of any clutter form an antichain. -/
theorem prop61_blocker_antichain (H : Set (Finset σ)) :
    ∀ C ∈ blocker H, ∀ D ∈ blocker H, C ⊆ D → C = D := by
  intro C hC D hD hCD
  by_contra hne
  have hnsub : ¬ D ⊆ C := by
    intro hDC
    exact hne (Finset.Subset.antisymm hCD hDC)
  rcases Finset.not_subset.mp hnsub with ⟨i, hiD, hiC⟩
  have hstrict : C ⊂ D := (Finset.ssubset_iff_of_subset hCD).2 ⟨i, hiD, hiC⟩
  exact hD.2 C hstrict hC.1

end Prop61BlockerHelpers
section Prop61ExponentHelpers
variable {σ : Type*} [DecidableEq σ]
theorem prop61_support_characteristicExp (A : Finset σ) :
    (characteristicExp A).support = A := by
  ext i
  by_cases hi : i ∈ A <;> simp [Finsupp.mem_support_iff, characteristicExp_apply, hi]

theorem prop61_characteristicExp_le_iff_subset (A B : Finset σ) :
    characteristicExp A ≤ characteristicExp B ↔ A ⊆ B := by
  constructor
  · intro h i hi
    by_contra hnot
    have h01 : (1 : ℕ) ≤ 0 := by
      simpa [characteristicExp_apply, hi, hnot] using h i
    omega
  · intro hsub i
    by_cases hi : i ∈ A
    · have hiB : i ∈ B := hsub hi
      simp [characteristicExp_apply, hi, hiB]
    · simp [characteristicExp_apply, hi]

theorem prop61_support_diagExp_characteristicExp {d : σ → ℕ} (hd : ∀ i, 0 < d i)
    (A : Finset σ) :
    (diagExp d (characteristicExp A)).support = A := by
  ext i
  by_cases hi : i ∈ A
  · have hd0 : d i ≠ 0 := Nat.ne_of_gt (hd i)
    simp [Finsupp.mem_support_iff, diagExp_apply, characteristicExp_apply, hi, hd0]
  · simp [Finsupp.mem_support_iff, diagExp_apply, characteristicExp_apply, hi]

theorem prop61_diagExp_characteristicExp_le_iff {d : σ → ℕ} (hd : ∀ i, 0 < d i)
    (A B : Finset σ) :
    diagExp d (characteristicExp A) ≤ diagExp d (characteristicExp B) ↔ A ⊆ B := by
  constructor
  · intro h i hi
    by_contra hnot
    have hdle : d i ≤ 0 := by
      simpa [diagExp_apply, characteristicExp_apply, hi, hnot] using h i
    exact (not_lt_of_ge hdle) (hd i)
  · intro hsub i
    have hle := (prop61_characteristicExp_le_iff_subset A B).mpr hsub i
    simpa [diagExp_apply] using Nat.mul_le_mul_right (d i) hle

end Prop61ExponentHelpers
section Prop61PowGensHelpers
variable {σ : Type*}
/-- A repeated generator lies in the corresponding ordinary-power exponent set. -/
theorem prop61_powGens_nsmul_mem {S : Set (σ →₀ ℕ)} {g : σ →₀ ℕ}
    (hg : g ∈ S) : ∀ n : ℕ, n • g ∈ powGens S n := by
  intro n
  induction n with
  | zero => simp [powGens]
  | succ n ih =>
      rw [powGens]
      refine ⟨n • g, ih, g, hg, ?_⟩
      simp [add_nsmul]

/-- Exponent sets of ordinary powers are closed under addition of exponent vectors. -/
theorem prop61_powGens_add {S : Set (σ →₀ ℕ)} {n k : ℕ} {u v : σ →₀ ℕ}
    (hu : u ∈ powGens S n) (hv : v ∈ powGens S k) :
    u + v ∈ powGens S (n + k) := by
  induction k generalizing v with
  | zero =>
      have hv0 : v = 0 := by simpa [powGens] using hv
      subst v
      simpa using hu
  | succ k ih =>
      rw [powGens] at hv
      rcases hv with ⟨v₀, hv₀, s, hs, rfl⟩
      have huv₀ : u + v₀ ∈ powGens S (n + k) := ih hv₀
      rw [Nat.add_succ, powGens]
      exact ⟨u + v₀, huv₀, s, hs, by ac_rfl⟩

end Prop61PowGensHelpers
section Prop61PowGensPrimeHelpers
variable {σ : Type*} [DecidableEq σ]
/-- A generator exponent of a variable prime power contributes one to the component sum. -/
theorem prop61_powGens_prime_sum_le {A : Finset σ} {q : ℕ} {u : σ →₀ ℕ}
    (hu : u ∈ powGens {e : σ →₀ ℕ | ∃ i ∈ A, e = Finsupp.single i (1 : ℕ)} q) :
    q ≤ ∑ i ∈ A, u i := by
  induction q generalizing u with
  | zero =>
      have hu0 : u = 0 := by simpa [powGens] using hu
      subst u
      simp
  | succ q ih =>
      rw [powGens] at hu
      rcases hu with ⟨v, hv, s, hs, huv⟩
      rcases hs with ⟨i, hiA, rfl⟩
      rw [huv]
      have hvi : q ≤ ∑ x ∈ A, v x := ih hv
      have hsingle :
          (∑ x ∈ A, (Finsupp.single i (1 : ℕ) : σ →₀ ℕ) x) = 1 := by
        simpa [Finsupp.single_apply] using
          (Finset.sum_ite_eq_of_mem A i (fun _ : σ => (1 : ℕ)) hiA)
      calc
        q + 1 ≤ (∑ x ∈ A, v x) + 1 := by omega
        _ = ∑ x ∈ A, (v + Finsupp.single i (1 : ℕ) : σ →₀ ℕ) x := by
          simp [Finset.sum_add_distrib, hsingle, Finsupp.add_apply]

end Prop61PowGensPrimeHelpers
section Prop61CountPowGensHelpers
variable {σ ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Any finite count vector gives a sum in the ordinary-power exponent set. -/
theorem prop61_count_sum_mem_powGens {S : Set (σ →₀ ℕ)} {g : ι → σ →₀ ℕ}
    (hg : ∀ i, g i ∈ S) (t : ι → ℕ) :
    (∑ i, t i • g i) ∈ powGens S (∑ i, t i) := by
  classical
  have h : ∀ s : Finset ι, (∑ i ∈ s, t i • g i) ∈ powGens S (∑ i ∈ s, t i) := by
    intro s
    induction s using Finset.induction with
    | empty => simp [powGens]
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        rw [Finset.sum_insert ha]
        exact prop61_powGens_add (prop61_powGens_nsmul_mem (hg a) (t a)) ih
  simpa using h Finset.univ

end Prop61CountPowGensHelpers
/-- The squarefree generators form an antichain because private vertices make the facets a clutter. -/
theorem prop61_char_antichain (m : ℕ) :
    ∀ u ∈ characteristicExp '' prop61_H m, ∀ v ∈ characteristicExp '' prop61_H m,
      u ≤ v → u = v := by
  rintro u ⟨E, hE, rfl⟩ v ⟨F, hF, rfl⟩ huv
  have hEF : E ⊆ F := (prop61_characteristicExp_le_iff_subset E F).mp huv
  have hEq : E = F := (prop61_H_isClutter m) E hE F hF hEF
  subst F
  rfl

/-- The weighted displayed generators form an antichain for positive weights. -/
theorem prop61_weighted_antichain (m : ℕ) {d : prop61_var m → ℕ} (hd : ∀ i, 0 < d i) :
    ∀ u ∈ diagExp d '' (characteristicExp '' prop61_H m),
      ∀ v ∈ diagExp d '' (characteristicExp '' prop61_H m), u ≤ v → u = v := by
  rintro u ⟨u₀, hu₀, rfl⟩ v ⟨v₀, hv₀, rfl⟩ huv
  rcases hu₀ with ⟨E, hE, rfl⟩
  rcases hv₀ with ⟨F, hF, rfl⟩
  have hEF : E ⊆ F := (prop61_diagExp_characteristicExp_le_iff hd E F).mp huv
  have hEq : E = F := (prop61_H_isClutter m) E hE F hF hEF
  subst F
  rfl

section Prop61MonomialHelper
variable {σ K : Type*} [Field K] [DecidableEq σ]
/-- If a displayed monomial generating set is an antichain, it is exactly `minGens`. -/
theorem prop61_minGens_eq_of_antichain {S : Set (σ →₀ ℕ)}
    (hanti : ∀ u ∈ S, ∀ v ∈ S, u ≤ v → u = v) :
    minGens (monomialIdeal S : Ideal (MvPolynomial σ K)) = S := by
  apply Set.Subset.antisymm
  · intro e he
    have heI : (monomial e (1 : K) : MvPolynomial σ K) ∈ monomialIdeal S :=
      (mem_minGens.mp he).1
    rcases monomial_mem_monomialIdeal.mp heI with ⟨u, huS, hue⟩
    have huI : (monomial u (1 : K) : MvPolynomial σ K) ∈ monomialIdeal S :=
      monomial_mem_monomialIdeal.mpr ⟨u, huS, le_rfl⟩
    have hueq : u = e := (mem_minGens.mp he).2 u huI hue
    simpa [hueq] using huS
  · intro e heS
    rw [mem_minGens]
    refine ⟨monomial_mem_monomialIdeal.mpr ⟨e, heS, le_rfl⟩, ?_⟩
    intro u huI hue
    rcases monomial_mem_monomialIdeal.mp huI with ⟨v, hvS, hvu⟩
    have hveq : v = e := hanti v hvS e heS (le_trans hvu hue)
    exact le_antisymm hue (by simpa [hveq] using hvu)

/-- A minimal generator of a squarefree monomial ideal is a characteristic exponent. -/
theorem prop61_minGen_eq_characteristicExp_of_squarefree
    {I : Ideal (MvPolynomial σ K)} (hI : IsSquarefreeMonomialIdeal I)
    {g : σ →₀ ℕ} (hg : g ∈ minGens I) :
    ∃ A : Finset σ, g = characteristicExp A := by
  rcases hI with ⟨H, hEq⟩
  have hg' : g ∈ minGens
      (monomialIdeal (K := K) (characteristicExp '' H) :
        Ideal (MvPolynomial σ K)) := by
    simpa [hEq] using hg
  have hgMem : (monomial g (1 : K) : MvPolynomial σ K) ∈
      monomialIdeal (characteristicExp '' H) := (mem_minGens.mp hg').1
  rcases monomial_mem_monomialIdeal.mp hgMem with ⟨u, hu, hug⟩
  rcases hu with ⟨A, hA, rfl⟩
  have hcharMem : (monomial (characteristicExp A) (1 : K) : MvPolynomial σ K) ∈
      monomialIdeal (characteristicExp '' H) :=
    monomial_mem_monomialIdeal.mpr ⟨characteristicExp A, ⟨A, hA, rfl⟩, le_rfl⟩
  have hAeq : characteristicExp A = g :=
    (mem_minGens.mp hg').2 (characteristicExp A) hcharMem hug
  exact ⟨A, hAeq.symm⟩

end Prop61MonomialHelper
section Prop61Ideals
variable {K : Type*} [Field K]
/-- The displayed squarefree generators are exactly the minimal generators of `J_m`. -/
theorem prop61_minGens_J (m : ℕ) :
    minGens (prop61_J (K := K) m) = characteristicExp '' prop61_H m := by
  simpa [prop61_J] using
    prop61_minGens_eq_of_antichain (K := K)
      (S := characteristicExp '' prop61_H m) (prop61_char_antichain m)

/-- The displayed weighted generators are exactly the minimal generators of `I_{m,d}`. -/
theorem prop61_minGens_I (m : ℕ) {d : prop61_var m → ℕ} (hd : ∀ i, 0 < d i) :
    minGens (prop61_I (K := K) m d) = diagExp d '' (characteristicExp '' prop61_H m) := by
  simpa [prop61_I] using
    prop61_minGens_eq_of_antichain (K := K)
      (S := diagExp d '' (characteristicExp '' prop61_H m)) (prop61_weighted_antichain m hd)

/-- The root is squarefree by construction. -/
theorem prop61_J_isSquarefree (m : ℕ) :
    IsSquarefreeMonomialIdeal (prop61_J (K := K) m) := by
  exact ⟨prop61_H m, rfl⟩

/-- Weighting by the all-one vector gives the root ideal. -/
theorem prop61_I_one (m : ℕ) :
    prop61_I (K := K) m (fun _ : prop61_var m => 1) = prop61_J (K := K) m := by
  rw [prop61_I, prop61_J]
  apply congrArg (fun S : Set (prop61_var m →₀ ℕ) =>
    (monomialIdeal (K := K) S : Ideal (MvPolynomial (prop61_var m) K)))
  ext e
  constructor
  · rintro ⟨u, hu, rfl⟩
    rcases hu with ⟨E, hE, rfl⟩
    refine ⟨E, hE, ?_⟩
    ext i
    simp [diagExp_apply]
  · rintro ⟨E, hE, rfl⟩
    refine ⟨characteristicExp E, ⟨E, hE, rfl⟩, ?_⟩
    ext i
    simp [diagExp_apply]

/-- The positive diagonal weighting is squarefree exactly for the all-one weights. -/
theorem prop61_I_isSquarefree_iff (m : ℕ) {d : prop61_var m → ℕ} (hd : ∀ i, 0 < d i) :
    IsSquarefreeMonomialIdeal (prop61_I (K := K) m d) ↔
      d = fun _ : prop61_var m => 1 := by
  constructor
  · intro hsq
    funext v
    by_contra hvne
    have hvpos : 0 < d v := hd v
    have hvge : 2 ≤ d v := by omega
    let g : prop61_var m →₀ ℕ := diagExp d (characteristicExp (prop61_edge v.2))
    have hmin : g ∈ minGens (prop61_I (K := K) m d) := by
      rw [prop61_minGens_I (K := K) m hd]
      refine ⟨characteristicExp (prop61_edge v.2), ?_, rfl⟩
      exact ⟨prop61_edge v.2, ⟨v.2, rfl⟩, rfl⟩
    rcases prop61_minGen_eq_characteristicExp_of_squarefree hsq hmin with ⟨A, hgA⟩
    have hgv : g v = d v := by
      simp [g, diagExp_apply, characteristicExp_apply, prop61_var_mem_own_edge v]
    have hle : g v ≤ 1 := by
      rw [hgA]
      by_cases hvA : v ∈ A <;> simp [characteristicExp_apply, hvA]
    omega
  · intro hdEq
    rw [hdEq]
    simpa [prop61_I_one (K := K) m] using prop61_J_isSquarefree (K := K) m

/-- A nonconstant positive weighting is not squarefree. -/
theorem prop61_I_not_squarefree_of_ne_one {m : ℕ} (hm : 2 ≤ m)
    {d : prop61_var m → ℕ} (hd : ∀ i, 0 < d i)
    (hdne : d ≠ fun _ : prop61_var m => 1) :
    ¬ IsSquarefreeMonomialIdeal (prop61_I (K := K) m d) := by
  have _ := hm
  intro hsq
  exact hdne ((prop61_I_isSquarefree_iff (K := K) m hd).mp hsq)

/-- Both displayed ideals are monomial ideals. -/
theorem prop61_I_isMonomial (m : ℕ) (d : prop61_var m → ℕ) :
    IsMonomialIdeal (prop61_I (K := K) m d) := by
  exact ⟨diagExp d '' (characteristicExp '' prop61_H m), rfl⟩

/-- `I_{m,d}` is the diagonal image of `J_m`. -/
theorem prop61_I_eq_diagonal (m : ℕ) (d : prop61_var m → ℕ) :
    prop61_I (K := K) m d = diagonal d (prop61_J (K := K) m) := by
  let _ : Fintype (prop61_var m) := prop61_varFintype m
  rw [prop61_I, prop61_J, diagonal_monomialIdeal]

/-- Support complex of `J_m`. -/
theorem prop61_supportComplex_J (m : ℕ) :
    supportComplex (prop61_J (K := K) m) = prop61_H m := by
  ext E
  constructor
  · intro hE
    change ∃ e ∈ minGens (prop61_J (K := K) m), e.support = E at hE
    rcases hE with ⟨e, heMin, hsupp⟩
    have heS : e ∈ characteristicExp '' prop61_H m := by
      simpa [prop61_minGens_J (K := K) m] using heMin
    rcases heS with ⟨F, hFH, rfl⟩
    have hF : (characteristicExp F).support = F := prop61_support_characteristicExp F
    rw [hF] at hsupp
    simpa [← hsupp] using hFH
  · intro hE
    change ∃ e ∈ minGens (prop61_J (K := K) m), e.support = E
    rcases hE with ⟨i, rfl⟩
    refine ⟨characteristicExp (prop61_edge i), ?_, prop61_support_characteristicExp _⟩
    rw [prop61_minGens_J (K := K) m]
    exact ⟨prop61_edge i, ⟨i, rfl⟩, rfl⟩

/-- Support complex of `I_{m,d}`; positive weighting preserves supports. -/
theorem prop61_supportComplex_I (m : ℕ) {d : prop61_var m → ℕ} (hd : ∀ i, 0 < d i) :
    supportComplex (prop61_I (K := K) m d) = prop61_H m := by
  ext E
  constructor
  · intro hE
    change ∃ e ∈ minGens (prop61_I (K := K) m d), e.support = E at hE
    rcases hE with ⟨e, heMin, hsupp⟩
    have heS : e ∈ diagExp d '' (characteristicExp '' prop61_H m) := by
      simpa [prop61_minGens_I (K := K) m hd] using heMin
    rcases heS with ⟨e₀, ⟨F, hFH, rfl⟩, rfl⟩
    have hF : (diagExp d (characteristicExp F)).support = F :=
      prop61_support_diagExp_characteristicExp hd F
    rw [hF] at hsupp
    simpa [← hsupp] using hFH
  · intro hE
    change ∃ e ∈ minGens (prop61_I (K := K) m d), e.support = E
    rcases hE with ⟨i, rfl⟩
    refine ⟨diagExp d (characteristicExp (prop61_edge i)), ?_,
      prop61_support_diagExp_characteristicExp hd _⟩
    rw [prop61_minGens_I (K := K) m hd]
    exact ⟨characteristicExp (prop61_edge i), ⟨prop61_edge i, ⟨i, rfl⟩, rfl⟩, rfl⟩

/-- No minimal generator of \(J_m\) has support size at most three. -/
theorem prop61_minGens_J_support_card_gt_three {m : ℕ} (hm : 2 ≤ m) :
    ∀ e ∈ minGens (prop61_J (K := K) m), 3 < e.support.card := by
  intro e he
  have heS : e ∈ characteristicExp '' prop61_H m := by
    simpa [prop61_minGens_J (K := K) m] using he
  rcases heS with ⟨E, hE, rfl⟩
  rw [prop61_support_characteristicExp]
  have h4 : E.card = 4 := prop61_H_four_uniform hm E hE
  omega

/-- No minimal generator of \(I_{m,d}\) has support size at most three. -/
theorem prop61_minGens_I_support_card_gt_three {m : ℕ} (hm : 2 ≤ m)
    {d : prop61_var m → ℕ} (hd : ∀ i, 0 < d i) :
    ∀ e ∈ minGens (prop61_I (K := K) m d), 3 < e.support.card := by
  intro e he
  have heS : e ∈ diagExp d '' (characteristicExp '' prop61_H m) := by
    simpa [prop61_minGens_I (K := K) m hd] using he
  rcases heS with ⟨u, ⟨E, hE, rfl⟩, rfl⟩
  rw [prop61_support_diagExp_characteristicExp hd E]
  have h4 : E.card = 4 := prop61_H_four_uniform hm E hE
  omega

/-- The diagonal representation without any Simis hypothesis. -/
theorem prop61_hasSqRoot (m : ℕ) {d : prop61_var m → ℕ} (hd : ∀ i, 0 < d i) :
    HasSqRoot (prop61_I (K := K) m d) := by
  refine ⟨prop61_J (K := K) m, d, prop61_J_isSquarefree m, hd, ?_⟩
  exact (prop61_I_eq_diagonal (K := K) m d).symm

/-- Explicit enumeration of minimal covers by an ambient powerset. -/
@[instance_reducible] noncomputable def prop61_componentIndexFintype (m : ℕ) :
    Fintype (prop61_componentIndex m) := by
  classical
  letI : Fintype (prop61_var m) := prop61_varFintype m
  refine Fintype.ofFinset ((Finset.univ : Finset (prop61_var m)).powerset.filter
    (fun C ↦ C ∈ blocker (prop61_H m))) ?_
  intro C
  simp

/-- Membership of an arbitrary polynomial in a pure-power component, supportwise. -/
theorem prop61_mem_purePower {σ : Type*} [DecidableEq σ] {A : Finset σ}
    {a : σ → ℕ} {p : MvPolynomial σ K} :
    p ∈ (purePower A a : Ideal (MvPolynomial σ K)) ↔
      ∀ e ∈ p.support, ∃ i ∈ A, a i ≤ e i := by
  rw [purePower, mem_monomialIdeal]
  constructor
  · intro hp e he
    rcases hp e he with ⟨u, ⟨i, hiA, rfl⟩, hue⟩
    exact ⟨i, hiA, Finsupp.single_le_iff.mp hue⟩
  · intro hp e he
    rcases hp e he with ⟨i, hiA, hai⟩
    exact ⟨Finsupp.single i (a i), ⟨i, hiA, rfl⟩, Finsupp.single_le_iff.mpr hai⟩

/-- The squarefree facet ideal is the intersection of the primes on minimal covers. -/
theorem prop61_J_hasComponents (m : ℕ) :
    HasComponents (prop61_J (K := K) m) (fun C : prop61_componentIndex m => C.1)
      (fun _ _ => 1) := by
  classical
  let _ : Fintype (prop61_var m) := prop61_varFintype m
  change prop61_J (K := K) m =
    ⨅ C : prop61_componentIndex m,
      (purePower C.1 (fun _ : prop61_var m => 1) : Ideal (MvPolynomial (prop61_var m) K))
  rw [prop61_J]
  apply le_antisymm
  · rw [monomialIdeal, Ideal.span_le]
    rintro y ⟨e, he, rfl⟩
    rcases he with ⟨E, hEH, rfl⟩
    exact Ideal.mem_iInf.mpr (fun C => by
      rw [monomial_mem_purePower]
      rcases C.property.1 E hEH with ⟨i, hiCE⟩
      have hiE : i ∈ E := (Finset.mem_inter.mp hiCE).1
      have hiC : i ∈ C.1 := (Finset.mem_inter.mp hiCE).2
      exact ⟨i, hiC, by simp [characteristicExp_apply, hiE]⟩)
  · intro p hp
    rw [mem_monomialIdeal]
    intro e heSupp
    have hmono (C : prop61_componentIndex m) :
        ∃ i ∈ C.1, 1 ≤ e i := by
      exact (prop61_mem_purePower.mp ((Ideal.mem_iInf.mp hp) C)) e heSupp
    have hmeets : ∀ C ∈ blocker (prop61_H m), (C ∩ e.support).Nonempty := by
      intro C hC
      rcases hmono ⟨C, hC⟩ with ⟨i, hiC, hie⟩
      have hine : e i ≠ 0 := by omega
      exact ⟨i, Finset.mem_inter.mpr ⟨hiC, by simpa [Finsupp.mem_support_iff] using hine⟩⟩
    rcases prop61_edge_subset_of_meets_blocker (prop61_H m) e.support hmeets with
      ⟨E, hEH, hEsub⟩
    refine ⟨characteristicExp E, ⟨E, hEH, rfl⟩, ?_⟩
    intro i
    by_cases hiE : i ∈ E
    · have hiSupp : i ∈ e.support := hEsub hiE
      have hine : e i ≠ 0 := by simpa [Finsupp.mem_support_iff] using hiSupp
      have hle : 1 ≤ e i := by omega
      simpa [characteristicExp_apply, hiE] using hle
    · simp [characteristicExp_apply, hiE]

/-- Positive diagonal weighting preserves the minimal-cover component decomposition. -/
theorem prop61_I_hasComponents (m : ℕ) {d : prop61_var m → ℕ} :
    HasComponents (prop61_I (K := K) m d) (fun C : prop61_componentIndex m => C.1)
      (fun _ i => d i) := by
  classical
  let _ : Fintype (prop61_var m) := prop61_varFintype m
  change prop61_I (K := K) m d =
    ⨅ C : prop61_componentIndex m,
      (purePower C.1 (fun i : prop61_var m => d i) : Ideal (MvPolynomial (prop61_var m) K))
  rw [prop61_I]
  apply le_antisymm
  · rw [monomialIdeal, Ideal.span_le]
    rintro y ⟨e, he, rfl⟩
    rcases he with ⟨u, hu, rfl⟩
    rcases hu with ⟨E, hEH, rfl⟩
    exact Ideal.mem_iInf.mpr (fun C => by
      rw [monomial_mem_purePower]
      rcases C.property.1 E hEH with ⟨i, hiCE⟩
      have hiE : i ∈ E := (Finset.mem_inter.mp hiCE).1
      have hiC : i ∈ C.1 := (Finset.mem_inter.mp hiCE).2
      exact ⟨i, hiC, by simp [diagExp_apply, characteristicExp_apply, hiE]⟩)
  · intro p hp
    rw [mem_monomialIdeal]
    intro e heSupp
    have hmono (C : prop61_componentIndex m) : ∃ i ∈ C.1, d i ≤ e i := by
      exact (prop61_mem_purePower.mp ((Ideal.mem_iInf.mp hp) C)) e heSupp
    let B : Finset (prop61_var m) := Finset.univ.filter (fun i ↦ d i ≤ e i)
    have hmeets : ∀ C ∈ blocker (prop61_H m), (C ∩ B).Nonempty := by
      intro C hC
      rcases hmono ⟨C, hC⟩ with ⟨i, hiC, hde⟩
      exact ⟨i, Finset.mem_inter.mpr ⟨hiC, by simp [B, hde]⟩⟩
    rcases prop61_edge_subset_of_meets_blocker (prop61_H m) B hmeets with ⟨E, hEH, hEsub⟩
    refine ⟨diagExp d (characteristicExp E), ?_, ?_⟩
    · exact ⟨characteristicExp E, ⟨E, hEH, rfl⟩, rfl⟩
    · intro i
      by_cases hiE : i ∈ E
      · have hiB : i ∈ B := hEsub hiE
        have hde : d i ≤ e i := by simpa [B] using hiB
        simpa [diagExp_apply, characteristicExp_apply, hiE] using hde
      · simp [diagExp_apply, characteristicExp_apply, hiE]

/-- The supports of minimal covers are pairwise incomparable. -/
theorem prop61_components_supportsAntichain (m : ℕ)
    {a : prop61_componentIndex m → prop61_var m → ℕ} :
    SupportsAntichain (fun C : prop61_componentIndex m => C.1) a := by
  rw [SupportsAntichain]
  intro C D hCD
  apply Subtype.ext
  exact prop61_blocker_antichain (prop61_H m) C.1 C.property D.1 D.property hCD

/-- Every component has a monomial witness omitting it from the other components. -/
theorem prop61_components_isIrredundant (m : ℕ) {a : prop61_var m → ℕ}
    (ha : ∀ i, 0 < a i) :
    IsIrredundant (K := K) (fun C : prop61_componentIndex m => C.1) (fun _ i => a i) := by
  classical
  rw [IsIrredundant]
  intro C
  let _ : Fintype (prop61_componentIndex m) := prop61_componentIndexFintype m
  let _ : Fintype {D : prop61_componentIndex m // D ≠ C} :=
    Fintype.ofFinset ((Finset.univ : Finset (prop61_componentIndex m)).filter (fun D ↦ D ≠ C))
      (by
        intro D
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rfl)
  have hchoice : ∀ D : {D : prop61_componentIndex m // D ≠ C},
      ∃ v : prop61_var m, v ∈ D.1.1 ∧ v ∉ C.1 := by
    intro D
    have hnsub : ¬ D.1.1 ⊆ C.1 := by
      intro hsub
      have heq : D.1 = C := by
        apply Subtype.ext
        exact prop61_blocker_antichain (prop61_H m) D.1.1 D.1.property C.1 C.property hsub
      exact D.2 heq
    exact Finset.not_subset.mp hnsub
  choose v hv_mem hv_not using hchoice
  let W : Finset (prop61_var m) := Finset.univ.image v
  let e : prop61_var m →₀ ℕ := diagExp a (characteristicExp W)
  have hW_mem (D : {D : prop61_componentIndex m // D ≠ C}) : v D ∈ W := by
    exact Finset.mem_image.mpr ⟨D, by simp, rfl⟩
  have hW_disjoint {i : prop61_var m} (hi : i ∈ W) : i ∉ C.1 := by
    rcases Finset.mem_image.mp hi with ⟨D, _, hDi⟩
    rw [← hDi]
    exact hv_not D
  have hOmit : (monomial e (1 : K) : MvPolynomial (prop61_var m) K) ∈
      decompOmit (fun C : prop61_componentIndex m => C.1) (fun _ i => a i) C := by
    rw [decompOmit, Ideal.mem_iInf]
    intro D
    rw [monomial_mem_purePower]
    refine ⟨v D, hv_mem D, ?_⟩
    simp [e, diagExp_apply, characteristicExp_apply, hW_mem D]
  intro hle
  have htarget := hle hOmit
  rcases monomial_mem_purePower.mp htarget with ⟨i, hiC, hai⟩
  have hiW : i ∈ W := by
    by_contra hnot
    have hzero : e i = 0 := by simp [e, diagExp_apply, characteristicExp_apply, hnot]
    rw [hzero] at hai
    exact (not_lt_of_ge hai) (ha i)
  exact (hW_disjoint hiW) hiC

/-- Both blocker decompositions exist, are irredundant, and have incomparable supports. -/
theorem prop61_decompositionInput (m : ℕ) {d : prop61_var m → ℕ} (hd : ∀ i, 0 < d i) :
    prop61_DecompositionInput (K := K) m d := by
  exact ⟨prop61_J_hasComponents (K := K) m,
    prop61_components_isIrredundant (K := K) m (a := fun _ => 1) (by simp),
    prop61_components_supportsAntichain m (a := fun _ _ => 1),
    prop61_I_hasComponents (K := K) m,
    prop61_components_isIrredundant (K := K) m (a := d) hd,
    prop61_components_supportsAntichain m (a := fun _ i => d i)⟩

/-- The weighted ideal has the squarefree facet ideal as its radical. -/
theorem prop61_radical_I_eq_J (m : ℕ) {d : prop61_var m → ℕ} (hd : ∀ i, 0 < d i) :
    (prop61_I (K := K) m d).radical = prop61_J (K := K) m := by
  classical
  let _ : Fintype (prop61_componentIndex m) := prop61_componentIndexFintype m
  have hJ : prop61_J (K := K) m =
      ⨅ C : prop61_componentIndex m,
        (purePower C.1 (fun _ : prop61_var m => 1) : Ideal (MvPolynomial (prop61_var m) K)) := by
    exact prop61_J_hasComponents (K := K) m
  have hI : prop61_I (K := K) m d =
      ⨅ C : prop61_componentIndex m,
        (purePower C.1 (fun i : prop61_var m => d i) : Ideal (MvPolynomial (prop61_var m) K)) := by
    exact prop61_I_hasComponents (K := K) m
  calc
    (prop61_I (K := K) m d).radical =
        (⨅ C : prop61_componentIndex m,
          purePower C.1 (fun i : prop61_var m => d i)).radical :=
      congrArg (fun L : Ideal (MvPolynomial (prop61_var m) K) ↦ L.radical) hI
    _ = ⨅ C : prop61_componentIndex m,
          (purePower C.1 (fun i : prop61_var m => d i)).radical := by
      exact radical_iInf_fintype
        (I := fun C : prop61_componentIndex m =>
          (purePower C.1 (fun i : prop61_var m => d i) : Ideal (MvPolynomial (prop61_var m) K)))
    _ = ⨅ C : prop61_componentIndex m,
          purePower C.1 (fun _ : prop61_var m => 1) := by
      apply iInf_congr
      intro C
      simpa [primeOf] using
        (purePower_radical_eq_primeOf (K := K) (A := C.1) (a := fun i => d i)
          (fun i _ => hd i))
    _ = prop61_J (K := K) m := hJ.symm

/-- Equation (2) for the squarefree blocker decomposition. -/
theorem prop61_stdSymbolic_J (m : ℕ) :
    HasStdSymbolicFormula (prop61_J (K := K) m)
      (fun C : prop61_componentIndex m =>
        (purePower C.1 (fun _ : prop61_var m => 1) : Ideal (MvPolynomial (prop61_var m) K))) := by
  classical
  let _ : Fintype (prop61_componentIndex m) := prop61_componentIndexFintype m
  exact eq2_standardSymbolic
    (I := prop61_J (K := K) m)
    (A := fun C : prop61_componentIndex m => C.1)
    (a := fun _ _ => 1)
    ⟨prop61_J_hasComponents (K := K) m,
      prop61_components_isIrredundant (K := K) m (a := fun _ => 1) (by simp)⟩
    (prop61_components_supportsAntichain m (a := fun _ _ => 1))

/-- Equation (2) for the weighted blocker decomposition. -/
theorem prop61_stdSymbolic_I (m : ℕ) {d : prop61_var m → ℕ} (hd : ∀ i, 0 < d i) :
    HasStdSymbolicFormula (prop61_I (K := K) m d)
      (fun C : prop61_componentIndex m =>
        (purePower C.1 (fun i : prop61_var m => d i) :
          Ideal (MvPolynomial (prop61_var m) K))) := by
  classical
  let _ : Fintype (prop61_componentIndex m) := prop61_componentIndexFintype m
  exact eq2_standardSymbolic
    (I := prop61_I (K := K) m d)
    (A := fun C : prop61_componentIndex m => C.1)
    (a := fun _ i => d i)
    ⟨prop61_I_hasComponents (K := K) m,
      prop61_components_isIrredundant (K := K) m (a := d) hd⟩
    (prop61_components_supportsAntichain m (a := fun _ i => d i))

/-- A strong cycle's vertex sequence follows incidence of the underlying cyclic \(x\)-vertices. -/
theorem prop61_strongCycle_indexMap {m q : ℕ} (hm : 2 ≤ m)
    (hc : HasStrongCycle (prop61_H m) q) :
    ∃ a : Fin q → Fin (2 * m), Function.Injective a ∧
      ∀ i : Fin q,
        a (finSuccMod i) = finSuccMod (a i) ∨
          a (finSuccMod i) = prop61_finPredMod (a i) := by
  classical
  have hn : 1 < 2 * m := by omega
  rcases hc with ⟨hq3, v, hv_inj, E, hE_inj, hE_mem, hcut⟩
  have hq1 : 1 < q := by omega
  choose e he using hE_mem
  have hv_current (i : Fin q) : v i ∈ E i := by
    have h : v i ∈ E i ∩ (Finset.univ.image v) := by
      rw [hcut i]
      simp
    exact (Finset.mem_inter.mp h).1
  have hv_previous (i : Fin q) : v i ∈ E (prop61_finPredMod i) := by
    have h : v i ∈ E (prop61_finPredMod i) ∩ (Finset.univ.image v) := by
      rw [hcut (prop61_finPredMod i)]
      simp [prop61_finSuccMod_finPredMod]
    exact (Finset.mem_inter.mp h).1
  have hsuccNe (i : Fin q) : finSuccMod i ≠ i :=
    prop61_finSuccMod_ne_self_of_one_lt hq1 i
  have hpredNe (i : Fin q) : prop61_finPredMod i ≠ i := by
    intro hp
    have hs : finSuccMod i = i := by
      simpa [hp] using prop61_finSuccMod_finPredMod i
    exact hsuccNe i hs
  have hv_x : ∀ i : Fin q, ∃ k : Fin (2 * m), v i = prop61_x k := by
    intro i
    rcases hvi : v i with ⟨r, k⟩
    fin_cases r
    · exact ⟨k, by simp [prop61_x]⟩
    · exfalso
      have hyCur : prop61_y k ∈ prop61_edge (e i) := by
        have hy := hv_current i
        rw [hvi] at hy
        change prop61_y k ∈ E i at hy
        rw [← he i] at hy
        exact hy
      have hyPrev : prop61_y k ∈ prop61_edge (e (prop61_finPredMod i)) := by
        have hy := hv_previous i
        rw [hvi] at hy
        change prop61_y k ∈ E (prop61_finPredMod i) at hy
        rw [← he (prop61_finPredMod i)] at hy
        exact hy
      have hki : k = e i := prop61_y_mem_edge_iff.mp hyCur
      have hkp : k = e (prop61_finPredMod i) := prop61_y_mem_edge_iff.mp hyPrev
      have heeq : e i = e (prop61_finPredMod i) := hki.symm.trans hkp
      have hEeq : E i = E (prop61_finPredMod i) := by
        calc
          E i = prop61_edge (e i) := (he i).symm
          _ = prop61_edge (e (prop61_finPredMod i)) := by rw [heeq]
          _ = E (prop61_finPredMod i) := he (prop61_finPredMod i)
      exact hpredNe i (hE_inj hEeq).symm
    · exfalso
      have hzCur : prop61_z k ∈ prop61_edge (e i) := by
        have hz := hv_current i
        rw [hvi] at hz
        change prop61_z k ∈ E i at hz
        rw [← he i] at hz
        exact hz
      have hzPrev : prop61_z k ∈ prop61_edge (e (prop61_finPredMod i)) := by
        have hz := hv_previous i
        rw [hvi] at hz
        change prop61_z k ∈ E (prop61_finPredMod i) at hz
        rw [← he (prop61_finPredMod i)] at hz
        exact hz
      have hki : k = e i := prop61_z_mem_edge_iff.mp hzCur
      have hkp : k = e (prop61_finPredMod i) := prop61_z_mem_edge_iff.mp hzPrev
      have heeq : e i = e (prop61_finPredMod i) := hki.symm.trans hkp
      have hEeq : E i = E (prop61_finPredMod i) := by
        calc
          E i = prop61_edge (e i) := (he i).symm
          _ = prop61_edge (e (prop61_finPredMod i)) := by rw [heeq]
          _ = E (prop61_finPredMod i) := he (prop61_finPredMod i)
      exact hpredNe i (hE_inj hEeq).symm
  choose a ha using hv_x
  have ha_inj : Function.Injective a := by
    intro i j hij
    apply hv_inj
    rw [ha i, ha j, hij]
  refine ⟨a, ha_inj, ?_⟩
  intro i
  have hanes : a i ≠ a (finSuccMod i) := by
    intro h
    exact hsuccNe i (ha_inj h).symm
  have hviE : prop61_x (a i) ∈ prop61_edge (e i) := by
    have h := hv_current i
    rw [ha i] at h
    rw [← he i] at h
    exact h
  have hvsE : prop61_x (a (finSuccMod i)) ∈ prop61_edge (e i) := by
    have h : v (finSuccMod i) ∈ E i ∩ (Finset.univ.image v) := by
      rw [hcut i]
      simp
    have hE : v (finSuccMod i) ∈ E i := (Finset.mem_inter.mp h).1
    rw [ha (finSuccMod i)] at hE
    rw [← he i] at hE
    exact hE
  rcases prop61_x_mem_edge_iff.mp hviE with hi | hi
  · rcases prop61_x_mem_edge_iff.mp hvsE with hs | hs
    · exact False.elim (hanes (hi.trans hs.symm))
    · exact Or.inl (by rw [hi, hs])
  · rcases prop61_x_mem_edge_iff.mp hvsE with hs | hs
    · exact Or.inr (by rw [hi, prop61_finPredMod_finSuccMod]; exact hs)
    · exact False.elim (hanes (hi.trans hs.symm))

/-- A nonempty proper subfamily has a first facet in one of its cyclic runs. -/
theorem prop61_proper_subfamily_endpoint {m : ℕ} (hm : 2 ≤ m)
    {K : Set (Finset (prop61_var m))} (hK : K ⊂ prop61_H m) (hKne : K.Nonempty) :
    ∃ i : Fin (2 * m), prop61_edge i ∈ K ∧ prop61_edge (prop61_finPredMod i) ∉ K := by
  classical
  have hn : 1 < 2 * m := by omega
  rcases hKne with ⟨E, hEK⟩
  rcases hK.1 hEK with ⟨i₀, rfl⟩
  have hKneH : K ≠ prop61_H m := ne_of_lt hK
  have hmissing : ∃ r : Fin (2 * m), prop61_edge r ∉ K := by
    by_contra h
    apply hKneH
    ext F
    constructor
    · intro hFK
      exact hK.1 hFK
    · intro hFH
      rcases hFH with ⟨r, rfl⟩
      by_contra hr
      exact h ⟨r, hr⟩
  rcases hmissing with ⟨r, hr⟩
  by_contra hno
  have hclosed : ∀ i : Fin (2 * m), prop61_edge i ∈ K →
      prop61_edge (prop61_finPredMod i) ∈ K := by
    intro i hi
    by_contra hp
    exact hno ⟨i, hi, hp⟩
  have hIter : ∀ k (i : Fin (2 * m)), prop61_edge i ∈ K →
      prop61_edge ((prop61_finPredMod^[k]) i) ∈ K := by
    intro k
    induction k with
    | zero =>
        intro i hi
        simpa using hi
    | succ k ih =>
        intro i hi
        rw [Function.iterate_succ_apply']
        exact hclosed _ (ih i hi)
  let z : Fin (2 * m) := ⟨0, by omega⟩
  have hleft : Function.LeftInverse (@prop61_finPredMod (2 * m)) (@finSuccMod (2 * m)) :=
    prop61_finPredMod_finSuccMod
  have hzIter : (finSuccMod^[i₀.val]) z = i₀ := by
    apply Fin.ext
    rw [prop61_finSuccMod_iterate_val hn]
    simp [z, Nat.mod_eq_of_lt i₀.isLt]
  have hpIterZ : (prop61_finPredMod^[i₀.val]) i₀ = z := by
    have hc := congrArg (fun x : Fin (2 * m) => (prop61_finPredMod^[i₀.val]) x) hzIter
    exact hc.symm.trans (hleft.iterate i₀.val z)
  have hz : prop61_edge z ∈ K := by
    have hmem := hIter i₀.val i₀ hEK
    simpa [hpIterZ] using hmem
  rcases Nat.eq_zero_or_pos r.val with hr0 | hrpos
  · have hrz : r = z := by
      apply Fin.ext
      simp [z, hr0]
    exact hr (by simpa [hrz] using hz)
  · let t : ℕ := 2 * m - r.val
    have hrIter : (finSuccMod^[t]) r = z := by
      apply Fin.ext
      rw [prop61_finSuccMod_iterate_val hn]
      have hsum : r.val + t = 2 * m := by
        simp only [t]
        omega
      simp [z, hsum]
    have hpIterR : (prop61_finPredMod^[t]) z = r := by
      have hc := congrArg (fun x : Fin (2 * m) => (prop61_finPredMod^[t]) x) hrIter
      exact hc.symm.trans (hleft.iterate t r)
    have hrmem := hIter t z hz
    exact hr (by simpa [hpIterR] using hrmem)

/-- An endpoint facet of a proper subfamily is a Faridi leaf. -/
theorem prop61_proper_subfamily_hasLeaf {m : ℕ} (hm : 2 ≤ m)
    {K : Set (Finset (prop61_var m))} (hK : K ⊂ prop61_H m) (hKne : K.Nonempty) :
    ∃ E ∈ K, IsLeaf K E := by
  classical
  have hn : 1 < 2 * m := by omega
  rcases prop61_proper_subfamily_endpoint hm hK hKne with ⟨i, hiK, hpnot⟩
  refine ⟨prop61_edge i, hiK, ?_⟩
  rw [IsLeaf]
  refine ⟨hiK, ?_⟩
  by_cases hall : ∀ G ∈ K, G = prop61_edge i
  · exact Or.inl hall
  · have hother : ∃ G ∈ K, G ≠ prop61_edge i := by
      by_contra h
      apply hall
      intro G hG
      by_contra hGne
      exact h ⟨G, hG, hGne⟩
    rcases hother with ⟨G, hGK, hGne⟩
    right
    by_cases hsucc : prop61_edge (finSuccMod i) ∈ K
    · have hSn : prop61_edge (finSuccMod i) ≠ prop61_edge i := by
        intro hEq
        exact (prop61_finSuccMod_ne_self_of_one_lt hn i) (prop61_edge_injective m hEq)
      refine ⟨prop61_edge (finSuccMod i), hsucc, hSn, ?_⟩
      intro F hFK hFne
      rcases hK.1 hFK with ⟨j, rfl⟩
      have hji : j ≠ i := by
        intro h; subst j; exact hFne rfl
      have hjp : j ≠ prop61_finPredMod i := by
        intro h; subst j; exact hpnot hFK
      exact prop61_edge_inter_subset_successor hji hjp
    · refine ⟨G, hGK, hGne, ?_⟩
      intro F hFK hFne
      rcases hK.1 hFK with ⟨j, rfl⟩
      have hji : j ≠ i := by
        intro h; subst j; exact hFne rfl
      have hjs : j ≠ finSuccMod i := by
        intro h; subst j; exact hsucc hFK
      have hjp : j ≠ prop61_finPredMod i := by
        intro h; subst j; exact hpnot hFK
      rw [prop61_edge_inter_empty_of_no_neighbors hji hjs hjp]
      exact bot_le

/-- No facet of the full even cycle is a leaf. -/
theorem prop61_H_not_simplicialForest {m : ℕ} (hm : 2 ≤ m) :
    ¬ IsSimplicialForest (prop61_H m) := by
  classical
  have hn : 1 < 2 * m := by omega
  have hn2 : 2 < 2 * m := by omega
  intro hforest
  have hnonempty : (prop61_H m).Nonempty := by
    refine ⟨prop61_edge (⟨0, by omega⟩ : Fin (2 * m)), ?_⟩
    exact ⟨⟨0, by omega⟩, rfl⟩
  rcases hforest (prop61_H m) (by intro E hE; exact hE) hnonempty with ⟨F, hFH, hleaf⟩
  rcases hFH with ⟨i, rfl⟩
  rcases hleaf with ⟨_, hsingle | hjoint⟩
  · have hedge : prop61_edge (finSuccMod i) = prop61_edge i :=
      hsingle (prop61_edge (finSuccMod i)) ⟨finSuccMod i, rfl⟩
    have hs : finSuccMod i = i := prop61_edge_injective m hedge
    exact (prop61_finSuccMod_ne_self_of_one_lt hn i) hs
  · rcases hjoint with ⟨G, hGH, hGne, hleafcond⟩
    rcases hGH with ⟨j, rfl⟩
    have hji : j ≠ i := by
      intro h; subst j; exact hGne rfl
    have hpredne : prop61_finPredMod i ≠ i := by
      intro hp
      have hs : finSuccMod i = i := by
        simpa [hp] using prop61_finSuccMod_finPredMod i
      exact (prop61_finSuccMod_ne_self_of_one_lt hn i) hs
    have hsuccne : finSuccMod i ≠ i := prop61_finSuccMod_ne_self_of_one_lt hn i
    have hEdgePredNe : prop61_edge (prop61_finPredMod i) ≠ prop61_edge i := by
      intro h; exact hpredne (prop61_edge_injective m h)
    have hEdgeSuccNe : prop61_edge (finSuccMod i) ≠ prop61_edge i := by
      intro h; exact hsuccne (prop61_edge_injective m h)
    have hxP : prop61_x i ∈
        prop61_edge (prop61_finPredMod i) ∩ prop61_edge i := by
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · exact prop61_x_mem_edge_iff.mpr (Or.inr (prop61_finSuccMod_finPredMod i).symm)
      · exact prop61_x_mem_edge_iff.mpr (Or.inl rfl)
    have hsubP := hleafcond (prop61_edge (prop61_finPredMod i))
      ⟨prop61_finPredMod i, rfl⟩ hEdgePredNe
    have hxPG : prop61_x i ∈ prop61_edge j := (Finset.mem_inter.mp (hsubP hxP)).2
    have hcaseP : j = i ∨ j = prop61_finPredMod i := by
      rcases prop61_x_mem_edge_iff.mp hxPG with hij | his
      · exact Or.inl hij.symm
      · exact Or.inr (by
          calc
            j = prop61_finPredMod (finSuccMod j) :=
              (prop61_finPredMod_finSuccMod j).symm
            _ = prop61_finPredMod i := (congrArg prop61_finPredMod his).symm)
    have hxS : prop61_x (finSuccMod i) ∈
        prop61_edge (finSuccMod i) ∩ prop61_edge i := by
      refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · exact prop61_x_mem_edge_iff.mpr (Or.inl rfl)
      · exact prop61_x_mem_edge_iff.mpr (Or.inr rfl)
    have hsubS := hleafcond (prop61_edge (finSuccMod i))
      ⟨finSuccMod i, rfl⟩ hEdgeSuccNe
    have hxSG : prop61_x (finSuccMod i) ∈ prop61_edge j :=
      (Finset.mem_inter.mp (hsubS hxS)).2
    have hcaseS : j = finSuccMod i ∨ j = i := by
      rcases prop61_x_mem_edge_iff.mp hxSG with hjs | hsj
      · exact Or.inl hjs.symm
      · exact Or.inr (prop61_finSuccMod_injective hsj).symm
    rcases hcaseP with hji' | hjp
    · exact hji hji'
    rcases hcaseS with hjs | hji'
    · have heq : prop61_finPredMod i = finSuccMod i := hjp.symm.trans hjs
      exact (prop61_finPredMod_ne_finSuccMod_of_two_lt hn2 i) heq
    · exact hji hji'

/-- Every strong cycle in the even-cycle family has length \(2m\), hence is even. -/
theorem prop61_H_isBalanced {m : ℕ} (hm : 2 ≤ m) : IsBalanced (prop61_H m) := by
  rw [IsBalanced]
  intro q hqOdd hc
  have hq3 : 3 ≤ q := hc.1
  rcases prop61_strongCycle_indexMap hm hc with ⟨a, ha, hstep⟩
  have hlength : q = 2 * m :=
    prop61_cyclicWalk_length_eq (n := 2 * m) (q := q) (by omega) hq3 ha hstep
  rw [hlength] at hqOdd
  rcases hqOdd with ⟨k, hk⟩
  omega

/-- Equation (2) reduces the remaining squarefree Simis input to ordinary/component equality. -/
theorem prop61_J_isSimis_iff_componentSimis (m : ℕ) :
    IsSimis (prop61_J (K := K) m) ↔
      ComponentSimis (prop61_J (K := K) m)
        (fun C : prop61_componentIndex m =>
          (purePower C.1 (fun _ : prop61_var m => 1) :
            Ideal (MvPolynomial (prop61_var m) K))) := by
  exact isSimis_iff_componentSimis_of_stdSymbolic (prop61_stdSymbolic_J (K := K) m)

/-- The squarefree even-cycle ideal is Simis. -/
theorem prop61_J_isSimis {m : ℕ} (hm : 2 ≤ m) :
    IsSimis (prop61_J (K := K) m) := by
  classical
  let _ : Fintype (prop61_var m) := prop61_varFintype m
  let _ : Fintype (prop61_componentIndex m) := prop61_componentIndexFintype m
  have hm0 : 0 < m := by omega
  have hn : 1 < 2 * m := by omega
  have hH : prop61_H m = evenCycleFlow_facets m :=
    prop61_H_eq_evenCycleFlow_facets m
  have hcomp : prop61_J (K := K) m =
      ⨅ C : prop61_componentIndex m,
        (purePower C.1 (fun _ : prop61_var m => 1) :
          Ideal (MvPolynomial (prop61_var m) K)) :=
    prop61_J_hasComponents (K := K) m
  apply (prop61_J_isSimis_iff_componentSimis (K := K) m).mpr
  intro q hq
  have _ := hq
  apply le_antisymm
  · intro p hp
    rw [componentSymbolic]
    refine Ideal.mem_iInf.mpr ?_
    intro C
    have hJC : prop61_J (K := K) m ≤
        (purePower C.1 (fun _ : prop61_var m => 1) :
          Ideal (MvPolynomial (prop61_var m) K)) := by
      rw [hcomp]
      exact iInf_le _ C
    exact Ideal.pow_right_mono hJC q hp
  · intro p hp
    rw [prop61_J, monomialIdeal_pow]
    rw [mem_monomialIdeal]
    intro e he
    have hblock : ∀ C ∈ blocker (prop61_H m), q ≤ ∑ v ∈ C, e v := by
      intro C hC
      have hpC := (Ideal.mem_iInf.mp hp) (⟨C, hC⟩ : prop61_componentIndex m)
      have hpC' : p ∈ monomialIdeal
          (powGens {u : prop61_var m →₀ ℕ |
            ∃ i ∈ C, u = Finsupp.single i (1 : ℕ)} q) := by
        simpa [purePower, monomialIdeal_pow] using hpC
      rcases mem_monomialIdeal.mp hpC' e he with ⟨u, huPow, hue⟩
      exact (prop61_powGens_prime_sum_le huPow).trans
        (Finset.sum_le_sum (fun v _ => hue v))
    rw [hH] at hblock
    rcases evenCycleFlow_packing_of_blocker (m := m) hm0 hblock with
      ⟨t, htSum, htY, htZ, htX⟩
    let z : prop61_var m →₀ ℕ :=
      ∑ i : Fin (2 * m), t i • characteristicExp (prop61_edge i)
    have hzPowSum : z ∈ powGens (characteristicExp '' prop61_H m) (∑ i, t i) := by
      exact prop61_count_sum_mem_powGens
        (S := characteristicExp '' prop61_H m)
        (g := fun i : Fin (2 * m) => characteristicExp (prop61_edge i))
        (fun i => ⟨prop61_edge i, ⟨i, rfl⟩, rfl⟩) t
    have hzPow : z ∈ powGens (characteristicExp '' prop61_H m) q := by
      simpa [htSum] using hzPowSum
    have hzY (i : Fin (2 * m)) : z (prop61_y i) = t i := by
      let f : Fin (2 * m) → ℕ := fun j =>
        (t j • characteristicExp (prop61_edge j) :
          prop61_var m →₀ ℕ) (prop61_y i)
      have hfi : f i = t i := by
        simp [f, prop61_y_mem_edge_iff, characteristicExp_apply]
      have hzero : ∀ j ∈ (Finset.univ : Finset (Fin (2 * m))), j ≠ i → f j = 0 := by
        intro j _ hji
        have hnotmem : prop61_y i ∉ prop61_edge j := by
          intro hj
          exact hji (prop61_y_mem_edge_iff.mp hj).symm
        simp [f, characteristicExp_apply, hnotmem]
      calc
        z (prop61_y i) = ∑ j, f j := by simp [z, f]
        _ = f i := Finset.sum_eq_single_of_mem i (by simp) hzero
        _ = t i := hfi
    have hzZ (i : Fin (2 * m)) : z (prop61_z i) = t i := by
      let f : Fin (2 * m) → ℕ := fun j =>
        (t j • characteristicExp (prop61_edge j) :
          prop61_var m →₀ ℕ) (prop61_z i)
      have hfi : f i = t i := by
        simp [f, prop61_z_mem_edge_iff, characteristicExp_apply]
      have hzero : ∀ j ∈ (Finset.univ : Finset (Fin (2 * m))), j ≠ i → f j = 0 := by
        intro j _ hji
        have hnotmem : prop61_z i ∉ prop61_edge j := by
          intro hj
          exact hji (prop61_z_mem_edge_iff.mp hj).symm
        simp [f, characteristicExp_apply, hnotmem]
      calc
        z (prop61_z i) = ∑ j, f j := by simp [z, f]
        _ = f i := Finset.sum_eq_single_of_mem i (by simp) hzero
        _ = t i := hfi
    have hzX (i : Fin (2 * m)) :
        z (prop61_x i) = t i + t (prop61_finPredMod i) := by
      let f : Fin (2 * m) → ℕ := fun j =>
        (t j • characteristicExp (prop61_edge j) :
          prop61_var m →₀ ℕ) (prop61_x i)
      have hpne : prop61_finPredMod i ≠ i := by
        intro hp'
        have hs : finSuccMod i = i := by
          simpa [hp'] using prop61_finSuccMod_finPredMod i
        exact (prop61_finSuccMod_ne_self_of_one_lt hn i) hs
      have hfi : f i = t i := by
        simp [f, prop61_x_mem_edge_iff_index, characteristicExp_apply]
      have hfp : f (prop61_finPredMod i) = t (prop61_finPredMod i) := by
        simp [f, prop61_x_mem_edge_iff_index, characteristicExp_apply, hpne]
      have hterm (j : Fin (2 * m)) :
          f j = (if j = i then t i else 0) +
            (if j = prop61_finPredMod i then t (prop61_finPredMod i) else 0) := by
        by_cases hji : j = i
        · subst j
          simp [f, prop61_x_mem_edge_iff_index, characteristicExp_apply, hpne.symm]
        · by_cases hjp : j = prop61_finPredMod i
          · subst j
            simp [f, prop61_x_mem_edge_iff_index, characteristicExp_apply, hpne]
          · have hnotmem : prop61_x i ∉ prop61_edge j := by
              intro hjmem
              rcases prop61_x_mem_edge_iff_index.mp hjmem with hcase | hcase
              · exact hji hcase
              · exact hjp hcase
            simp [f, characteristicExp_apply, hnotmem, hji, hjp]
      calc
        z (prop61_x i) = ∑ j, f j := by simp [z, f]
        _ = ∑ j : Fin (2 * m),
              ((if j = i then t i else 0) +
                (if j = prop61_finPredMod i then t (prop61_finPredMod i) else 0)) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hterm j
        _ = (∑ j : Fin (2 * m), if j = i then t i else 0) +
              (∑ j : Fin (2 * m), if j = prop61_finPredMod i then
                t (prop61_finPredMod i) else 0) := by
          rw [Finset.sum_add_distrib]
        _ = t i + t (prop61_finPredMod i) := by
          simp
    have hzle : z ≤ e := by
      intro v
      rcases v with ⟨r, i⟩
      fin_cases r
      · change z (prop61_x i) ≤ e (prop61_x i)
        rw [hzX i]
        simpa [prop61_x, prop61_finPredMod_eq_evenCycleFlow_pred] using htX i
      · change z (prop61_y i) ≤ e (prop61_y i)
        rw [hzY i]
        simpa [prop61_y] using htY i
      · change z (prop61_z i) ≤ e (prop61_z i)
        rw [hzZ i]
        simpa [prop61_z] using htZ i
    exact ⟨z, hzPow, hzle⟩

/-- Packaging of the balanced/forest assertions of Proposition 6.1(iv). -/
def prop61_BalancedForestInput (m : ℕ) : Prop :=
  IsBalanced (prop61_H m) ∧ ¬ IsSimplicialForest (prop61_H m) ∧
    ∀ K : Set (Finset (prop61_var m)), K ⊂ prop61_H m → K.Nonempty → IsSimplicialForest K

/-- Balancedness, non-forestness, and forestness of every nonempty proper subfamily. -/
theorem prop61_balancedForestInput {m : ℕ} (hm : 2 ≤ m) :
    prop61_BalancedForestInput m := by
  refine ⟨prop61_H_isBalanced hm, prop61_H_not_simplicialForest hm, ?_⟩
  intro K hK hKne
  rw [IsSimplicialForest]
  intro U hUK hUne
  exact prop61_proper_subfamily_hasLeaf hm (lt_of_le_of_lt hUK hK) hUne

/-- Deleting any one facet leaves a forest. -/
theorem prop61_H_delete_facet_simplicialForest {m : ℕ} (hm : 2 ≤ m)
    {E : Finset (prop61_var m)} (hE : E ∈ prop61_H m) :
    IsSimplicialForest (prop61_H m \ {E}) := by
  classical
  rcases hE with ⟨i, rfl⟩
  have hn : 1 < 2 * m := by omega
  have hsucc : finSuccMod i ≠ i := prop61_finSuccMod_ne_self_of_one_lt hn i
  have hproper : prop61_H m \ {prop61_edge i} ⊂ prop61_H m := by
    refine Set.ssubset_iff_subset_ne.mpr ?_
    constructor
    · intro F hF
      exact hF.1
    · intro hEq
      have hmem : prop61_edge i ∈ prop61_H m \ {prop61_edge i} := by
        rw [hEq]
        exact ⟨i, rfl⟩
      exact hmem.2 (by simp)
  have hnonempty : (prop61_H m \ {prop61_edge i}).Nonempty := by
    refine ⟨prop61_edge (finSuccMod i), ?_⟩
    constructor
    · exact ⟨finSuccMod i, rfl⟩
    · intro hsingle
      have heq : prop61_edge (finSuccMod i) = prop61_edge i := by
        simpa using hsingle
      exact hsucc (prop61_edge_injective m heq)
  exact (prop61_balancedForestInput hm).2.2
    (prop61_H m \ {prop61_edge i}) hproper hnonempty

/-- Packaging of Eq. (4) for this family. -/
def prop61_Eq4Input (m : ℕ) (d : prop61_var m → ℕ) : Prop :=
  IsSimis (prop61_J (K := K) m) ↔ IsSimis (diagonal d (prop61_J (K := K) m))

/-- Equation (4), derived from Equation (2) for both displayed decompositions. -/
theorem prop61_eq4Input (m : ℕ) {d : prop61_var m → ℕ} (hd : ∀ i, 0 < d i) :
    prop61_Eq4Input (K := K) m d := by
  classical
  let _ : Fintype (prop61_var m) := prop61_varFintype m
  let _ : Fintype (prop61_componentIndex m) := prop61_componentIndexFintype m
  have hJmono : IsMonomialIdeal (prop61_J (K := K) m) := by
    exact ⟨characteristicExp '' prop61_H m, rfl⟩
  have hstdJ := prop61_stdSymbolic_J (K := K) m
  have hstdI := prop61_stdSymbolic_I (K := K) m hd
  have hIeq : prop61_I (K := K) m d = diagonal d (prop61_J (K := K) m) :=
    prop61_I_eq_diagonal (K := K) m d
  have hstdD : HasStdSymbolicFormula (diagonal d (prop61_J (K := K) m))
      (fun C : prop61_componentIndex m =>
        (purePower C.1 (fun i : prop61_var m => (fun _ : prop61_var m => 1) i * d i) :
          Ideal (MvPolynomial (prop61_var m) K))) := by
    simpa [hIeq] using hstdI
  exact eq4_isSimis_diagonal_iff_of_stdPurePower (K := K)
    (J := prop61_J (K := K) m)
    (A := fun C : prop61_componentIndex m => C.1)
    (a := fun _ _ => 1) (d := d) hJmono hd hstdJ hstdD

/-- External positive-diagonal preservation of associated primes for monomial ideals. -/
def prop61_DiagonalAssInput (m : ℕ) (d : prop61_var m → ℕ) : Prop :=
  ∀ L : Ideal (MvPolynomial (prop61_var m) K), IsMonomialIdeal L →
    associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ diagonal d L) =
      associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ L)

/-- The squarefree ideal has exactly the displayed component primes as associated primes. -/
theorem prop61_associatedPrimes_J (m : ℕ) :
    associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ prop61_J (K := K) m) =
      Set.range (fun C : prop61_componentIndex m =>
        (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) := by
  let _ : Fintype (prop61_var m) := prop61_varFintype m
  let _ : Fintype (prop61_componentIndex m) := prop61_componentIndexFintype m
  exact prop21_associatedPrimes_eq_range_of_supportsAntichain
    (prop61_J_hasComponents (K := K) m)
    (prop61_components_isIrredundant (K := K) m (a := fun _ => 1) (by simp))
    (prop61_components_supportsAntichain m (a := fun _ _ => 1))

/-- The weighted ideal has exactly the displayed component primes as associated primes. -/
theorem prop61_associatedPrimes_I (m : ℕ) {d : prop61_var m → ℕ} (hd : ∀ i, 0 < d i) :
    associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ prop61_I (K := K) m d) =
      Set.range (fun C : prop61_componentIndex m =>
        (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) := by
  let _ : Fintype (prop61_var m) := prop61_varFintype m
  let _ : Fintype (prop61_componentIndex m) := prop61_componentIndexFintype m
  exact prop21_associatedPrimes_eq_range_of_supportsAntichain
    (prop61_I_hasComponents (K := K) m)
    (prop61_components_isIrredundant (K := K) m (a := d) hd)
    (prop61_components_supportsAntichain m (a := fun _ i => d i))

/-- Squarefree normal torsion-freeness upgrades to equality of associated primes of all powers. -/
theorem prop61_associatedPrimes_J_pow_eq_of_ntf (m : ℕ)
    (hntfJ : prop21NormallyTorsionFree (prop61_J (K := K) m)) :
    ∀ q : ℕ, 1 ≤ q →
      associatedPrimes (MvPolynomial (prop61_var m) K)
          ((MvPolynomial (prop61_var m) K) ⧸ (prop61_J (K := K) m) ^ q) =
        Set.range (fun C : prop61_componentIndex m =>
          (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) := by
  classical
  let _ : Fintype (prop61_var m) := prop61_varFintype m
  let _ : Fintype (prop61_componentIndex m) := prop61_componentIndexFintype m
  intro q hq
  have hAssRange := prop61_associatedPrimes_J (K := K) m
  have hAssMin :
      associatedPrimes (MvPolynomial (prop61_var m) K)
          ((MvPolynomial (prop61_var m) K) ⧸ prop61_J (K := K) m) =
        (prop61_J (K := K) m).minimalPrimes :=
    prop21_associatedPrimes_eq_minimalPrimes_of_supportsAntichain
      (prop61_J_hasComponents (K := K) m)
      (prop61_components_isIrredundant (K := K) m (a := fun _ => 1) (by simp))
      (prop61_components_supportsAntichain m (a := fun _ _ => 1))
  have hqne : q ≠ 0 := by omega
  have hminpow :
      ((prop61_J (K := K) m) ^ q).minimalPrimes = (prop61_J (K := K) m).minimalPrimes := by
    calc
      ((prop61_J (K := K) m) ^ q).minimalPrimes =
          (((prop61_J (K := K) m) ^ q).radical).minimalPrimes :=
        (Ideal.radical_minimalPrimes (I := (prop61_J (K := K) m) ^ q)).symm
      _ = ((prop61_J (K := K) m).radical).minimalPrimes := by
        rw [Ideal.radical_pow (prop61_J (K := K) m) (n := q) hqne]
      _ = (prop61_J (K := K) m).minimalPrimes :=
        Ideal.radical_minimalPrimes (I := prop61_J (K := K) m)
  have hAnn :
      Module.annihilator (MvPolynomial (prop61_var m) K)
          ((MvPolynomial (prop61_var m) K) ⧸ (prop61_J (K := K) m) ^ q) =
        (prop61_J (K := K) m) ^ q := by
    simpa [Submodule.colon_univ] using
      (Submodule.annihilator_quotient
        (N := (((prop61_J (K := K) m) ^ q : Ideal (MvPolynomial (prop61_var m) K)) :
          Submodule (MvPolynomial (prop61_var m) K) (MvPolynomial (prop61_var m) K))))
  have hminAssoc :
      ((prop61_J (K := K) m) ^ q).minimalPrimes ⊆
        associatedPrimes (MvPolynomial (prop61_var m) K)
          ((MvPolynomial (prop61_var m) K) ⧸ (prop61_J (K := K) m) ^ q) := by
    simpa [hAnn] using
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
        (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ (prop61_J (K := K) m) ^ q))
  apply Set.Subset.antisymm
  · intro P hP
    have hPJ := hntfJ q hq hP
    simpa [hAssRange] using hPJ
  · intro P hP
    have hPJ : P ∈ associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ prop61_J (K := K) m) := by
      simpa [hAssRange] using hP
    have hPmin : P ∈ (prop61_J (K := K) m).minimalPrimes := by
      simpa [hAssMin] using hPJ
    have hPminPow : P ∈ ((prop61_J (K := K) m) ^ q).minimalPrimes := by
      simpa [hminpow] using hPmin
    exact hminAssoc hPminPow

/-- Normal torsion-freeness transfers from the squarefree root to its positive diagonal image. -/
theorem prop61_NormallyTorsionFree_I_of_inputs (m : ℕ) {d : prop61_var m → ℕ}
    (hd : ∀ i, 0 < d i)
    (hntfJ : prop21NormallyTorsionFree (prop61_J (K := K) m))
    (hdiagAss : prop61_DiagonalAssInput (K := K) m d) :
    prop21NormallyTorsionFree (prop61_I (K := K) m d) := by
  let _ : Fintype (prop61_var m) := prop61_varFintype m
  have hdiag : diagonal d (prop61_J (K := K) m) = prop61_I (K := K) m d :=
    (prop61_I_eq_diagonal (K := K) m d).symm
  exact (prop21_NormallyTorsionFree_iff_of_sqRoot (I := prop61_I (K := K) m d)
    (J := prop61_J (K := K) m) (d := d) (prop61_J_isSquarefree (K := K) m) hd hdiag
    (fun L hL _ => hdiagAss L hL)).mpr hntfJ

/-- The displayed associated primes of every positive power of \(I_{m,d}\). -/
theorem prop61_associatedPrimes_I_pow_eq_of_inputs (m : ℕ) {d : prop61_var m → ℕ}
    (hd : ∀ i, 0 < d i)
    (hntfJ : prop21NormallyTorsionFree (prop61_J (K := K) m))
    (hdiagAss : prop61_DiagonalAssInput (K := K) m d) :
    ∀ q : ℕ, 1 ≤ q →
      associatedPrimes (MvPolynomial (prop61_var m) K)
          ((MvPolynomial (prop61_var m) K) ⧸ (prop61_I (K := K) m d) ^ q) =
        Set.range (fun C : prop61_componentIndex m =>
          (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) := by
  let _ : Fintype (prop61_var m) := prop61_varFintype m
  have _ := hd
  intro q hq
  have hJmono : IsMonomialIdeal (prop61_J (K := K) m) := by
    exact ⟨characteristicExp '' prop61_H m, rfl⟩
  have hJqmono : IsMonomialIdeal ((prop61_J (K := K) m) ^ q) :=
    prop21_isMonomialIdeal_pow hJmono q
  have hpowDiag : (prop61_I (K := K) m d) ^ q =
      diagonal d ((prop61_J (K := K) m) ^ q) := by
    calc
      (prop61_I (K := K) m d) ^ q =
          (diagonal d (prop61_J (K := K) m)) ^ q := by
        rw [prop61_I_eq_diagonal (K := K) m d]
      _ = diagonal d ((prop61_J (K := K) m) ^ q) := by
        simpa [diagonal] using
          (Ideal.map_pow (diagHom (K := K) d) (prop61_J (K := K) m) q).symm
  calc
    associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ (prop61_I (K := K) m d) ^ q) =
        associatedPrimes (MvPolynomial (prop61_var m) K)
          ((MvPolynomial (prop61_var m) K) ⧸ diagonal d ((prop61_J (K := K) m) ^ q)) := by
      rw [hpowDiag]
    _ = associatedPrimes (MvPolynomial (prop61_var m) K)
          ((MvPolynomial (prop61_var m) K) ⧸ (prop61_J (K := K) m) ^ q) :=
      hdiagAss ((prop61_J (K := K) m) ^ q) hJqmono
    _ = Set.range (fun C : prop61_componentIndex m =>
          (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) :=
      prop61_associatedPrimes_J_pow_eq_of_ntf (K := K) m hntfJ q hq

/-- Proposition 6.1 with the FHO/HHTZ balanced-squarefree Simis implication as its only
external input. The radical, blocker decomposition, balanced/forest assertions, Equation (2), and
Equation (4) are proved here; the latter two use the shared conditional symbolic-power results.
Associated-prime and normally-torsion-free assertions remain outside this formal statement. -/
theorem prop61_main_ofSimisJ {m : ℕ} (hm : 2 ≤ m) {d : prop61_var m → ℕ}
    (hd : ∀ i, 0 < d i)
    (hsimisJ : IsSimis (prop61_J (K := K) m)) :
    minGens (prop61_J (K := K) m) = characteristicExp '' prop61_H m ∧
    minGens (prop61_I (K := K) m d) = diagExp d '' (characteristicExp '' prop61_H m) ∧
    (prop61_I (K := K) m d).radical = prop61_J (K := K) m ∧
    supportComplex (prop61_J (K := K) m) = prop61_H m ∧
    supportComplex (prop61_I (K := K) m d) = prop61_H m ∧
    (∀ E ∈ prop61_H m, E.card = 4) ∧
    IsBalanced (prop61_H m) ∧
    ¬ IsSimplicialForest (prop61_H m) ∧
    (∀ U : Set (Finset (prop61_var m)), U ⊂ prop61_H m → U.Nonempty →
      IsSimplicialForest U) ∧
    prop61_DecompositionInput (K := K) m d ∧
    IsSimis (prop61_J (K := K) m) ∧ IsSimis (prop61_I (K := K) m d) ∧
      MPVConc (prop61_I (K := K) m d) := by
  have hrad : (prop61_I (K := K) m d).radical = prop61_J (K := K) m :=
    prop61_radical_I_eq_J (K := K) m hd
  have hstruct : prop61_DecompositionInput (K := K) m d :=
    prop61_decompositionInput (K := K) m hd
  have hbf : prop61_BalancedForestInput m := prop61_balancedForestInput hm
  have heq4 : prop61_Eq4Input (K := K) m d := prop61_eq4Input (K := K) m hd
  have hsimisI : IsSimis (prop61_I (K := K) m d) := by
    rw [prop61_I_eq_diagonal (K := K) m d]
    exact heq4.mp hsimisJ
  refine ⟨prop61_minGens_J (K := K) m, prop61_minGens_I (K := K) m hd, hrad,
    prop61_supportComplex_J (K := K) m, prop61_supportComplex_I (K := K) m hd,
    prop61_H_four_uniform hm, hbf.1, hbf.2.1, hbf.2.2, hstruct, hsimisJ, hsimisI, ?_⟩
  exact ⟨prop61_J (K := K) m, d, prop61_J_isSquarefree (K := K) m, hsimisJ, hd,
    (prop61_I_eq_diagonal (K := K) m d).symm⟩

/-- Conditional Proposition 6.1, retaining the original input-compatible header. The named
radical, structural, balanced/forest, and Eq. (4) inputs are accepted for compatibility but are no
longer needed by the proof; `prop61_main_ofSimisJ` supplies the stronger unconditional version. -/
theorem prop61_main_ofInputs {m : ℕ} (hm : 2 ≤ m) {d : prop61_var m → ℕ}
    (hd : ∀ i, 0 < d i)
    (hrad : (prop61_I (K := K) m d).radical = prop61_J (K := K) m)
    (hstruct : prop61_DecompositionInput (K := K) m d)
    (hbf : prop61_BalancedForestInput m)
    (hsimisJ : IsSimis (prop61_J (K := K) m))
    (heq4 : prop61_Eq4Input (K := K) m d) :
    minGens (prop61_J (K := K) m) = characteristicExp '' prop61_H m ∧
    minGens (prop61_I (K := K) m d) = diagExp d '' (characteristicExp '' prop61_H m) ∧
    (prop61_I (K := K) m d).radical = prop61_J (K := K) m ∧
    supportComplex (prop61_J (K := K) m) = prop61_H m ∧
    supportComplex (prop61_I (K := K) m d) = prop61_H m ∧
    (∀ E ∈ prop61_H m, E.card = 4) ∧
    IsBalanced (prop61_H m) ∧
    ¬ IsSimplicialForest (prop61_H m) ∧
    (∀ U : Set (Finset (prop61_var m)), U ⊂ prop61_H m → U.Nonempty →
      IsSimplicialForest U) ∧
    prop61_DecompositionInput (K := K) m d ∧
    IsSimis (prop61_J (K := K) m) ∧ IsSimis (prop61_I (K := K) m d) ∧
      MPVConc (prop61_I (K := K) m d) := by
  have _ := hrad
  have _ := hstruct
  have _ := hbf
  have _ := heq4
  exact prop61_main_ofSimisJ (K := K) hm hd hsimisJ

/-- Full Proposition 6.1 with the cited external inputs kept explicit: squarefree Simis and
normal torsion-freeness from balanced-clutter theory, and preservation of associated primes under
positive diagonal weighting. Everything finite/combinatorial and Equation (2)/(4) is proved above.
The compatibility theorem `prop61_main_ofInputs` is unchanged. -/
theorem prop61_main_full_ofSimisNtfAss {m : ℕ} (hm : 2 ≤ m) {d : prop61_var m → ℕ}
    (hd : ∀ i, 0 < d i)
    (hsimisJ : IsSimis (prop61_J (K := K) m))
    (hntfJ : prop21NormallyTorsionFree (prop61_J (K := K) m))
    (hdiagAss : prop61_DiagonalAssInput (K := K) m d) :
    (minGens (prop61_J (K := K) m) = characteristicExp '' prop61_H m ∧
    minGens (prop61_I (K := K) m d) = diagExp d '' (characteristicExp '' prop61_H m) ∧
    (prop61_I (K := K) m d).radical = prop61_J (K := K) m ∧
    supportComplex (prop61_J (K := K) m) = prop61_H m ∧
    supportComplex (prop61_I (K := K) m d) = prop61_H m ∧
    (∀ E ∈ prop61_H m, E.card = 4) ∧
    IsBalanced (prop61_H m) ∧
    ¬ IsSimplicialForest (prop61_H m) ∧
    (∀ U : Set (Finset (prop61_var m)), U ⊂ prop61_H m → U.Nonempty →
      IsSimplicialForest U) ∧
    prop61_DecompositionInput (K := K) m d ∧
    IsSimis (prop61_J (K := K) m) ∧ IsSimis (prop61_I (K := K) m d) ∧
      MPVConc (prop61_I (K := K) m d)) ∧
    associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ prop61_J (K := K) m) =
      Set.range (fun C : prop61_componentIndex m =>
        (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) ∧
    associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ prop61_I (K := K) m d) =
      Set.range (fun C : prop61_componentIndex m =>
        (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) ∧
    prop21NormallyTorsionFree (prop61_J (K := K) m) ∧
    prop21NormallyTorsionFree (prop61_I (K := K) m d) ∧
    (∀ q : ℕ, 1 ≤ q →
      associatedPrimes (MvPolynomial (prop61_var m) K)
          ((MvPolynomial (prop61_var m) K) ⧸ (prop61_I (K := K) m d) ^ q) =
        Set.range (fun C : prop61_componentIndex m =>
          (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K)))) := by
  let _ : Fintype (prop61_var m) := prop61_varFintype m
  let _ : Fintype (prop61_componentIndex m) := prop61_componentIndexFintype m
  have hcore := prop61_main_ofSimisJ (K := K) hm hd hsimisJ
  have hAssJ := prop61_associatedPrimes_J (K := K) m
  have hAssI := prop61_associatedPrimes_I (K := K) m hd
  have hNtfI : prop21NormallyTorsionFree (prop61_I (K := K) m d) :=
    prop61_NormallyTorsionFree_I_of_inputs (K := K) m hd hntfJ hdiagAss
  have hAssPow : ∀ q : ℕ, 1 ≤ q →
      associatedPrimes (MvPolynomial (prop61_var m) K)
          ((MvPolynomial (prop61_var m) K) ⧸ (prop61_I (K := K) m d) ^ q) =
        Set.range (fun C : prop61_componentIndex m =>
          (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) :=
    prop61_associatedPrimes_I_pow_eq_of_inputs (K := K) m hd hntfJ hdiagAss
  exact ⟨hcore, hAssJ, hAssI, hntfJ, hNtfI, hAssPow⟩

/-- Full Proposition 6.1 using the shared finite-irredundant-decomposition predicate to discharge
diagonal associated-prime preservation. The FHO/HHTZ squarefree Simis and normal-torsion-free
inputs remain explicit; no existing theorem signature is changed. -/
theorem prop61_main_full_ofSimisNtfFinite {m : ℕ} (hm : 2 ≤ m) {d : prop61_var m → ℕ}
    (hd : ∀ i, 0 < d i)
    (hsimisJ : IsSimis (prop61_J (K := K) m))
    (hntfJ : prop21NormallyTorsionFree (prop61_J (K := K) m))
    (hfin : ∀ L : Ideal (MvPolynomial (prop61_var m) K), IsMonomialIdeal L →
      HasFiniteIrredundantDecomp L) :
    (minGens (prop61_J (K := K) m) = characteristicExp '' prop61_H m ∧
    minGens (prop61_I (K := K) m d) = diagExp d '' (characteristicExp '' prop61_H m) ∧
    (prop61_I (K := K) m d).radical = prop61_J (K := K) m ∧
    supportComplex (prop61_J (K := K) m) = prop61_H m ∧
    supportComplex (prop61_I (K := K) m d) = prop61_H m ∧
    (∀ E ∈ prop61_H m, E.card = 4) ∧
    IsBalanced (prop61_H m) ∧
    ¬ IsSimplicialForest (prop61_H m) ∧
    (∀ U : Set (Finset (prop61_var m)), U ⊂ prop61_H m → U.Nonempty →
      IsSimplicialForest U) ∧
    prop61_DecompositionInput (K := K) m d ∧
    IsSimis (prop61_J (K := K) m) ∧ IsSimis (prop61_I (K := K) m d) ∧
      MPVConc (prop61_I (K := K) m d)) ∧
    associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ prop61_J (K := K) m) =
      Set.range (fun C : prop61_componentIndex m =>
        (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) ∧
    associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ prop61_I (K := K) m d) =
      Set.range (fun C : prop61_componentIndex m =>
        (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) ∧
    prop21NormallyTorsionFree (prop61_J (K := K) m) ∧
    prop21NormallyTorsionFree (prop61_I (K := K) m d) ∧
    (∀ q : ℕ, 1 ≤ q →
      associatedPrimes (MvPolynomial (prop61_var m) K)
          ((MvPolynomial (prop61_var m) K) ⧸ (prop61_I (K := K) m d) ^ q) =
        Set.range (fun C : prop61_componentIndex m =>
          (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K)))) := by
  let _ : Fintype (prop61_var m) := prop61_varFintype m
  have hfinLocal : ∀ L : Ideal (MvPolynomial (prop61_var m) K), IsMonomialIdeal L →
      diagAssoc_HasFiniteIrredundantDecomposition L := by
    intro L hL
    exact hfin L hL
  have hpres : diagAssoc_PreservesAssociatedPrimes (K := K) d :=
    diagAssoc_preservesAssociatedPrimes_of_allFiniteDecompositions (d := d) hfinLocal
  have hdiagAss : prop61_DiagonalAssInput (K := K) m d := by
    intro L hL
    exact hpres L hL hd
  exact prop61_main_full_ofSimisNtfAss (K := K) hm hd hsimisJ hntfJ hdiagAss

/-- Full Proposition 6.1 using the registered existence theorem for finite irredundant
decompositions of monomial ideals. The two FHO/HHTZ inputs `hsimisJ` and `hntfJ` remain explicit;
all other structural, symbolic, and associated-prime inputs are derived above. -/
theorem prop61_main_full_ofSimisNtf {m : ℕ} (hm : 2 ≤ m) {d : prop61_var m → ℕ}
    (hd : ∀ i, 0 < d i)
    (hsimisJ : IsSimis (prop61_J (K := K) m))
    (hntfJ : prop21NormallyTorsionFree (prop61_J (K := K) m)) :
    (minGens (prop61_J (K := K) m) = characteristicExp '' prop61_H m ∧
    minGens (prop61_I (K := K) m d) = diagExp d '' (characteristicExp '' prop61_H m) ∧
    (prop61_I (K := K) m d).radical = prop61_J (K := K) m ∧
    supportComplex (prop61_J (K := K) m) = prop61_H m ∧
    supportComplex (prop61_I (K := K) m d) = prop61_H m ∧
    (∀ E ∈ prop61_H m, E.card = 4) ∧
    IsBalanced (prop61_H m) ∧
    ¬ IsSimplicialForest (prop61_H m) ∧
    (∀ U : Set (Finset (prop61_var m)), U ⊂ prop61_H m → U.Nonempty →
      IsSimplicialForest U) ∧
    prop61_DecompositionInput (K := K) m d ∧
    IsSimis (prop61_J (K := K) m) ∧ IsSimis (prop61_I (K := K) m d) ∧
      MPVConc (prop61_I (K := K) m d)) ∧
    associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ prop61_J (K := K) m) =
      Set.range (fun C : prop61_componentIndex m =>
        (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) ∧
    associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ prop61_I (K := K) m d) =
      Set.range (fun C : prop61_componentIndex m =>
        (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) ∧
    prop21NormallyTorsionFree (prop61_J (K := K) m) ∧
    prop21NormallyTorsionFree (prop61_I (K := K) m d) ∧
    (∀ q : ℕ, 1 ≤ q →
      associatedPrimes (MvPolynomial (prop61_var m) K)
          ((MvPolynomial (prop61_var m) K) ⧸ (prop61_I (K := K) m d) ^ q) =
        Set.range (fun C : prop61_componentIndex m =>
          (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K)))) := by
  let _ : Fintype (prop61_var m) := prop61_varFintype m
  have hfin : ∀ L : Ideal (MvPolynomial (prop61_var m) K), IsMonomialIdeal L →
      HasFiniteIrredundantDecomp L := by
    intro L hL
    exact hasFiniteIrredundantDecomp_of_isMonomialIdeal (K := K) hL
  exact prop61_main_full_ofSimisNtfFinite (K := K) hm hd hsimisJ hntfJ hfin

/-- Full Proposition 6.1 with only the cited balanced-squarefree Simis input explicit. Positive
ordinary-power associated primes and squarefree normal torsion-freeness are obtained from the
component decomposition via `PowerAssociated`; the weighted assertions then follow from the
finite-decomposition wrapper above. All older declarations are preserved unchanged. -/
theorem prop61_main_full_ofSimis {m : ℕ} (hm : 2 ≤ m) {d : prop61_var m → ℕ}
    (hd : ∀ i, 0 < d i)
    (hsimisJ : IsSimis (prop61_J (K := K) m)) :
    (minGens (prop61_J (K := K) m) = characteristicExp '' prop61_H m ∧
    minGens (prop61_I (K := K) m d) = diagExp d '' (characteristicExp '' prop61_H m) ∧
    (prop61_I (K := K) m d).radical = prop61_J (K := K) m ∧
    supportComplex (prop61_J (K := K) m) = prop61_H m ∧
    supportComplex (prop61_I (K := K) m d) = prop61_H m ∧
    (∀ E ∈ prop61_H m, E.card = 4) ∧
    IsBalanced (prop61_H m) ∧
    ¬ IsSimplicialForest (prop61_H m) ∧
    (∀ U : Set (Finset (prop61_var m)), U ⊂ prop61_H m → U.Nonempty →
      IsSimplicialForest U) ∧
    prop61_DecompositionInput (K := K) m d ∧
    IsSimis (prop61_J (K := K) m) ∧ IsSimis (prop61_I (K := K) m d) ∧
      MPVConc (prop61_I (K := K) m d)) ∧
    associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ prop61_J (K := K) m) =
      Set.range (fun C : prop61_componentIndex m =>
        (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) ∧
    associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ prop61_I (K := K) m d) =
      Set.range (fun C : prop61_componentIndex m =>
        (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) ∧
    prop21NormallyTorsionFree (prop61_J (K := K) m) ∧
    prop21NormallyTorsionFree (prop61_I (K := K) m d) ∧
    (∀ q : ℕ, 1 ≤ q →
      associatedPrimes (MvPolynomial (prop61_var m) K)
          ((MvPolynomial (prop61_var m) K) ⧸ (prop61_I (K := K) m d) ^ q) =
        Set.range (fun C : prop61_componentIndex m =>
          (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K)))) := by
  let _ : Fintype (prop61_var m) := prop61_varFintype m
  let _ : Fintype (prop61_componentIndex m) := prop61_componentIndexFintype m
  have hcomp : HasComponents (prop61_J (K := K) m)
      (fun C : prop61_componentIndex m => C.1) (fun _ _ => 1) :=
    prop61_J_hasComponents (K := K) m
  have hirr : IsIrredundant (K := K) (fun C : prop61_componentIndex m => C.1)
      (fun _ _ => 1) :=
    prop61_components_isIrredundant (K := K) m (a := fun _ => 1) (by simp)
  have hanti : SupportsAntichain (fun C : prop61_componentIndex m => C.1)
      (fun _ _ => 1) :=
    prop61_components_supportsAntichain m (a := fun _ _ => 1)
  have hstd : HasStdSymbolicFormula (prop61_J (K := K) m)
      (fun C : prop61_componentIndex m =>
        (purePower C.1 (fun _ : prop61_var m => 1) : Ideal (MvPolynomial (prop61_var m) K))) :=
    prop61_stdSymbolic_J (K := K) m
  have hcompSimis : ComponentSimis (prop61_J (K := K) m)
      (fun C : prop61_componentIndex m =>
        (purePower C.1 (fun _ : prop61_var m => 1) : Ideal (MvPolynomial (prop61_var m) K))) :=
    (isSimis_iff_componentSimis_of_stdSymbolic hstd).mp hsimisJ
  have hAssPow : ∀ {q : ℕ}, 0 < q →
      associatedPrimes (MvPolynomial (prop61_var m) K)
          ((MvPolynomial (prop61_var m) K) ⧸ (prop61_J (K := K) m) ^ q) =
        Set.range (fun C : prop61_componentIndex m =>
          (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) := by
    intro q hq
    exact associatedPrimes_pow_eq_range_of_componentSimis_antichain
      hcomp hirr hanti hcompSimis hq
  have hAssBase : associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ prop61_J (K := K) m) =
      Set.range (fun C : prop61_componentIndex m =>
        (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) :=
    prop61_associatedPrimes_J (K := K) m
  have hntfJ : prop21NormallyTorsionFree (prop61_J (K := K) m) :=
    normallyTorsionFree_of_powerAssociatedPrimes_eq_range hAssBase hAssPow
  exact prop61_main_full_ofSimisNtf (K := K) hm hd hsimisJ hntfJ

/-- Full Proposition 6.1 with no external hypotheses beyond `m ≥ 2` and positive weights. The
remaining squarefree Simis input is discharged by the even-cycle flow packing theorem; all older
declarations are preserved unchanged. -/
theorem prop61_main_full {m : ℕ} (hm : 2 ≤ m) {d : prop61_var m → ℕ}
    (hd : ∀ i, 0 < d i) :
    (minGens (prop61_J (K := K) m) = characteristicExp '' prop61_H m ∧
    minGens (prop61_I (K := K) m d) = diagExp d '' (characteristicExp '' prop61_H m) ∧
    (prop61_I (K := K) m d).radical = prop61_J (K := K) m ∧
    supportComplex (prop61_J (K := K) m) = prop61_H m ∧
    supportComplex (prop61_I (K := K) m d) = prop61_H m ∧
    (∀ E ∈ prop61_H m, E.card = 4) ∧
    IsBalanced (prop61_H m) ∧
    ¬ IsSimplicialForest (prop61_H m) ∧
    (∀ U : Set (Finset (prop61_var m)), U ⊂ prop61_H m → U.Nonempty →
      IsSimplicialForest U) ∧
    prop61_DecompositionInput (K := K) m d ∧
    IsSimis (prop61_J (K := K) m) ∧ IsSimis (prop61_I (K := K) m d) ∧
      MPVConc (prop61_I (K := K) m d)) ∧
    associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ prop61_J (K := K) m) =
      Set.range (fun C : prop61_componentIndex m =>
        (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) ∧
    associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ prop61_I (K := K) m d) =
      Set.range (fun C : prop61_componentIndex m =>
        (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) ∧
    prop21NormallyTorsionFree (prop61_J (K := K) m) ∧
    prop21NormallyTorsionFree (prop61_I (K := K) m d) ∧
    (∀ q : ℕ, 1 ≤ q →
      associatedPrimes (MvPolynomial (prop61_var m) K)
          ((MvPolynomial (prop61_var m) K) ⧸ (prop61_I (K := K) m d) ^ q) =
        Set.range (fun C : prop61_componentIndex m =>
          (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K)))) := by
  exact prop61_main_full_ofSimis (K := K) hm hd (prop61_J_isSimis (K := K) hm)

/-- Proposition 6.1 together with the additional prose after the proposition: non-squarefree
nonconstant weightings, one-facet deletion forests, and absence of generators of support at most
three. This declaration is additive; the previous main theorems are unchanged. -/
theorem prop61_main_full_with_prose {m : ℕ} (hm : 2 ≤ m) {d : prop61_var m → ℕ}
    (hd : ∀ i, 0 < d i) :
    ((minGens (prop61_J (K := K) m) = characteristicExp '' prop61_H m ∧
    minGens (prop61_I (K := K) m d) = diagExp d '' (characteristicExp '' prop61_H m) ∧
    (prop61_I (K := K) m d).radical = prop61_J (K := K) m ∧
    supportComplex (prop61_J (K := K) m) = prop61_H m ∧
    supportComplex (prop61_I (K := K) m d) = prop61_H m ∧
    (∀ E ∈ prop61_H m, E.card = 4) ∧
    IsBalanced (prop61_H m) ∧
    ¬ IsSimplicialForest (prop61_H m) ∧
    (∀ U : Set (Finset (prop61_var m)), U ⊂ prop61_H m → U.Nonempty →
      IsSimplicialForest U) ∧
    prop61_DecompositionInput (K := K) m d ∧
    IsSimis (prop61_J (K := K) m) ∧ IsSimis (prop61_I (K := K) m d) ∧
      MPVConc (prop61_I (K := K) m d)) ∧
    associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ prop61_J (K := K) m) =
      Set.range (fun C : prop61_componentIndex m =>
        (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) ∧
    associatedPrimes (MvPolynomial (prop61_var m) K)
        ((MvPolynomial (prop61_var m) K) ⧸ prop61_I (K := K) m d) =
      Set.range (fun C : prop61_componentIndex m =>
        (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))) ∧
    prop21NormallyTorsionFree (prop61_J (K := K) m) ∧
    prop21NormallyTorsionFree (prop61_I (K := K) m d) ∧
    (∀ q : ℕ, 1 ≤ q →
      associatedPrimes (MvPolynomial (prop61_var m) K)
          ((MvPolynomial (prop61_var m) K) ⧸ (prop61_I (K := K) m d) ^ q) =
        Set.range (fun C : prop61_componentIndex m =>
          (primeOf C.1 : Ideal (MvPolynomial (prop61_var m) K))))) ∧
    (d ≠ (fun _ : prop61_var m => 1) →
      ¬ IsSquarefreeMonomialIdeal (prop61_I (K := K) m d)) ∧
    (IsSquarefreeMonomialIdeal (prop61_I (K := K) m d) ↔
      d = (fun _ : prop61_var m => 1)) ∧
    (∀ E ∈ prop61_H m, IsSimplicialForest (prop61_H m \ {E})) ∧
    (∀ e ∈ minGens (prop61_J (K := K) m), 3 < e.support.card) ∧
    (∀ e ∈ minGens (prop61_I (K := K) m d), 3 < e.support.card) := by
  refine ⟨prop61_main_full (K := K) hm hd, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hdne hsq
    exact hdne ((prop61_I_isSquarefree_iff (K := K) m hd).mp hsq)
  · exact prop61_I_isSquarefree_iff (K := K) m hd
  · intro E hE
    exact prop61_H_delete_facet_simplicialForest hm hE
  · exact prop61_minGens_J_support_card_gt_three (K := K) hm
  · exact prop61_minGens_I_support_card_gt_three (K := K) hm hd

end Prop61Ideals
end SimisFormal
