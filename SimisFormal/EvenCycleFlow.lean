import SimisFormal.Defs
import SimisFormal.Basic

namespace SimisFormal
open scoped BigOperators
/-- Cyclic predecessor on `Fin q`, kept local so this file does not import `Prop6_1`. -/
def evenCycleFlow_pred {q : ℕ} (i : Fin q) : Fin q :=
  if h : i.val = 0 then ⟨q - 1, by
    have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
    omega⟩
  else ⟨i.val - 1, by omega⟩

@[simp] theorem evenCycleFlow_pred_val {q : ℕ} (i : Fin q) :
    (evenCycleFlow_pred i).val = if i.val = 0 then q - 1 else i.val - 1 := by
  rw [evenCycleFlow_pred]
  split_ifs <;> rfl

@[simp] theorem evenCycleFlow_succ_val {q : ℕ} (i : Fin q) :
    (finSuccMod i).val = if i.val + 1 < q then i.val + 1 else 0 := by
  rw [finSuccMod]
  split_ifs <;> rfl

theorem evenCycleFlow_pred_succ {q : ℕ} (i : Fin q) :
    evenCycleFlow_pred (finSuccMod i) = i := by
  apply Fin.ext
  rw [evenCycleFlow_pred_val, evenCycleFlow_succ_val]
  by_cases hs : i.val + 1 < q
  · rw [if_pos hs]
    have hnot : ¬ i.val + 1 = 0 := by omega
    rw [if_neg hnot]
    omega
  · rw [if_neg hs, if_pos rfl]
    omega

theorem evenCycleFlow_succ_pred {q : ℕ} (i : Fin q) :
    finSuccMod (evenCycleFlow_pred i) = i := by
  apply Fin.ext
  rw [evenCycleFlow_succ_val, evenCycleFlow_pred_val]
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

/-- The bijection `Fin m × Fin 2 ≃ Fin (2*m)`, ordered as an even/odd pair. -/
def evenCycleFlow_indexEquiv (m : ℕ) : Fin m × Fin 2 ≃ Fin (2 * m) :=
  (finProdFinEquiv : Fin m × Fin 2 ≃ Fin (m * 2)).trans (finCongr (Nat.mul_comm m 2))

/-- The even coordinate \(2k\). -/
def evenCycleFlow_even (m : ℕ) (k : Fin m) : Fin (2 * m) :=
  evenCycleFlow_indexEquiv m (k, (0 : Fin 2))

/-- The odd coordinate \(2k+1\). -/
def evenCycleFlow_odd (m : ℕ) (k : Fin m) : Fin (2 * m) :=
  evenCycleFlow_indexEquiv m (k, (1 : Fin 2))

@[simp] theorem evenCycleFlow_even_val {m : ℕ} (k : Fin m) :
    (evenCycleFlow_even m k).val = 2 * k.val := by
  simp [evenCycleFlow_even, evenCycleFlow_indexEquiv, finProdFinEquiv]

@[simp] theorem evenCycleFlow_odd_val {m : ℕ} (k : Fin m) :
    (evenCycleFlow_odd m k).val = 2 * k.val + 1 := by
  simp [evenCycleFlow_odd, evenCycleFlow_indexEquiv, finProdFinEquiv]
  omega

theorem evenCycleFlow_even_ne_odd {m : ℕ} (i j : Fin m) :
    evenCycleFlow_even m i ≠ evenCycleFlow_odd m j := by
  intro h
  have hp : (i, (0 : Fin 2)) = (j, (1 : Fin 2)) :=
    (evenCycleFlow_indexEquiv m).injective (by simpa only [evenCycleFlow_even,
      evenCycleFlow_odd] using h)
  have hc : (0 : Fin 2) = 1 := congrArg Prod.snd hp
  exact Fin.zero_ne_one hc

theorem evenCycleFlow_succ_even {m : ℕ} (_hm : 0 < m) (k : Fin m) :
    finSuccMod (evenCycleFlow_even m k) = evenCycleFlow_odd m k := by
  apply Fin.ext
  rw [evenCycleFlow_succ_val, evenCycleFlow_even_val, evenCycleFlow_odd_val]
  rw [if_pos (by omega : 2 * k.val + 1 < 2 * m)]

theorem evenCycleFlow_succ_odd {m : ℕ} (_hm : 0 < m) (k : Fin m) :
    finSuccMod (evenCycleFlow_odd m k) =
      evenCycleFlow_even m (finSuccMod k) := by
  apply Fin.ext
  simp only [evenCycleFlow_succ_val, evenCycleFlow_odd_val, evenCycleFlow_even_val]
  by_cases hk : k.val + 1 < m
  · rw [if_pos hk, if_pos (by omega : 2 * k.val + 1 + 1 < 2 * m)]
    omega
  · rw [if_neg hk, if_neg (by omega : ¬ 2 * k.val + 1 + 1 < 2 * m)]

theorem evenCycleFlow_pred_even {m : ℕ} (hm : 0 < m) (k : Fin m) :
    evenCycleFlow_pred (evenCycleFlow_even m k) =
      evenCycleFlow_odd m (evenCycleFlow_pred k) := by
  apply Fin.ext
  simp only [evenCycleFlow_pred_val, evenCycleFlow_even_val, evenCycleFlow_odd_val]
  by_cases hk : k.val = 0
  · rw [if_pos hk]
    have hz : 2 * k.val = 0 := by omega
    rw [if_pos hz]
    omega
  · rw [if_neg hk]
    rw [if_neg (by omega : ¬ 2 * k.val = 0)]
    omega

theorem evenCycleFlow_pred_odd {m : ℕ} (_hm : 0 < m) (k : Fin m) :
    evenCycleFlow_pred (evenCycleFlow_odd m k) = evenCycleFlow_even m k := by
  apply Fin.ext
  simp only [evenCycleFlow_pred_val, evenCycleFlow_odd_val, evenCycleFlow_even_val]
  rw [if_neg (by omega : ¬ 2 * k.val + 1 = 0)]
  omega

/-- Interleave even and odd coordinates through `evenCycleFlow_indexEquiv`. -/
def evenCycleFlow_interleave {m : ℕ} (u v : Fin m → ℕ) : Fin (2 * m) → ℕ :=
  fun i => match (evenCycleFlow_indexEquiv m).symm i with
    | (k, c) => if c = 0 then u k else v k

@[simp] theorem evenCycleFlow_interleave_even {m : ℕ} (u v : Fin m → ℕ) (k : Fin m) :
    evenCycleFlow_interleave u v (evenCycleFlow_even m k) = u k := by
  simp [evenCycleFlow_interleave, evenCycleFlow_even]

@[simp] theorem evenCycleFlow_interleave_odd {m : ℕ} (u v : Fin m → ℕ) (k : Fin m) :
    evenCycleFlow_interleave u v (evenCycleFlow_odd m k) = v k := by
  simp [evenCycleFlow_interleave, evenCycleFlow_odd]

/-- Split a cyclic sum into its even and odd coordinates. -/
theorem evenCycleFlow_sum_split {m : ℕ} (w : Fin (2 * m) → ℕ) :
    (∑ i, w i) = (∑ k : Fin m, w (evenCycleFlow_even m k)) +
      ∑ k : Fin m, w (evenCycleFlow_odd m k) := by
  rw [← Equiv.sum_comp (evenCycleFlow_indexEquiv m) w]
  rw [Fintype.sum_prod_type]
  change (∑ k : Fin m, ∑ c : Fin 2, w (evenCycleFlow_indexEquiv m (k, c))) = _
  simp only [Fin.sum_univ_two]
  simp [Finset.sum_add_distrib, evenCycleFlow_even, evenCycleFlow_odd]

/-- The four-element facet indexed by a cyclic edge. -/
noncomputable def evenCycleFlow_facet {m : ℕ} (i : Fin (2 * m)) :
    Finset (Fin 3 × Fin (2 * m)) :=
  {((0 : Fin 3), i), ((0 : Fin 3), finSuccMod i), ((1 : Fin 3), i), ((2 : Fin 3), i)}

/-- The clutter of all cyclic facets. -/
def evenCycleFlow_facets (m : ℕ) : Set (Finset (Fin 3 × Fin (2 * m))) :=
  Set.range (@evenCycleFlow_facet m)

private theorem evenCycleFlow_exists_minimalTransversal_subset
    {σ : Type*} [DecidableEq σ] (H : Set (Finset σ)) {T : Finset σ}
    (hT : IsTransversal H T) : ∃ C ∈ blocker H, C ⊆ T := by
  classical
  let S : Finset (Finset σ) := T.powerset.filter (fun U ↦ IsTransversal H U)
  have hTS : T ∈ S := by simp [S, hT]
  obtain ⟨C, hCS, hmin⟩ := Finset.exists_min_image S (fun U ↦ U.card) ⟨T, hTS⟩
  have hCS' := Finset.mem_filter.mp hCS
  have hCT : C ⊆ T := by simpa using hCS'.1
  refine ⟨C, ⟨hCS'.2, ?_⟩, hCT⟩
  intro U hUC hUtrans
  have hUT : U ⊆ T := fun i hi ↦ hCT (hUC.1 hi)
  have hUS : U ∈ S := by simp [S, hUT, hUtrans]
  exact (not_lt_of_ge (hmin U hUS)) (Finset.card_lt_card hUC)

private theorem evenCycleFlow_transversal_bound
    {σ : Type*} [DecidableEq σ] {H : Set (Finset σ)} {e : σ →₀ ℕ} {q : ℕ}
    (hblock : ∀ C ∈ blocker H, q ≤ ∑ v ∈ C, e v)
    {T : Finset σ} (hT : IsTransversal H T) :
    q ≤ ∑ v ∈ T, e v := by
  rcases evenCycleFlow_exists_minimalTransversal_subset H hT with ⟨C, hC, hCT⟩
  exact (hblock C hC).trans (Finset.sum_le_sum_of_subset hCT)

/-- Cheaper of the two private vertices in the facet indexed by `i`. -/
def evenCycleFlow_choice {m : ℕ} (e : Fin 3 × Fin (2 * m) →₀ ℕ) (i : Fin (2 * m)) :
    Fin 3 × Fin (2 * m) :=
  if e ((1 : Fin 3), i) ≤ e ((2 : Fin 3), i) then ((1 : Fin 3), i) else ((2 : Fin 3), i)

@[simp] theorem evenCycleFlow_choice_weight {m : ℕ}
    (e : Fin 3 × Fin (2 * m) →₀ ℕ) (i : Fin (2 * m)) :
    e (evenCycleFlow_choice e i) = min (e ((1 : Fin 3), i)) (e ((2 : Fin 3), i)) := by
  rw [evenCycleFlow_choice]
  split_ifs with h
  · simp [Nat.min_eq_left h]
  · simp [Nat.min_eq_right (Nat.le_of_not_ge h)]

/-- The minimum-weight transversal determined by a set of cyclic `x`-vertices. -/
noncomputable def evenCycleFlow_cover {m : ℕ}
    (e : Fin 3 × Fin (2 * m) →₀ ℕ) (S : Finset (Fin (2 * m))) :
    Finset (Fin 3 × Fin (2 * m)) :=
  (S.image fun i ↦ ((0 : Fin 3), i)) ∪
    ((Finset.univ.filter fun i ↦ i ∉ S ∧ finSuccMod i ∉ S).image
      (evenCycleFlow_choice e))

private theorem evenCycleFlow_choice_injective_on {m : ℕ}
    (e : Fin 3 × Fin (2 * m) →₀ ℕ) (s : Finset (Fin (2 * m))) :
    Set.InjOn (evenCycleFlow_choice e) s := by
  intro i hi j hj hij
  simp only [evenCycleFlow_choice] at hij
  split_ifs at hij <;> exact congrArg Prod.snd hij

private theorem evenCycleFlow_cover_transversal {m : ℕ}
    (e : Fin 3 × Fin (2 * m) →₀ ℕ) (S : Finset (Fin (2 * m))) :
    IsTransversal (evenCycleFlow_facets m) (evenCycleFlow_cover e S) := by
  classical
  intro E hE
  rcases hE with ⟨i, rfl⟩
  by_cases hi : i ∈ S
  · refine ⟨((0 : Fin 3), i), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · simp [evenCycleFlow_facet]
    · simp [evenCycleFlow_cover, hi]
  · by_cases hs : finSuccMod i ∈ S
    · refine ⟨((0 : Fin 3), finSuccMod i), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · simp [evenCycleFlow_facet]
      · simp [evenCycleFlow_cover, hs]
    · refine ⟨evenCycleFlow_choice e i, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · rw [evenCycleFlow_choice]
        split_ifs <;> simp [evenCycleFlow_facet]
      · simp only [evenCycleFlow_cover, Finset.mem_union, Finset.mem_image,
          Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr ⟨i, ⟨hi, hs⟩, rfl⟩

private theorem evenCycleFlow_cover_weight {m : ℕ}
    (e : Fin 3 × Fin (2 * m) →₀ ℕ) (S : Finset (Fin (2 * m))) :
    (∑ v ∈ evenCycleFlow_cover e S, e v) =
      (∑ i ∈ S, e ((0 : Fin 3), i)) +
        ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S ∧ finSuccMod i ∉ S),
          min (e ((1 : Fin 3), i)) (e ((2 : Fin 3), i)) := by
  classical
  let xs : Finset (Fin 3 × Fin (2 * m)) := S.image fun i ↦ ((0 : Fin 3), i)
  let ps : Finset (Fin 3 × Fin (2 * m)) :=
    (Finset.univ.filter fun i ↦ i ∉ S ∧ finSuccMod i ∉ S).image (evenCycleFlow_choice e)
  have hdis : Disjoint xs ps := by
    rw [Finset.disjoint_left]
    intro v hvx hvp
    rcases Finset.mem_image.mp hvx with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hvp with ⟨j, hj, hjv⟩
    rw [evenCycleFlow_choice] at hjv
    split_ifs at hjv with hle
    all_goals
      have hc := congrArg (fun z : Fin 3 => z.val) (congrArg Prod.fst hjv)
      simp at hc
  have hxs : (∑ v ∈ xs, e v) = ∑ i ∈ S, e ((0 : Fin 3), i) := by
    rw [Finset.sum_image]
    intro i hi j hj hij
    exact congrArg Prod.snd hij
  have hps : (∑ v ∈ ps, e v) =
      ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S ∧ finSuccMod i ∉ S),
        min (e ((1 : Fin 3), i)) (e ((2 : Fin 3), i)) := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i hi
      exact evenCycleFlow_choice_weight e i
    · exact evenCycleFlow_choice_injective_on e _
  change (∑ v ∈ xs ∪ ps, e v) = _
  rw [Finset.sum_union hdis, hxs, hps]

/-- Blocker inequalities imply the displayed inequality for every `x`-subset. -/
private theorem evenCycleFlow_subset_bound
    {m : ℕ} {e : Fin 3 × Fin (2 * m) →₀ ℕ} {q : ℕ}
    (hblock : ∀ C ∈ blocker (evenCycleFlow_facets m), q ≤ ∑ v ∈ C, e v)
    (S : Finset (Fin (2 * m))) :
    q ≤ (∑ i ∈ S, e ((0 : Fin 3), i)) +
      ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S ∧ finSuccMod i ∉ S),
        min (e ((1 : Fin 3), i)) (e ((2 : Fin 3), i)) := by
  have hT := evenCycleFlow_cover_transversal e S
  have hW := evenCycleFlow_transversal_bound hblock hT
  simpa [evenCycleFlow_cover_weight e S] using hW

/-- A bounded pair of integral arc values for the reindexed even cycle. -/
structure evenCycleFlow_box {m : ℕ} (U V : Fin m → ℕ) where
  u : ∀ k, Fin (U k + 1)
  v : ∀ k, Fin (V k + 1)
  deriving DecidableEq, Fintype

/-- The zero element of the bounded flow box. -/
def evenCycleFlow_boxZero {m : ℕ} (U V : Fin m → ℕ) : evenCycleFlow_box U V where
  u := fun k ↦ ⟨0, Nat.succ_pos (U k)⟩
  v := fun k ↦ ⟨0, Nat.succ_pos (V k)⟩

/-- Total value of a bounded flow. -/
def evenCycleFlow_boxValue {m : ℕ} {U V : Fin m → ℕ} (B : evenCycleFlow_box U V) : ℕ :=
  (∑ k, (B.u k).val) + ∑ k, (B.v k).val

/-- Load at the even vertex \(x_{2k}\). -/
def evenCycleFlow_left {m : ℕ} (u v : Fin m → ℕ) (k : Fin m) : ℕ :=
  u k + v (evenCycleFlow_pred k)

/-- Load at the odd vertex \(x_{2k+1}\). -/
def evenCycleFlow_right {m : ℕ} (u v : Fin m → ℕ) (k : Fin m) : ℕ :=
  u k + v k

/-- Total value of an unbounded pair of arc values. -/
def evenCycleFlow_value {m : ℕ} (u v : Fin m → ℕ) : ℕ :=
  (∑ k, u k) + ∑ k, v k

/-- Vertex-capacity feasibility; arc capacities are built into the box. -/
def evenCycleFlow_feasible {m : ℕ} {U V X R : Fin m → ℕ}
    (B : evenCycleFlow_box U V) : Prop :=
  let u : Fin m → ℕ := fun k ↦ (B.u k).val
  let v : Fin m → ℕ := fun k ↦ (B.v k).val
  (∀ k, evenCycleFlow_left u v k ≤ X k) ∧
    ∀ k, evenCycleFlow_right u v k ≤ R k

/-- A residual walk, with an explicit step bound to support shortest-path extraction. -/
inductive evenCycleFlow_reachAt
    {m : ℕ} (X U V : Fin m → ℕ) (u v : Fin m → ℕ) :
    ℕ → (Fin m ⊕ Fin m) → Prop where
  | source (k : Fin m) (hk : evenCycleFlow_left u v k < X k) :
      evenCycleFlow_reachAt X U V u v 0 (Sum.inl k)
  | wait {n : ℕ} {x : Fin m ⊕ Fin m}
      (h : evenCycleFlow_reachAt X U V u v n x) :
      evenCycleFlow_reachAt X U V u v (n + 1) x
  | forwardSame {n : ℕ} {k : Fin m}
      (h : evenCycleFlow_reachAt X U V u v n (Sum.inl k)) (hk : u k < U k) :
      evenCycleFlow_reachAt X U V u v (n + 1) (Sum.inr k)
  | forwardNext {n : ℕ} {k : Fin m}
      (h : evenCycleFlow_reachAt X U V u v n (Sum.inl (finSuccMod k)))
      (hk : v k < V k) :
      evenCycleFlow_reachAt X U V u v (n + 1) (Sum.inr k)
  | backwardSame {n : ℕ} {k : Fin m}
      (h : evenCycleFlow_reachAt X U V u v n (Sum.inr k)) (hk : 0 < u k) :
      evenCycleFlow_reachAt X U V u v (n + 1) (Sum.inl k)
  | backwardNext {n : ℕ} {k : Fin m}
      (h : evenCycleFlow_reachAt X U V u v n (Sum.inr k)) (hk : 0 < v k) :
      evenCycleFlow_reachAt X U V u v (n + 1) (Sum.inl (finSuccMod k))

/-- Residual reachability, obtained by forgetting the step bound. -/
def evenCycleFlow_reachable
    {m : ℕ} (X U V : Fin m → ℕ) (u v : Fin m → ℕ) (x : Fin m ⊕ Fin m) : Prop :=
  ∃ n, evenCycleFlow_reachAt X U V u v n x

/-- Least length of a residual walk; zero is a harmless value for unreachable vertices. -/
noncomputable def evenCycleFlow_rank
    {m : ℕ} (X U V : Fin m → ℕ) (u v : Fin m → ℕ) (x : Fin m ⊕ Fin m) : ℕ := by
  classical
  exact if h : evenCycleFlow_reachable X U V u v x then Nat.find h else 0

private theorem evenCycleFlow_rank_eq_find
    {m : ℕ} {X U V u v : Fin m → ℕ} {x : Fin m ⊕ Fin m}
    (h : evenCycleFlow_reachable X U V u v x) :
    evenCycleFlow_rank X U V u v x = @Nat.find _ (Classical.decPred _) h := by
  classical
  simp [evenCycleFlow_rank, h]

private theorem evenCycleFlow_rank_spec
    {m : ℕ} {X U V u v : Fin m → ℕ} {x : Fin m ⊕ Fin m}
    (h : evenCycleFlow_reachable X U V u v x) :
    evenCycleFlow_reachAt X U V u v (evenCycleFlow_rank X U V u v x) x := by
  classical
  rw [evenCycleFlow_rank_eq_find h]
  exact Nat.find_spec h

private theorem evenCycleFlow_rank_le
    {m : ℕ} {X U V u v : Fin m → ℕ} {x : Fin m ⊕ Fin m} {n : ℕ}
    (h : evenCycleFlow_reachAt X U V u v n x) :
    evenCycleFlow_rank X U V u v x ≤ n := by
  classical
  rw [evenCycleFlow_rank_eq_find (x := x) ⟨n, h⟩]
  exact Nat.find_min'
    (p := fun n ↦ evenCycleFlow_reachAt X U V u v n x) (H := ⟨n, h⟩) h

/-- A pseudo-flow differs from the initial flow only on vertices of rank at most `n`. -/
noncomputable def evenCycleFlow_support
    {m : ℕ} (X U V : Fin m → ℕ) (u v u' v' : Fin m → ℕ) (n : ℕ) : Prop :=
  (∀ k, evenCycleFlow_rank X U V u v (Sum.inl k) > n → u' k = u k) ∧
  (∀ k, evenCycleFlow_rank X U V u v (Sum.inr k) > n → u' k = u k) ∧
  (∀ k, evenCycleFlow_rank X U V u v (Sum.inl (finSuccMod k)) > n → v' k = v k) ∧
  (∀ k, evenCycleFlow_rank X U V u v (Sum.inr k) > n → v' k = v k)

/-- A pseudo-flow with one free unit at a reachable even vertex. -/
def evenCycleFlow_pseudoL
    {m : ℕ} {X R U V : Fin m → ℕ} (u v : Fin m → ℕ) (k : Fin m)
    (u' v' : Fin m → ℕ) : Prop :=
  (∀ j, u' j ≤ U j) ∧ (∀ j, v' j ≤ V j) ∧
  (∀ j, evenCycleFlow_left u' v' j + (if j = k then 1 else 0) ≤ X j) ∧
  (∀ j, evenCycleFlow_right u' v' j ≤ R j) ∧
  evenCycleFlow_value u' v' = evenCycleFlow_value u v

/-- A pseudo-flow with one unit to dispose of at a reachable odd vertex. -/
def evenCycleFlow_pseudoR
    {m : ℕ} {X R U V : Fin m → ℕ} (u v : Fin m → ℕ) (k : Fin m)
    (u' v' : Fin m → ℕ) : Prop :=
  (∀ j, u' j ≤ U j) ∧ (∀ j, v' j ≤ V j) ∧
  (∀ j, evenCycleFlow_left u' v' j ≤ X j) ∧
  (∀ j, j ≠ k → evenCycleFlow_right u' v' j ≤ R j) ∧
  evenCycleFlow_right u' v' k = evenCycleFlow_right u v k + 1 ∧
  evenCycleFlow_value u' v' = evenCycleFlow_value u v + 1

/-- Type-directed packaging of the two pseudo-flow predicates. -/
def evenCycleFlow_pseudo
    {m : ℕ} (X R U V : Fin m → ℕ) (u v : Fin m → ℕ)
    (x : Fin m ⊕ Fin m) (u' v' : Fin m → ℕ) : Prop :=
  match x with
  | Sum.inl k => evenCycleFlow_pseudoL (X := X) (R := R) (U := U) (V := V) u v k u' v'
  | Sum.inr k => evenCycleFlow_pseudoR (X := X) (R := R) (U := U) (V := V) u v k u' v'

private theorem evenCycleFlow_sum_update_add
    {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℕ) (k : α) :
    (∑ j, Function.update f k (f k + 1) j) = ∑ j, f j + 1 := by
  classical
  rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hE : (∑ x ∈ (Finset.univ : Finset α) \ {k}, f x) + f k = ∑ x, f x := by
    simpa [Finset.erase_eq] using
      Finset.sum_erase_add (Finset.univ : Finset α) f (Finset.mem_univ k)
  omega

private theorem evenCycleFlow_sum_update_sub
    {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℕ) (k : α) (hk : 0 < f k) :
    (∑ j, Function.update f k (f k - 1) j) + 1 = ∑ j, f j := by
  classical
  rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hE : (∑ x ∈ (Finset.univ : Finset α) \ {k}, f x) + f k = ∑ x, f x := by
    simpa [Finset.erase_eq] using
      Finset.sum_erase_add (Finset.univ : Finset α) f (Finset.mem_univ k)
  omega

/-- Every residually reachable vertex supports the appropriate integral pseudo-flow.

The proof uses a shortest residual walk.  The support component says that a pseudo-flow
realizing a vertex of rank `d` only changes arcs incident with vertices of rank at most `d`;
this makes the final residual edge equal to its value in the original flow. -/
private theorem evenCycleFlow_exists_pseudo
    {m : ℕ} {X R U V u v : Fin m → ℕ}
    (hu : ∀ k, u k ≤ U k) (hv : ∀ k, v k ≤ V k)
    (hXL : ∀ k, evenCycleFlow_left u v k ≤ X k)
    (hXR : ∀ k, evenCycleFlow_right u v k ≤ R k) :
    ∀ x, evenCycleFlow_reachable X U V u v x →
      ∃ u' v', evenCycleFlow_pseudo X R U V u v x u' v' ∧
        evenCycleFlow_support X U V u v u' v' (evenCycleFlow_rank X U V u v x) := by
  classical
  have main : ∀ n, ∀ x, evenCycleFlow_reachable X U V u v x →
      evenCycleFlow_rank X U V u v x = n →
      ∃ u' v', evenCycleFlow_pseudo X R U V u v x u' v' ∧
        evenCycleFlow_support X U V u v u' v' n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx hxn
      have hspec := evenCycleFlow_rank_spec hx
      rw [hxn] at hspec
      cases n with
      | zero =>
        cases hspec with
        | source k hk =>
          refine ⟨u, v, ?_, ?_⟩
          · change evenCycleFlow_pseudoL (X := X) (R := R) (U := U) (V := V) u v k u v
            refine ⟨hu, hv, ?_, hXR, rfl⟩
            intro j
            by_cases hj : j = k
            · subst j
              simpa using hk
            · simpa [hj] using hXL j
          · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro j hj <;> rfl
      | succ n =>
        have getPseudo (y : Fin m ⊕ Fin m)
            (hyAt : evenCycleFlow_reachAt X U V u v n y) :
            ∃ u0 v0, evenCycleFlow_pseudo X R U V u v y u0 v0 ∧
              evenCycleFlow_support X U V u v u0 v0
                (evenCycleFlow_rank X U V u v y) := by
          have hy : evenCycleFlow_reachable X U V u v y := ⟨n, hyAt⟩
          have hyRank : evenCycleFlow_rank X U V u v y ≤ n :=
            evenCycleFlow_rank_le hyAt
          exact ih (evenCycleFlow_rank X U V u v y) (by omega) y hy rfl
        cases hspec with
        | wait hprev =>
          have hle := evenCycleFlow_rank_le hprev
          omega
        | forwardSame hprev hcap =>
          rename_i k
          rcases getPseudo (Sum.inl k) hprev with ⟨u0, v0, hp0, hs0⟩
          have hpL : evenCycleFlow_pseudoL (X := X) (R := R) (U := U) (V := V)
              u v k u0 v0 := by simpa [evenCycleFlow_pseudo] using hp0
          rcases hpL with ⟨hu0, hv0, hL0, hR0, hVal0⟩
          have hpre : evenCycleFlow_rank X U V u v (Sum.inl k) ≤ n :=
            evenCycleFlow_rank_le hprev
          have hnew : evenCycleFlow_rank X U V u v (Sum.inr k) >
              evenCycleFlow_rank X U V u v (Sum.inl k) := by
            rw [hxn]
            omega
          have huEq : u0 k = u k := hs0.2.1 k hnew
          have hvEq : v0 k = v k := hs0.2.2.2 k hnew
          let u1 : Fin m → ℕ := Function.update u0 k (u0 k + 1)
          refine ⟨u1, v0, ?_, ?_⟩
          · change evenCycleFlow_pseudoR (X := X) (R := R) (U := U) (V := V)
                u v k u1 v0
            refine ⟨?_, hv0, ?_, ?_, ?_, ?_⟩
            · intro j
              by_cases hj : j = k
              · subst j
                have hc : u0 k < U k := by simpa [huEq] using hcap
                simp [u1]
                omega
              · simpa [u1, hj] using hu0 j
            · intro j
              by_cases hj : j = k
              · subst j
                have hLk : evenCycleFlow_left u0 v0 k + 1 ≤ X k := by simpa using hL0 k
                simp [evenCycleFlow_left] at hLk
                simp [evenCycleFlow_left, u1]
                omega
              · have hLj : evenCycleFlow_left u0 v0 j ≤ X j := by simpa [hj] using hL0 j
                simpa [evenCycleFlow_left, u1, hj] using hLj
            · intro j hj
              have hRj := hR0 j
              simpa [evenCycleFlow_right, u1, hj] using hRj
            · simp [evenCycleFlow_right, u1, huEq, hvEq]
              omega
            · have hsum := evenCycleFlow_sum_update_add u0 k
              change (∑ j, u1 j) + ∑ j, v0 j = evenCycleFlow_value u v + 1
              change (∑ j, u0 j) + ∑ j, v0 j = evenCycleFlow_value u v at hVal0
              rw [show (∑ j, u1 j) = ∑ j, u0 j + 1 by simpa [u1] using hsum]
              omega
          · refine ⟨?_, ?_, ?_, ?_⟩
            · intro j hj
              by_cases hjk : j = k
              · subst j
                omega
              · simpa [u1, hjk] using hs0.1 j (by omega)
            · intro j hj
              by_cases hjk : j = k
              · subst j
                rw [hxn] at hj
                omega
              · simpa [u1, hjk] using hs0.2.1 j (by omega)
            · intro j hj
              exact hs0.2.2.1 j (by omega)
            · intro j hj
              exact hs0.2.2.2 j (by omega)
        | forwardNext hprev hcap =>
          rename_i k
          rcases getPseudo (Sum.inl (finSuccMod k)) hprev with ⟨u0, v0, hp0, hs0⟩
          have hpL : evenCycleFlow_pseudoL (X := X) (R := R) (U := U) (V := V)
              u v (finSuccMod k) u0 v0 := by simpa [evenCycleFlow_pseudo] using hp0
          rcases hpL with ⟨hu0, hv0, hL0, hR0, hVal0⟩
          have hpre : evenCycleFlow_rank X U V u v (Sum.inl (finSuccMod k)) ≤ n :=
            evenCycleFlow_rank_le hprev
          have hnew : evenCycleFlow_rank X U V u v (Sum.inr k) >
              evenCycleFlow_rank X U V u v (Sum.inl (finSuccMod k)) := by
            rw [hxn]
            omega
          have huEq : u0 k = u k := hs0.2.1 k hnew
          have hvEq : v0 k = v k := hs0.2.2.2 k hnew
          let v1 : Fin m → ℕ := Function.update v0 k (v0 k + 1)
          refine ⟨u0, v1, ?_, ?_⟩
          · change evenCycleFlow_pseudoR (X := X) (R := R) (U := U) (V := V)
                u v k u0 v1
            refine ⟨hu0, ?_, ?_, ?_, ?_, ?_⟩
            · intro j
              by_cases hj : j = k
              · subst j
                have hc : v0 k < V k := by simpa [hvEq] using hcap
                simp [v1]
                omega
              · simpa [v1, hj] using hv0 j
            · intro j
              by_cases hj : j = finSuccMod k
              · subst j
                have hLk : evenCycleFlow_left u0 v0 (finSuccMod k) + 1 ≤
                    X (finSuccMod k) := by simpa using hL0 (finSuccMod k)
                simp [evenCycleFlow_left, evenCycleFlow_pred_succ] at hLk
                simp [evenCycleFlow_left, v1, evenCycleFlow_pred_succ]
                omega
              · have hLj : evenCycleFlow_left u0 v0 j ≤ X j := by simpa [hj] using hL0 j
                have hpj : evenCycleFlow_pred j ≠ k := by
                  intro hpj'
                  have heq := congrArg finSuccMod hpj'
                  exact hj (by simpa [evenCycleFlow_succ_pred] using heq)
                simpa [evenCycleFlow_left, v1, hpj] using hLj
            · intro j hj
              have hRj := hR0 j
              simpa [evenCycleFlow_right, v1, hj] using hRj
            · simp [evenCycleFlow_right, v1, huEq, hvEq]
              omega
            · have hsum := evenCycleFlow_sum_update_add v0 k
              change (∑ j, u0 j) + ∑ j, v1 j = evenCycleFlow_value u v + 1
              change (∑ j, u0 j) + ∑ j, v0 j = evenCycleFlow_value u v at hVal0
              rw [show (∑ j, v1 j) = ∑ j, v0 j + 1 by simpa [v1] using hsum]
              omega
          · refine ⟨?_, ?_, ?_, ?_⟩
            · intro j hj
              exact hs0.1 j (by omega)
            · intro j hj
              exact hs0.2.1 j (by omega)
            · intro j hj
              by_cases hjk : j = k
              · subst j
                omega
              · simpa [v1, hjk] using hs0.2.2.1 j (by omega)
            · intro j hj
              by_cases hjk : j = k
              · subst j
                rw [hxn] at hj
                omega
              · simpa [v1, hjk] using hs0.2.2.2 j (by omega)
        | backwardSame hprev hpos =>
          rename_i k
          rcases getPseudo (Sum.inr k) hprev with ⟨u0, v0, hp0, hs0⟩
          have hpR : evenCycleFlow_pseudoR (X := X) (R := R) (U := U) (V := V)
              u v k u0 v0 := by simpa [evenCycleFlow_pseudo] using hp0
          rcases hpR with ⟨hu0, hv0, hL0, hR0, hExact0, hVal0⟩
          have hpre : evenCycleFlow_rank X U V u v (Sum.inr k) ≤ n :=
            evenCycleFlow_rank_le hprev
          have hnew : evenCycleFlow_rank X U V u v (Sum.inl k) >
              evenCycleFlow_rank X U V u v (Sum.inr k) := by
            rw [hxn]
            omega
          have huEq : u0 k = u k := hs0.1 k hnew
          have hu0pos : 0 < u0 k := by simpa [huEq] using hpos
          let u1 : Fin m → ℕ := Function.update u0 k (u0 k - 1)
          refine ⟨u1, v0, ?_, ?_⟩
          · change evenCycleFlow_pseudoL (X := X) (R := R) (U := U) (V := V)
                u v k u1 v0
            refine ⟨?_, hv0, ?_, ?_, ?_⟩
            · intro j
              by_cases hj : j = k
              · subst j
                have huk := hu0 k
                simp [u1]
                omega
              · simpa [u1, hj] using hu0 j
            · intro j
              by_cases hj : j = k
              · subst j
                have hLk := hL0 k
                simp [evenCycleFlow_left, u1] at hLk ⊢
                omega
              · have hLj : evenCycleFlow_left u0 v0 j ≤ X j := hL0 j
                simpa [evenCycleFlow_left, u1, hj] using hLj
            · intro j
              by_cases hj : j = k
              · subst j
                have hRorig := hXR k
                simp [evenCycleFlow_right, u1, huEq] at hExact0 hRorig ⊢
                omega
              · have hRj := hR0 j hj
                simpa [evenCycleFlow_right, u1, hj] using hRj
            · have hsum := evenCycleFlow_sum_update_sub u0 k hu0pos
              change (∑ j, u1 j) + ∑ j, v0 j = evenCycleFlow_value u v
              change (∑ j, u0 j) + ∑ j, v0 j = evenCycleFlow_value u v + 1 at hVal0
              have hsum' : (∑ j, u1 j) + 1 = ∑ j, u0 j := by simpa [u1] using hsum
              omega
          · refine ⟨?_, ?_, ?_, ?_⟩
            · intro j hj
              by_cases hjk : j = k
              · subst j
                rw [hxn] at hj
                omega
              · simpa [u1, hjk] using hs0.1 j (by omega)
            · intro j hj
              by_cases hjk : j = k
              · subst j
                omega
              · simpa [u1, hjk] using hs0.2.1 j (by omega)
            · intro j hj
              exact hs0.2.2.1 j (by omega)
            · intro j hj
              exact hs0.2.2.2 j (by omega)
        | backwardNext hprev hpos =>
          rename_i k
          rcases getPseudo (Sum.inr k) hprev with ⟨u0, v0, hp0, hs0⟩
          have hpR : evenCycleFlow_pseudoR (X := X) (R := R) (U := U) (V := V)
              u v k u0 v0 := by simpa [evenCycleFlow_pseudo] using hp0
          rcases hpR with ⟨hu0, hv0, hL0, hR0, hExact0, hVal0⟩
          have hpre : evenCycleFlow_rank X U V u v (Sum.inr k) ≤ n :=
            evenCycleFlow_rank_le hprev
          have hnew : evenCycleFlow_rank X U V u v (Sum.inl (finSuccMod k)) >
              evenCycleFlow_rank X U V u v (Sum.inr k) := by
            rw [hxn]
            omega
          have hvEq : v0 k = v k := hs0.2.2.1 k hnew
          have hv0pos : 0 < v0 k := by simpa [hvEq] using hpos
          let v1 : Fin m → ℕ := Function.update v0 k (v0 k - 1)
          refine ⟨u0, v1, ?_, ?_⟩
          · change evenCycleFlow_pseudoL (X := X) (R := R) (U := U) (V := V)
                u v (finSuccMod k) u0 v1
            refine ⟨hu0, ?_, ?_, ?_, ?_⟩
            · intro j
              by_cases hj : j = k
              · subst j
                have hvk := hv0 k
                simp [v1]
                omega
              · simpa [v1, hj] using hv0 j
            · intro j
              by_cases hj : j = finSuccMod k
              · subst j
                have hLk := hL0 (finSuccMod k)
                simp [evenCycleFlow_left, v1, evenCycleFlow_pred_succ] at hLk ⊢
                omega
              · have hLj : evenCycleFlow_left u0 v0 j ≤ X j := hL0 j
                have hpj : evenCycleFlow_pred j ≠ k := by
                  intro hpj'
                  have heq := congrArg finSuccMod hpj'
                  exact hj (by simpa [evenCycleFlow_succ_pred] using heq)
                simpa [evenCycleFlow_left, v1, hj, hpj] using hLj
            · intro j
              by_cases hj : j = k
              · subst j
                have hRorig := hXR k
                simp [evenCycleFlow_right, v1, hvEq] at hExact0 hRorig ⊢
                omega
              · have hRj := hR0 j hj
                simpa [evenCycleFlow_right, v1, hj] using hRj
            · have hsum := evenCycleFlow_sum_update_sub v0 k hv0pos
              change (∑ j, u0 j) + ∑ j, v1 j = evenCycleFlow_value u v
              change (∑ j, u0 j) + ∑ j, v0 j = evenCycleFlow_value u v + 1 at hVal0
              have hsum' : (∑ j, v1 j) + 1 = ∑ j, v0 j := by simpa [v1] using hsum
              omega
          · refine ⟨?_, ?_, ?_, ?_⟩
            · intro j hj
              exact hs0.1 j (by omega)
            · intro j hj
              exact hs0.2.1 j (by omega)
            · intro j hj
              by_cases hjk : j = k
              · subst j
                rw [hxn] at hj
                omega
              · simpa [v1, hjk] using hs0.2.2.1 j (by omega)
            · intro j hj
              by_cases hjk : j = k
              · subst j
                omega
              · simpa [v1, hjk] using hs0.2.2.2 j (by omega)
  intro x hx
  exact main (evenCycleFlow_rank X U V u v x) x hx rfl

/-- Reindex a filtered sum by the cyclic predecessor. -/
private theorem evenCycleFlow_sum_filter_pred
    {m : ℕ} (P : Fin m → Prop) [DecidablePred P] (v : Fin m → ℕ) :
    (∑ k ∈ Finset.univ.filter P, v (evenCycleFlow_pred k)) =
      ∑ k ∈ Finset.univ.filter (fun k ↦ P (finSuccMod k)), v k := by
  classical
  refine Finset.sum_bij (fun a _ ↦ evenCycleFlow_pred a) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    simpa [evenCycleFlow_succ_pred] using ha
  · intro a₁ ha₁ a₂ ha₂ h
    have hh := congrArg finSuccMod h
    simpa [evenCycleFlow_succ_pred] using hh
  · intro b hb
    refine ⟨finSuccMod b, ?_, ?_⟩
    · simpa using hb
    · exact evenCycleFlow_pred_succ b
  · intro a ha
    rfl

/-- A flow with no augmenting sink has value equal to the capacity of its residual cut. -/
private theorem evenCycleFlow_cut_identity
    {m : ℕ} {u v X R U V : Fin m → ℕ}
    (P Q : Fin m → Prop) [DecidablePred P] [DecidablePred Q]
    (hsource : ∀ k, ¬ P k → evenCycleFlow_left u v k = X k)
    (hsink : ∀ k, Q k → evenCycleFlow_right u v k = R k)
    (hforwardU : ∀ k, P k → ¬ Q k → u k = U k)
    (hforwardV : ∀ k, P (finSuccMod k) → ¬ Q k → v k = V k)
    (hbackwardU : ∀ k, Q k → ¬ P k → u k = 0)
    (hbackwardV : ∀ k, Q k → ¬ P (finSuccMod k) → v k = 0) :
    evenCycleFlow_value u v =
      (∑ k ∈ Finset.univ.filter (fun k ↦ ¬ P k), X k) +
        (∑ k ∈ Finset.univ.filter Q, R k) +
        (∑ k ∈ Finset.univ.filter (fun k ↦ P k ∧ ¬ Q k), U k) +
        (∑ k ∈ Finset.univ.filter (fun k ↦ P (finSuccMod k) ∧ ¬ Q k), V k) := by
  classical
  have hpred : (∑ k : Fin m, v (evenCycleFlow_pred k)) = ∑ k, v k := by
    have h := evenCycleFlow_sum_filter_pred (fun _ : Fin m ↦ True) v
    simpa using h
  have hvalueLeft : evenCycleFlow_value u v =
      ∑ k : Fin m, evenCycleFlow_left u v k := by
    rw [evenCycleFlow_value, ← hpred]
    change (∑ k, u k) + (∑ k, v (evenCycleFlow_pred k)) =
      ∑ k, (u k + v (evenCycleFlow_pred k))
    rw [Finset.sum_add_distrib]
  have huSplitP :
      (∑ k ∈ Finset.univ.filter (fun k ↦ P k ∧ Q k), u k) +
          (∑ k ∈ Finset.univ.filter (fun k ↦ P k ∧ ¬ Q k), u k) =
        ∑ k ∈ Finset.univ.filter P, u k := by
    simpa [Finset.filter_filter, and_assoc, and_comm, and_left_comm] using
      (Finset.sum_filter_add_sum_filter_not (Finset.univ.filter P) Q u)
  have hvReindex :
      (∑ k ∈ Finset.univ.filter P, v (evenCycleFlow_pred k)) =
        ∑ k ∈ Finset.univ.filter (fun k ↦ P (finSuccMod k)), v k :=
    evenCycleFlow_sum_filter_pred P v
  have hvSplitP :
      (∑ k ∈ Finset.univ.filter (fun k ↦ P (finSuccMod k) ∧ Q k), v k) +
          (∑ k ∈ Finset.univ.filter (fun k ↦ P (finSuccMod k) ∧ ¬ Q k), v k) =
        ∑ k ∈ Finset.univ.filter (fun k ↦ P (finSuccMod k)), v k := by
    simpa [Finset.filter_filter, and_assoc, and_comm, and_left_comm] using
      (Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun k ↦ P (finSuccMod k))) Q v)
  have hsourceSplit :
      (∑ k ∈ Finset.univ.filter P, evenCycleFlow_left u v k) =
        (∑ k ∈ Finset.univ.filter (fun k ↦ P k ∧ Q k), u k) +
          (∑ k ∈ Finset.univ.filter (fun k ↦ P k ∧ ¬ Q k), u k) +
          (∑ k ∈ Finset.univ.filter (fun k ↦ P (finSuccMod k) ∧ Q k), v k) +
          (∑ k ∈ Finset.univ.filter (fun k ↦ P (finSuccMod k) ∧ ¬ Q k), v k) := by
    calc
      (∑ k ∈ Finset.univ.filter P, evenCycleFlow_left u v k) =
          (∑ k ∈ Finset.univ.filter P, u k) +
            (∑ k ∈ Finset.univ.filter P, v (evenCycleFlow_pred k)) := by
              change (∑ k ∈ Finset.univ.filter P,
                (u k + v (evenCycleFlow_pred k))) = _
              rw [Finset.sum_add_distrib]
      _ = (∑ k ∈ Finset.univ.filter (fun k ↦ P k ∧ Q k), u k) +
          (∑ k ∈ Finset.univ.filter (fun k ↦ P k ∧ ¬ Q k), u k) +
          (∑ k ∈ Finset.univ.filter (fun k ↦ P (finSuccMod k) ∧ Q k), v k) +
          (∑ k ∈ Finset.univ.filter (fun k ↦ P (finSuccMod k) ∧ ¬ Q k), v k) := by
            rw [hvReindex, ← huSplitP, ← hvSplitP]
            ac_rfl
  have huSplitQ :
      (∑ k ∈ Finset.univ.filter (fun k ↦ P k ∧ Q k), u k) +
          (∑ k ∈ Finset.univ.filter (fun k ↦ ¬ P k ∧ Q k), u k) =
        ∑ k ∈ Finset.univ.filter Q, u k := by
    simpa [Finset.filter_filter, and_assoc, and_comm, and_left_comm] using
      (Finset.sum_filter_add_sum_filter_not (Finset.univ.filter Q) P u)
  have hvSplitQ :
      (∑ k ∈ Finset.univ.filter (fun k ↦ P (finSuccMod k) ∧ Q k), v k) +
          (∑ k ∈ Finset.univ.filter (fun k ↦ ¬ P (finSuccMod k) ∧ Q k), v k) =
        ∑ k ∈ Finset.univ.filter Q, v k := by
    simpa [Finset.filter_filter, and_assoc, and_comm, and_left_comm] using
      (Finset.sum_filter_add_sum_filter_not (Finset.univ.filter Q)
        (fun k ↦ P (finSuccMod k)) v)
  have hbackUzero :
      (∑ k ∈ Finset.univ.filter (fun k ↦ ¬ P k ∧ Q k), u k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    exact hbackwardU k hk'.2.2 hk'.2.1
  have hbackVzero :
      (∑ k ∈ Finset.univ.filter (fun k ↦ ¬ P (finSuccMod k) ∧ Q k), v k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    exact hbackwardV k hk'.2.2 hk'.2.1
  have hsinkSplit :
      (∑ k ∈ Finset.univ.filter Q, R k) =
        (∑ k ∈ Finset.univ.filter (fun k ↦ P k ∧ Q k), u k) +
          (∑ k ∈ Finset.univ.filter (fun k ↦ P (finSuccMod k) ∧ Q k), v k) := by
    calc
      (∑ k ∈ Finset.univ.filter Q, R k) =
          ∑ k ∈ Finset.univ.filter Q, evenCycleFlow_right u v k := by
            apply Finset.sum_congr rfl
            intro k hk
            exact (hsink k (Finset.mem_filter.mp hk).2).symm
      _ = (∑ k ∈ Finset.univ.filter Q, u k) +
            ∑ k ∈ Finset.univ.filter Q, v k := by
              change (∑ k ∈ Finset.univ.filter Q, (u k + v k)) = _
              rw [Finset.sum_add_distrib]
      _ = (∑ k ∈ Finset.univ.filter (fun k ↦ P k ∧ Q k), u k) +
            (∑ k ∈ Finset.univ.filter (fun k ↦ ¬ P k ∧ Q k), u k) +
            ((∑ k ∈ Finset.univ.filter (fun k ↦ P (finSuccMod k) ∧ Q k), v k) +
              (∑ k ∈ Finset.univ.filter (fun k ↦ ¬ P (finSuccMod k) ∧ Q k), v k)) := by
                rw [← huSplitQ, ← hvSplitQ]
      _ = _ := by rw [hbackUzero, hbackVzero]; omega
  have hreachable :
      (∑ k ∈ Finset.univ.filter P, evenCycleFlow_left u v k) =
        (∑ k ∈ Finset.univ.filter (fun k ↦ P k ∧ ¬ Q k), u k) +
          (∑ k ∈ Finset.univ.filter (fun k ↦ P (finSuccMod k) ∧ ¬ Q k), v k) +
          (∑ k ∈ Finset.univ.filter Q, R k) := by
    rw [hsourceSplit, hsinkSplit]
    omega
  have hcrossU :
      (∑ k ∈ Finset.univ.filter (fun k ↦ P k ∧ ¬ Q k), u k) =
        ∑ k ∈ Finset.univ.filter (fun k ↦ P k ∧ ¬ Q k), U k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    exact hforwardU k hk'.2.1 hk'.2.2
  have hcrossV :
      (∑ k ∈ Finset.univ.filter (fun k ↦ P (finSuccMod k) ∧ ¬ Q k), v k) =
        ∑ k ∈ Finset.univ.filter (fun k ↦ P (finSuccMod k) ∧ ¬ Q k), V k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    exact hforwardV k hk'.2.1 hk'.2.2
  have hunreachable :
      (∑ k ∈ Finset.univ.filter (fun k ↦ ¬ P k), evenCycleFlow_left u v k) =
        ∑ k ∈ Finset.univ.filter (fun k ↦ ¬ P k), X k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hsource k (Finset.mem_filter.mp hk).2
  calc
    evenCycleFlow_value u v =
        (∑ k ∈ Finset.univ.filter P, evenCycleFlow_left u v k) +
          (∑ k ∈ Finset.univ.filter (fun k ↦ ¬ P k), evenCycleFlow_left u v k) := by
            rw [hvalueLeft]
            exact (Finset.sum_filter_add_sum_filter_not Finset.univ P
              (fun k ↦ evenCycleFlow_left u v k)).symm
    _ = ((∑ k ∈ Finset.univ.filter (fun k ↦ P k ∧ ¬ Q k), u k) +
          (∑ k ∈ Finset.univ.filter (fun k ↦ P (finSuccMod k) ∧ ¬ Q k), v k) +
          (∑ k ∈ Finset.univ.filter Q, R k)) +
          (∑ k ∈ Finset.univ.filter (fun k ↦ ¬ P k), evenCycleFlow_left u v k) := by
            rw [hreachable]
    _ = _ := by
      rw [hcrossU, hcrossV, hunreachable]
      ac_rfl

/-- Truncate a finite natural-valued function to a prescribed sub-sum. -/
private theorem evenCycleFlow_exists_truncate
    {α : Type*} [Fintype α] [DecidableEq α] (t : α → ℕ) {q : ℕ}
    (hq : q ≤ ∑ i, t i) : ∃ r : α → ℕ, (∑ i, r i) = q ∧ ∀ i, r i ≤ t i := by
  classical
  have aux : ∀ s : Finset α, ∀ {q : ℕ}, q ≤ ∑ i ∈ s, t i →
      ∃ r : α → ℕ, (∑ i ∈ s, r i) = q ∧
        (∀ i ∈ s, r i ≤ t i) ∧ (∀ i, i ∉ s → r i = 0) := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro q hq
      have hq0 : q = 0 := by simpa using hq
      refine ⟨fun _ ↦ 0, ?_, ?_, ?_⟩
      · simp [hq0]
      · simp
      · simp
    | @insert a s ha ih =>
      intro q hq
      have hsum : (∑ i ∈ insert a s, t i) = t a + ∑ i ∈ s, t i := by
        simp [ha]
      by_cases hqa : q ≤ t a
      · let r : α → ℕ := Function.update (fun _ ↦ 0) a q
        refine ⟨r, ?_, ?_, ?_⟩
        · rw [Finset.sum_insert ha]
          have hz : (∑ i ∈ s, r i) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have hne : i ≠ a := by
              intro h
              subst i
              exact ha hi
            simp [r, hne]
          simp [r, hz]
        · intro i hi
          rw [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · simpa [r] using hqa
          · have hne : i ≠ a := by
              intro h
              subst i
              exact ha hi
            simp [r, hne]
        · intro i hi
          have hia : i ≠ a := by
            intro h
            subst i
            exact hi (Finset.mem_insert_self a s)
          simp [r, hia]
      · have htaq : t a < q := Nat.lt_of_not_ge hqa
        have hrest : q - t a ≤ ∑ i ∈ s, t i := by
          rw [hsum] at hq
          omega
        rcases ih hrest with ⟨r0, hr0sum, hr0le, hr0out⟩
        let r : α → ℕ := Function.update r0 a (t a)
        refine ⟨r, ?_, ?_, ?_⟩
        · rw [Finset.sum_insert ha]
          have hs : (∑ i ∈ s, r i) = ∑ i ∈ s, r0 i := by
            apply Finset.sum_congr rfl
            intro i hi
            have hne : i ≠ a := by
              intro h
              subst i
              exact ha hi
            simp [r, hne]
          simp [r, hs, hr0sum]
          omega
        · intro i hi
          rw [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · simp [r]
          · have hne : i ≠ a := by
              intro h
              subst i
              exact ha hi
            simpa [r, hne] using hr0le i hi
        · intro i hi
          have hia : i ≠ a := by
            intro h
            subst i
            exact hi (Finset.mem_insert_self a s)
          have his : i ∉ s := fun his => hi (Finset.mem_insert_of_mem his)
          simpa [r, hia] using hr0out i his
  rcases aux Finset.univ hq with ⟨r, hrsum, hrle, _⟩
  exact ⟨r, by simpa using hrsum, fun i => hrle i (Finset.mem_univ i)⟩

/-- A value-maximizing integral flow exists in the bounded finite flow space. -/
private theorem evenCycleFlow_exists_maximalFlow
    {m : ℕ} (X R U V : Fin m → ℕ) :
    ∃ u v : Fin m → ℕ,
      (∀ k, u k ≤ U k) ∧ (∀ k, v k ≤ V k) ∧
      (∀ k, evenCycleFlow_left u v k ≤ X k) ∧
      (∀ k, evenCycleFlow_right u v k ≤ R k) ∧
      (∀ u' v' : Fin m → ℕ,
        (∀ k, u' k ≤ U k) → (∀ k, v' k ≤ V k) →
        (∀ k, evenCycleFlow_left u' v' k ≤ X k) →
        (∀ k, evenCycleFlow_right u' v' k ≤ R k) →
        evenCycleFlow_value u' v' ≤ evenCycleFlow_value u v) := by
  classical
  let F : Finset (evenCycleFlow_box U V) :=
    Finset.univ.filter (evenCycleFlow_feasible (X := X) (R := R))
  have hzero : evenCycleFlow_boxZero U V ∈ F := by
    have hf : evenCycleFlow_feasible (X := X) (R := R) (evenCycleFlow_boxZero U V) := by
      simp [evenCycleFlow_feasible, evenCycleFlow_boxZero,
        evenCycleFlow_left, evenCycleFlow_right]
    simpa [F] using hf
  obtain ⟨B, hBF, hBmax⟩ :=
    Finset.exists_max_image F evenCycleFlow_boxValue ⟨evenCycleFlow_boxZero U V, hzero⟩
  let u : Fin m → ℕ := fun k ↦ (B.u k).val
  let v : Fin m → ℕ := fun k ↦ (B.v k).val
  have hu : ∀ k, u k ≤ U k := by
    intro k
    have hk := (B.u k).isLt
    dsimp [u]
    omega
  have hv : ∀ k, v k ≤ V k := by
    intro k
    have hk := (B.v k).isLt
    dsimp [v]
    omega
  have hBfeas : evenCycleFlow_feasible (X := X) (R := R) B := by
    simpa [F] using hBF
  have hXL : ∀ k, evenCycleFlow_left u v k ≤ X k := by
    simpa [evenCycleFlow_feasible, u, v] using hBfeas.1
  have hXR : ∀ k, evenCycleFlow_right u v k ≤ R k := by
    simpa [evenCycleFlow_feasible, u, v] using hBfeas.2
  refine ⟨u, v, hu, hv, hXL, hXR, ?_⟩
  intro u' v' hu' hv' hXL' hXR'
  let B' : evenCycleFlow_box U V :=
    { u := fun k ↦ ⟨u' k, by have hk := hu' k; omega⟩
      v := fun k ↦ ⟨v' k, by have hk := hv' k; omega⟩ }
  have hBfeas' : evenCycleFlow_feasible (X := X) (R := R) B' := by
    change (∀ k, evenCycleFlow_left u' v' k ≤ X k) ∧
      ∀ k, evenCycleFlow_right u' v' k ≤ R k
    exact ⟨hXL', hXR'⟩
  have hBF' : B' ∈ F := by simpa [F] using hBfeas'
  have hle := hBmax B' hBF'
  change evenCycleFlow_value u' v' ≤ evenCycleFlow_value u v at hle
  exact hle

/-- Integral packing for the even-cycle family, from inequalities on its blocker. -/
theorem evenCycleFlow_packing_of_blocker
    {m : ℕ} (hm : 0 < m)
    {e : Fin 3 × Fin (2 * m) →₀ ℕ} {q : ℕ}
    (hblock : ∀ C ∈ blocker (evenCycleFlow_facets m),
      q ≤ ∑ v ∈ C, e v) :
    ∃ t : Fin (2 * m) → ℕ,
      ∑ i, t i = q ∧
      (∀ i, t i ≤ e (1, i)) ∧
      (∀ i, t i ≤ e (2, i)) ∧
      (∀ i, t i + t (evenCycleFlow_pred i) ≤ e (0, i)) := by
  classical
  let XC : Fin m → ℕ := fun k ↦ e ((0 : Fin 3), evenCycleFlow_even m k)
  let RC : Fin m → ℕ := fun k ↦ e ((0 : Fin 3), evenCycleFlow_odd m k)
  let UC : Fin m → ℕ := fun k ↦
    min (e ((1 : Fin 3), evenCycleFlow_even m k))
      (e ((2 : Fin 3), evenCycleFlow_even m k))
  let VC : Fin m → ℕ := fun k ↦
    min (e ((1 : Fin 3), evenCycleFlow_odd m k))
      (e ((2 : Fin 3), evenCycleFlow_odd m k))
  rcases evenCycleFlow_exists_maximalFlow XC RC UC VC with
    ⟨u, v, hu, hv, hXL, hXR, hmax⟩
  let PL : Fin m → Prop := fun k ↦
    evenCycleFlow_reachable XC UC VC u v (Sum.inl k)
  let PR : Fin m → Prop := fun k ↦
    evenCycleFlow_reachable XC UC VC u v (Sum.inr k)
  have hNoSink : ¬ ∃ k, PR k ∧ evenCycleFlow_right u v k < RC k := by
    rintro ⟨k, hkR, hslack⟩
    rcases evenCycleFlow_exists_pseudo
        (X := XC) (R := RC) (U := UC) (V := VC) hu hv hXL hXR (Sum.inr k) hkR with
      ⟨u', v', hp, _⟩
    have hpR : evenCycleFlow_pseudoR (X := XC) (R := RC) (U := UC) (V := VC)
        u v k u' v' := by simpa [evenCycleFlow_pseudo] using hp
    rcases hpR with ⟨hu', hv', hXL', hXR', hExact, hValue⟩
    have hXRall : ∀ j, evenCycleFlow_right u' v' j ≤ RC j := by
      intro j
      by_cases hj : j = k
      · subst j
        rw [hExact]
        omega
      · exact hXR' j hj
    have hle := hmax u' v' hu' hv' hXL' hXRall
    omega
  have hsource : ∀ k, ¬ PL k → evenCycleFlow_left u v k = XC k := by
    intro k hk
    have hnlt : ¬ evenCycleFlow_left u v k < XC k := by
      intro hlt
      exact hk ⟨0, evenCycleFlow_reachAt.source k hlt⟩
    exact le_antisymm (hXL k) (le_of_not_gt hnlt)
  have hsink : ∀ k, PR k → evenCycleFlow_right u v k = RC k := by
    intro k hk
    have hnlt : ¬ evenCycleFlow_right u v k < RC k := by
      intro hlt
      exact hNoSink ⟨k, hk, hlt⟩
    exact le_antisymm (hXR k) (le_of_not_gt hnlt)
  have hforwardU : ∀ k, PL k → ¬ PR k → u k = UC k := by
    intro k hPL hnPR
    have hnlt : ¬ u k < UC k := by
      intro hlt
      apply hnPR
      rcases hPL with ⟨n, hAt⟩
      exact ⟨n + 1, evenCycleFlow_reachAt.forwardSame hAt hlt⟩
    exact le_antisymm (hu k) (le_of_not_gt hnlt)
  have hforwardV : ∀ k, PL (finSuccMod k) → ¬ PR k → v k = VC k := by
    intro k hPL hnPR
    have hnlt : ¬ v k < VC k := by
      intro hlt
      apply hnPR
      rcases hPL with ⟨n, hAt⟩
      exact ⟨n + 1, evenCycleFlow_reachAt.forwardNext hAt hlt⟩
    exact le_antisymm (hv k) (le_of_not_gt hnlt)
  have hbackwardU : ∀ k, PR k → ¬ PL k → u k = 0 := by
    intro k hPR hnPL
    apply Nat.eq_zero_of_not_pos
    intro hpos
    apply hnPL
    rcases hPR with ⟨n, hAt⟩
    exact ⟨n + 1, evenCycleFlow_reachAt.backwardSame hAt hpos⟩
  have hbackwardV : ∀ k, PR k → ¬ PL (finSuccMod k) → v k = 0 := by
    intro k hPR hnPL
    apply Nat.eq_zero_of_not_pos
    intro hpos
    apply hnPL
    rcases hPR with ⟨n, hAt⟩
    exact ⟨n + 1, evenCycleFlow_reachAt.backwardNext hAt hpos⟩
  have hcut := evenCycleFlow_cut_identity PL PR hsource hsink
    hforwardU hforwardV hbackwardU hbackwardV
  let A : Finset (Fin m) := Finset.univ.filter (fun k ↦ ¬ PL k)
  let B : Finset (Fin m) := Finset.univ.filter PR
  let S : Finset (Fin (2 * m)) :=
    A.image (evenCycleFlow_even m) ∪ B.image (evenCycleFlow_odd m)
  have hevInj : Set.InjOn (evenCycleFlow_even m) A := by
    intro i hi j hj hij
    have hp : (i, (0 : Fin 2)) = (j, (0 : Fin 2)) :=
      (evenCycleFlow_indexEquiv m).injective (by simpa [evenCycleFlow_even] using hij)
    exact congrArg Prod.fst hp
  have hodInj : Set.InjOn (evenCycleFlow_odd m) B := by
    intro i hi j hj hij
    have hp : (i, (1 : Fin 2)) = (j, (1 : Fin 2)) :=
      (evenCycleFlow_indexEquiv m).injective (by simpa [evenCycleFlow_odd] using hij)
    exact congrArg Prod.fst hp
  have hABdis : Disjoint (A.image (evenCycleFlow_even m))
      (B.image (evenCycleFlow_odd m)) := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    rcases Finset.mem_image.mp hzA with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hzB with ⟨j, hj, hji⟩
    exact evenCycleFlow_even_ne_odd i j hji.symm
  have hmemEven (k : Fin m) : evenCycleFlow_even m k ∈ S ↔ ¬ PL k := by
    constructor
    · intro hk
      rcases Finset.mem_union.mp hk with hk | hk
      · rcases Finset.mem_image.mp hk with ⟨j, hjA, hEq⟩
        have hp : (j, (0 : Fin 2)) = (k, (0 : Fin 2)) :=
          (evenCycleFlow_indexEquiv m).injective (by simpa [evenCycleFlow_even] using hEq)
        have hjk : j = k := congrArg Prod.fst hp
        subst j
        exact (Finset.mem_filter.mp hjA).2
      · rcases Finset.mem_image.mp hk with ⟨j, hjB, hEq⟩
        exact (evenCycleFlow_even_ne_odd k j hEq.symm).elim
    · intro hk
      apply Finset.mem_union.mpr
      exact Or.inl (Finset.mem_image.mpr ⟨k, by simpa [A] using hk, rfl⟩)
  have hmemOdd (k : Fin m) : evenCycleFlow_odd m k ∈ S ↔ PR k := by
    constructor
    · intro hk
      rcases Finset.mem_union.mp hk with hk | hk
      · rcases Finset.mem_image.mp hk with ⟨j, hjA, hEq⟩
        exact (evenCycleFlow_even_ne_odd j k hEq).elim
      · rcases Finset.mem_image.mp hk with ⟨j, hjB, hEq⟩
        have hp : (j, (1 : Fin 2)) = (k, (1 : Fin 2)) :=
          (evenCycleFlow_indexEquiv m).injective (by simpa [evenCycleFlow_odd] using hEq)
        have hjk : j = k := congrArg Prod.fst hp
        subst j
        exact (Finset.mem_filter.mp hjB).2
    · intro hk
      apply Finset.mem_union.mpr
      exact Or.inr (Finset.mem_image.mpr ⟨k, by simpa [B] using hk, rfl⟩)
  have hxSum :
      (∑ i ∈ S, e ((0 : Fin 3), i)) =
        (∑ k ∈ A, XC k) + ∑ k ∈ B, RC k := by
    change (∑ i ∈ A.image (evenCycleFlow_even m) ∪
        B.image (evenCycleFlow_odd m), e ((0 : Fin 3), i)) = _
    rw [Finset.sum_union hABdis]
    rw [Finset.sum_image hevInj, Finset.sum_image hodInj]
  have hUncovered :
      (∑ i ∈ Finset.univ.filter
          (fun i ↦ i ∉ S ∧ finSuccMod i ∉ S),
          min (e ((1 : Fin 3), i)) (e ((2 : Fin 3), i))) =
        (∑ k ∈ Finset.univ.filter (fun k ↦ PL k ∧ ¬ PR k), UC k) +
        ∑ k ∈ Finset.univ.filter (fun k ↦ PL (finSuccMod k) ∧ ¬ PR k), VC k := by
    rw [Finset.sum_filter]
    rw [evenCycleFlow_sum_split]
    congr 1
    · rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      simp [hmemEven, hmemOdd, evenCycleFlow_succ_even hm, UC]
    · rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      simp [hmemEven, hmemOdd, evenCycleFlow_succ_odd hm, and_comm, VC]
  have hsubset := evenCycleFlow_subset_bound hblock S
  have hWeights :
      (∑ i ∈ S, e ((0 : Fin 3), i)) +
          (∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S ∧ finSuccMod i ∉ S),
            min (e ((1 : Fin 3), i)) (e ((2 : Fin 3), i))) =
        ((∑ k ∈ Finset.univ.filter (fun k ↦ ¬ PL k), XC k) +
          (∑ k ∈ Finset.univ.filter PR, RC k) +
          (∑ k ∈ Finset.univ.filter (fun k ↦ PL k ∧ ¬ PR k), UC k) +
          (∑ k ∈ Finset.univ.filter
            (fun k ↦ PL (finSuccMod k) ∧ ¬ PR k), VC k)) := by
    change _ = ((∑ k ∈ A, XC k) + (∑ k ∈ B, RC k) + _ + _)
    rw [hxSum, hUncovered]
    ac_rfl
  have hqValue : q ≤ evenCycleFlow_value u v := by
    calc
      q ≤ (∑ i ∈ S, e ((0 : Fin 3), i)) +
          (∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S ∧ finSuccMod i ∉ S),
            min (e ((1 : Fin 3), i)) (e ((2 : Fin 3), i))) := hsubset
      _ = ((∑ k ∈ Finset.univ.filter (fun k ↦ ¬ PL k), XC k) +
          (∑ k ∈ Finset.univ.filter PR, RC k) +
          (∑ k ∈ Finset.univ.filter (fun k ↦ PL k ∧ ¬ PR k), UC k) +
          (∑ k ∈ Finset.univ.filter
            (fun k ↦ PL (finSuccMod k) ∧ ¬ PR k), VC k)) := hWeights
      _ = evenCycleFlow_value u v := hcut.symm
  let t0 : Fin (2 * m) → ℕ := evenCycleFlow_interleave u v
  have ht0Sum : (∑ i, t0 i) = evenCycleFlow_value u v := by
    rw [evenCycleFlow_sum_split]
    simp [t0, evenCycleFlow_value]
  have huY : ∀ k, u k ≤ e ((1 : Fin 3), evenCycleFlow_even m k) := by
    intro k
    have hk := hu k
    dsimp [UC] at hk
    exact hk.trans (Nat.min_le_left _ _)
  have huZ : ∀ k, u k ≤ e ((2 : Fin 3), evenCycleFlow_even m k) := by
    intro k
    have hk := hu k
    dsimp [UC] at hk
    exact hk.trans (Nat.min_le_right _ _)
  have hvY : ∀ k, v k ≤ e ((1 : Fin 3), evenCycleFlow_odd m k) := by
    intro k
    have hk := hv k
    dsimp [VC] at hk
    exact hk.trans (Nat.min_le_left _ _)
  have hvZ : ∀ k, v k ≤ e ((2 : Fin 3), evenCycleFlow_odd m k) := by
    intro k
    have hk := hv k
    dsimp [VC] at hk
    exact hk.trans (Nat.min_le_right _ _)
  have ht0Y : ∀ i, t0 i ≤ e ((1 : Fin 3), i) := by
    intro i
    rcases (evenCycleFlow_indexEquiv m).surjective i with ⟨⟨k, c⟩, rfl⟩
    fin_cases c
    · simpa [t0, evenCycleFlow_interleave, evenCycleFlow_even] using huY k
    · simpa [t0, evenCycleFlow_interleave, evenCycleFlow_odd] using hvY k
  have ht0Z : ∀ i, t0 i ≤ e ((2 : Fin 3), i) := by
    intro i
    rcases (evenCycleFlow_indexEquiv m).surjective i with ⟨⟨k, c⟩, rfl⟩
    fin_cases c
    · simpa [t0, evenCycleFlow_interleave, evenCycleFlow_even] using huZ k
    · simpa [t0, evenCycleFlow_interleave, evenCycleFlow_odd] using hvZ k
  have ht0X : ∀ i, t0 i + t0 (evenCycleFlow_pred i) ≤ e ((0 : Fin 3), i) := by
    intro i
    rcases (evenCycleFlow_indexEquiv m).surjective i with ⟨⟨k, c⟩, rfl⟩
    fin_cases c
    · change t0 (evenCycleFlow_even m k) +
          t0 (evenCycleFlow_pred (evenCycleFlow_even m k)) ≤
        e ((0 : Fin 3), evenCycleFlow_even m k)
      rw [evenCycleFlow_pred_even hm k]
      simpa [t0, evenCycleFlow_interleave, XC, evenCycleFlow_left] using hXL k
    · change t0 (evenCycleFlow_odd m k) +
          t0 (evenCycleFlow_pred (evenCycleFlow_odd m k)) ≤
        e ((0 : Fin 3), evenCycleFlow_odd m k)
      rw [evenCycleFlow_pred_odd hm k]
      simpa [t0, evenCycleFlow_interleave, RC, evenCycleFlow_right, Nat.add_comm] using hXR k
  have hqT0 : q ≤ ∑ i, t0 i := by simpa [ht0Sum] using hqValue
  rcases evenCycleFlow_exists_truncate t0 hqT0 with ⟨t, htSum, htLe⟩
  refine ⟨t, htSum, ?_, ?_, ?_⟩
  · intro i
    exact (htLe i).trans (ht0Y i)
  · intro i
    exact (htLe i).trans (ht0Z i)
  · intro i
    have hi := htLe i
    have hp := htLe (evenCycleFlow_pred i)
    have hx := ht0X i
    omega

end SimisFormal
