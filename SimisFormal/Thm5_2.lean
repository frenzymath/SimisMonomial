/-
Theorem 5.2: at most one intervening component forces exponent coherence and hence a
squarefree diagonal root.

Equation (2) and the core cases of Lemma 5.1 are imported from their dedicated files.
The `_ofStdSymbolic` declarations retain explicit `HasStdSymbolicFormula` and
`thm52_lem51Obstruction` arguments for compatibility.  The `_ofCoreObstruction`
declarations use `eq2_standardSymbolic` but retain the specialized obstruction.  The
final `thm52`, `thm52_exponent_coherence`, and `thm52_hasSqRoot` declarations discharge
both inputs: `thm52_lem51Obstruction_holds` pads a core monomial by all variables
outside `A k ∪ A l`, factors its image under the global square equality, and restricts
the two factors to the paper's three selected variables before applying the imported
core obstructions.
-/
import SimisFormal.Defs
import SimisFormal.Basic
import SimisFormal.Eq2_StandardSymbolic
import SimisFormal.Lem5_1
import SimisFormal.Thm3_1
import SimisFormal.DiagAssociatedPreserve

open MvPolynomial
open SimisFormal
open scoped BigOperators
variable {σ ι : Type*} [DecidableEq σ]
/-- Forced positive weights; an unused variable is assigned weight one. -/
noncomputable def thm52_weights (A : ι → Finset σ) (a : ι → σ → ℕ) (i : σ) : ℕ := by
  classical
  exact if h : ∃ j, i ∈ A j then a (Classical.choose h) i else 1

/-- Expand a core exponent vector along an injective choice of ambient variables. -/
noncomputable def thm52_expandExp {ν : Type*} (f : ν ↪ σ) (e : ν →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.embDomain f e

/-- Restrict an ambient exponent vector to an injective core. -/
noncomputable def thm52_restrictExp {ν : Type*} (f : ν ↪ σ) (e : σ →₀ ℕ) : ν →₀ ℕ :=
  Finsupp.comapDomain f e (by
    intro x _ y _ hxy
    exact f.injective hxy)

omit [DecidableEq σ] in
/-- Expanded exponents recover the original coordinates. -/
@[simp] theorem thm52_expandExp_apply_of_range {ν : Type*} (f : ν ↪ σ)
    (e : ν →₀ ℕ) (r : ν) : thm52_expandExp f e (f r) = e r := by
  simp [thm52_expandExp, Finsupp.embDomain_apply]

omit [DecidableEq σ] in
/-- An expanded exponent vanishes off the chosen variables. -/
theorem thm52_expandExp_apply_of_not_range {ν : Type*} (f : ν ↪ σ)
    (e : ν →₀ ℕ) {x : σ} (hx : ¬ ∃ r, f r = x) : thm52_expandExp f e x = 0 := by
  rw [thm52_expandExp, Finsupp.embDomain_apply, dif_neg hx]

omit [DecidableEq σ] in
/-- Restricted exponents evaluate at the corresponding ambient variables. -/
@[simp] theorem thm52_restrictExp_apply {ν : Type*} (f : ν ↪ σ)
    (e : σ →₀ ℕ) (r : ν) : thm52_restrictExp f e r = e (f r) := by
  rfl

omit [DecidableEq σ] in
/-- Expansion preserves single basis vectors. -/
@[simp] theorem thm52_expandExp_single {ν : Type*} (f : ν ↪ σ) (r : ν) (n : ℕ) :
    thm52_expandExp f (Finsupp.single r n) = Finsupp.single (f r) n := by
  ext x
  by_cases hx : ∃ s, f s = x
  · rcases hx with ⟨s, rfl⟩
    by_cases hrs : s = r
    · subst s
      simp
    · have hfs : f s ≠ f r := by
        intro h
        exact hrs (f.injective h)
      simp [hrs, hfs]
  · have hrx : f r ≠ x := by
      intro h
      exact hx ⟨r, h⟩
    rw [thm52_expandExp_apply_of_not_range f (Finsupp.single r n) hx]
    simp [hrx]

omit [DecidableEq σ] in
/-- Expansion commutes with addition. -/
@[simp] theorem thm52_expandExp_add {ν : Type*} (f : ν ↪ σ) (u v : ν →₀ ℕ) :
    thm52_expandExp f (u + v) = thm52_expandExp f u + thm52_expandExp f v := by
  change Finsupp.embDomain f (u + v) = Finsupp.embDomain f u + Finsupp.embDomain f v
  exact Finsupp.embDomain_add f u v

omit [DecidableEq σ] in
/-- Expansion is monotone for coordinatewise inequality. -/
theorem thm52_expandExp_mono {ν : Type*} (f : ν ↪ σ) {u v : ν →₀ ℕ}
    (h : u ≤ v) : thm52_expandExp f u ≤ thm52_expandExp f v := by
  intro x
  by_cases hx : ∃ r, f r = x
  · rcases hx with ⟨r, rfl⟩
    simpa using h r
  · rw [thm52_expandExp_apply_of_not_range f u hx,
      thm52_expandExp_apply_of_not_range f v hx]

variable {K : Type*} [Field K] [Fintype σ] [Fintype ι]
/-- The monomial criterion for an arbitrary intersection of pure-power components. -/
def thm52_componentGens (A : ι → Finset σ) (a : ι → σ → ℕ) : Set (σ →₀ ℕ) :=
  {e | ∀ j, ∃ i ∈ A j, a j i ≤ e i}

omit [Fintype σ] in
/-- Monomial membership in a square of a monomial ideal, as a two-generator divisibility test. -/
theorem thm52_monomial_mem_monomialIdeal_sq_iff {S : Set (σ →₀ ℕ)} {e : σ →₀ ℕ} :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ (monomialIdeal (K := K) S) ^ 2 ↔
      ∃ u ∈ S, ∃ v ∈ S, u + v ≤ e := by
  rw [monomialIdeal_pow, monomial_mem_monomialIdeal]
  constructor
  · rintro ⟨z, hz, hzle⟩
    change ∃ w ∈ powGens S 1, ∃ v ∈ S, z = w + v at hz
    rcases hz with ⟨w, hw, v, hv, rfl⟩
    change ∃ u ∈ powGens S 0, ∃ s ∈ S, w = u + s at hw
    rcases hw with ⟨u, hu0, s, hs, rfl⟩
    simp only [powGens] at hu0
    subst u
    exact ⟨s, hs, v, hv, by simpa using hzle⟩
  · rintro ⟨u, hu, v, hv, huv⟩
    refine ⟨u + v, ?_, huv⟩
    change ∃ w ∈ powGens S 1, ∃ t ∈ S, u + v = w + t
    refine ⟨u, ?_, v, hv, rfl⟩
    change ∃ w ∈ powGens S 0, ∃ t ∈ S, u = w + t
    refine ⟨0, ?_, u, hu, by simp⟩
    simp [powGens]

omit [Fintype σ] in
/-- Every monomial occurring in a square of a pure-power component lies in that square. -/
theorem thm52_monomial_mem_of_mem_purePower_sq
    {A : Finset σ} {a : σ → ℕ} {x : MvPolynomial σ K} {e : σ →₀ ℕ}
    (hx : x ∈ (purePower (K := K) A a : Ideal (MvPolynomial σ K)) ^ 2)
    (he : e ∈ x.support) :
    (monomial e (1 : K) : MvPolynomial σ K) ∈
      (purePower (K := K) A a : Ideal (MvPolynomial σ K)) ^ 2 := by
  rw [purePower, monomialIdeal_pow] at hx ⊢
  rw [mem_monomialIdeal] at hx
  exact monomial_mem_monomialIdeal.mpr (hx e he)

omit [Fintype σ] in
/-- A monomial occurring in a pure-power component is itself in that component. -/
theorem thm52_monomial_mem_of_mem_purePower
    {A : Finset σ} {a : σ → ℕ} {x : MvPolynomial σ K} {e : σ →₀ ℕ}
    (hx : x ∈ (purePower (K := K) A a : Ideal (MvPolynomial σ K))) (he : e ∈ x.support) :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ purePower (K := K) A a := by
  rw [purePower, monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image] at hx ⊢
  intro xi hxi
  have hcoeff : coeff xi (monomial e (1 : K) : MvPolynomial σ K) ≠ 0 := by
    simpa [MvPolynomial.mem_support_iff] using hxi
  have hxie : xi = e := by
    by_contra hne
    have hexi : e ≠ xi := by
      intro h
      exact hne h.symm
    have hcoeff0 : coeff xi (monomial e (1 : K) : MvPolynomial σ K) = 0 := by
      rw [MvPolynomial.coeff_monomial]
      simp [hexi]
    exact hcoeff hcoeff0
  subst xi
  exact hx e he

omit [Fintype σ] [Fintype ι] in
/-- An arbitrary intersection of pure-power components is explicitly monomial. -/
theorem thm52_iInf_purePower_eq (A : ι → Finset σ) (a : ι → σ → ℕ) :
    (⨅ j, (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K))) =
      monomialIdeal (K := K) (thm52_componentGens A a) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [monomialIdeal, MvPolynomial.mem_ideal_span_monomial_image]
    intro e he
    refine ⟨e, ?_, le_rfl⟩
    intro j
    have hxj : x ∈ (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K)) :=
      Ideal.mem_iInf.mp hx j
    have hej := thm52_monomial_mem_of_mem_purePower hxj he
    exact monomial_mem_purePower.mp hej
  · rw [monomialIdeal, Ideal.span_le]
    rintro y ⟨e, he, rfl⟩
    exact Ideal.mem_iInf.mpr (fun j => monomial_mem_purePower.mpr (he j))

/-- Internal restriction of the global square equality to any finite list of surviving
components.  The proof pads a core monomial with all variables outside the surviving union;
factorizing the padded monomial in the global product then reflects to the chosen core. -/
theorem thm52_coreEquality_of_globalEquality
    {ν τ : Type*} [DecidableEq ν]
    {A : ι → Finset σ} {a : ι → σ → ℕ} {U : Finset σ}
    (B : τ → Finset ν) (b : τ → ν → ℕ) (emb : ν ↪ σ) (idx : τ → ι)
    (hembU : ∀ r, emb r ∈ U)
    (hidxU : ∀ r, A (idx r) ⊆ U)
    (hsurv : ∀ j, A j ⊆ U → ∃ r, idx r = j)
    (hB : ∀ r t, t ∈ B r ↔ emb t ∈ A (idx r))
    (hb : ∀ r t, t ∈ B r → b r t = a (idx r) (emb t))
    (hpos : ∀ j i, i ∈ A j → 0 < a j i)
    (hglobal :
      (⨅ j, (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K))) ^ 2 =
        ⨅ j, (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K)) ^ 2) :
    (⨅ r, (purePower (K := K) (B r) (b r) : Ideal (MvPolynomial ν K))) ^ 2 =
      ⨅ r, (purePower (K := K) (B r) (b r) : Ideal (MvPolynomial ν K)) ^ 2 := by
  classical
  let M : ℕ := Finset.univ.sup fun j : ι =>
    (A j \ U).sup fun x : σ => 2 * a j x
  let O : Finset σ := Finset.univ.filter fun x : σ => x ∉ U
  let pad : σ →₀ ℕ := Finsupp.onFinset O (fun x => if x ∈ O then M else 0) (by
    intro x hx
    by_contra hxO
    exact hx (by simp [hxO]))
  have hM {j : ι} {x : σ} (hxA : x ∈ A j) (hxU : x ∉ U) : 2 * a j x ≤ M := by
    have hxmem : x ∈ A j \ U := by simp [hxA, hxU]
    have h1 : 2 * a j x ≤ (A j \ U).sup (fun y : σ => 2 * a j y) :=
      Finset.le_sup (f := fun y : σ => 2 * a j y) hxmem
    have h2 : (A j \ U).sup (fun y : σ => 2 * a j y) ≤
        (Finset.univ : Finset ι).sup (fun t : ι =>
          (A t \ U).sup (fun y : σ => 2 * a t y)) :=
      Finset.le_sup (s := (Finset.univ : Finset ι))
        (f := fun t : ι => (A t \ U).sup (fun y : σ => 2 * a t y)) (by simp)
    exact le_trans h1 (by simpa [M] using h2)
  have hcoreLe :
      (⨅ r, (purePower (K := K) (B r) (b r) : Ideal (MvPolynomial ν K))) ^ 2 ≤
        ⨅ r, (purePower (K := K) (B r) (b r) : Ideal (MvPolynomial ν K)) ^ 2 := by
    simp only [pow_two]
    refine le_iInf (fun r => ?_)
    have hle : (⨅ s, (purePower (K := K) (B s) (b s) : Ideal (MvPolynomial ν K))) ≤
        purePower (K := K) (B r) (b r) := iInf_le _ r
    exact Ideal.mul_mono hle hle
  apply le_antisymm hcoreLe
  intro x hxR
  let Sc : Set (ν →₀ ℕ) := thm52_componentGens B b
  let SG : Set (σ →₀ ℕ) := thm52_componentGens A a
  have hJc : (⨅ r, (purePower (K := K) (B r) (b r) : Ideal (MvPolynomial ν K))) =
      monomialIdeal (K := K) Sc := by
    simpa [Sc] using (thm52_iInf_purePower_eq (K := K) B b)
  have hL : (⨅ r, (purePower (K := K) (B r) (b r) : Ideal (MvPolynomial ν K))) ^ 2 =
      monomialIdeal (K := K) (powGens Sc 2) := by
    rw [hJc, monomialIdeal_pow]
  rw [hL, mem_monomialIdeal]
  intro e he
  have heR (r : τ) : (monomial e (1 : K) : MvPolynomial ν K) ∈
      (purePower (K := K) (B r) (b r) : Ideal (MvPolynomial ν K)) ^ 2 :=
    thm52_monomial_mem_of_mem_purePower_sq (K := K) (Ideal.mem_iInf.mp hxR r) he
  let g : σ →₀ ℕ := thm52_expandExp emb e + pad
  have hg_at (r : ν) : g (emb r) = e r := by
    have hrU : emb r ∈ U := hembU r
    simp [g, pad, O, hrU]
  have hg_unselected {z : σ} (hzU : z ∈ U) (hzrange : ¬ ∃ r, emb r = z) : g z = 0 := by
    have hexp : thm52_expandExp emb e z = 0 :=
      thm52_expandExp_apply_of_not_range emb e hzrange
    have hpad : pad z = 0 := by simp [pad, O, hzU]
    simp [g, hexp, hpad]
  have hgR : (monomial g (1 : K) : MvPolynomial σ K) ∈
      ⨅ j, (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K)) ^ 2 := by
    refine Ideal.mem_iInf.mpr (fun j => ?_)
    by_cases hj : A j ⊆ U
    · rcases hsurv j hj with ⟨r, rfl⟩
      have heRr := heR r
      rw [purePower] at heRr
      rcases (thm52_monomial_mem_monomialIdeal_sq_iff (K := K)
          (S := {q : ν →₀ ℕ | ∃ t ∈ B r, q = Finsupp.single t (b r t)})
          (e := e)).mp heRr with ⟨u, hu, v, hv, huv⟩
      have huG : thm52_expandExp emb u ∈
          {q : σ →₀ ℕ | ∃ z ∈ A (idx r), q = Finsupp.single z (a (idx r) z)} := by
        rcases hu with ⟨t, ht, rfl⟩
        refine ⟨emb t, (hB r t).1 ht, ?_⟩
        simp [thm52_expandExp_single, hb r t ht]
      have hvG : thm52_expandExp emb v ∈
          {q : σ →₀ ℕ | ∃ z ∈ A (idx r), q = Finsupp.single z (a (idx r) z)} := by
        rcases hv with ⟨t, ht, rfl⟩
        refine ⟨emb t, (hB r t).1 ht, ?_⟩
        simp [thm52_expandExp_single, hb r t ht]
      have huvG : thm52_expandExp emb u + thm52_expandExp emb v ≤ thm52_expandExp emb e := by
        rw [← thm52_expandExp_add]
        exact thm52_expandExp_mono emb huv
      have hexpleg : thm52_expandExp emb e ≤ g := by
        intro z
        simp [g]
      rw [purePower]
      exact (thm52_monomial_mem_monomialIdeal_sq_iff (K := K) (e := g)).mpr
        ⟨thm52_expandExp emb u, huG, thm52_expandExp emb v, hvG, le_trans huvG hexpleg⟩
    · obtain ⟨z, hzA, hzU⟩ : ∃ z, z ∈ A j ∧ z ∉ U := by
        by_contra h
        apply hj
        intro z hzA
        by_contra hzU
        exact h ⟨z, hzA, hzU⟩
      let s : σ →₀ ℕ := Finsupp.single z (a j z)
      have hM' : 2 * a j z ≤ M := hM hzA hzU
      have hss : s + s ≤ g := by
        intro w
        by_cases hw : w = z
        · subst w
          have hzrange : ¬ ∃ r, emb r = z := by
            rintro ⟨r, hr⟩
            exact hzU (by simpa [hr] using hembU r)
          have hexp : thm52_expandExp emb e z = 0 :=
            thm52_expandExp_apply_of_not_range emb e hzrange
          have hpad : pad z = M := by simp [pad, O, hzU]
          have hgz : g z = M := by simp [g, hexp, hpad]
          rw [hgz]
          simpa [s, two_mul] using hM'
        · have hs0 : (s + s) w = 0 := by simp [s, hw]
          rw [hs0]
          exact Nat.zero_le _
      rw [purePower]
      exact (thm52_monomial_mem_monomialIdeal_sq_iff (K := K) (e := g)).mpr
        ⟨s, ⟨z, hzA, rfl⟩, s, ⟨z, hzA, rfl⟩, hss⟩
  have hgL : (monomial g (1 : K) : MvPolynomial σ K) ∈
      (⨅ j, (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K))) ^ 2 := by
    rw [hglobal]
    exact hgR
  have hJg : (⨅ j, (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K))) =
      monomialIdeal (K := K) SG := by
    simpa [SG] using (thm52_iInf_purePower_eq (K := K) A a)
  rw [hJg] at hgL
  rcases (thm52_monomial_mem_monomialIdeal_sq_iff (K := K) (S := SG) (e := g)).mp hgL with
    ⟨u, hu, v, hv, huv⟩
  let u' : ν →₀ ℕ := thm52_restrictExp emb u
  let v' : ν →₀ ℕ := thm52_restrictExp emb v
  have hrestrict_mem (w : σ →₀ ℕ) (hw : w ∈ SG) (hwpart : w = u ∨ w = v) :
      thm52_restrictExp emb w ∈ Sc := by
    have hw' : w ∈ thm52_componentGens A a := by simpa [SG] using hw
    change thm52_restrictExp emb w ∈ thm52_componentGens B b
    intro r
    rcases hw' (idx r) with ⟨z, hzA, haz⟩
    have hzU : z ∈ U := hidxU r hzA
    by_cases hzrange : ∃ t, emb t = z
    · rcases hzrange with ⟨t, rfl⟩
      have ht : t ∈ B r := (hB r t).2 hzA
      refine ⟨t, ht, ?_⟩
      have hbt : b r t = a (idx r) (emb t) := hb r t ht
      rw [thm52_restrictExp_apply, hbt]
      exact haz
    · have hgz : g z = 0 := hg_unselected hzU hzrange
      have hsum : u z + v z ≤ g z := by simpa using huv z
      rw [hgz] at hsum
      have hwz : w z = 0 := by
        rcases hwpart with hwu | hwv
        · subst w
          omega
        · subst w
          omega
      have hzpos : 0 < a (idx r) z := hpos (idx r) z hzA
      have hwzpos : 0 < w z := lt_of_lt_of_le hzpos haz
      exact False.elim ((Nat.ne_of_gt hwzpos) hwz)
  have hu' : u' ∈ Sc := by simpa [u'] using hrestrict_mem u hu (Or.inl rfl)
  have hv' : v' ∈ Sc := by simpa [v'] using hrestrict_mem v hv (Or.inr rfl)
  have huv' : u' + v' ≤ e := by
    intro r
    have hsum : u (emb r) + v (emb r) ≤ g (emb r) := by simpa using huv (emb r)
    have hgr : g (emb r) = e r := hg_at r
    simpa [u', v', hgr] using hsum
  have heL : (monomial e (1 : K) : MvPolynomial ν K) ∈ (monomialIdeal (K := K) Sc) ^ 2 :=
    (thm52_monomial_mem_monomialIdeal_sq_iff (K := K) (S := Sc) (e := e)).mpr
      ⟨u', hu', v', hv', huv'⟩
  rw [monomialIdeal_pow] at heL
  exact monomial_mem_monomialIdeal.mp heL

omit [DecidableEq σ] [Fintype σ] in
/-- Binary infimum of ideals indexed by `Fin 2`. -/
theorem thm52_iInf_fin_two (Q : Fin 2 → Ideal (MvPolynomial σ K)) :
    (⨅ r, Q r) = Q 0 ⊓ Q 1 := by
  apply le_antisymm
  · exact le_inf (iInf_le _ 0) (iInf_le _ 1)
  · refine le_iInf (fun r => ?_)
    fin_cases r
    · exact inf_le_left
    · exact inf_le_right

omit [DecidableEq σ] [Fintype σ] in
/-- Ternary infimum of ideals indexed by `Fin 3`. -/
theorem thm52_iInf_fin_three (Q : Fin 3 → Ideal (MvPolynomial σ K)) :
    (⨅ r, Q r) = Q 0 ⊓ Q 1 ⊓ Q 2 := by
  apply le_antisymm
  · exact le_inf (le_inf (iInf_le _ 0) (iInf_le _ 1)) (iInf_le _ 2)
  · refine le_iInf (fun r => ?_)
    fin_cases r
    · exact le_trans inf_le_left inf_le_left
    · exact le_trans inf_le_left inf_le_right
    · exact inf_le_right

omit [Fintype σ] [Fintype ι] in
/-- Irredundance forces every exponent used by a component to be positive. -/
theorem thm52_component_exponents_pos {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hirr : IsIrredundant (K := K) A a) :
    ∀ j i, i ∈ A j → 0 < a j i := by
  intro j i hi
  by_contra hnot
  have ha0 : a j i = 0 := Nat.eq_zero_of_not_pos hnot
  have hone : (1 : MvPolynomial σ K) ∈ purePower (K := K) (A j) (a j) := by
    have hm : (monomial (0 : σ →₀ ℕ) (1 : K) : MvPolynomial σ K) ∈
        purePower (K := K) (A j) (a j) := by
      exact monomial_mem_purePower.mpr ⟨i, hi, by simp [ha0]⟩
    simpa using hm
  have htop : purePower (K := K) (A j) (a j) = (⊤ : Ideal (MvPolynomial σ K)) :=
    (Ideal.eq_top_iff_one (purePower (K := K) (A j) (a j))).mpr hone
  apply hirr j
  rw [htop]
  exact le_top

/--
The specialized form of Lemma 5.1 needed below.  Besides the positivity and
incomparability used in its statement, it includes the standard localization,
contraction, and three-variable restriction steps.  It is kept explicit rather
than silently assuming a cross-file import.
-/
def thm52_lem51Obstruction (A : ι → Finset σ) (a : ι → σ → ℕ) : Prop :=
  SupportsAntichain A a →
    (∀ j i, i ∈ A j → 0 < a j i) →
      ∀ {k l : ι} {i : σ}, k ≠ l → i ∈ A k → i ∈ A l → a k i < a l i →
        thm52_AtMostOneIntervenor A k l →
          ¬ ((⨅ j, (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K))) ^ 2 =
              ⨅ j, (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K)) ^ 2)

/-- The specialized obstruction follows from the imported core Lemma 5.1 cases. -/
theorem thm52_lem51Obstruction_holds (A : ι → Finset σ) (a : ι → σ → ℕ) :
    thm52_lem51Obstruction (K := K) A a := by
  intro hanti hpos k l i hkl hiA hiB hlt hatmost hglobal
  let U : Finset σ := A k ∪ A l
  by_cases hex : ∃ c, thm52_isIntervenor A k l c
  · rcases hex with ⟨c, hc⟩
    have hck : c ≠ k := hc.1
    have hcl : c ≠ l := hc.2.1
    have hcsub : A c ⊆ U := hc.2.2
    have hnotSubCL : ¬ A c ⊆ A l := by
      intro hsub
      exact hcl (hanti c l hsub)
    obtain ⟨y₁, hy₁, hy₁notl⟩ : ∃ y, y ∈ A k ∩ A c ∧ y ∉ A l := by
      by_contra hno
      apply hnotSubCL
      intro z hzAc
      have hzU : z ∈ U := hcsub hzAc
      rcases Finset.mem_union.mp hzU with hzAk | hzAl
      · have hzKc : z ∈ A k ∩ A c := Finset.mem_inter.mpr ⟨hzAk, hzAc⟩
        by_contra hznotAl
        exact hno ⟨z, hzKc, hznotAl⟩
      · exact hzAl
    have hy₁k : y₁ ∈ A k := (Finset.mem_inter.mp hy₁).1
    have hy₁c : y₁ ∈ A c := (Finset.mem_inter.mp hy₁).2
    have hnotSubCK : ¬ A c ⊆ A k := by
      intro hsub
      exact hck (hanti c k hsub)
    obtain ⟨y₂, hy₂, hy₂notk⟩ : ∃ y, y ∈ A l ∩ A c ∧ y ∉ A k := by
      by_contra hno
      apply hnotSubCK
      intro z hzAc
      have hzU : z ∈ U := hcsub hzAc
      rcases Finset.mem_union.mp hzU with hzAk | hzAl
      · exact hzAk
      · have hzLc : z ∈ A l ∩ A c := Finset.mem_inter.mpr ⟨hzAl, hzAc⟩
        by_contra hznotAk
        exact hno ⟨z, hzLc, hznotAk⟩
    have hy₂l : y₂ ∈ A l := (Finset.mem_inter.mp hy₂).1
    have hy₂c : y₂ ∈ A c := (Finset.mem_inter.mp hy₂).2
    have hi_y₁ : i ≠ y₁ := by
      intro h
      exact hy₁notl (by simpa [h] using hiB)
    have hi_y₂ : i ≠ y₂ := by
      intro h
      exact hy₂notk (by simpa [h] using hiA)
    have hy₁_y₂ : y₁ ≠ y₂ := by
      intro h
      exact hy₂notk (by simpa [h] using hy₁k)
    have hy₁_i : y₁ ≠ i := fun h => hi_y₁ h.symm
    have hy₂_i : y₂ ≠ i := fun h => hi_y₂ h.symm
    have hy₂_y₁ : y₂ ≠ y₁ := fun h => hy₁_y₂ h.symm
    let f : Fin 3 → σ := ![i, y₁, y₂]
    have hf : Function.Injective f := by
      intro r s hrs
      fin_cases r <;> fin_cases s <;> simp_all [f]
    let emb : Fin 3 ↪ σ := ⟨f, hf⟩
    let idx : Fin 3 → ι := ![k, l, c]
    have hembU : ∀ r, emb r ∈ U := by
      intro r
      change emb r ∈ A k ∪ A l
      fin_cases r
      · exact Finset.mem_union.mpr (Or.inl (by simpa [emb, f] using hiA))
      · exact Finset.mem_union.mpr (Or.inl (by simpa [emb, f] using hy₁k))
      · exact Finset.mem_union.mpr (Or.inr (by simpa [emb, f] using hy₂l))
    have hidxU : ∀ r, A (idx r) ⊆ U := by
      intro r z hz
      change z ∈ A k ∪ A l
      fin_cases r
      · exact Finset.mem_union.mpr (Or.inl (by simpa [idx] using hz))
      · exact Finset.mem_union.mpr (Or.inr (by simpa [idx] using hz))
      · exact hcsub (by simpa [idx] using hz)
    have hsurv : ∀ j, A j ⊆ U → ∃ r, idx r = j := by
      intro j hjU
      by_cases hjk : j = k
      · exact ⟨0, by simp [idx, hjk]⟩
      by_cases hjl : j = l
      · exact ⟨1, by simp [idx, hjl]⟩
      by_cases hjc : j = c
      · exact ⟨2, by simp [idx, hjc]⟩
      · exfalso
        have hjInter : thm52_isIntervenor A k l j := ⟨hjk, hjl, hjU⟩
        have heq : c = j := hatmost hc hjInter
        exact hjc heq.symm
    by_cases hiC : i ∈ A c
    · let Bcore : Fin 3 → Finset (Fin 3) :=
        ![({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))]
      let bcore : Fin 3 → Fin 3 → ℕ :=
        ![(![a k i, a k y₁, 0] : Fin 3 → ℕ),
          (![a l i, 0, a l y₂] : Fin 3 → ℕ),
          (![a c i, a c y₁, a c y₂] : Fin 3 → ℕ)]
      let Qcore : Fin 3 → Ideal (MvPolynomial (Fin 3) K) := fun r =>
        purePower (K := K) (Bcore r) (bcore r)
      have hB : ∀ r t, t ∈ Bcore r ↔ emb t ∈ A (idx r) := by
        intro r t
        fin_cases r <;> fin_cases t <;>
          simp [Bcore, emb, idx, f, hiA, hiB, hy₁k, hy₁notl, hy₂l, hy₂notk, hy₁c, hy₂c, hiC]
      have hb : ∀ r t, t ∈ Bcore r → bcore r t = a (idx r) (emb t) := by
        intro r t ht
        fin_cases r <;> fin_cases t <;> simp_all [Bcore, bcore, emb, idx, f]
      have hcoreEq : (⨅ r, Qcore r) ^ 2 = ⨅ r, Qcore r ^ 2 := by
        simpa [Qcore] using
          (thm52_coreEquality_of_globalEquality (A := A) (a := a) (U := U)
            Bcore bcore emb idx hembU hidxU hsurv hB hb hpos hglobal)
      have hcoreNested : (Qcore 0 ⊓ Qcore 1 ⊓ Qcore 2) ^ 2 =
          Qcore 0 ^ 2 ⊓ Qcore 1 ^ 2 ⊓ Qcore 2 ^ 2 := by
        rw [thm52_iInf_fin_three (K := K) Qcore,
          thm52_iInf_fin_three (K := K) (fun r : Fin 3 => (Qcore r) ^ 2)] at hcoreEq
        exact hcoreEq
      have hstrict : (Qcore 0 ⊓ Qcore 1 ⊓ Qcore 2) ^ 2 <
          Qcore 0 ^ 2 ⊓ Qcore 1 ^ 2 ⊓ Qcore 2 ^ 2 := by
        simpa [Qcore, Bcore, bcore] using
          (lem51_threeComponents_C3 (K := K)
            (l := a k i) (m := a l i) (a := a k y₁) (b := a l y₂)
            (t := a c i) (g := a c y₁) (d := a c y₂)
            (hpos k i hiA) hlt (hpos k y₁ hy₁k) (hpos l y₂ hy₂l)
            (hpos c i hiC) (hpos c y₁ hy₁c) (hpos c y₂ hy₂c))
      have hleRev : Qcore 0 ^ 2 ⊓ Qcore 1 ^ 2 ⊓ Qcore 2 ^ 2 ≤
          (Qcore 0 ⊓ Qcore 1 ⊓ Qcore 2) ^ 2 := by
        rw [hcoreNested]
      exact (lt_irrefl _ (lt_of_lt_of_le hstrict hleRev))
    · let Bcore : Fin 3 → Finset (Fin 3) :=
        ![({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3))]
      let bcore : Fin 3 → Fin 3 → ℕ :=
        ![(![a k i, a k y₁, 0] : Fin 3 → ℕ),
          (![a l i, 0, a l y₂] : Fin 3 → ℕ),
          (![0, a c y₁, a c y₂] : Fin 3 → ℕ)]
      let Qcore : Fin 3 → Ideal (MvPolynomial (Fin 3) K) := fun r =>
        purePower (K := K) (Bcore r) (bcore r)
      have hB : ∀ r t, t ∈ Bcore r ↔ emb t ∈ A (idx r) := by
        intro r t
        fin_cases r <;> fin_cases t <;>
          simp [Bcore, emb, idx, f, hiA, hiB, hy₁k, hy₁notl, hy₂l, hy₂notk, hy₁c, hy₂c, hiC]
      have hb : ∀ r t, t ∈ Bcore r → bcore r t = a (idx r) (emb t) := by
        intro r t ht
        fin_cases r <;> fin_cases t <;> simp_all [Bcore, bcore, emb, idx, f]
      have hcoreEq : (⨅ r, Qcore r) ^ 2 = ⨅ r, Qcore r ^ 2 := by
        simpa [Qcore] using
          (thm52_coreEquality_of_globalEquality (A := A) (a := a) (U := U)
            Bcore bcore emb idx hembU hidxU hsurv hB hb hpos hglobal)
      have hcoreNested : (Qcore 0 ⊓ Qcore 1 ⊓ Qcore 2) ^ 2 =
          Qcore 0 ^ 2 ⊓ Qcore 1 ^ 2 ⊓ Qcore 2 ^ 2 := by
        rw [thm52_iInf_fin_three (K := K) Qcore,
          thm52_iInf_fin_three (K := K) (fun r : Fin 3 => (Qcore r) ^ 2)] at hcoreEq
        exact hcoreEq
      have hstrict : (Qcore 0 ⊓ Qcore 1 ⊓ Qcore 2) ^ 2 <
          Qcore 0 ^ 2 ⊓ Qcore 1 ^ 2 ⊓ Qcore 2 ^ 2 := by
        simpa [Qcore, Bcore, bcore] using
          (lem51_threeComponents_C2 (K := K)
            (l := a k i) (m := a l i) (a := a k y₁) (b := a l y₂)
            (g := a c y₁) (d := a c y₂)
            (hpos k i hiA) hlt (hpos k y₁ hy₁k) (hpos l y₂ hy₂l)
            (hpos c y₁ hy₁c) (hpos c y₂ hy₂c))
      have hleRev : Qcore 0 ^ 2 ⊓ Qcore 1 ^ 2 ⊓ Qcore 2 ^ 2 ≤
          (Qcore 0 ⊓ Qcore 1 ⊓ Qcore 2) ^ 2 := by
        rw [hcoreNested]
      exact (lt_irrefl _ (lt_of_lt_of_le hstrict hleRev))
  · have hnotKL : ¬ A k ⊆ A l := by
      intro hsub
      exact hkl (hanti k l hsub)
    obtain ⟨y₁, hy₁k, hy₁notl⟩ : ∃ y, y ∈ A k ∧ y ∉ A l := by
      by_contra hno
      apply hnotKL
      intro z hzAk
      by_contra hznotAl
      exact hno ⟨z, hzAk, hznotAl⟩
    have hnotLK : ¬ A l ⊆ A k := by
      intro hsub
      exact hkl (hanti l k hsub).symm
    obtain ⟨y₂, hy₂l, hy₂notk⟩ : ∃ y, y ∈ A l ∧ y ∉ A k := by
      by_contra hno
      apply hnotLK
      intro z hzAl
      by_contra hznotAk
      exact hno ⟨z, hzAl, hznotAk⟩
    have hi_y₁ : i ≠ y₁ := by
      intro h
      exact hy₁notl (by simpa [h] using hiB)
    have hi_y₂ : i ≠ y₂ := by
      intro h
      exact hy₂notk (by simpa [h] using hiA)
    have hy₁_y₂ : y₁ ≠ y₂ := by
      intro h
      exact hy₂notk (by simpa [h] using hy₁k)
    have hy₁_i : y₁ ≠ i := fun h => hi_y₁ h.symm
    have hy₂_i : y₂ ≠ i := fun h => hi_y₂ h.symm
    have hy₂_y₁ : y₂ ≠ y₁ := fun h => hy₁_y₂ h.symm
    let f : Fin 3 → σ := ![i, y₁, y₂]
    have hf : Function.Injective f := by
      intro r s hrs
      fin_cases r <;> fin_cases s <;> simp_all [f]
    let emb : Fin 3 ↪ σ := ⟨f, hf⟩
    let idx : Fin 2 → ι := ![k, l]
    have hembU : ∀ r, emb r ∈ U := by
      intro r
      change emb r ∈ A k ∪ A l
      fin_cases r
      · exact Finset.mem_union.mpr (Or.inl (by simpa [emb, f] using hiA))
      · exact Finset.mem_union.mpr (Or.inl (by simpa [emb, f] using hy₁k))
      · exact Finset.mem_union.mpr (Or.inr (by simpa [emb, f] using hy₂l))
    have hidxU : ∀ r, A (idx r) ⊆ U := by
      intro r z hz
      change z ∈ A k ∪ A l
      fin_cases r
      · exact Finset.mem_union.mpr (Or.inl (by simpa [idx] using hz))
      · exact Finset.mem_union.mpr (Or.inr (by simpa [idx] using hz))
    have hsurv : ∀ j, A j ⊆ U → ∃ r, idx r = j := by
      intro j hjU
      by_cases hjk : j = k
      · exact ⟨0, by simp [idx, hjk]⟩
      by_cases hjl : j = l
      · exact ⟨1, by simp [idx, hjl]⟩
      · exfalso
        exact hex ⟨j, hjk, hjl, hjU⟩
    let Bcore : Fin 2 → Finset (Fin 3) :=
      ![({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3))]
    let bcore : Fin 2 → Fin 3 → ℕ :=
      ![(![a k i, a k y₁, 0] : Fin 3 → ℕ),
        (![a l i, 0, a l y₂] : Fin 3 → ℕ)]
    let Qcore : Fin 2 → Ideal (MvPolynomial (Fin 3) K) := fun r =>
      purePower (K := K) (Bcore r) (bcore r)
    have hB : ∀ r t, t ∈ Bcore r ↔ emb t ∈ A (idx r) := by
      intro r t
      fin_cases r
      · fin_cases t
        · simp [Bcore, emb, idx, f, hiA]
        · simp [Bcore, emb, idx, f, hy₁k]
        · simp [Bcore, emb, idx, f, hy₂notk]
      · fin_cases t
        · simp [Bcore, emb, idx, f, hiB]
        · simp [Bcore, emb, idx, f, hy₁notl]
        · simp [Bcore, emb, idx, f, hy₂l]
    have hb : ∀ r t, t ∈ Bcore r → bcore r t = a (idx r) (emb t) := by
      intro r t ht
      fin_cases r
      · fin_cases t
        · simp [bcore, emb, idx, f]
        · simp [bcore, emb, idx, f]
        · simp [Bcore] at ht
      · fin_cases t
        · simp [bcore, emb, idx, f]
        · simp [Bcore] at ht
        · simp [bcore, emb, idx, f]
    have hcoreEq : (⨅ r, Qcore r) ^ 2 = ⨅ r, Qcore r ^ 2 := by
      simpa [Qcore] using
        (thm52_coreEquality_of_globalEquality (A := A) (a := a) (U := U)
          Bcore bcore emb idx hembU hidxU hsurv hB hb hpos hglobal)
    have hcorePair : (Qcore 0 ⊓ Qcore 1) ^ 2 = Qcore 0 ^ 2 ⊓ Qcore 1 ^ 2 := by
      rw [thm52_iInf_fin_two (K := K) Qcore,
        thm52_iInf_fin_two (K := K) (fun r : Fin 2 => (Qcore r) ^ 2)] at hcoreEq
      exact hcoreEq
    have hstrict : (Qcore 0 ⊓ Qcore 1) ^ 2 < Qcore 0 ^ 2 ⊓ Qcore 1 ^ 2 := by
      simpa [Qcore, Bcore, bcore] using
        (lem51_twoComponents (K := K)
          (l := a k i) (m := a l i) (a := a k y₁) (b := a l y₂)
          (hpos k i hiA) hlt (hpos k y₁ hy₁k) (hpos l y₂ hy₂l))
    have hleRev : Qcore 0 ^ 2 ⊓ Qcore 1 ^ 2 ≤ (Qcore 0 ⊓ Qcore 1) ^ 2 := by
      rw [hcorePair]
    exact (lt_irrefl _ (lt_of_lt_of_le hstrict hleRev))

omit [Fintype σ] in
/-- The forced weights agree with every positive occurrence exponent. -/
theorem thm52_weights_eq {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hcoh : ∀ j k i, i ∈ A j → i ∈ A k → a j i = a k i) {i : σ} {j : ι}
    (hi : i ∈ A j) : thm52_weights A a i = a j i := by
  classical
  rw [thm52_weights]
  split_ifs with h
  · exact hcoh (Classical.choose h) j i (Classical.choose_spec h) hi
  · exact False.elim (h ⟨j, hi⟩)

omit [Fintype σ] in
/-- The forced diagonal weights are positive. -/
theorem thm52_weights_pos {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hpos : ∀ j i, i ∈ A j → 0 < a j i) :
    ∀ i, 0 < thm52_weights A a i := by
  classical
  intro i
  rw [thm52_weights]
  split_ifs with h
  · exact hpos (Classical.choose h) i (Classical.choose_spec h)
  · omega

omit [Fintype σ] [Fintype ι] in
/-- The displayed root is a squarefree monomial ideal. -/
theorem thm52_root_squarefree (A : ι → Finset σ) :
    IsSquarefreeMonomialIdeal (thm52_root (K := K) A) := by
  exact ⟨{T : Finset σ | IsTransversal (Set.range A) T}, rfl⟩

omit [Fintype σ] [Fintype ι] in
/-- The displayed root is a monomial ideal. -/
theorem thm52_root_isMonomial (A : ι → Finset σ) :
    IsMonomialIdeal (thm52_root (K := K) A) := by
  exact ⟨characteristicExp '' {T : Finset σ | IsTransversal (Set.range A) T}, rfl⟩

omit [Fintype σ] [Fintype ι] in
/-- Monomial membership in the root is exactly transversality of the support. -/
theorem thm52_monomial_mem_root_iff (A : ι → Finset σ) (e : σ →₀ ℕ) :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ thm52_root (K := K) A ↔
      ∀ j, ∃ i ∈ A j, 0 < e i := by
  classical
  rw [thm52_root, monomial_mem_monomialIdeal]
  constructor
  · rintro ⟨u, ⟨T, hT, rfl⟩, hule⟩ j
    rcases hT (A j) ⟨j, rfl⟩ with ⟨i, hiInter⟩
    have hiA : i ∈ A j := (Finset.mem_inter.mp hiInter).1
    have hiT : i ∈ T := (Finset.mem_inter.mp hiInter).2
    have hiU : characteristicExp T i = 1 := by simp [hiT]
    have hie : 1 ≤ e i := by simpa [hiU] using hule i
    exact ⟨i, hiA, Nat.lt_of_lt_of_le Nat.zero_lt_one hie⟩
  · intro h
    let T : Finset σ := e.support
    refine ⟨characteristicExp T, ⟨T, ?_, rfl⟩, ?_⟩
    · intro E hE
      rcases hE with ⟨j, rfl⟩
      rcases h j with ⟨i, hiA, hie⟩
      have hiT : i ∈ T := by
        exact Finsupp.mem_support_iff.mpr (Nat.ne_of_gt hie)
      exact ⟨i, Finset.mem_inter.mpr ⟨hiA, by simpa [T] using hiT⟩⟩
    · intro i
      by_cases hiT : i ∈ T
      · have hiSupp : i ∈ e.support := by simpa [T] using hiT
        have hie : 0 < e i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hiSupp)
        have hie' : 1 ≤ e i := by omega
        simpa [characteristicExp_apply, hiT] using hie'
      · simp [characteristicExp_apply, hiT]

omit [Fintype σ] [Fintype ι] in
/-- The root has the expected irredundant prime decomposition. -/
theorem thm52_root_hasComponents (A : ι → Finset σ) :
    HasComponents (thm52_root (K := K) A) A (fun _ _ => 1) := by
  classical
  rw [HasComponents]
  change monomialIdeal (K := K)
      (characteristicExp '' {T : Finset σ | IsTransversal (Set.range A) T}) =
    (⨅ j, (purePower (K := K) (A j) (fun _ => 1) : Ideal (MvPolynomial σ K)))
  rw [thm52_iInf_purePower_eq]
  apply monomialIdeal_eq_iff.mpr
  intro e
  constructor
  · intro he
    have hall := (thm52_monomial_mem_root_iff (K := K) A e).mp
      (monomial_mem_monomialIdeal.mpr he)
    refine ⟨e, ?_, le_rfl⟩
    intro j
    rcases hall j with ⟨i, hiA, hie⟩
    exact ⟨i, hiA, by
      change 1 ≤ e i
      exact (Nat.succ_le_iff).2 hie⟩
  · rintro ⟨v, hv, hve⟩
    have hall : ∀ j, ∃ i ∈ A j, 0 < e i := by
      intro j
      rcases hv j with ⟨i, hiA, hvi⟩
      exact ⟨i, hiA, lt_of_lt_of_le (Nat.lt_of_lt_of_le Nat.zero_lt_one hvi) (hve i)⟩
    have hm := (thm52_monomial_mem_root_iff (K := K) A e).mpr hall
    exact monomial_mem_monomialIdeal.mp hm

/-- Irredundance of the squarefree prime decomposition. -/
theorem thm52_root_irredundant {A : ι → Finset σ} (hanti : SupportsAntichain A a) :
    IsIrredundant (K := K) A (fun _ _ => (1 : ℕ)) := by
  classical
  rw [IsIrredundant]
  intro j hle
  let U : Finset σ := Finset.univ.filter
    (fun v => ∃ k, k ≠ j ∧ v ∈ A k ∧ v ∉ A j)
  have hUomit : (monomial (characteristicExp U) (1 : K) : MvPolynomial σ K) ∈
      decompOmit (K := K) A (fun _ _ => (1 : ℕ)) j := by
    rw [decompOmit]
    apply Ideal.mem_iInf.mpr
    rintro ⟨k, hkj⟩
    have hnotSub : ¬ A k ⊆ A j := by
      intro hsub
      exact hkj (hanti k j hsub)
    obtain ⟨v, hvA, hvnot⟩ : ∃ v, v ∈ A k ∧ v ∉ A j := by
      by_contra h
      apply hnotSub
      intro v hvA
      by_contra hvnot
      exact h ⟨v, hvA, hvnot⟩
    have hvU : v ∈ U := by
      change v ∈ Finset.univ.filter (fun w => ∃ k, k ≠ j ∧ w ∈ A k ∧ w ∉ A j)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, ⟨k, hkj, hvA, hvnot⟩⟩
    exact monomial_mem_purePower.mpr ⟨v, hvA, by simp [hvU]⟩
  have hUnot : (monomial (characteristicExp U) (1 : K) : MvPolynomial σ K) ∉
      purePower (K := K) (A j) (fun _ => (1 : ℕ)) := by
    rw [monomial_mem_purePower]
    rintro ⟨i, hiA, hie⟩
    have hiU : i ∈ U := by
      by_contra hiU
      have hi0 : characteristicExp U i = 0 := by simp [hiU]
      omega
    have hinot : i ∉ A j := by
      rcases (Finset.mem_filter.mp hiU).2 with ⟨k, hkj, hiAk, hinotAj⟩
      exact hinotAj
    exact hinot hiA
  exact hUnot (hle hUomit)

/-- The projection setting the variables in a finite set to zero. -/
noncomputable def thm52_projectionHom (A : Finset σ) :
    MvPolynomial σ K →+* MvPolynomial σ K :=
  eval₂Hom C (fun i => if i ∈ A then 0 else X i)

/-- Action of the projection on a monomial. -/
theorem thm52_projectionHom_monomial (A : Finset σ) (e : σ →₀ ℕ) (c : K) :
    thm52_projectionHom (K := K) A (monomial e c) =
      if _h : ∀ i, i ∈ A → e i = 0 then monomial e c else 0 := by
  rw [thm52_projectionHom, MvPolynomial.eval₂Hom_monomial]
  split_ifs with h
  · have heq : (e.prod fun i k => (if i ∈ A then 0 else X i : MvPolynomial σ K) ^ k) =
        e.prod fun i k => (X i : MvPolynomial σ K) ^ k := by
      apply Finsupp.prod_congr
      intro i hi
      by_cases hiA : i ∈ A
      · have hne : e i ≠ 0 := by simpa using hi
        exact False.elim (hne (h i hiA))
      · simp [hiA]
    rw [heq, ← MvPolynomial.monic_monomial_eq]
    rw [MvPolynomial.C_mul_monomial]
    simp
  · push Not at h
    rcases h with ⟨i, hiA, hie⟩
    have hiSupp : i ∈ e.support := by simpa [Finsupp.mem_support_iff] using hie
    have hprod : (e.prod fun i k =>
        (if i ∈ A then 0 else X i : MvPolynomial σ K) ^ k) = 0 := by
      rw [Finsupp.prod_eq_zero_iff]
      exact ⟨i, hiSupp, by simp [hiA, hie]⟩
    rw [hprod, mul_zero]

omit [DecidableEq σ] [Fintype σ] in
/-- `primeOf` is the usual ideal generated by its displayed variables. -/
theorem thm52_primeOf_eq_span (A : Finset σ) :
    (primeOf (K := K) A : Ideal (MvPolynomial σ K)) =
      Ideal.span (X '' (A : Set σ)) := by
  rw [primeOf, purePower, monomialIdeal]
  congr 1
  ext x
  constructor
  · rintro ⟨e, ⟨i, hiA, rfl⟩, rfl⟩
    exact ⟨i, hiA, by simp [MvPolynomial.X]⟩
  · rintro ⟨i, hiA, rfl⟩
    exact ⟨Finsupp.single i 1, ⟨i, hiA, rfl⟩, by simp [MvPolynomial.X]⟩

/-- Kernel of the projection is the variable prime. -/
theorem thm52_projectionHom_ker (A : Finset σ) :
    RingHom.ker (thm52_projectionHom (K := K) A) = primeOf (K := K) A := by
  rw [thm52_primeOf_eq_span]
  ext x
  constructor
  · rw [RingHom.mem_ker]
    intro hx
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro e he
    by_contra hno
    have hz : ∀ i, i ∈ A → e i = 0 := by
      intro i hiA
      by_contra hne
      exact hno ⟨i, hiA, hne⟩
    have hcoeff : coeff e (thm52_projectionHom (K := K) A x) = coeff e x := by
      calc
        coeff e (thm52_projectionHom (K := K) A x) =
            coeff e (Finset.sum x.support (fun v =>
              thm52_projectionHom (K := K) A (monomial v (coeff v x)))) := by
                rw [← map_sum, MvPolynomial.support_sum_monomial_coeff]
        _ = Finset.sum x.support (fun v =>
              coeff e (if _h : (∀ i, i ∈ A → v i = 0) then
                monomial v (coeff v x) else 0)) := by
                  simp_rw [thm52_projectionHom_monomial]
                  rw [MvPolynomial.coeff_sum]
        _ = coeff e x := by
              rw [Finset.sum_eq_single e]
              · rw [dif_pos hz]
                simp
              · intro v hv hve
                by_cases hvz : ∀ i, i ∈ A → v i = 0
                · rw [dif_pos hvz, MvPolynomial.coeff_monomial]
                  simp [hve]
                · rw [dif_neg hvz]
                  simp
              · intro heNot
                exact False.elim (heNot he)
    have hcx0 : coeff e x = 0 := by simpa [hx] using hcoeff.symm
    exact (by simpa [Finsupp.mem_support_iff] using hcx0 : e ∉ x.support) he
  · rw [MvPolynomial.mem_ideal_span_X_image]
    intro hx
    rw [RingHom.mem_ker]
    calc
      thm52_projectionHom (K := K) A x = Finset.sum x.support (fun v =>
          thm52_projectionHom (K := K) A (monomial v (coeff v x))) := by
            rw [← map_sum, MvPolynomial.support_sum_monomial_coeff]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        rcases hx v hv with ⟨i, hiA, hvi⟩
        have hnot : ¬ (∀ j, j ∈ A → v j = 0) := by
          intro hz
          exact hvi (hz i hiA)
        rw [thm52_projectionHom_monomial, dif_neg hnot]

/-- Variable primes are prime. -/
theorem thm52_primeOf_isPrime (A : Finset σ) : (primeOf (K := K) A).IsPrime := by
  rw [← thm52_projectionHom_ker (K := K) A]
  exact RingHom.ker_isPrime _

/-- Radical of a positive pure-power component. -/
theorem thm52_purePower_radical {A : Finset σ} {a : σ → ℕ}
    (ha : ∀ i, i ∈ A → 0 < a i) :
    (purePower (K := K) A a).radical = primeOf (K := K) A := by
  have hp : (primeOf (K := K) A).IsPrime := thm52_primeOf_isPrime A
  apply le_antisymm
  · calc
      (purePower (K := K) A a).radical ≤ (primeOf (K := K) A).radical := by
        apply Ideal.radical_mono
        rw [primeOf]
        apply monomialIdeal_le_iff.mpr
        rintro e ⟨u, ⟨i, hi, rfl⟩, hule⟩
        have hai : a i ≤ e i := Finsupp.single_le_iff.mp hule
        exact ⟨Finsupp.single i 1, ⟨i, hi, rfl⟩,
          Finsupp.single_le_iff.mpr (le_trans (ha i hi) hai)⟩
      _ = primeOf (K := K) A := hp.radical
  · rw [thm52_primeOf_eq_span]
    rw [Ideal.span_le]
    rintro x ⟨i, hi, rfl⟩
    refine Ideal.mem_radical_iff.mpr ?_
    refine ⟨a i, ?_⟩
    have hm : (monomial (Finsupp.single i (a i)) (1 : K) : MvPolynomial σ K) ∈
        purePower (K := K) A a :=
      monomial_mem_purePower.mpr ⟨i, hi, by simp⟩
    simpa [MvPolynomial.X, MvPolynomial.monomial_pow] using hm

/-- The displayed root is the radical of the given component intersection. -/
theorem thm52_root_eq_radical {I : Ideal (MvPolynomial σ K)}
    {A : ι → Finset σ} {a : ι → σ → ℕ} (hI : HasComponents I A a)
    (hpos : ∀ j i, i ∈ A j → 0 < a j i) :
    thm52_root (K := K) A = I.radical := by
  classical
  have hroot : thm52_root (K := K) A =
      (⨅ j, (primeOf (K := K) (A j) : Ideal (MvPolynomial σ K))) := by
    simpa [HasComponents, primeOf] using thm52_root_hasComponents (K := K) A
  have hrad : I.radical =
      (⨅ j, (primeOf (K := K) (A j) : Ideal (MvPolynomial σ K))) := by
    rw [hI]
    have hmap : (⨅ j, (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K))).radical =
        ⨅ j, (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K)).radical := by
      change Ideal.radicalInfTopHom
          (⨅ j, (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K))) = _
      rw [Set.map_finite_iInf Ideal.radicalInfTopHom]
      rfl
    rw [hmap]
    have hcomp : ∀ j, (purePower (K := K) (A j) (a j)).radical =
        primeOf (K := K) (A j) := fun j => thm52_purePower_radical (hpos j)
    simp_rw [hcomp]
  exact hroot.trans hrad.symm

/-- Diagonal weighting of the transversal root gives back the original ideal. -/
theorem thm52_diagonal_root_eq {I : Ideal (MvPolynomial σ K)}
    {A : ι → Finset σ} {a : ι → σ → ℕ} (hI : HasComponents I A a)
    (hpos : ∀ j i, i ∈ A j → 0 < a j i)
    (hcoh : ∀ j k i, i ∈ A j → i ∈ A k → a j i = a k i) :
    diagonal (K := K) (thm52_weights A a) (thm52_root (K := K) A) = I := by
  classical
  let d : σ → ℕ := thm52_weights A a
  let J : Ideal (MvPolynomial σ K) := thm52_root (K := K) A
  have hJmono : IsMonomialIdeal J := by
    exact thm52_root_isMonomial (K := K) A
  have hd : ∀ i, 0 < d i := by
    simpa [d] using thm52_weights_pos hpos
  have hIgens : I = monomialIdeal (K := K) (thm52_componentGens A a) :=
    hI.trans (thm52_iInf_purePower_eq (K := K) A a)
  have hdiaggens : diagonal d J =
      monomialIdeal (K := K) (diagExp d '' (characteristicExp ''
        {T : Finset σ | IsTransversal (Set.range A) T})) := by
    change diagonal d (monomialIdeal (K := K) (characteristicExp ''
      {T : Finset σ | IsTransversal (Set.range A) T})) = _
    exact diagonal_monomialIdeal (K := K) d _
  rw [hIgens, hdiaggens]
  apply monomialIdeal_eq_iff.mpr
  intro e
  constructor
  · intro hdiag
    have hdiagMem : (monomial e (1 : K) : MvPolynomial σ K) ∈ diagonal d J := by
      rw [hdiaggens]
      exact monomial_mem_monomialIdeal.mpr hdiag
    have hrootFloor : (monomial (floorDiv d e) (1 : K) : MvPolynomial σ K) ∈ J :=
      (monomial_mem_diagonal hJmono hd).mp hdiagMem
    have hall := (thm52_monomial_mem_root_iff (K := K) A (floorDiv d e)).mp hrootFloor
    refine ⟨e, ?_, le_rfl⟩
    intro j
    rcases hall j with ⟨i, hiA, hfloorPos⟩
    refine ⟨i, hiA, ?_⟩
    have hfloor : 1 ≤ floorDiv d e i := (Nat.succ_le_iff).2 hfloorPos
    have hdi : d i = a j i := thm52_weights_eq hcoh hiA
    have hquot : 1 ≤ e i / d i := by
      simpa only [floorDiv_apply] using hfloor
    have hmul : d i ≤ e i := by
      have hmul' : 1 * d i ≤ e i := (Nat.le_div_iff_mul_le (hd i)).1 hquot
      simpa using hmul'
    simpa [hdi] using hmul
  · rintro ⟨u, hu, hule⟩
    have hrootFloor : (monomial (floorDiv d e) (1 : K) : MvPolynomial σ K) ∈ J := by
      apply (thm52_monomial_mem_root_iff (K := K) A (floorDiv d e)).mpr
      intro j
      rcases hu j with ⟨i, hiA, hau⟩
      refine ⟨i, hiA, ?_⟩
      have hdi : d i = a j i := by
        exact thm52_weights_eq hcoh hiA
      have hle : d i ≤ e i := by
        simpa [hdi] using le_trans hau (hule i)
      have hfloor : 1 ≤ e i / d i := (Nat.le_div_iff_mul_le (hd i)).2 (by simpa using hle)
      rw [floorDiv_apply]
      exact Nat.lt_of_lt_of_le Nat.zero_lt_one hfloor
    have hdiagMem : (monomial e (1 : K) : MvPolynomial σ K) ∈ diagonal d J :=
      (monomial_mem_diagonal hJmono hd).mpr hrootFloor
    rw [hdiaggens] at hdiagMem
    exact monomial_mem_monomialIdeal.mp hdiagMem

omit [Fintype σ] [Fintype ι] in
/-- Exponent coherence is the only place where the specialized obstruction is used. -/
theorem thm52_exponent_coherence_ofStdSymbolic {I : Ideal (MvPolynomial σ K)}
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (_hI0 : I ≠ ⊥) (_hItop : I ≠ ⊤)
    (hdec : IsIrredundantDecomp I A a) (hanti : SupportsAntichain A a)
    (hinc : thm52_IncidenceBound A)
    (hsym : HasStdSymbolicFormula I (fun j => purePower (K := K) (A j) (a j)))
    (hsymbolic2 : symbolicPower I 2 = I ^ 2)
    (lem51Obstruction : thm52_lem51Obstruction (K := K) A a) :
    ∀ j k i, i ∈ A j → i ∈ A k → a j i = a k i := by
  classical
  rcases hdec with ⟨hI, hirr⟩
  have hpos : ∀ j i, i ∈ A j → 0 < a j i := thm52_component_exponents_pos hirr
  have hcomp : I ^ 2 = componentSymbolic (fun j => purePower (K := K) (A j) (a j)) 2 :=
    hsymbolic2.symm.trans (hsym 2 (by norm_num))
  have hcomp' :
      (⨅ j, (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K))) ^ 2 =
        ⨅ j, (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K)) ^ 2 := by
    rw [← hI]
    simpa [componentSymbolic] using hcomp
  intro j k i hiAj hiAk
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hjk : j ≠ k := by
      intro h
      exact hne (by simp [h])
    have hmeet : (A j ∩ A k).Nonempty := ⟨i, by simp [hiAj, hiAk]⟩
    exact (lem51Obstruction hanti hpos hjk hiAj hiAk hlt (hinc hjk hmeet)) hcomp'
  · have hkj : k ≠ j := by
      intro h
      exact hne (by simp [h])
    have hmeet : (A k ∩ A j).Nonempty := ⟨i, by simp [hiAk, hiAj]⟩
    exact (lem51Obstruction hanti hpos hkj hiAk hiAj hgt (hinc hkj hmeet)) hcomp'

/-- Theorem 5.2, including the precise root and forced-weight conclusions. -/
theorem thm52_ofStdSymbolic {I : Ideal (MvPolynomial σ K)}
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (_hI0 : I ≠ ⊥) (_hItop : I ≠ ⊤)
    (hdec : IsIrredundantDecomp I A a) (hanti : SupportsAntichain A a)
    (hinc : thm52_IncidenceBound A)
    (hsym : HasStdSymbolicFormula I (fun j => purePower (K := K) (A j) (a j)))
    (hsymbolic2 : symbolicPower I 2 = I ^ 2)
    (lem51Obstruction : thm52_lem51Obstruction (K := K) A a) :
    (∀ j k i, i ∈ A j → i ∈ A k → a j i = a k i) ∧
      ∃ d : σ → ℕ,
        (∀ i, 0 < d i) ∧
        (∀ j i, i ∈ A j → d i = a j i) ∧
        IsSquarefreeMonomialIdeal (thm52_root (K := K) A) ∧
        IsIrredundantDecomp (thm52_root (K := K) A) A (fun _ _ => (1 : ℕ)) ∧
        thm52_root (K := K) A = I.radical ∧
        diagonal d (thm52_root (K := K) A) = I := by
  classical
  let d : σ → ℕ := thm52_weights A a
  have hcoh := thm52_exponent_coherence_ofStdSymbolic
    _hI0 _hItop hdec hanti hinc hsym hsymbolic2 lem51Obstruction
  rcases hdec with ⟨hI, hirr⟩
  have hpos : ∀ j i, i ∈ A j → 0 < a j i := thm52_component_exponents_pos hirr
  have hd : ∀ i, 0 < d i := by simpa [d] using thm52_weights_pos hpos
  have hwd : ∀ j i, i ∈ A j → d i = a j i := by
    intro j i hi
    exact thm52_weights_eq hcoh hi
  refine ⟨hcoh, d, hd, hwd, thm52_root_squarefree (K := K) A, ?_, ?_, ?_⟩
  · exact ⟨thm52_root_hasComponents (K := K) A, thm52_root_irredundant hanti⟩
  · exact thm52_root_eq_radical hI hpos
  · exact thm52_diagonal_root_eq hI hpos hcoh

/-- Theorem 5.2 in the `HasSqRoot` form used by the MPV conjecture. -/
theorem thm52_hasSqRoot_ofStdSymbolic {I : Ideal (MvPolynomial σ K)}
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤)
    (hdec : IsIrredundantDecomp I A a) (hanti : SupportsAntichain A a)
    (hinc : thm52_IncidenceBound A)
    (hsym : HasStdSymbolicFormula I (fun j => purePower (K := K) (A j) (a j)))
    (hsymbolic2 : symbolicPower I 2 = I ^ 2)
    (lem51Obstruction : thm52_lem51Obstruction (K := K) A a) : HasSqRoot I := by
  rcases thm52_ofStdSymbolic hI0 hItop hdec hanti hinc hsym hsymbolic2
      lem51Obstruction with ⟨_, d, hd, _, hsqfree, _, _, hdiag⟩
  exact ⟨thm52_root (K := K) A, d, hsqfree, hd, hdiag⟩

omit [Fintype σ] in
/-- Coherence with Eq. (2) supplied by `eq2_standardSymbolic`; only the specialized
Lemma 5.1 reduction remains explicit. -/
theorem thm52_exponent_coherence_ofCoreObstruction {I : Ideal (MvPolynomial σ K)}
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (_hI0 : I ≠ ⊥) (_hItop : I ≠ ⊤)
    (hdec : IsIrredundantDecomp I A a) (hanti : SupportsAntichain A a)
    (hinc : thm52_IncidenceBound A)
    (hsymbolic2 : symbolicPower I 2 = I ^ 2)
    (lem51Obstruction : thm52_lem51Obstruction (K := K) A a) :
    ∀ j k i, i ∈ A j → i ∈ A k → a j i = a k i := by
  exact thm52_exponent_coherence_ofStdSymbolic _hI0 _hItop hdec hanti hinc
    (eq2_standardSymbolic hdec hanti) hsymbolic2 lem51Obstruction

/-- Theorem 5.2 with Eq. (2) internalized via `eq2_standardSymbolic`. -/
theorem thm52_ofCoreObstruction {I : Ideal (MvPolynomial σ K)}
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (_hI0 : I ≠ ⊥) (_hItop : I ≠ ⊤)
    (hdec : IsIrredundantDecomp I A a) (hanti : SupportsAntichain A a)
    (hinc : thm52_IncidenceBound A)
    (hsymbolic2 : symbolicPower I 2 = I ^ 2)
    (lem51Obstruction : thm52_lem51Obstruction (K := K) A a) :
    (∀ j k i, i ∈ A j → i ∈ A k → a j i = a k i) ∧
      ∃ d : σ → ℕ,
        (∀ i, 0 < d i) ∧
        (∀ j i, i ∈ A j → d i = a j i) ∧
        IsSquarefreeMonomialIdeal (thm52_root (K := K) A) ∧
        IsIrredundantDecomp (thm52_root (K := K) A) A (fun _ _ => (1 : ℕ)) ∧
        thm52_root (K := K) A = I.radical ∧
        diagonal d (thm52_root (K := K) A) = I := by
  exact thm52_ofStdSymbolic _hI0 _hItop hdec hanti hinc
    (eq2_standardSymbolic hdec hanti) hsymbolic2 lem51Obstruction

/-- `HasSqRoot` form of Theorem 5.2 with Eq. (2) internalized. -/
theorem thm52_hasSqRoot_ofCoreObstruction {I : Ideal (MvPolynomial σ K)}
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤)
    (hdec : IsIrredundantDecomp I A a) (hanti : SupportsAntichain A a)
    (hinc : thm52_IncidenceBound A)
    (hsymbolic2 : symbolicPower I 2 = I ^ 2)
    (lem51Obstruction : thm52_lem51Obstruction (K := K) A a) : HasSqRoot I := by
  exact thm52_hasSqRoot_ofStdSymbolic hI0 hItop hdec hanti hinc
    (eq2_standardSymbolic hdec hanti) hsymbolic2 lem51Obstruction

/-- Theorem 5.2's exponent-coherence conclusion with both Eq. (2) and Lemma 5.1 internalized. -/
theorem thm52_exponent_coherence {I : Ideal (MvPolynomial σ K)}
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (_hI0 : I ≠ ⊥) (_hItop : I ≠ ⊤)
    (hdec : IsIrredundantDecomp I A a) (hanti : SupportsAntichain A a)
    (hinc : thm52_IncidenceBound A)
    (hsymbolic2 : symbolicPower I 2 = I ^ 2) :
    ∀ j k i, i ∈ A j → i ∈ A k → a j i = a k i := by
  exact thm52_exponent_coherence_ofCoreObstruction _hI0 _hItop hdec hanti hinc
    hsymbolic2 (thm52_lem51Obstruction_holds A a)

/-- Theorem 5.2 with Eq. (2) and the specialized Lemma 5.1 reduction internalized. -/
theorem thm52 {I : Ideal (MvPolynomial σ K)}
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (_hI0 : I ≠ ⊥) (_hItop : I ≠ ⊤)
    (hdec : IsIrredundantDecomp I A a) (hanti : SupportsAntichain A a)
    (hinc : thm52_IncidenceBound A)
    (hsymbolic2 : symbolicPower I 2 = I ^ 2) :
    (∀ j k i, i ∈ A j → i ∈ A k → a j i = a k i) ∧
      ∃ d : σ → ℕ,
        (∀ i, 0 < d i) ∧
        (∀ j i, i ∈ A j → d i = a j i) ∧
        IsSquarefreeMonomialIdeal (thm52_root (K := K) A) ∧
        IsIrredundantDecomp (thm52_root (K := K) A) A (fun _ _ => (1 : ℕ)) ∧
        thm52_root (K := K) A = I.radical ∧
        diagonal d (thm52_root (K := K) A) = I := by
  exact thm52_ofCoreObstruction _hI0 _hItop hdec hanti hinc
    hsymbolic2 (thm52_lem51Obstruction_holds A a)

/-- `HasSqRoot` form of Theorem 5.2 with all cross-file reductions internalized. -/
theorem thm52_hasSqRoot {I : Ideal (MvPolynomial σ K)}
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤)
    (hdec : IsIrredundantDecomp I A a) (hanti : SupportsAntichain A a)
    (hinc : thm52_IncidenceBound A)
    (hsymbolic2 : symbolicPower I 2 = I ^ 2) : HasSqRoot I := by
  exact thm52_hasSqRoot_ofCoreObstruction hI0 hItop hdec hanti hinc
    hsymbolic2 (thm52_lem51Obstruction_holds A a)

omit [Fintype σ] [Fintype ι] in
/-- Condition (11) holds automatically for an antichain of two-element supports. -/
theorem thm52_IncidenceBound_of_card_eq_two {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hanti : SupportsAntichain A a) (hcard : ∀ j, (A j).card = 2) :
    thm52_IncidenceBound A := by
  classical
  intro k l hkl hmeet
  rcases hmeet with ⟨x, hx⟩
  have hxk : x ∈ A k := (Finset.mem_inter.mp hx).1
  have hxl : x ∈ A l := (Finset.mem_inter.mp hx).2
  have hleInter : (A k ∩ A l).card ≤ (A k).card :=
    Finset.card_le_card Finset.inter_subset_left
  have hleInter' : (A k ∩ A l).card ≤ 2 := by simpa [hcard k] using hleInter
  have hneInter : (A k ∩ A l).card ≠ 2 := by
    intro hcardInter
    have heq : A k ∩ A l = A k :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
        rw [hcardInter, hcard k])
    have hsub : A k ⊆ A l := by
      intro y hy
      have hyInter : y ∈ A k ∩ A l := by simpa [heq] using hy
      exact (Finset.mem_inter.mp hyInter).2
    exact hkl (hanti k l hsub)
  have hposInter : 0 < (A k ∩ A l).card :=
    Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxk, hxl⟩⟩
  have hInter : (A k ∩ A l).card = 1 := by omega
  let U : Finset σ := A k ∪ A l
  have hxU : x ∈ U := Finset.mem_union.mpr (Or.inl hxk)
  have hU : U.card = 3 := by
    have hformula := Finset.card_union_add_card_inter (A k) (A l)
    dsimp [U]
    rw [hInter, hcard k, hcard l] at hformula
    omega
  have hUerase : (U.erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hxU, hU]
  have hIntervenor (j : ι) (hj : thm52_isIntervenor A k l j) : A j = U.erase x := by
    have hxnot : x ∉ A j := by
      intro hxj
      rcases Finset.card_eq_two.mp (hcard j) with ⟨u, v, _huv, hAj⟩
      have hxuv : x = u ∨ x = v := by simpa [hAj] using hxj
      rcases hxuv with hxu | hxv
      · have hvj : v ∈ A j := by simp [hAj]
        have hvU : v ∈ U := hj.2.2 hvj
        rcases Finset.mem_union.mp hvU with hvk | hvl
        · have hsub : A j ⊆ A k := by
            intro y hy
            have hyuv : y = u ∨ y = v := by simpa [hAj] using hy
            rcases hyuv with rfl | rfl
            · simpa [hxu] using hxk
            · exact hvk
          exact hj.1 (hanti j k hsub)
        · have hsub : A j ⊆ A l := by
            intro y hy
            have hyuv : y = u ∨ y = v := by simpa [hAj] using hy
            rcases hyuv with rfl | rfl
            · simpa [hxu] using hxl
            · exact hvl
          exact hj.2.1 (hanti j l hsub)
      · have huj : u ∈ A j := by simp [hAj]
        have huU : u ∈ U := hj.2.2 huj
        rcases Finset.mem_union.mp huU with huk | hul
        · have hsub : A j ⊆ A k := by
            intro y hy
            have hyuv : y = u ∨ y = v := by simpa [hAj] using hy
            rcases hyuv with rfl | rfl
            · exact huk
            · simpa [hxv] using hxk
          exact hj.1 (hanti j k hsub)
        · have hsub : A j ⊆ A l := by
            intro y hy
            have hyuv : y = u ∨ y = v := by simpa [hAj] using hy
            rcases hyuv with rfl | rfl
            · exact hul
            · simpa [hxv] using hxl
          exact hj.2.1 (hanti j l hsub)
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      have hyU : y ∈ U := hj.2.2 hy
      have hyx : y ≠ x := by
        intro h
        exact hxnot (by simpa [h] using hy)
      exact Finset.mem_erase.mpr ⟨hyx, hyU⟩
    · rw [hUerase, hcard j]
  intro j₁ j₂ hj₁ hj₂
  apply hanti j₁ j₂
  rw [hIntervenor j₁ hj₁, hIntervenor j₂ hj₂]

omit [Fintype σ] in
/-- A family of at most four components automatically satisfies the two-intervenor bound. -/
theorem thm52_TwoIntervenorBound_of_card_le_four (A : ι → Finset σ)
    (hcardι : Fintype.card ι ≤ 4) : thm52_TwoIntervenorBound A := by
  classical
  intro k l hkl _hmeet j₁ j₂ j₃ hj₁ hj₂ hj₃
  by_contra hne
  push Not at hne
  have hk₁ : k ≠ j₁ := fun h ↦ hj₁.1 h.symm
  have hk₂ : k ≠ j₂ := fun h ↦ hj₂.1 h.symm
  have hk₃ : k ≠ j₃ := fun h ↦ hj₃.1 h.symm
  have hl₁ : l ≠ j₁ := fun h ↦ hj₁.2.1 h.symm
  have hl₂ : l ≠ j₂ := fun h ↦ hj₂.2.1 h.symm
  have hl₃ : l ≠ j₃ := fun h ↦ hj₃.2.1 h.symm
  let T : Finset ι := {k, l, j₁, j₂, j₃}
  have hT : T.card = 5 := by
    dsimp [T]
    simp [hkl, hk₁, hk₂, hk₃, hl₁, hl₂, hl₃, hne.1, hne.2.1, hne.2.2]
  have hle : T.card ≤ Fintype.card ι := Finset.card_le_univ T
  omega

/-- Theorem 3.1 has four components, hence its incidence bound is at most two. -/
theorem thm31_support_thm52_TwoIntervenorBound :
    thm52_TwoIntervenorBound thm31_support := by
  exact thm52_TwoIntervenorBound_of_card_le_four thm31_support (by simp)

/-- For the pair with supports `{a,b,z}` and `{c,d,z}`, the intervenors are exactly the
components with supports `{a,d}` and `{b,c}`. -/
theorem thm31_isIntervenor_ABZ_CDZ_iff (j : Fin 4) :
    thm52_isIntervenor thm31_support (0 : Fin 4) 3 j ↔ j = 1 ∨ j = 2 := by
  fin_cases j <;>
    simp [thm52_isIntervenor, thm31_support, thm31_a, thm31_b, thm31_c, thm31_d,
      thm31_z, Finset.subset_iff]

omit [Fintype ι] in
/-- Arbitrary positive diagonal weights agreeing on used variables recover the original
intersection of pure-power components. -/
theorem thm52_diagonal_root_eq_of_agreement {I : Ideal (MvPolynomial σ K)}
    {A : ι → Finset σ} {a : ι → σ → ℕ} {d : σ → ℕ}
    (hI : HasComponents I A a)
    (hd : ∀ i, 0 < d i)
    (hdEq : ∀ j i, i ∈ A j → d i = a j i) :
    diagonal (K := K) d (thm52_root (K := K) A) = I := by
  classical
  let J : Ideal (MvPolynomial σ K) := thm52_root (K := K) A
  have hJmono : IsMonomialIdeal J := by
    exact thm52_root_isMonomial (K := K) A
  have hIgens : I = monomialIdeal (K := K) (thm52_componentGens A a) :=
    hI.trans (thm52_iInf_purePower_eq (K := K) A a)
  have hdiaggens : diagonal d J =
      monomialIdeal (K := K) (diagExp d '' (characteristicExp ''
        {T : Finset σ | IsTransversal (Set.range A) T})) := by
    change diagonal d (monomialIdeal (K := K) (characteristicExp ''
      {T : Finset σ | IsTransversal (Set.range A) T})) = _
    exact diagonal_monomialIdeal (K := K) d _
  rw [hIgens, hdiaggens]
  apply monomialIdeal_eq_iff.mpr
  intro e
  constructor
  · intro hdiag
    have hdiagMem : (monomial e (1 : K) : MvPolynomial σ K) ∈ diagonal d J := by
      rw [hdiaggens]
      exact monomial_mem_monomialIdeal.mpr hdiag
    have hrootFloor : (monomial (floorDiv d e) (1 : K) : MvPolynomial σ K) ∈ J :=
      (monomial_mem_diagonal hJmono hd).mp hdiagMem
    have hall := (thm52_monomial_mem_root_iff (K := K) A (floorDiv d e)).mp hrootFloor
    refine ⟨e, ?_, le_rfl⟩
    intro j
    rcases hall j with ⟨i, hiA, hfloorPos⟩
    refine ⟨i, hiA, ?_⟩
    have hfloor : 1 ≤ floorDiv d e i := (Nat.succ_le_iff).2 hfloorPos
    have hdi : d i = a j i := hdEq j i hiA
    have hquot : 1 ≤ e i / d i := by
      simpa only [floorDiv_apply] using hfloor
    have hmul : d i ≤ e i := by
      have hmul' : 1 * d i ≤ e i := (Nat.le_div_iff_mul_le (hd i)).1 hquot
      simpa using hmul'
    simpa [hdi] using hmul
  · rintro ⟨u, hu, hule⟩
    have hrootFloor : (monomial (floorDiv d e) (1 : K) : MvPolynomial σ K) ∈ J := by
      apply (thm52_monomial_mem_root_iff (K := K) A (floorDiv d e)).mpr
      intro j
      rcases hu j with ⟨i, hiA, hau⟩
      refine ⟨i, hiA, ?_⟩
      have hdi : d i = a j i := hdEq j i hiA
      have hle : d i ≤ e i := by
        simpa [hdi] using le_trans hau (hule i)
      have hfloor : 1 ≤ e i / d i := (Nat.le_div_iff_mul_le (hd i)).2 (by simpa using hle)
      rw [floorDiv_apply]
      exact Nat.lt_of_lt_of_le Nat.zero_lt_one hfloor
    have hdiagMem : (monomial e (1 : K) : MvPolynomial σ K) ∈ diagonal d J :=
      (monomial_mem_diagonal hJmono hd).mpr hrootFloor
    rw [hdiaggens] at hdiagMem
    exact monomial_mem_monomialIdeal.mp hdiagMem

omit [Fintype ι] in
/-- Under all hypotheses of Theorem 5.2, weights on unused variables are arbitrary. -/
theorem thm52_arbitraryUnusedWeights {I : Ideal (MvPolynomial σ K)}
    {A : ι → Finset σ} {a : ι → σ → ℕ} {w : σ → ℕ}
    (_hI0 : I ≠ ⊥) (_hItop : I ≠ ⊤)
    (hdec : IsIrredundantDecomp I A a) (_hanti : SupportsAntichain A a)
    (_hinc : thm52_IncidenceBound A)
    (_hsymbolic2 : symbolicPower I 2 = I ^ 2)
    (hwpos : ∀ i, 0 < w i)
    (hwEq : ∀ j i, i ∈ A j → w i = a j i) :
    diagonal (K := K) w (thm52_root (K := K) A) = I := by
  rcases hdec with ⟨hI, _hirr⟩
  exact thm52_diagonal_root_eq_of_agreement (K := K) hI hwpos hwEq

/-- The bound one is sharp.  For every unequal positive `r` and `s`, Theorem 3.1 supplies
an all-power Simis ideal satisfying every other hypothesis of Theorem 5.2 and the relaxed
two-intervenor bound, but admitting no squarefree diagonal representation. -/
theorem thm52_bound_one_sharp (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) :
    ∃ (I : Ideal (MvPolynomial thm31_var K))
      (A : Fin 4 → Finset thm31_var)
      (a : Fin 4 → thm31_var → ℕ),
      I ≠ ⊥ ∧ I ≠ ⊤ ∧
      IsIrredundantDecomp I A a ∧ SupportsAntichain A a ∧
      ¬ thm52_IncidenceBound A ∧ thm52_TwoIntervenorBound A ∧
      IsSimis I ∧ symbolicPower I 2 = I ^ 2 ∧
      ¬ HasSqRoot I ∧ ¬ MPVConc I := by
  have hmeet :
      (thm31_support (0 : Fin 4) ∩ thm31_support (3 : Fin 4)).Nonempty := by
    refine ⟨thm31_z, ?_⟩
    simp [thm31_support]
  have hnotOne : ¬ thm52_IncidenceBound thm31_support := by
    intro hinc
    have hone : thm52_AtMostOneIntervenor thm31_support (0 : Fin 4) 3 :=
      hinc (k := (0 : Fin 4)) (l := 3) (by decide) hmeet
    have h1 : thm52_isIntervenor thm31_support (0 : Fin 4) 3 1 :=
      (thm31_isIntervenor_ABZ_CDZ_iff (1 : Fin 4)).2 (Or.inl rfl)
    have h2 : thm52_isIntervenor thm31_support (0 : Fin 4) 3 2 :=
      (thm31_isIntervenor_ABZ_CDZ_iff (2 : Fin 4)).2 (Or.inr rfl)
    exact (by decide : (1 : Fin 4) ≠ 2) (hone h1 h2)
  refine ⟨thm31_I (K := K) r s, thm31_support, thm31_componentExp r s,
    thm31_I_ne_bot (K := K) r s, thm31_I_ne_top (K := K) r s,
    thm31_isIrredundantDecomp (K := K) r s hr hs,
    thm31_supportsAntichain r s, hnotOne,
    thm31_support_thm52_TwoIntervenorBound, thm31_isSimis (K := K) r s hr hs,
    thm31_symbolicPower_eq_pow (K := K) r s hr hs 2 (by omega), ?_, ?_⟩
  · intro hroot
    exact hrs ((thm31_hasSqRoot_iff (K := K) r s hr hs).mp hroot)
  · intro hmpv
    exact hrs ((thm31_MPVConc_iff (K := K) r s hr hs).mp hmpv)

omit [Fintype σ] [Fintype ι] in
/-- The paper's irredundance, unmixedness, and pairwise-distinct-radical hypotheses imply
the support antichain used by the internal form of Theorem 5.2. -/
theorem thm52_supportsAntichain_of_paperHypotheses [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hdec : IsIrredundantDecomp I A a)
    (hNoEmb : associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) =
      I.minimalPrimes)
    (hDistinct : ∀ j k, (primeOf (A j) : Ideal (MvPolynomial σ K)) =
      primeOf (A k) → j = k) :
    SupportsAntichain A a := by
  classical
  rcases hdec with ⟨hI, hirr⟩
  have hpos : ∀ j i, i ∈ A j → 0 < a j i := thm52_component_exponents_pos hirr
  have hAssRange :
      associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) =
        Set.range (fun j ↦ (primeOf (A j) : Ideal (MvPolynomial σ K))) :=
    SimisFormal.diagAssoc_quotientAssociatedPrimes_eq_range
      (K := K) (I := I) (A := A) (a := a) hI hirr
  have hIleP (j : ι) : I ≤ (primeOf (A j) : Ideal (MvPolynomial σ K)) := by
    rw [hI]
    exact (iInf_le (fun k : ι ↦
      (purePower (K := K) (A k) (a k) : Ideal (MvPolynomial σ K))) j).trans
        (SimisFormal.purePower_le_primeOf_of_pos (K := K) (A := A j) (a := a j)
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
    rw [SimisFormal.primeOf_eq_span_X (K := K) (A := A j),
      SimisFormal.primeOf_eq_span_X (K := K) (A := A k)]
    exact Ideal.span_mono (Set.image_mono hsub)
  have hkMin := hMin k
  change I.IsMinimalPrime (primeOf (A k) : Ideal (MvPolynomial σ K)) at hkMin
  have hPkSubPj : (primeOf (A k) : Ideal (MvPolynomial σ K)) ≤
      (primeOf (A j) : Ideal (MvPolynomial σ K)) :=
    hkMin.2
      ⟨SimisFormal.primeOf_isPrime (K := K) (A j), hIleP j⟩ hPsub
  have hEq : (primeOf (A j) : Ideal (MvPolynomial σ K)) =
      (primeOf (A k) : Ideal (MvPolynomial σ K)) := le_antisymm hPsub hPkSubPj
  exact hDistinct j k hEq

omit [Fintype σ] [Fintype ι] in
/-- Theorem 5.2 under exactly the hypotheses stated in the manuscript. -/
theorem thm52_of_paperHypotheses [Fintype σ] [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hI0 : I ≠ ⊥) (hItop : I ≠ ⊤)
    (hdec : IsIrredundantDecomp I A a)
    (hNoEmb : associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) =
      I.minimalPrimes)
    (hDistinct : ∀ j k, (primeOf (A j) : Ideal (MvPolynomial σ K)) =
      primeOf (A k) → j = k)
    (hinc : thm52_IncidenceBound A)
    (hsymbolic2 : symbolicPower I 2 = I ^ 2) :
    (∀ j k i, i ∈ A j → i ∈ A k → a j i = a k i) ∧
      ∃ d : σ → ℕ,
        (∀ i, 0 < d i) ∧
        (∀ j i, i ∈ A j → d i = a j i) ∧
        IsSquarefreeMonomialIdeal (thm52_root (K := K) A) ∧
        IsIrredundantDecomp (thm52_root (K := K) A) A (fun _ _ => (1 : ℕ)) ∧
        thm52_root (K := K) A = I.radical ∧
        diagonal d (thm52_root (K := K) A) = I := by
  have hanti : SupportsAntichain A a :=
    thm52_supportsAntichain_of_paperHypotheses (K := K) (I := I) (A := A) (a := a)
      hdec hNoEmb hDistinct
  exact thm52 hI0 hItop hdec hanti hinc hsymbolic2
