/-
Theorem 3.1: the family \(I_{r,s}=(ac,bd,abz^r,cdz^s)\).

The file uses the explicit monomial-ideal API from `SimisFormal`.  Intrinsic symbolic
statements are formulated with the standard explicit `HasStdSymbolicFormula` hypothesis.
-/
import SimisFormal.Defs
import SimisFormal.Basic
import SimisFormal.Prop2_1
import SimisFormal.Eq2_StandardSymbolic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
open MvPolynomial
open SimisFormal
open scoped BigOperators
variable {K : Type*} [Field K]
/-- The exponent generating set of an irreducible component. -/
noncomputable def thm31_componentGens (r s : ℕ) (j : Fin 4) : Set (thm31_var →₀ ℕ) :=
  {e | ∃ i ∈ thm31_support j, e = Finsupp.single i (thm31_componentExp r s j i)}

/-- The four inequalities of Eq. (7), for an arbitrary exponent vector. -/
def thm31_numeric (r s q : ℕ) (e : thm31_var →₀ ℕ) : Prop :=
  q ≤ e thm31_a + e thm31_b + e thm31_z / s ∧
  q ≤ e thm31_a + e thm31_d ∧
  q ≤ e thm31_b + e thm31_c ∧
  q ≤ e thm31_c + e thm31_d + e thm31_z / r

/-- Exponents in `thm31_support` occur positively. -/
theorem thm31_componentExp_pos (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    ∀ j i, i ∈ thm31_support j → 0 < thm31_componentExp r s j i := by
  intro j i hi
  fin_cases j <;> fin_cases i <;>
    simp_all [thm31_support, thm31_componentExp,
      thm31_a, thm31_b, thm31_c, thm31_d, thm31_z]

/-- Powers of an irreducible monomial component are detected by total capacity. -/
theorem thm31_mon_mem_purePower_pow
    {A : Finset thm31_var} {a : thm31_var → ℕ} (ha : ∀ i ∈ A, 0 < a i)
    (e : thm31_var →₀ ℕ) :
    ∀ q : ℕ,
      (monomial e (1 : K) : MvPolynomial thm31_var K) ∈ purePower (K := K) A a ^ q ↔
        q ≤ ∑ i ∈ A, e i / a i := by
  classical
  let S : Set (thm31_var →₀ ℕ) :=
    {u | ∃ i ∈ A, u = Finsupp.single i (a i)}
  let cap : (thm31_var →₀ ℕ) → ℕ := fun u ↦ ∑ i ∈ A, u i / a i
  change ∀ q : ℕ,
      (monomial e (1 : K) : MvPolynomial thm31_var K) ∈ (monomialIdeal S : _) ^ q ↔
        q ≤ cap e
  intro q
  induction q generalizing e with
  | zero => simp [cap]
  | succ n ih =>
      have cap_add_single : ∀ (v : thm31_var →₀ ℕ) (i : thm31_var), i ∈ A →
          cap (v + Finsupp.single i (a i)) = cap v + 1 := by
        intro v i hi
        dsimp [cap]
        calc
          (∑ j ∈ A, (v + Finsupp.single i (a i)) j / a j) =
              ∑ j ∈ A, (v j / a j + if j = i then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hji : j = i
            · subst j
              simp [Nat.add_div_right, ha i hi]
            · simp [hji]
          _ = (∑ j ∈ A, v j / a j) + ∑ j ∈ A, (if j = i then 1 else 0) := by
            rw [Finset.sum_add_distrib]
          _ = (∑ j ∈ A, v j / a j) + 1 := by simp [hi]
      have cap_mono : ∀ {v w : thm31_var →₀ ℕ}, v ≤ w → cap v ≤ cap w := by
        intro v w hvw
        dsimp [cap]
        exact Finset.sum_le_sum fun j hj ↦ Nat.div_le_div_right (hvw j)
      constructor
      · rw [monomialIdeal_pow, monomial_mem_monomialIdeal, powGens]
        rintro ⟨z, hz, hze⟩
        rcases hz with ⟨v, hv, g, hg, rfl⟩
        rcases hg with ⟨i, hi, rfl⟩
        have hvMem : (monomial v (1 : K) : MvPolynomial thm31_var K) ∈
            (monomialIdeal S : Ideal (MvPolynomial thm31_var K)) ^ n := by
          rw [monomialIdeal_pow]
          exact monomial_mem_monomialIdeal.mpr ⟨v, hv, le_rfl⟩
        have hnv : n ≤ cap v := (ih v).mp hvMem
        have hle : cap (v + Finsupp.single i (a i)) ≤ cap e := cap_mono hze
        rw [cap_add_single v i hi] at hle
        omega
      · intro hqe
        rw [monomialIdeal_pow, monomial_mem_monomialIdeal, powGens]
        have hex : ∃ i ∈ A, 0 < e i / a i := by
          by_contra hnone
          have hzero : cap e = 0 := by
            dsimp [cap]
            apply Finset.sum_eq_zero
            intro i hi
            exact Nat.eq_zero_of_not_pos (fun hpos ↦ hnone ⟨i, hi, hpos⟩)
          omega
        rcases hex with ⟨i, hi, hquot⟩
        have hai : a i ≤ e i := (Nat.div_pos_iff.mp hquot).2
        let e' : thm31_var →₀ ℕ := e - Finsupp.single i (a i)
        have hge : Finsupp.single i (a i) ≤ e := by
          rw [Finsupp.le_def]
          intro j
          by_cases hji : j = i
          · subst j
            simp [hai]
          · simp [hji]
        have hadd : e' + Finsupp.single i (a i) = e := by
          ext j
          by_cases hji : j = i
          · subst j
            simp [e', Nat.sub_add_cancel hai]
          · simp [e', hji]
        have hcap := cap_add_single e' i hi
        rw [hadd] at hcap
        have hcap' : n ≤ cap e' := by omega
        have he'mem : (monomial e' (1 : K) : MvPolynomial thm31_var K) ∈
            (monomialIdeal S : Ideal (MvPolynomial thm31_var K)) ^ n :=
          (ih e').mpr hcap'
        rw [monomialIdeal_pow, monomial_mem_monomialIdeal] at he'mem
        rcases he'mem with ⟨v, hv, hve'⟩
        refine ⟨v + Finsupp.single i (a i), ?_, ?_⟩
        · exact ⟨v, hv, Finsupp.single i (a i), ⟨i, hi, rfl⟩, rfl⟩
        · rw [Finsupp.le_def]
          intro j
          calc
            (v + Finsupp.single i (a i)) j ≤
                e' j + Finsupp.single i (a i) j := Nat.add_le_add_right (hve' j) _
            _ = e j := by
              exact congrArg (fun u : thm31_var →₀ ℕ ↦ u j) hadd

/-- Multiply a monomial in \(I^n\) by one more minimal generator. -/
theorem thm31_mon_mem_pow_succ_of_generator
    {I : Ideal (MvPolynomial thm31_var K)} {n : ℕ}
    {g e : thm31_var →₀ ℕ}
    (hg : (monomial g (1 : K) : MvPolynomial thm31_var K) ∈ I)
    (hge : g ≤ e)
    (he : (monomial (e - g) (1 : K) : MvPolynomial thm31_var K) ∈ I ^ n) :
    (monomial e (1 : K) : MvPolynomial thm31_var K) ∈ I ^ (n + 1) := by
  have hsum : e - g + g = e := by
    ext i
    exact Nat.sub_add_cancel (hge i)
  have hmono : (monomial e (1 : K) : MvPolynomial thm31_var K) =
      monomial (e - g) (1 : K) * monomial g (1 : K) := by
    rw [monomial_mul]
    simp [hsum]
  rw [pow_succ, hmono]
  exact Ideal.mul_mem_mul he hg

/-- A single generator repeated \(q\) times yields membership in the \(q\)th power. -/
theorem thm31_mon_mem_pow_of_generator
    {I : Ideal (MvPolynomial thm31_var K)} {q : ℕ}
    {g e : thm31_var →₀ ℕ}
    (hg : (monomial g (1 : K) : MvPolynomial thm31_var K) ∈ I)
    (hge : q • g ≤ e) :
    (monomial e (1 : K) : MvPolynomial thm31_var K) ∈ I ^ q := by
  have hpow : (monomial (q • g) (1 : K) : MvPolynomial thm31_var K) ∈ I ^ q := by
    simpa [MvPolynomial.monomial_pow] using Ideal.pow_mem_pow hg q
  have hsum : e - q • g + q • g = e := by
    ext i
    exact Nat.sub_add_cancel (hge i)
  have hmono : (monomial e (1 : K) : MvPolynomial thm31_var K) =
      monomial (e - q • g) (1 : K) * monomial (q • g) (1 : K) := by
    rw [monomial_mul]
    simp [hsum]
  rw [hmono]
  exact Ideal.mul_mem_left _ _ hpow

/-- The power-capacity formula, specialized to the four components of (5). -/
theorem thm31_mon_mem_component_pow (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (j : Fin 4) (q : ℕ) (e : thm31_var →₀ ℕ) :
    (monomial e (1 : K) : MvPolynomial thm31_var K) ∈ thm31_component (K := K) r s j ^ q ↔
      q ≤ ∑ i ∈ thm31_support j, e i / thm31_componentExp r s j i := by
  simpa [thm31_component] using
    (thm31_mon_mem_purePower_pow (K := K)
      (A := thm31_support j) (a := thm31_componentExp r s j)
      (fun i hi ↦ thm31_componentExp_pos r s hr hs j i hi) e q)

/-- Equation (7): monomial membership in the intersection of the component powers. -/
theorem thm31_mem_componentSymbolic_iff (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (q : ℕ) (e : thm31_var →₀ ℕ) :
    (monomial e (1 : K) : MvPolynomial thm31_var K) ∈
        componentSymbolic (thm31_component (K := K) r s) q ↔
      thm31_numeric r s q e := by
  constructor
  · intro h
    have h0 := Ideal.mem_iInf.mp h (0 : Fin 4)
    have h1 := Ideal.mem_iInf.mp h (1 : Fin 4)
    have h2 := Ideal.mem_iInf.mp h (2 : Fin 4)
    have h3 := Ideal.mem_iInf.mp h (3 : Fin 4)
    have c0 := (thm31_mon_mem_component_pow (K := K) r s hr hs (0 : Fin 4) q e).mp h0
    have c1 := (thm31_mon_mem_component_pow (K := K) r s hr hs (1 : Fin 4) q e).mp h1
    have c2 := (thm31_mon_mem_component_pow (K := K) r s hr hs (2 : Fin 4) q e).mp h2
    have c3 := (thm31_mon_mem_component_pow (K := K) r s hr hs (3 : Fin 4) q e).mp h3
    rw [thm31_numeric]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [thm31_support, thm31_componentExp,
        thm31_a, thm31_b, thm31_c, thm31_d, thm31_z,
        add_assoc, add_comm, add_left_comm] at c0 c1 c2 c3 ⊢
    · exact c0
    · exact c1
    · exact c2
    · exact c3
  · rw [thm31_numeric]
    rintro ⟨h0, h1, h2, h3⟩
    apply Ideal.mem_iInf.mpr
    intro j
    fin_cases j
    · exact (thm31_mon_mem_component_pow (K := K) r s hr hs (0 : Fin 4) q e).mpr
        (by simpa [thm31_support, thm31_componentExp,
          thm31_a, thm31_b, thm31_c, thm31_d, thm31_z,
          add_assoc, add_comm, add_left_comm] using h0)
    · exact (thm31_mon_mem_component_pow (K := K) r s hr hs (1 : Fin 4) q e).mpr
        (by simpa [thm31_support, thm31_componentExp,
          thm31_a, thm31_b, thm31_c, thm31_d, thm31_z,
          add_assoc, add_comm, add_left_comm] using h1)
    · exact (thm31_mon_mem_component_pow (K := K) r s hr hs (2 : Fin 4) q e).mpr
        (by simpa [thm31_support, thm31_componentExp,
          thm31_a, thm31_b, thm31_c, thm31_d, thm31_z,
          add_assoc, add_comm, add_left_comm] using h2)
    · exact (thm31_mon_mem_component_pow (K := K) r s hr hs (3 : Fin 4) q e).mpr
        (by simpa [thm31_support, thm31_componentExp,
          thm31_a, thm31_b, thm31_c, thm31_d, thm31_z,
          add_assoc, add_comm, add_left_comm] using h3)

/-- Each minimal generator of \(I_{r,s}\) lies in every component \(Q_j\). -/
theorem thm31_generator_mem_component (r s : ℕ) {g : thm31_var →₀ ℕ}
    (hg : g ∈ thm31_gens r s) (j : Fin 4) :
    (monomial g (1 : K) : MvPolynomial thm31_var K) ∈
      thm31_component (K := K) r s j := by
  simp only [thm31_gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  all_goals
    fin_cases j
    all_goals
      rw [thm31_component, monomial_mem_purePower]
      simp [thm31_support, thm31_componentExp, thm31_gAC, thm31_gBD,
        thm31_gABZ, thm31_gCDZ,
        thm31_a, thm31_b, thm31_c, thm31_d, thm31_z]

/-- \(I_{r,s}\) is contained in each component. -/
theorem thm31_I_le_component (r s : ℕ) (j : Fin 4) :
    thm31_I (K := K) r s ≤ thm31_component (K := K) r s j := by
  rw [thm31_I, monomialIdeal, Ideal.span_le]
  rintro y ⟨g, hg, rfl⟩
  exact thm31_generator_mem_component (K := K) r s hg j

/-- The easy inclusion \(I_{r,s}^q\subseteq D_q\) used in the proof of (6). -/
theorem thm31_pow_le_componentSymbolic (r s q : ℕ) :
    thm31_I (K := K) r s ^ q ≤ componentSymbolic (thm31_component (K := K) r s) q := by
  rw [componentSymbolic]
  exact le_iInf fun j ↦ pow_le_pow_left' (thm31_I_le_component (K := K) r s j) q

/-- Explicit monomial generators for \(D_q=\bigcap_jQ_j^q\). -/
noncomputable def thm31_Dgens (r s q : ℕ) : Set (thm31_var →₀ ℕ) :=
  iInfGens (fun j : Fin 4 ↦ powGens (thm31_componentGens r s j) q)

/-- The componentwise symbolic ideal is itself represented by explicit monomial generators. -/
theorem thm31_componentSymbolic_as_monomialIdeal (r s q : ℕ) :
    componentSymbolic (thm31_component (K := K) r s) q =
      monomialIdeal (K := K) (thm31_Dgens r s q) := by
  unfold componentSymbolic thm31_Dgens
  simp_rw [thm31_component]
  unfold purePower thm31_componentGens
  simp_rw [monomialIdeal_pow]
  exact monomialIdeal_iInf (fun j : Fin 4 ↦
    powGens {e : thm31_var →₀ ℕ |
      ∃ i ∈ thm31_support j, e = Finsupp.single i (thm31_componentExp r s j i)} q)

/-- The four named monomials are members of \(I_{r,s}\). -/
theorem thm31_gAC_mem_I (r s : ℕ) :
    (monomial thm31_gAC (1 : K) : MvPolynomial thm31_var K) ∈ thm31_I (K := K) r s := by
  rw [thm31_I]
  exact monomial_mem_monomialIdeal.mpr ⟨thm31_gAC, by simp [thm31_gens], le_rfl⟩

theorem thm31_gBD_mem_I (r s : ℕ) :
    (monomial thm31_gBD (1 : K) : MvPolynomial thm31_var K) ∈ thm31_I (K := K) r s := by
  rw [thm31_I]
  exact monomial_mem_monomialIdeal.mpr ⟨thm31_gBD, by simp [thm31_gens], le_rfl⟩

theorem thm31_gABZ_mem_I (r s : ℕ) :
    (monomial (thm31_gABZ r) (1 : K) : MvPolynomial thm31_var K) ∈ thm31_I (K := K) r s := by
  rw [thm31_I]
  exact monomial_mem_monomialIdeal.mpr ⟨thm31_gABZ r, by simp [thm31_gens], le_rfl⟩

theorem thm31_gCDZ_mem_I (r s : ℕ) :
    (monomial (thm31_gCDZ s) (1 : K) : MvPolynomial thm31_var K) ∈ thm31_I (K := K) r s := by
  rw [thm31_I]
  exact monomial_mem_monomialIdeal.mpr ⟨thm31_gCDZ s, by simp [thm31_gens], le_rfl⟩

/-- Divisibility criteria for the named generators. -/
theorem thm31_gAC_le_of {e : thm31_var →₀ ℕ}
    (ha : 1 ≤ e thm31_a) (hc : 1 ≤ e thm31_c) : thm31_gAC ≤ e := by
  have ha' : 1 ≤ e (0 : thm31_var) := by simpa [thm31_a] using ha
  have hc' : 1 ≤ e (2 : thm31_var) := by simpa [thm31_c] using hc
  rw [Finsupp.le_def]
  intro i
  fin_cases i <;>
    simp [thm31_gAC, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z, ha', hc']

theorem thm31_gBD_le_of {e : thm31_var →₀ ℕ}
    (hb : 1 ≤ e thm31_b) (hd : 1 ≤ e thm31_d) : thm31_gBD ≤ e := by
  have hb' : 1 ≤ e (1 : thm31_var) := by simpa [thm31_b] using hb
  have hd' : 1 ≤ e (3 : thm31_var) := by simpa [thm31_d] using hd
  rw [Finsupp.le_def]
  intro i
  fin_cases i <;>
    simp [thm31_gBD, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z, hb', hd']

theorem thm31_gCDZ_pow_le (s q : ℕ) {e : thm31_var →₀ ℕ}
    (hc : q ≤ e thm31_c) (hd : q ≤ e thm31_d) (hz : q * s ≤ e thm31_z) :
    q • thm31_gCDZ s ≤ e := by
  have hc' : q ≤ e (2 : thm31_var) := by simpa [thm31_c] using hc
  have hd' : q ≤ e (3 : thm31_var) := by simpa [thm31_d] using hd
  have hz' : q * s ≤ e (4 : thm31_var) := by simpa [thm31_z] using hz
  rw [Finsupp.le_def]
  intro i
  fin_cases i <;>
    simp [thm31_gCDZ, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z] <;>
    omega

theorem thm31_gABZ_pow_le (r q : ℕ) {e : thm31_var →₀ ℕ}
    (ha : q ≤ e thm31_a) (hb : q ≤ e thm31_b) (hz : q * r ≤ e thm31_z) :
    q • thm31_gABZ r ≤ e := by
  have ha' : q ≤ e (0 : thm31_var) := by simpa [thm31_a] using ha
  have hb' : q ≤ e (1 : thm31_var) := by simpa [thm31_b] using hb
  have hz' : q * r ≤ e (4 : thm31_var) := by simpa [thm31_z] using hz
  rw [Finsupp.le_def]
  intro i
  fin_cases i <;>
    simp [thm31_gABZ, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z] <;>
    omega

/-- The reverse inclusion of the inductive proof of Eq. (6). -/
theorem thm31_componentSymbolic_le_pow (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    ∀ q : ℕ, componentSymbolic (thm31_component (K := K) r s) q ≤
      thm31_I (K := K) r s ^ q := by
  intro q
  induction q with
  | zero =>
      rw [componentSymbolic]
      simp
  | succ n ih =>
      rw [thm31_componentSymbolic_as_monomialIdeal (K := K) r s (n + 1)]
      rw [thm31_I, monomialIdeal_pow]
      apply monomialIdeal_le_iff.mpr
      intro e heD
      have hmemComp : (monomial e (1 : K) : MvPolynomial thm31_var K) ∈
          componentSymbolic (thm31_component (K := K) r s) (n + 1) := by
        rw [thm31_componentSymbolic_as_monomialIdeal (K := K) r s (n + 1)]
        exact monomial_mem_monomialIdeal.mpr heD
      have hnum := (thm31_mem_componentSymbolic_iff (K := K) r s hr hs (n + 1) e).mp hmemComp
      rw [thm31_numeric] at hnum
      rcases hnum with ⟨hQ1, hQ2, hQ3, hQ4⟩
      have hpow : (monomial e (1 : K) : MvPolynomial thm31_var K) ∈
          thm31_I (K := K) r s ^ (n + 1) := by
        by_cases hac : thm31_gAC ≤ e
        · let e' : thm31_var →₀ ℕ := e - thm31_gAC
          have hA : 1 ≤ e thm31_a := by
            simpa [thm31_gAC] using hac thm31_a
          have hC : 1 ≤ e thm31_c := by
            simpa [thm31_gAC] using hac thm31_c
          have he'a : e' thm31_a = e thm31_a - 1 := by simp [e', thm31_gAC]
          have he'b : e' thm31_b = e thm31_b := by simp [e', thm31_gAC]
          have he'c : e' thm31_c = e thm31_c - 1 := by simp [e', thm31_gAC]
          have he'd : e' thm31_d = e thm31_d := by simp [e', thm31_gAC]
          have he'z : e' thm31_z = e thm31_z := by simp [e', thm31_gAC]
          have hnum' : thm31_numeric r s n e' := by
            rw [thm31_numeric, he'a, he'b, he'c, he'd, he'z]
            omega
          have hprevComp :=
            (thm31_mem_componentSymbolic_iff (K := K) r s hr hs n e').mpr hnum'
          exact thm31_mon_mem_pow_succ_of_generator
            (I := thm31_I (K := K) r s) (n := n) (g := thm31_gAC) (e := e)
            (thm31_gAC_mem_I (K := K) r s) hac (by simpa [e'] using ih hprevComp)
        · by_cases hbd : thm31_gBD ≤ e
          · let e' : thm31_var →₀ ℕ := e - thm31_gBD
            have hB : 1 ≤ e thm31_b := by
              simpa [thm31_gBD] using hbd thm31_b
            have hD : 1 ≤ e thm31_d := by
              simpa [thm31_gBD] using hbd thm31_d
            have he'a : e' thm31_a = e thm31_a := by simp [e', thm31_gBD]
            have he'b : e' thm31_b = e thm31_b - 1 := by simp [e', thm31_gBD]
            have he'c : e' thm31_c = e thm31_c := by simp [e', thm31_gBD]
            have he'd : e' thm31_d = e thm31_d - 1 := by simp [e', thm31_gBD]
            have he'z : e' thm31_z = e thm31_z := by simp [e', thm31_gBD]
            have hnum' : thm31_numeric r s n e' := by
              rw [thm31_numeric, he'a, he'b, he'c, he'd, he'z]
              omega
            have hprevComp :=
              (thm31_mem_componentSymbolic_iff (K := K) r s hr hs n e').mpr hnum'
            exact thm31_mon_mem_pow_succ_of_generator
              (I := thm31_I (K := K) r s) (n := n) (g := thm31_gBD) (e := e)
              (thm31_gBD_mem_I (K := K) r s) hbd (by simpa [e'] using ih hprevComp)
          · by_cases hA0 : e thm31_a = 0
            · have hDge : n + 1 ≤ e thm31_d := by omega
              have hDone : 1 ≤ e thm31_d := by omega
              have hB0 : e thm31_b = 0 := by
                by_contra hbne
                have hBpos : 0 < e thm31_b := Nat.pos_of_ne_zero hbne
                have hBone : 1 ≤ e thm31_b := by omega
                exact hbd (thm31_gBD_le_of hBone hDone)
              have hCge : n + 1 ≤ e thm31_c := by omega
              have hfloor : n + 1 ≤ e thm31_z / s := by omega
              have hz : (n + 1) * s ≤ e thm31_z :=
                (Nat.le_div_iff_mul_le hs).mp hfloor
              exact thm31_mon_mem_pow_of_generator
                (I := thm31_I (K := K) r s) (q := n + 1)
                (g := thm31_gCDZ s) (e := e)
                (thm31_gCDZ_mem_I (K := K) r s)
                (thm31_gCDZ_pow_le s (n + 1) hCge hDge hz)
            · have hApos : 0 < e thm31_a := Nat.pos_of_ne_zero hA0
              have hAone : 1 ≤ e thm31_a := by omega
              have hC0 : e thm31_c = 0 := by
                by_contra hcne
                have hCpos : 0 < e thm31_c := Nat.pos_of_ne_zero hcne
                have hCone : 1 ≤ e thm31_c := by omega
                exact hac (thm31_gAC_le_of hAone hCone)
              have hBge : n + 1 ≤ e thm31_b := by omega
              have hBone : 1 ≤ e thm31_b := by omega
              have hD0 : e thm31_d = 0 := by
                by_contra hdne
                have hDpos : 0 < e thm31_d := Nat.pos_of_ne_zero hdne
                have hDone : 1 ≤ e thm31_d := by omega
                exact hbd (thm31_gBD_le_of hBone hDone)
              have hAge : n + 1 ≤ e thm31_a := by omega
              have hfloor : n + 1 ≤ e thm31_z / r := by omega
              have hz : (n + 1) * r ≤ e thm31_z :=
                (Nat.le_div_iff_mul_le hr).mp hfloor
              exact thm31_mon_mem_pow_of_generator
                (I := thm31_I (K := K) r s) (q := n + 1)
                (g := thm31_gABZ r) (e := e)
                (thm31_gABZ_mem_I (K := K) r s)
                (thm31_gABZ_pow_le r (n + 1) hAge hBge hz)
      rw [thm31_I, monomialIdeal_pow] at hpow
      exact monomial_mem_monomialIdeal.mp hpow

/-- Equation (6) in its componentwise form, for every nonnegative exponent. -/
theorem thm31_pow_eq_componentSymbolic (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (q : ℕ) :
    thm31_I (K := K) r s ^ q = componentSymbolic (thm31_component (K := K) r s) q := by
  apply le_antisymm
  · exact thm31_pow_le_componentSymbolic (K := K) r s q
  · exact thm31_componentSymbolic_le_pow (K := K) r s hr hs q

/-- Componentwise Simis equality; the intrinsic version is conditional on Eq. (2). -/
theorem thm31_componentSimis (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    ComponentSimis (thm31_I (K := K) r s) (thm31_component (K := K) r s) := by
  intro q hq
  exact thm31_pow_eq_componentSymbolic (K := K) r s hr hs q

/-- Witnesses showing that no component of (5) contains the others' intersection. -/
noncomputable def thm31_witness (r s : ℕ) : Fin 4 → thm31_var →₀ ℕ := fun j ↦
  match j.val with
  | 0 => Finsupp.single thm31_c 1 + Finsupp.single thm31_d 1 +
      Finsupp.single thm31_z (s - 1)
  | 1 => Finsupp.single thm31_b 1 + Finsupp.single thm31_c 1
  | 2 => Finsupp.single thm31_a 1 + Finsupp.single thm31_d 1
  | _ => Finsupp.single thm31_a 1 + Finsupp.single thm31_b 1 +
      Finsupp.single thm31_z (r - 1)

/-- Each witness lies in every component other than the one it excludes. -/
theorem thm31_witness_mem_other (r s : ℕ) (j k : Fin 4) (hkj : k ≠ j) :
    (monomial (thm31_witness r s j) (1 : K) : MvPolynomial thm31_var K) ∈
      thm31_component (K := K) r s k := by
  rw [thm31_component, monomial_mem_purePower]
  fin_cases j <;> fin_cases k <;>
    simp [thm31_witness, thm31_support, thm31_componentExp,
      thm31_a, thm31_b, thm31_c, thm31_d, thm31_z] at hkj ⊢

/-- Each witness is outside its corresponding component. -/
theorem thm31_witness_not_mem (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (j : Fin 4) :
    (monomial (thm31_witness r s j) (1 : K) : MvPolynomial thm31_var K) ∉
      thm31_component (K := K) r s j := by
  rw [thm31_component, monomial_mem_purePower]
  fin_cases j <;>
    simp [thm31_witness, thm31_support, thm31_componentExp,
      thm31_a, thm31_b, thm31_c, thm31_d, thm31_z] <;>
    omega

/-- The display (5) is an irredundant decomposition. -/
theorem thm31_isIrredundantDecomp (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    IsIrredundantDecomp (thm31_I (K := K) r s) thm31_support (thm31_componentExp r s) := by
  constructor
  · rw [HasComponents]
    simpa [componentSymbolic, thm31_component] using
      (thm31_pow_eq_componentSymbolic (K := K) r s hr hs 1)
  · intro j hle
    apply thm31_witness_not_mem (K := K) r s hr hs j
    apply hle
    rw [decompOmit]
    apply Ideal.mem_iInf.mpr
    rintro ⟨k, hkj⟩
    exact thm31_witness_mem_other (K := K) r s j k hkj

/-- The four component supports are pairwise incomparable. -/
theorem thm31_supportsAntichain (r s : ℕ) :
    SupportsAntichain thm31_support (thm31_componentExp r s) := by
  intro j k
  fin_cases j <;> fin_cases k <;> decide

/-- Conditional intrinsic Simis conclusion from the standard formula Eq. (2). -/
theorem thm31_isSimis_of_hasStdSymbolicFormula (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hsym : HasStdSymbolicFormula (thm31_I (K := K) r s) (thm31_component (K := K) r s)) :
    IsSimis (thm31_I (K := K) r s) := by
  exact (isSimis_iff_componentSimis_of_stdSymbolic hsym).mpr
    (thm31_componentSimis (K := K) r s hr hs)

/-- Conditional full MPV hypotheses, with Eq. (2) made explicit. -/
theorem thm31_MPVHypotheses_of_hasStdSymbolicFormula (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hsym : HasStdSymbolicFormula (thm31_I (K := K) r s) (thm31_component (K := K) r s)) :
    MPVHypotheses (thm31_I (K := K) r s) thm31_support (thm31_componentExp r s) := by
  exact ⟨thm31_isIrredundantDecomp (K := K) r s hr hs,
    thm31_supportsAntichain r s,
    thm31_isSimis_of_hasStdSymbolicFormula (K := K) r s hr hs hsym⟩

/-- The four generator supports of \(M\). -/
def thm31_Msupports : Set (Finset thm31_var) :=
  {{thm31_a, thm31_c}, {thm31_b, thm31_d},
   {thm31_a, thm31_b, thm31_z}, {thm31_c, thm31_d, thm31_z}}

@[simp] theorem thm31_char_AC :
    characteristicExp ({thm31_a, thm31_c} : Finset thm31_var) = thm31_gAC := by
  ext i
  fin_cases i <;>
    simp [characteristicExp, thm31_gAC,
      thm31_a, thm31_b, thm31_c, thm31_d, thm31_z]

@[simp] theorem thm31_char_BD :
    characteristicExp ({thm31_b, thm31_d} : Finset thm31_var) = thm31_gBD := by
  ext i
  fin_cases i <;>
    simp [characteristicExp, thm31_gBD,
      thm31_a, thm31_b, thm31_c, thm31_d, thm31_z]

@[simp] theorem thm31_char_ABZ :
    characteristicExp ({thm31_a, thm31_b, thm31_z} : Finset thm31_var) = thm31_gABZ 1 := by
  ext i
  fin_cases i <;>
    simp [characteristicExp, thm31_gABZ,
      thm31_a, thm31_b, thm31_c, thm31_d, thm31_z]

@[simp] theorem thm31_char_CDZ :
    characteristicExp ({thm31_c, thm31_d, thm31_z} : Finset thm31_var) = thm31_gCDZ 1 := by
  ext i
  fin_cases i <;>
    simp [characteristicExp, thm31_gCDZ,
      thm31_a, thm31_b, thm31_c, thm31_d, thm31_z]

/-- \(M\) is represented by squarefree monomial generators. -/
theorem thm31_M_isSquarefree : IsSquarefreeMonomialIdeal (thm31_M (K := K)) := by
  refine ⟨thm31_Msupports, ?_⟩
  unfold thm31_M thm31_I
  congr 1
  ext e
  constructor
  · intro he
    simp only [thm31_gens, Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl
    · refine ⟨{thm31_a, thm31_c}, by simp [thm31_Msupports], ?_⟩
      change characteristicExp ({thm31_a, thm31_c} : Finset thm31_var) = thm31_gAC
      exact thm31_char_AC
    · refine ⟨{thm31_b, thm31_d}, by simp [thm31_Msupports], ?_⟩
      change characteristicExp ({thm31_b, thm31_d} : Finset thm31_var) = thm31_gBD
      exact thm31_char_BD
    · refine ⟨{thm31_a, thm31_b, thm31_z}, by simp [thm31_Msupports], ?_⟩
      change characteristicExp ({thm31_a, thm31_b, thm31_z} : Finset thm31_var) =
        thm31_gABZ 1
      exact thm31_char_ABZ
    · refine ⟨{thm31_c, thm31_d, thm31_z}, by simp [thm31_Msupports], ?_⟩
      change characteristicExp ({thm31_c, thm31_d, thm31_z} : Finset thm31_var) =
        thm31_gCDZ 1
      exact thm31_char_CDZ
  · rintro ⟨A, hA, hAe⟩
    simp only [thm31_Msupports, Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl | rfl | rfl
    · simp only [thm31_gens, Set.mem_insert_iff, Set.mem_singleton_iff]
      left
      change characteristicExp ({thm31_a, thm31_c} : Finset thm31_var) = e at hAe
      rw [thm31_char_AC] at hAe
      exact hAe.symm
    · simp only [thm31_gens, Set.mem_insert_iff, Set.mem_singleton_iff]
      right; left
      change characteristicExp ({thm31_b, thm31_d} : Finset thm31_var) = e at hAe
      rw [thm31_char_BD] at hAe
      exact hAe.symm
    · simp only [thm31_gens, Set.mem_insert_iff, Set.mem_singleton_iff]
      right; right; left
      change characteristicExp ({thm31_a, thm31_b, thm31_z} : Finset thm31_var) = e at hAe
      rw [thm31_char_ABZ] at hAe
      exact hAe.symm
    · simp only [thm31_gens, Set.mem_insert_iff, Set.mem_singleton_iff]
      right; right; right
      change characteristicExp ({thm31_c, thm31_d, thm31_z} : Finset thm31_var) = e at hAe
      rw [thm31_char_CDZ] at hAe
      exact hAe.symm

theorem thm31_weight_pos (t : ℕ) (ht : 0 < t) : ∀ i, 0 < thm31_weight t i := by
  intro i
  fin_cases i <;> simp [thm31_weight, ht]

@[simp] theorem thm31_diagWeight_gAC (t : ℕ) :
    diagExp (thm31_weight t) thm31_gAC = thm31_gAC := by
  ext i
  fin_cases i <;>
    simp [diagExp, thm31_weight, thm31_gAC,
      thm31_a, thm31_b, thm31_c, thm31_d, thm31_z]

@[simp] theorem thm31_diagWeight_gBD (t : ℕ) :
    diagExp (thm31_weight t) thm31_gBD = thm31_gBD := by
  ext i
  fin_cases i <;>
    simp [diagExp, thm31_weight, thm31_gBD,
      thm31_a, thm31_b, thm31_c, thm31_d, thm31_z]

@[simp] theorem thm31_diagWeight_gABZ (t : ℕ) :
    diagExp (thm31_weight t) (thm31_gABZ 1) = thm31_gABZ t := by
  ext i
  fin_cases i <;>
    simp [diagExp, thm31_weight, thm31_gABZ,
      thm31_a, thm31_b, thm31_c, thm31_d, thm31_z]

@[simp] theorem thm31_diagWeight_gCDZ (t : ℕ) :
    diagExp (thm31_weight t) (thm31_gCDZ 1) = thm31_gCDZ t := by
  ext i
  fin_cases i <;>
    simp [diagExp, thm31_weight, thm31_gCDZ,
      thm31_a, thm31_b, thm31_c, thm31_d, thm31_z]

/-- The displayed squarefree root produces \(I_{t,t}\) under the forced weight. -/
theorem thm31_diagonal_M (t : ℕ) :
    diagonal (K := K) (thm31_weight t) (thm31_M (K := K)) = thm31_I (K := K) t t := by
  rw [thm31_M, thm31_I, thm31_I, diagonal_monomialIdeal]
  congr 1
  ext e
  simp [thm31_gens, eq_comm]

/-- \(abz^r\) is a minimal generator of \(I_{r,s}\). -/
theorem thm31_gABZ_minimal (r s : ℕ) {u : thm31_var →₀ ℕ}
    (hu : (monomial u (1 : K) : MvPolynomial thm31_var K) ∈ thm31_I (K := K) r s)
    (hule : u ≤ thm31_gABZ r) : u = thm31_gABZ r := by
  rw [thm31_I] at hu
  rcases monomial_mem_monomialIdeal.mp hu with ⟨g, hg, hgu⟩
  simp only [thm31_gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exfalso
    have h1 := hgu thm31_c
    have h2 := hule thm31_c
    simp [thm31_gAC, thm31_gABZ] at h1 h2
    omega
  · exfalso
    have h1 := hgu thm31_d
    have h2 := hule thm31_d
    simp [thm31_gBD, thm31_gABZ] at h1 h2
    omega
  · exact le_antisymm hule hgu
  · exfalso
    have h1 := hgu thm31_c
    have h2 := hule thm31_c
    simp [thm31_gCDZ, thm31_gABZ] at h1 h2
    omega

/-- \(cdz^s\) is a minimal generator of \(I_{r,s}\). -/
theorem thm31_gCDZ_minimal (r s : ℕ) {u : thm31_var →₀ ℕ}
    (hu : (monomial u (1 : K) : MvPolynomial thm31_var K) ∈ thm31_I (K := K) r s)
    (hule : u ≤ thm31_gCDZ s) : u = thm31_gCDZ s := by
  rw [thm31_I] at hu
  rcases monomial_mem_monomialIdeal.mp hu with ⟨g, hg, hgu⟩
  simp only [thm31_gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exfalso
    have h1 := hgu thm31_a
    have h2 := hule thm31_a
    simp [thm31_gAC, thm31_gCDZ] at h1 h2
    omega
  · exfalso
    have h1 := hgu thm31_b
    have h2 := hule thm31_b
    simp [thm31_gBD, thm31_gCDZ] at h1 h2
    omega
  · exfalso
    have h1 := hgu thm31_a
    have h2 := hule thm31_a
    simp [thm31_gABZ, thm31_gCDZ] at h1 h2
    omega
  · exact le_antisymm hule hgu

/-- A squarefree diagonal representation forces \(d_z\) from a minimal generator
containing \(z\).  This is the specialization of \(C_z=D_z\) from Proposition 2.1. -/
theorem thm31_forced_weight
    {I J : Ideal (MvPolynomial thm31_var K)} {d : thm31_var → ℕ} {g : thm31_var →₀ ℕ}
    (hJs : IsSquarefreeMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hdiag : diagonal (K := K) d J = I)
    (hg : (monomial g (1 : K) : MvPolynomial thm31_var K) ∈ I)
    (hmin : ∀ u, (monomial u (1 : K) : MvPolynomial thm31_var K) ∈ I → u ≤ g → u = g)
    (hgz : 0 < g thm31_z) : d thm31_z = g thm31_z := by
  classical
  rcases hJs with ⟨H, hJ⟩
  have hJmono : IsMonomialIdeal J := ⟨characteristicExp '' H, hJ⟩
  have hgDiag : (monomial g (1 : K) : MvPolynomial thm31_var K) ∈ diagonal (K := K) d J := by
    simpa [hdiag] using hg
  have hfloor : (monomial (floorDiv d g) (1 : K) : MvPolynomial thm31_var K) ∈ J :=
    (monomial_mem_diagonal (K := K) hJmono hd (e := g)).mp hgDiag
  rw [hJ, monomial_mem_monomialIdeal] at hfloor
  rcases hfloor with ⟨u, ⟨A, hAH, hu⟩, hule⟩
  subst u
  have huJ : (monomial (characteristicExp A) (1 : K) : MvPolynomial thm31_var K) ∈ J := by
    rw [hJ]
    exact monomial_mem_monomialIdeal.mpr
      ⟨characteristicExp A, ⟨A, hAH, rfl⟩, le_rfl⟩
  have huDiag : (monomial (diagExp d (characteristicExp A)) (1 : K) :
      MvPolynomial thm31_var K) ∈ diagonal (K := K) d J := by
    simpa [diagonal, diagHom_monomial] using
      (Ideal.mem_map_of_mem (diagHom (K := K) d) huJ)
  have huI : (monomial (diagExp d (characteristicExp A)) (1 : K) :
      MvPolynomial thm31_var K) ∈ I := by
    simpa [hdiag] using huDiag
  have huLe : diagExp d (characteristicExp A) ≤ g :=
    (diagExp_le_iff_floor hd (characteristicExp A) g).mpr hule
  have heq : diagExp d (characteristicExp A) = g := hmin _ huI huLe
  have hzEq := congrArg (fun v : thm31_var →₀ ℕ ↦ v thm31_z) heq
  by_cases hzA : thm31_z ∈ A
  · simpa [diagExp_apply, characteristicExp_apply, hzA] using hzEq
  · have hz0 : g thm31_z = 0 := by
      simpa [diagExp_apply, characteristicExp_apply, hzA] using hzEq.symm
    exact (Nat.ne_of_gt hgz hz0).elim

/-- Squarefree diagonal representability holds precisely when \(r=s\). -/
theorem thm31_hasSqRoot_iff (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    HasSqRoot (thm31_I (K := K) r s) ↔ r = s := by
  constructor
  · rintro ⟨J, d, hJs, hd, hdiag⟩
    have hzR : d thm31_z = r := by
      simpa [thm31_gABZ] using
        (thm31_forced_weight (K := K) hJs hd hdiag
          (thm31_gABZ_mem_I (K := K) r s)
          (fun u hu hule ↦ thm31_gABZ_minimal (K := K) r s hu hule)
          (by simpa [thm31_gABZ] using hr))
    have hzS : d thm31_z = s := by
      simpa [thm31_gCDZ] using
        (thm31_forced_weight (K := K) hJs hd hdiag
          (thm31_gCDZ_mem_I (K := K) r s)
          (fun u hu hule ↦ thm31_gCDZ_minimal (K := K) r s hu hule)
          (by simpa [thm31_gCDZ] using hs))
    exact hzR.symm.trans hzS
  · intro hrs
    subst s
    exact ⟨thm31_M (K := K), thm31_weight r, thm31_M_isSquarefree (K := K),
      thm31_weight_pos r hr, thm31_diagonal_M (K := K) r⟩

/-- Under Eq. (2) for \(M\), the squarefree root is intrinsically Simis. -/
theorem thm31_M_isSimis_of_hasStdSymbolicFormula
    (hsym : HasStdSymbolicFormula (thm31_M (K := K))
      (thm31_component (K := K) 1 1)) :
    IsSimis (thm31_M (K := K)) := by
  apply (isSimis_iff_componentSimis_of_stdSymbolic hsym).mpr
  intro q hq
  simpa [thm31_M] using
    (thm31_pow_eq_componentSymbolic (K := K) 1 1 (by omega) (by omega) q)

/-- Conditional MPV conclusion, using Eq. (2) for the squarefree root. -/
theorem thm31_MPVConc_iff_of_stdM (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hsymM : HasStdSymbolicFormula (thm31_M (K := K))
      (thm31_component (K := K) 1 1)) :
    MPVConc (thm31_I (K := K) r s) ↔ r = s := by
  constructor
  · rintro ⟨J, d, hJs, _hSimis, hd, hdiag⟩
    exact (thm31_hasSqRoot_iff (K := K) r s hr hs).mp ⟨J, d, hJs, hd, hdiag⟩
  · intro hrs
    subst s
    exact ⟨thm31_M (K := K), thm31_weight r, thm31_M_isSquarefree (K := K),
      thm31_M_isSimis_of_hasStdSymbolicFormula (K := K) hsymM,
      thm31_weight_pos r hr, thm31_diagonal_M (K := K) r⟩

/-- \(abz\) divides \(abz^r\) when \(r\) is positive. -/
theorem thm31_gABZ_one_le (r : ℕ) (hr : 0 < r) : thm31_gABZ 1 ≤ thm31_gABZ r := by
  have hr' : 1 ≤ r := by omega
  rw [Finsupp.le_def]
  intro i
  fin_cases i <;>
    simp [thm31_gABZ, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z, hr']

/-- \(cdz\) divides \(cdz^s\) when \(s\) is positive. -/
theorem thm31_gCDZ_one_le (s : ℕ) (hs : 0 < s) : thm31_gCDZ 1 ≤ thm31_gCDZ s := by
  have hs' : 1 ≤ s := by omega
  rw [Finsupp.le_def]
  intro i
  fin_cases i <;>
    simp [thm31_gCDZ, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z, hs']

/-- The \(r\)th power of \(abz\) is divisible by \(abz^r\). -/
theorem thm31_gABZ_le_power (r : ℕ) (hr : 0 < r) :
    thm31_gABZ r ≤ r • thm31_gABZ 1 := by
  have hr' : 1 ≤ r := by omega
  rw [Finsupp.le_def]
  intro i
  fin_cases i <;>
    simp [thm31_gABZ, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z, hr']

/-- The \(s\)th power of \(cdz\) is divisible by \(cdz^s\). -/
theorem thm31_gCDZ_le_power (s : ℕ) (hs : 0 < s) :
    thm31_gCDZ s ≤ s • thm31_gCDZ 1 := by
  have hs' : 1 ≤ s := by omega
  rw [Finsupp.le_def]
  intro i
  fin_cases i <;>
    simp [thm31_gCDZ, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z, hs']

/-- \(I_{r,s}\subseteq M\), so the radical is at most \(M\) if \(M\) is radical. -/
theorem thm31_I_le_M (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    thm31_I (K := K) r s ≤ thm31_M (K := K) := by
  rw [thm31_M, thm31_I]
  apply monomialIdeal_le_iff.mpr
  intro e he
  rcases he with ⟨g, hg, hge⟩
  simp only [thm31_gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact ⟨thm31_gAC, by simp [thm31_gens], hge⟩
  · exact ⟨thm31_gBD, by simp [thm31_gens], hge⟩
  · exact ⟨thm31_gABZ 1, by simp [thm31_gens],
      le_trans (thm31_gABZ_one_le r hr) hge⟩
  · exact ⟨thm31_gCDZ 1, by simp [thm31_gens],
      le_trans (thm31_gCDZ_one_le s hs) hge⟩

/-- \(M\subseteq\sqrt{I_{r,s}}\): each squarefree generator has a power in \(I_{r,s}\). -/
theorem thm31_M_le_radical_I (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    thm31_M (K := K) ≤ (thm31_I (K := K) r s).radical := by
  rw [thm31_M, thm31_I, monomialIdeal, Ideal.span_le]
  rintro y ⟨g, hg, rfl⟩
  simp only [thm31_gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact Ideal.le_radical (thm31_gAC_mem_I (K := K) r s)
  · exact Ideal.le_radical (thm31_gBD_mem_I (K := K) r s)
  · apply Ideal.mem_radical_iff.mpr
    refine ⟨r, ?_⟩
    have hpow : (monomial (r • thm31_gABZ 1) (1 : K) : MvPolynomial thm31_var K) ∈
        thm31_I (K := K) r s ^ 1 :=
      thm31_mon_mem_pow_of_generator (I := thm31_I (K := K) r s) (q := 1)
        (g := thm31_gABZ r) (e := r • thm31_gABZ 1)
        (thm31_gABZ_mem_I (K := K) r s) (by simpa using thm31_gABZ_le_power r hr)
    simpa [MvPolynomial.monomial_pow] using hpow
  · apply Ideal.mem_radical_iff.mpr
    refine ⟨s, ?_⟩
    have hpow : (monomial (s • thm31_gCDZ 1) (1 : K) : MvPolynomial thm31_var K) ∈
        thm31_I (K := K) r s ^ 1 :=
      thm31_mon_mem_pow_of_generator (I := thm31_I (K := K) r s) (q := 1)
        (g := thm31_gCDZ s) (e := s • thm31_gCDZ 1)
        (thm31_gCDZ_mem_I (K := K) r s) (by simpa using thm31_gCDZ_le_power s hs)
    simpa [MvPolynomial.monomial_pow] using hpow

/-- Conditional radicality of \(M\), from explicitly assuming its displayed components are prime. -/
theorem thm31_M_isRadical_of_component_primes
    (hprime : ∀ j, (thm31_component (K := K) 1 1 j).IsPrime) :
    (thm31_M (K := K)).IsRadical := by
  have hdecomp : thm31_M (K := K) =
      ⨅ j, (purePower (K := K) (thm31_support j) (thm31_componentExp 1 1 j) :
        Ideal (MvPolynomial thm31_var K)) := by
    simpa [thm31_M, HasComponents] using
      (thm31_isIrredundantDecomp (K := K) 1 1 (by omega) (by omega)).1
  rw [hdecomp]
  apply Ideal.isRadical_iInf
  intro j
  change (thm31_component (K := K) 1 1 j).IsRadical
  exact (hprime j).isRadical

/-- Conditional radical formula, with the primality input kept explicit. -/
theorem thm31_radical_eq_M_of_component_primes (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hprime : ∀ j, (thm31_component (K := K) 1 1 j).IsPrime) :
    (thm31_I (K := K) r s).radical = thm31_M (K := K) := by
  apply le_antisymm
  · calc
      (thm31_I (K := K) r s).radical ≤ (thm31_M (K := K)).radical :=
        Ideal.radical_mono (thm31_I_le_M (K := K) r s hr hs)
      _ = thm31_M (K := K) := Ideal.radical_eq_iff.mpr
        (thm31_M_isRadical_of_component_primes (K := K) hprime)
  · exact thm31_M_le_radical_I (K := K) r s hr hs

/-- \(ac\) is a minimal generator of \(I_{r,s}\). -/
theorem thm31_gAC_minimal (r s : ℕ) {u : thm31_var →₀ ℕ}
    (hu : (monomial u (1 : K) : MvPolynomial thm31_var K) ∈ thm31_I (K := K) r s)
    (hule : u ≤ thm31_gAC) : u = thm31_gAC := by
  rw [thm31_I] at hu
  rcases monomial_mem_monomialIdeal.mp hu with ⟨g, hg, hgu⟩
  simp only [thm31_gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact le_antisymm hule hgu
  · exfalso
    have h1 := hgu thm31_b
    have h2 := hule thm31_b
    simp [thm31_gBD, thm31_gAC] at h1 h2
    omega
  · exfalso
    have h1 := hgu thm31_b
    have h2 := hule thm31_b
    simp [thm31_gABZ, thm31_gAC] at h1 h2
    omega
  · exfalso
    have h1 := hgu thm31_d
    have h2 := hule thm31_d
    simp [thm31_gCDZ, thm31_gAC] at h1 h2
    omega

/-- \(bd\) is a minimal generator of \(I_{r,s}\). -/
theorem thm31_gBD_minimal (r s : ℕ) {u : thm31_var →₀ ℕ}
    (hu : (monomial u (1 : K) : MvPolynomial thm31_var K) ∈ thm31_I (K := K) r s)
    (hule : u ≤ thm31_gBD) : u = thm31_gBD := by
  rw [thm31_I] at hu
  rcases monomial_mem_monomialIdeal.mp hu with ⟨g, hg, hgu⟩
  simp only [thm31_gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exfalso
    have h1 := hgu thm31_a
    have h2 := hule thm31_a
    simp [thm31_gAC, thm31_gBD] at h1 h2
    omega
  · exact le_antisymm hule hgu
  · exfalso
    have h1 := hgu thm31_a
    have h2 := hule thm31_a
    simp [thm31_gABZ, thm31_gBD] at h1 h2
    omega
  · exfalso
    have h1 := hgu thm31_c
    have h2 := hule thm31_c
    simp [thm31_gCDZ, thm31_gBD] at h1 h2
    omega

/-- The displayed exponent vectors are exactly the minimal monomial generators. -/
theorem thm31_minGens (r s : ℕ) :
    minGens (thm31_I (K := K) r s) = thm31_gens r s := by
  ext e
  constructor
  · intro he
    rcases mem_minGens.mp he with ⟨heI, hmin⟩
    rw [thm31_I] at heI
    rcases monomial_mem_monomialIdeal.mp heI with ⟨g, hg, hge⟩
    have hgm : (monomial g (1 : K) : MvPolynomial thm31_var K) ∈ thm31_I (K := K) r s := by
      rw [thm31_I]
      exact monomial_mem_monomialIdeal.mpr ⟨g, hg, le_rfl⟩
    have h_eq : g = e := hmin g hgm hge
    simpa [h_eq] using hg
  · intro he
    rw [mem_minGens]
    simp only [thm31_gens, Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl
    · refine ⟨thm31_gAC_mem_I (K := K) r s, ?_⟩
      intro u hu hule
      exact thm31_gAC_minimal (K := K) r s hu hule
    · refine ⟨thm31_gBD_mem_I (K := K) r s, ?_⟩
      intro u hu hule
      exact thm31_gBD_minimal (K := K) r s hu hule
    · refine ⟨thm31_gABZ_mem_I (K := K) r s, ?_⟩
      intro u hu hule
      exact thm31_gABZ_minimal (K := K) r s hu hule
    · refine ⟨thm31_gCDZ_mem_I (K := K) r s, ?_⟩
      intro u hu hule
      exact thm31_gCDZ_minimal (K := K) r s hu hule

@[simp] theorem thm31_support_gAC :
    thm31_gAC.support = ({thm31_a, thm31_c} : Finset thm31_var) := by
  ext i
  fin_cases i <;>
    simp [thm31_gAC, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z]

@[simp] theorem thm31_support_gBD :
    thm31_gBD.support = ({thm31_b, thm31_d} : Finset thm31_var) := by
  ext i
  fin_cases i <;>
    simp [thm31_gBD, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z]

/-- The support of \(abz^r\), for a positive exponent. -/
theorem thm31_support_gABZ (r : ℕ) (hr : 0 < r) :
    (thm31_gABZ r).support = ({thm31_a, thm31_b, thm31_z} : Finset thm31_var) := by
  ext i
  fin_cases i <;>
    simp [thm31_gABZ, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z]
  omega

/-- The support of \(cdz^s\), for a positive exponent. -/
theorem thm31_support_gCDZ (s : ℕ) (hs : 0 < s) :
    (thm31_gCDZ s).support = ({thm31_c, thm31_d, thm31_z} : Finset thm31_var) := by
  ext i
  fin_cases i <;>
    simp [thm31_gCDZ, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z]
  omega

/-- The generator-support complex of \(I_{r,s}\) is the displayed four-edge clutter. -/
theorem thm31_supportComplex_I (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    supportComplex (thm31_I (K := K) r s) = thm31_Msupports := by
  ext A
  rw [supportComplex]
  constructor
  · rintro ⟨e, he, hA⟩
    rw [thm31_minGens (K := K) r s] at he
    simp only [thm31_gens, Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl
    · rw [← hA]
      simp [thm31_Msupports]
    · rw [← hA]
      simp [thm31_Msupports]
    · rw [← hA]
      simp [thm31_Msupports, thm31_support_gABZ r hr]
    · rw [← hA]
      simp [thm31_Msupports, thm31_support_gCDZ s hs]
  · intro hA
    simp only [thm31_Msupports, Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl | rfl | rfl
    · exact ⟨thm31_gAC, by rw [thm31_minGens]; simp [thm31_gens], thm31_support_gAC⟩
    · exact ⟨thm31_gBD, by rw [thm31_minGens]; simp [thm31_gens], thm31_support_gBD⟩
    · exact ⟨thm31_gABZ r, by rw [thm31_minGens]; simp [thm31_gens],
        thm31_support_gABZ r hr⟩
    · exact ⟨thm31_gCDZ s, by rw [thm31_minGens]; simp [thm31_gens],
        thm31_support_gCDZ s hs⟩

/-- The generator-support complex of \(M\). -/
theorem thm31_supportComplex_M :
    supportComplex (thm31_M (K := K)) = thm31_Msupports := by
  simpa [thm31_M] using
    (thm31_supportComplex_I (K := K) 1 1 (by omega) (by omega))

/-- At weight one, every displayed component is the corresponding variable prime. -/
theorem thm31_component_eq_primeOf_one_one (j : Fin 4) :
    thm31_component (K := K) 1 1 j = primeOf (K := K) (thm31_support j) := by
  fin_cases j <;>
    simp [thm31_component, primeOf, purePower, thm31_support, thm31_componentExp,
      thm31_a, thm31_b, thm31_c, thm31_d, thm31_z]

/-- Every displayed component at weight one is prime. -/
theorem thm31_component_isPrime_one_one (j : Fin 4) :
    (thm31_component (K := K) 1 1 j).IsPrime := by
  rw [thm31_component_eq_primeOf_one_one]
  exact primeOf_isPrime _

/-- The squarefree ideal \(M\) is radical, using the already proved primality theorem. -/
theorem thm31_M_isRadical : (thm31_M (K := K)).IsRadical :=
  thm31_M_isRadical_of_component_primes (K := K)
    (thm31_component_isPrime_one_one (K := K))

/-- The radical formula \(\sqrt{I_{r,s}}=M\) for positive \(r,s\), now unconditionally. -/
theorem thm31_radical_eq_M (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    (thm31_I (K := K) r s).radical = thm31_M (K := K) :=
  thm31_radical_eq_M_of_component_primes (K := K) r s hr hs
    (thm31_component_isPrime_one_one (K := K))

/-- Support preservation \(F(I_{r,s})=F(\sqrt{I_{r,s}})=F(M)\). -/
theorem thm31_supportPreserving (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    SupportPreserving (thm31_I (K := K) r s) := by
  unfold SupportPreserving
  rw [thm31_radical_eq_M (K := K) r s hr hs]
  exact (thm31_supportComplex_I (K := K) r s hr hs).trans
    (thm31_supportComplex_M (K := K)).symm

/-- A squarefree diagonal representation forces a used weight from any minimal generator.
This is the specialization of \(C_i=D_i\) from Proposition 2.1 at an arbitrary variable. -/
theorem thm31_forced_weight_at
    {I J : Ideal (MvPolynomial thm31_var K)} {d : thm31_var → ℕ} {g : thm31_var →₀ ℕ}
    {i : thm31_var}
    (hJs : IsSquarefreeMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hdiag : diagonal (K := K) d J = I)
    (hg : (monomial g (1 : K) : MvPolynomial thm31_var K) ∈ I)
    (hmin : ∀ u, (monomial u (1 : K) : MvPolynomial thm31_var K) ∈ I → u ≤ g → u = g)
    (hgi : 0 < g i) : d i = g i := by
  classical
  rcases hJs with ⟨H, hJ⟩
  have hJmono : IsMonomialIdeal J := ⟨characteristicExp '' H, hJ⟩
  have hgDiag : (monomial g (1 : K) : MvPolynomial thm31_var K) ∈ diagonal (K := K) d J := by
    simpa [hdiag] using hg
  have hfloor : (monomial (floorDiv d g) (1 : K) : MvPolynomial thm31_var K) ∈ J :=
    (monomial_mem_diagonal (K := K) hJmono hd (e := g)).mp hgDiag
  rw [hJ, monomial_mem_monomialIdeal] at hfloor
  rcases hfloor with ⟨u, ⟨A, hAH, hu⟩, hule⟩
  subst u
  have huJ : (monomial (characteristicExp A) (1 : K) : MvPolynomial thm31_var K) ∈ J := by
    rw [hJ]
    exact monomial_mem_monomialIdeal.mpr
      ⟨characteristicExp A, ⟨A, hAH, rfl⟩, le_rfl⟩
  have huDiag : (monomial (diagExp d (characteristicExp A)) (1 : K) :
      MvPolynomial thm31_var K) ∈ diagonal (K := K) d J := by
    simpa [diagonal, diagHom_monomial] using
      (Ideal.mem_map_of_mem (diagHom (K := K) d) huJ)
  have huI : (monomial (diagExp d (characteristicExp A)) (1 : K) :
      MvPolynomial thm31_var K) ∈ I := by
    simpa [hdiag] using huDiag
  have huLe : diagExp d (characteristicExp A) ≤ g :=
    (diagExp_le_iff_floor hd (characteristicExp A) g).mpr hule
  have heq : diagExp d (characteristicExp A) = g := hmin _ huI huLe
  have hiEq := congrArg (fun v : thm31_var →₀ ℕ ↦ v i) heq
  by_cases hiA : i ∈ A
  · simpa [diagExp_apply, characteristicExp_apply, hiA] using hiEq
  · have hi0 : g i = 0 := by
      simpa [diagExp_apply, characteristicExp_apply, hiA] using hiEq.symm
    exact (Nat.ne_of_gt hgi hi0).elim

/-- Floor division is monotone in the exponent vector. -/
theorem thm31_floorDiv_mono {d : thm31_var → ℕ} {v w : thm31_var →₀ ℕ} (h : v ≤ w) :
    floorDiv d v ≤ floorDiv d w := by
  rw [Finsupp.le_def] at h ⊢
  intro i
  exact Nat.div_le_div_right (h i)

/-- Floor division undoes a positive diagonal weighting. -/
theorem thm31_floorDiv_diagExp (d : thm31_var → ℕ) (hd : ∀ i, 0 < d i)
    (v : thm31_var →₀ ℕ) : floorDiv d (diagExp d v) = v := by
  ext i
  simp [floorDiv_apply, diagExp_apply, hd i]

/-- For \(r=s=t\), the squarefree diagonal root and its positive weight vector are unique. -/
theorem thm31_root_unique (t : ℕ) (ht : 0 < t)
    {J : Ideal (MvPolynomial thm31_var K)} {d : thm31_var → ℕ}
    (hJs : IsSquarefreeMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hdiag : diagonal (K := K) d J = thm31_I (K := K) t t) :
    J = thm31_M (K := K) ∧ d = thm31_weight t := by
  classical
  rcases hJs with ⟨H, hJ⟩
  have hJs' : IsSquarefreeMonomialIdeal J := ⟨H, hJ⟩
  have hJmono : IsMonomialIdeal J := ⟨characteristicExp '' H, hJ⟩
  have hda : d thm31_a = 1 := by
    simpa [thm31_gAC] using
      (thm31_forced_weight_at (K := K) (i := thm31_a) hJs' hd hdiag
        (thm31_gAC_mem_I (K := K) t t)
        (fun u hu hule ↦ thm31_gAC_minimal (K := K) t t hu hule)
        (by simp [thm31_gAC]))
  have hdc : d thm31_c = 1 := by
    simpa [thm31_gAC] using
      (thm31_forced_weight_at (K := K) (i := thm31_c) hJs' hd hdiag
        (thm31_gAC_mem_I (K := K) t t)
        (fun u hu hule ↦ thm31_gAC_minimal (K := K) t t hu hule)
        (by simp [thm31_gAC]))
  have hdb : d thm31_b = 1 := by
    simpa [thm31_gBD] using
      (thm31_forced_weight_at (K := K) (i := thm31_b) hJs' hd hdiag
        (thm31_gBD_mem_I (K := K) t t)
        (fun u hu hule ↦ thm31_gBD_minimal (K := K) t t hu hule)
        (by simp [thm31_gBD]))
  have hdd : d thm31_d = 1 := by
    simpa [thm31_gBD] using
      (thm31_forced_weight_at (K := K) (i := thm31_d) hJs' hd hdiag
        (thm31_gBD_mem_I (K := K) t t)
        (fun u hu hule ↦ thm31_gBD_minimal (K := K) t t hu hule)
        (by simp [thm31_gBD]))
  have hdz : d thm31_z = t := by
    simpa [thm31_gABZ] using
      (thm31_forced_weight_at (K := K) (i := thm31_z) hJs' hd hdiag
        (thm31_gABZ_mem_I (K := K) t t)
        (fun u hu hule ↦ thm31_gABZ_minimal (K := K) t t hu hule)
        (by simpa [thm31_gABZ] using ht))
  have hda0 : d (0 : thm31_var) = 1 := by simpa [thm31_a] using hda
  have hdb0 : d (1 : thm31_var) = 1 := by simpa [thm31_b] using hdb
  have hdc0 : d (2 : thm31_var) = 1 := by simpa [thm31_c] using hdc
  have hdd0 : d (3 : thm31_var) = 1 := by simpa [thm31_d] using hdd
  have hdz0 : d (4 : thm31_var) = t := by simpa [thm31_z] using hdz
  have hdvec : d = thm31_weight t := by
    funext i
    fin_cases i <;> simp [thm31_weight, hda0, hdb0, hdc0, hdd0, hdz0]
  have hflAC : floorDiv d thm31_gAC = thm31_gAC := by
    ext i
    fin_cases i <;>
      simp [floorDiv_apply, thm31_gAC, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z,
        hda0, hdc0]
  have hflBD : floorDiv d thm31_gBD = thm31_gBD := by
    ext i
    fin_cases i <;>
      simp [floorDiv_apply, thm31_gBD, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z,
        hdb0, hdd0]
  have hflABZ : floorDiv d (thm31_gABZ t) = thm31_gABZ 1 := by
    ext i
    fin_cases i <;>
      simp [floorDiv_apply, thm31_gABZ, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z,
        hda0, hdb0, hdz0, ht]
  have hflCDZ : floorDiv d (thm31_gCDZ t) = thm31_gCDZ 1 := by
    ext i
    fin_cases i <;>
      simp [floorDiv_apply, thm31_gCDZ, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z,
        hdc0, hdd0, hdz0, ht]
  have hcharAC : (monomial thm31_gAC (1 : K) : MvPolynomial thm31_var K) ∈ J := by
    have hmem : (monomial thm31_gAC (1 : K) : MvPolynomial thm31_var K) ∈
        diagonal (K := K) d J := by
      rw [hdiag]
      exact thm31_gAC_mem_I (K := K) t t
    have hfl := (monomial_mem_diagonal (K := K) hJmono hd (e := thm31_gAC)).mp hmem
    simpa [hflAC] using hfl
  have hcharBD : (monomial thm31_gBD (1 : K) : MvPolynomial thm31_var K) ∈ J := by
    have hmem : (monomial thm31_gBD (1 : K) : MvPolynomial thm31_var K) ∈
        diagonal (K := K) d J := by
      rw [hdiag]
      exact thm31_gBD_mem_I (K := K) t t
    have hfl := (monomial_mem_diagonal (K := K) hJmono hd (e := thm31_gBD)).mp hmem
    simpa [hflBD] using hfl
  have hcharABZ : (monomial (thm31_gABZ 1) (1 : K) : MvPolynomial thm31_var K) ∈ J := by
    have hmem : (monomial (thm31_gABZ t) (1 : K) : MvPolynomial thm31_var K) ∈
        diagonal (K := K) d J := by
      rw [hdiag]
      exact thm31_gABZ_mem_I (K := K) t t
    have hfl :=
      (monomial_mem_diagonal (K := K) hJmono hd (e := thm31_gABZ t)).mp hmem
    simpa [hflABZ] using hfl
  have hcharCDZ : (monomial (thm31_gCDZ 1) (1 : K) : MvPolynomial thm31_var K) ∈ J := by
    have hmem : (monomial (thm31_gCDZ t) (1 : K) : MvPolynomial thm31_var K) ∈
        diagonal (K := K) d J := by
      rw [hdiag]
      exact thm31_gCDZ_mem_I (K := K) t t
    have hfl :=
      (monomial_mem_diagonal (K := K) hJmono hd (e := thm31_gCDZ t)).mp hmem
    simpa [hflCDZ] using hfl
  refine ⟨?_, hdvec⟩
  apply le_antisymm
  · rw [hJ, thm31_M, thm31_I]
    apply monomialIdeal_le_iff.mpr
    rintro e ⟨u, ⟨A, hAH, hAu⟩, hue⟩
    subst u
    have hcharJ : (monomial (characteristicExp A) (1 : K) : MvPolynomial thm31_var K) ∈ J := by
      rw [hJ]
      exact monomial_mem_monomialIdeal.mpr
        ⟨characteristicExp A, ⟨A, hAH, rfl⟩, le_rfl⟩
    obtain ⟨v, hvMin, hvle⟩ := exists_minGens_le hcharJ
    rcases mem_minGens.mp hvMin with ⟨hvJ, hvmin⟩
    have hvee : v ≤ e := hvle.trans hue
    have hvDiag : (monomial (diagExp d v) (1 : K) : MvPolynomial thm31_var K) ∈
        diagonal (K := K) d J := by
      simpa [diagonal, diagHom_monomial] using
        (Ideal.mem_map_of_mem (diagHom (K := K) d) hvJ)
    have hvI : (monomial (diagExp d v) (1 : K) : MvPolynomial thm31_var K) ∈
        thm31_I (K := K) t t := by
      simpa [hdiag] using hvDiag
    rw [thm31_I, monomial_mem_monomialIdeal] at hvI
    rcases hvI with ⟨g, hg, hgle⟩
    have hgDiag : (monomial g (1 : K) : MvPolynomial thm31_var K) ∈
        diagonal (K := K) d J := by
      rw [hdiag, thm31_I]
      exact monomial_mem_monomialIdeal.mpr ⟨g, hg, le_rfl⟩
    have hgFloor : (monomial (floorDiv d g) (1 : K) : MvPolynomial thm31_var K) ∈ J :=
      (monomial_mem_diagonal (K := K) hJmono hd (e := g)).mp hgDiag
    have hfloorle : floorDiv d g ≤ v := by
      calc
        floorDiv d g ≤ floorDiv d (diagExp d v) := thm31_floorDiv_mono hgle
        _ = v := thm31_floorDiv_diagExp d hd v
    have heqv : floorDiv d g = v := hvmin _ hgFloor hfloorle
    simp only [thm31_gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · have hvEq : v = thm31_gAC := heqv.symm.trans hflAC
      exact ⟨thm31_gAC, by simp [thm31_gens], by simpa [hvEq] using hvee⟩
    · have hvEq : v = thm31_gBD := heqv.symm.trans hflBD
      exact ⟨thm31_gBD, by simp [thm31_gens], by simpa [hvEq] using hvee⟩
    · have hvEq : v = thm31_gABZ 1 := heqv.symm.trans hflABZ
      exact ⟨thm31_gABZ 1, by simp [thm31_gens], by simpa [hvEq] using hvee⟩
    · have hvEq : v = thm31_gCDZ 1 := heqv.symm.trans hflCDZ
      exact ⟨thm31_gCDZ 1, by simp [thm31_gens], by simpa [hvEq] using hvee⟩
  · rw [thm31_M, thm31_I, hJ]
    apply monomialIdeal_le_iff.mpr
    rintro e ⟨g, hg, hge⟩
    simp only [thm31_gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · have hc : (monomial thm31_gAC (1 : K) : MvPolynomial thm31_var K) ∈
          (monomialIdeal (K := K) (characteristicExp '' H)) := by
        simpa [hJ] using hcharAC
      rcases monomial_mem_monomialIdeal.mp hc with ⟨u, hu, hule⟩
      exact ⟨u, hu, hule.trans hge⟩
    · have hc : (monomial thm31_gBD (1 : K) : MvPolynomial thm31_var K) ∈
          (monomialIdeal (K := K) (characteristicExp '' H)) := by
        simpa [hJ] using hcharBD
      rcases monomial_mem_monomialIdeal.mp hc with ⟨u, hu, hule⟩
      exact ⟨u, hu, hule.trans hge⟩
    · have hc : (monomial (thm31_gABZ 1) (1 : K) : MvPolynomial thm31_var K) ∈
          (monomialIdeal (K := K) (characteristicExp '' H)) := by
        simpa [hJ] using hcharABZ
      rcases monomial_mem_monomialIdeal.mp hc with ⟨u, hu, hule⟩
      exact ⟨u, hu, hule.trans hge⟩
    · have hc : (monomial (thm31_gCDZ 1) (1 : K) : MvPolynomial thm31_var K) ∈
          (monomialIdeal (K := K) (characteristicExp '' H)) := by
        simpa [hJ] using hcharCDZ
      rcases monomial_mem_monomialIdeal.mp hc with ⟨u, hu, hule⟩
      exact ⟨u, hu, hule.trans hge⟩

/-- The radical of each displayed component (5) is its variable prime. -/
theorem thm31_component_radical (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (j : Fin 4) :
    (thm31_component (K := K) r s j).radical = primeOf (K := K) (thm31_support j) := by
  simpa [thm31_component] using
    (purePower_radical_eq_primeOf (K := K)
      (A := thm31_support j) (a := thm31_componentExp r s j)
      (fun i hi ↦ thm31_componentExp_pos r s hr hs j i hi))

/-- The component radicals are pairwise incomparable. -/
theorem thm31_component_radicals_antichain (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    ∀ j k, (thm31_component (K := K) r s j).radical ≤
      (thm31_component (K := K) r s k).radical → j = k := by
  intro j k hle
  rw [thm31_component_radical (K := K) r s hr hs j,
    thm31_component_radical (K := K) r s hr hs k] at hle
  exact thm31_supportsAntichain r s j k ((primeOf_le_iff_subset (K := K)).mp hle)

/-- The component radicals are pairwise distinct. -/
theorem thm31_component_radicals_injective (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    Function.Injective (fun j ↦ (thm31_component (K := K) r s j).radical) := by
  intro j k h
  have hle : (thm31_component (K := K) r s j).radical ≤
      (thm31_component (K := K) r s k).radical := le_of_eq h
  exact thm31_component_radicals_antichain (K := K) r s hr hs j k hle

/-- \(I_{r,s}\) is nonzero. -/
theorem thm31_I_ne_bot (r s : ℕ) : thm31_I (K := K) r s ≠ ⊥ := by
  intro hbot
  have hm := thm31_gAC_mem_I (K := K) r s
  rw [hbot] at hm
  have hz : (monomial thm31_gAC (1 : K) : MvPolynomial thm31_var K) = 0 :=
    Ideal.mem_bot.mp hm
  have hc := congrArg (fun p ↦ coeff thm31_gAC p) hz
  simp at hc

/-- \(I_{r,s}\) is a proper ideal. -/
theorem thm31_I_ne_top (r s : ℕ) : thm31_I (K := K) r s ≠ ⊤ := by
  intro htop
  have h1 : (1 : MvPolynomial thm31_var K) ∈ thm31_I (K := K) r s := by
    rw [htop]
    exact trivial
  have h0 : (monomial (0 : thm31_var →₀ ℕ) (1 : K) : MvPolynomial thm31_var K) ∈
      thm31_I (K := K) r s := by
    simpa using h1
  rw [thm31_I, monomial_mem_monomialIdeal] at h0
  rcases h0 with ⟨g, hg, hg0⟩
  simp only [thm31_gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · have ha := hg0 thm31_a
    simp [thm31_gAC] at ha
  · have hb := hg0 thm31_b
    simp [thm31_gBD] at hb
  · have ha := hg0 thm31_a
    simp [thm31_gABZ] at ha
  · have hc := hg0 thm31_c
    simp [thm31_gCDZ] at hc

/-- \(M\) is nonzero and proper. -/
theorem thm31_M_ne_bot : thm31_M (K := K) ≠ ⊥ := by
  simpa [thm31_M] using thm31_I_ne_bot (K := K) 1 1

theorem thm31_M_ne_top : thm31_M (K := K) ≠ ⊤ := by
  simpa [thm31_M] using thm31_I_ne_top (K := K) 1 1

/-- A variable prime with a nonempty support is nonzero. -/
theorem thm31_primeOf_ne_bot_of_mem {A : Finset thm31_var} {i : thm31_var} (hi : i ∈ A) :
    (primeOf (K := K) A : Ideal (MvPolynomial thm31_var K)) ≠ ⊥ := by
  intro h
  have hm : (monomial (Finsupp.single i (1 : ℕ)) (1 : K) : MvPolynomial thm31_var K) ∈
      primeOf (K := K) A := monomial_mem_primeOf.mpr ⟨i, hi, by simp⟩
  rw [h] at hm
  have hz := Ideal.mem_bot.mp hm
  have hc := congrArg (fun p ↦ coeff (Finsupp.single i (1 : ℕ)) p) hz
  simp at hc

/-- Strict containment of supports gives a strict containment of variable primes. -/
theorem thm31_primeOf_lt_of_ssubset {A B : Finset thm31_var} (hAB : A ⊂ B) :
    (primeOf (K := K) A : Ideal (MvPolynomial thm31_var K)) < primeOf (K := K) B := by
  have hle : (primeOf (K := K) A : Ideal (MvPolynomial thm31_var K)) ≤
      primeOf (K := K) B :=
    (primeOf_le_iff_subset (K := K)).mpr hAB.1
  refine lt_of_le_of_ne hle ?_
  intro hEq
  have hle' : (primeOf (K := K) B : Ideal (MvPolynomial thm31_var K)) ≤
      primeOf (K := K) A := by
    rw [← hEq]
  exact hAB.2 ((primeOf_le_iff_subset (K := K)).mp hle')

/-- A one-variable prime has height at least one. -/
theorem thm31_primeOf_height_one_le {x : thm31_var} :
    (1 : ℕ∞) ≤ (primeOf (K := K) ({x} : Finset thm31_var)).height := by
  have hbot : (⊥ : Ideal (MvPolynomial thm31_var K)).IsPrime := Ideal.isPrime_bot
  have hp : (primeOf (K := K) ({x} : Finset thm31_var)).IsPrime := primeOf_isPrime _
  have hn : (primeOf (K := K) ({x} : Finset thm31_var) :
      Ideal (MvPolynomial thm31_var K)) ≠ ⊥ :=
    thm31_primeOf_ne_bot_of_mem (K := K) (A := {x}) (i := x) (by simp)
  have hlt : (⊥ : Ideal (MvPolynomial thm31_var K)) <
      primeOf (K := K) ({x} : Finset thm31_var) :=
    lt_of_le_of_ne bot_le hn.symm
  have hstep := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  simpa [Ideal.height_bot] using hstep

/-- A two-variable prime generated by distinct variables has height at least two. -/
theorem thm31_primeOf_height_two_le {x y : thm31_var} (hxy : x ≠ y) :
    (2 : ℕ∞) ≤ (primeOf (K := K) ({x, y} : Finset thm31_var)).height := by
  have hp1 : (primeOf (K := K) ({x} : Finset thm31_var)).IsPrime := primeOf_isPrime _
  have hp2 : (primeOf (K := K) ({x, y} : Finset thm31_var)).IsPrime := primeOf_isPrime _
  have hs : ({x} : Finset thm31_var) ⊂ {x, y} := by
    constructor
    · intro i hi
      simp at hi ⊢
      exact Or.inl hi
    · intro hsub
      have hyx : y ∈ ({x} : Finset thm31_var) := hsub (by simp)
      have hy_eq : y = x := by simpa using hyx
      exact hxy hy_eq.symm
  have hlt : (primeOf (K := K) ({x} : Finset thm31_var) :
      Ideal (MvPolynomial thm31_var K)) < primeOf (K := K) ({x, y} : Finset thm31_var) :=
    thm31_primeOf_lt_of_ssubset (K := K) hs
  have hstep := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h1 := thm31_primeOf_height_one_le (K := K) (x := x)
  calc
    (2 : ℕ∞) = (1 : ℕ∞) + 1 := by norm_num
    _ ≤ (primeOf (K := K) ({x} : Finset thm31_var)).height + 1 :=
      add_le_add_left h1 1
    _ ≤ (primeOf (K := K) ({x, y} : Finset thm31_var)).height := hstep

/-- A three-variable prime generated by distinct variables has height at least three. -/
theorem thm31_primeOf_height_three_le {x y z : thm31_var}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (3 : ℕ∞) ≤ (primeOf (K := K) ({x, y, z} : Finset thm31_var)).height := by
  have hp2 : (primeOf (K := K) ({x, y} : Finset thm31_var)).IsPrime := primeOf_isPrime _
  have hp3 : (primeOf (K := K) ({x, y, z} : Finset thm31_var)).IsPrime := primeOf_isPrime _
  have hs : ({x, y} : Finset thm31_var) ⊂ {x, y, z} := by
    constructor
    · intro i hi
      simp at hi ⊢
      rcases hi with rfl | rfl <;> simp
    · intro hsub
      have hzxy : z ∈ ({x, y} : Finset thm31_var) := hsub (by simp)
      have hz_eq : z = x ∨ z = y := by simpa using hzxy
      rcases hz_eq with hzx | hzy
      · exact hxz hzx.symm
      · exact hyz hzy.symm
  have hlt : (primeOf (K := K) ({x, y} : Finset thm31_var) :
      Ideal (MvPolynomial thm31_var K)) <
      primeOf (K := K) ({x, y, z} : Finset thm31_var) :=
    thm31_primeOf_lt_of_ssubset (K := K) hs
  have hstep := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h2 := thm31_primeOf_height_two_le (K := K) hxy
  calc
    (3 : ℕ∞) = (2 : ℕ∞) + 1 := by norm_num
    _ ≤ (primeOf (K := K) ({x, y} : Finset thm31_var)).height + 1 :=
      add_le_add_left h2 1
    _ ≤ (primeOf (K := K) ({x, y, z} : Finset thm31_var)).height := hstep

/-- Krull's height theorem gives the reverse bound for a variable prime. -/
theorem thm31_primeOf_height_le_card (A : Finset thm31_var) :
    (primeOf (K := K) A).height ≤ A.card := by
  classical
  let s : Finset (MvPolynomial thm31_var K) :=
    A.image (MvPolynomial.X : thm31_var → MvPolynomial thm31_var K)
  have hspan : Ideal.span ((s : Finset (MvPolynomial thm31_var K)) :
      Set (MvPolynomial thm31_var K)) = primeOf (K := K) A := by
    rw [primeOf, purePower, monomialIdeal]
    congr 1
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      exact ⟨Finsupp.single i 1, ⟨i, hi, rfl⟩, rfl⟩
    · rintro ⟨e, ⟨i, hi, rfl⟩, rfl⟩
      exact Finset.mem_image.mpr ⟨i, hi, by rfl⟩
  have hprime : (primeOf (K := K) A).IsPrime := primeOf_isPrime A
  have hpmin : primeOf (K := K) A ∈
      (Ideal.span ((s : Finset (MvPolynomial thm31_var K)) :
        Set (MvPolynomial thm31_var K))).minimalPrimes := by
    rw [hspan]
    simp [Ideal.minimalPrimes_eq_subsingleton_self]
  have hu := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
      (R := MvPolynomial thm31_var K) (p := primeOf (K := K) A) (s := s) hpmin
  have hcard : s.card = A.card := by
    dsimp [s]
    exact Finset.card_image_of_injective A MvPolynomial.X_injective
  simpa [hcard] using hu

/-- The four component radicals have heights \(3,2,2,3\), as stated in Theorem 3.1. -/
theorem thm31_radical_heights (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    (thm31_component (K := K) r s (0 : Fin 4)).radical.height = (3 : ℕ∞) ∧
    (thm31_component (K := K) r s (1 : Fin 4)).radical.height = (2 : ℕ∞) ∧
    (thm31_component (K := K) r s (2 : Fin 4)).radical.height = (2 : ℕ∞) ∧
    (thm31_component (K := K) r s (3 : Fin 4)).radical.height = (3 : ℕ∞) := by
  have hab : thm31_a ≠ thm31_b := by decide
  have hac : thm31_a ≠ thm31_c := by decide
  have had : thm31_a ≠ thm31_d := by decide
  have haz : thm31_a ≠ thm31_z := by decide
  have hbc : thm31_b ≠ thm31_c := by decide
  have hbz : thm31_b ≠ thm31_z := by decide
  have hcd : thm31_c ≠ thm31_d := by decide
  have hcz : thm31_c ≠ thm31_z := by decide
  have hdz : thm31_d ≠ thm31_z := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    rw [thm31_component_radical (K := K) r s hr hs]
    apply le_antisymm
  · simpa [thm31_support, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z] using
      (thm31_primeOf_height_le_card (K := K)
        ({thm31_a, thm31_b, thm31_z} : Finset thm31_var))
  · simpa [thm31_support, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z] using
      (thm31_primeOf_height_three_le (K := K) hab haz hbz)
  · simpa [thm31_support, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z] using
      (thm31_primeOf_height_le_card (K := K) ({thm31_a, thm31_d} : Finset thm31_var))
  · simpa [thm31_support, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z] using
      (thm31_primeOf_height_two_le (K := K) had)
  · simpa [thm31_support, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z] using
      (thm31_primeOf_height_le_card (K := K) ({thm31_b, thm31_c} : Finset thm31_var))
  · simpa [thm31_support, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z] using
      (thm31_primeOf_height_two_le (K := K) hbc)
  · simpa [thm31_support, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z] using
      (thm31_primeOf_height_le_card (K := K)
        ({thm31_c, thm31_d, thm31_z} : Finset thm31_var))
  · simpa [thm31_support, thm31_a, thm31_b, thm31_c, thm31_d, thm31_z] using
      (thm31_primeOf_height_three_le (K := K) hcd hcz hdz)

/-- Equation (2) for \(I_{r,s}\), obtained from the proved irredundant antichain
decomposition (5). -/
theorem thm31_hasStdSymbolicFormula (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    HasStdSymbolicFormula (thm31_I (K := K) r s) (thm31_component (K := K) r s) := by
  change HasStdSymbolicFormula (thm31_I (K := K) r s)
    (fun j ↦ (purePower (K := K) (thm31_support j) (thm31_componentExp r s j) :
      Ideal (MvPolynomial thm31_var K)))
  exact eq2_standardSymbolic (K := K)
    (thm31_isIrredundantDecomp (K := K) r s hr hs)
    (thm31_supportsAntichain r s)

/-- Equation (2) for the squarefree root \(M=I_{1,1}\). -/
theorem thm31_M_hasStdSymbolicFormula :
    HasStdSymbolicFormula (thm31_M (K := K)) (thm31_component (K := K) 1 1) := by
  simpa [thm31_M] using
    (thm31_hasStdSymbolicFormula (K := K) 1 1 (by omega) (by omega))

/-- The intrinsic Simis conclusion of Theorem 3.1, without an explicit Eq. (2) input. -/
theorem thm31_isSimis (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    IsSimis (thm31_I (K := K) r s) :=
  thm31_isSimis_of_hasStdSymbolicFormula (K := K) r s hr hs
    (thm31_hasStdSymbolicFormula (K := K) r s hr hs)

/-- The intrinsic symbolic-power formula \(I_{r,s}^{(q)}=I_{r,s}^{\,q}\). -/
theorem thm31_symbolicPower_eq_pow (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (q : ℕ) (hq : 1 ≤ q) :
    symbolicPower (thm31_I (K := K) r s) q = thm31_I (K := K) r s ^ q :=
  thm31_isSimis (K := K) r s hr hs q hq

/-- The full MPV hypotheses for \(I_{r,s}\), without an explicit Eq. (2) input. -/
theorem thm31_MPVHypotheses (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    MPVHypotheses (thm31_I (K := K) r s) thm31_support (thm31_componentExp r s) :=
  thm31_MPVHypotheses_of_hasStdSymbolicFormula (K := K) r s hr hs
    (thm31_hasStdSymbolicFormula (K := K) r s hr hs)

/-- The squarefree root \(M\) is intrinsically Simis. -/
theorem thm31_M_isSimis : IsSimis (thm31_M (K := K)) :=
  thm31_M_isSimis_of_hasStdSymbolicFormula (K := K)
    (thm31_M_hasStdSymbolicFormula (K := K))

/-- The MPV conclusion holds precisely when \(r=s\), without an explicit Eq. (2) input. -/
theorem thm31_MPVConc_iff (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    MPVConc (thm31_I (K := K) r s) ↔ r = s :=
  thm31_MPVConc_iff_of_stdM (K := K) r s hr hs
    (thm31_M_hasStdSymbolicFormula (K := K))

/-- The associated primes of \(S/I_{r,s}\) are the four displayed component radicals. -/
theorem thm31_associatedPrimes_eq_range (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    associatedPrimes (MvPolynomial thm31_var K)
        (MvPolynomial thm31_var K ⧸ thm31_I (K := K) r s) =
      Set.range (fun j : Fin 4 ↦
        (primeOf (K := K) (thm31_support j) : Ideal (MvPolynomial thm31_var K))) := by
  have hdecomp := thm31_isIrredundantDecomp (K := K) r s hr hs
  exact prop21_associatedPrimes_eq_range_of_supportsAntichain (K := K)
    hdecomp.1 hdecomp.2 (thm31_supportsAntichain r s)

/-- The minimal primes of \(I_{r,s}\) are the four displayed component radicals. -/
theorem thm31_minimalPrimes_eq_range (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    (thm31_I (K := K) r s).minimalPrimes =
      Set.range (fun j : Fin 4 ↦
        (primeOf (K := K) (thm31_support j) : Ideal (MvPolynomial thm31_var K))) := by
  have hdecomp := thm31_isIrredundantDecomp (K := K) r s hr hs
  exact prop21_minimalPrimes_eq_range_of_supportsAntichain (K := K)
    hdecomp.1 hdecomp.2 (thm31_supportsAntichain r s)

/-- There are no embedded primes in the irredundant decomposition (5). -/
theorem thm31_associatedPrimes_eq_minimalPrimes (r s : ℕ)
    (hr : 0 < r) (hs : 0 < s) :
    associatedPrimes (MvPolynomial thm31_var K)
        (MvPolynomial thm31_var K ⧸ thm31_I (K := K) r s) =
      (thm31_I (K := K) r s).minimalPrimes := by
  exact (thm31_associatedPrimes_eq_range (K := K) r s hr hs).trans
    (thm31_minimalPrimes_eq_range (K := K) r s hr hs).symm

/-- The support complex of \(I_{r,s}\) equals that of its radical \(M\). -/
theorem thm31_supportComplex_eq_M (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    supportComplex (thm31_I (K := K) r s) = supportComplex (thm31_M (K := K)) :=
  (thm31_supportComplex_I (K := K) r s hr hs).trans
    (thm31_supportComplex_M (K := K)).symm

/-- The decomposition and prime-height assertions in Theorem 3.1. -/
theorem thm31_main_decomposition (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    IsIrredundantDecomp (thm31_I (K := K) r s) thm31_support
        (thm31_componentExp r s) ∧
      (∀ j : Fin 4,
        (thm31_component (K := K) r s j).radical =
          primeOf (K := K) (thm31_support j)) ∧
      (∀ j k : Fin 4,
        (thm31_component (K := K) r s j).radical ≤
          (thm31_component (K := K) r s k).radical → j = k) ∧
      Function.Injective (fun j : Fin 4 ↦
        (thm31_component (K := K) r s j).radical) ∧
      ((thm31_component (K := K) r s (0 : Fin 4)).radical.height = (3 : ℕ∞) ∧
        (thm31_component (K := K) r s (1 : Fin 4)).radical.height = (2 : ℕ∞) ∧
        (thm31_component (K := K) r s (2 : Fin 4)).radical.height = (2 : ℕ∞) ∧
        (thm31_component (K := K) r s (3 : Fin 4)).radical.height = (3 : ℕ∞)) := by
  exact ⟨thm31_isIrredundantDecomp (K := K) r s hr hs,
    thm31_component_radical (K := K) r s hr hs,
    thm31_component_radicals_antichain (K := K) r s hr hs,
    thm31_component_radicals_injective (K := K) r s hr hs,
    thm31_radical_heights (K := K) r s hr hs⟩

/-- The associated and minimal prime assertions in Theorem 3.1. -/
theorem thm31_main_primes (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    associatedPrimes (MvPolynomial thm31_var K)
        (MvPolynomial thm31_var K ⧸ thm31_I (K := K) r s) =
      Set.range (fun j : Fin 4 ↦
        (primeOf (K := K) (thm31_support j) : Ideal (MvPolynomial thm31_var K))) ∧
      (thm31_I (K := K) r s).minimalPrimes =
        Set.range (fun j : Fin 4 ↦
          (primeOf (K := K) (thm31_support j) : Ideal (MvPolynomial thm31_var K))) ∧
      associatedPrimes (MvPolynomial thm31_var K)
          (MvPolynomial thm31_var K ⧸ thm31_I (K := K) r s) =
        (thm31_I (K := K) r s).minimalPrimes := by
  exact ⟨thm31_associatedPrimes_eq_range (K := K) r s hr hs,
    thm31_minimalPrimes_eq_range (K := K) r s hr hs,
    thm31_associatedPrimes_eq_minimalPrimes (K := K) r s hr hs⟩

/-- Equation (6), the Simis property, and the full MPV hypotheses for \(I_{r,s}\). -/
theorem thm31_main_symbolic (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    HasStdSymbolicFormula (thm31_I (K := K) r s) (thm31_component (K := K) r s) ∧
      IsSimis (thm31_I (K := K) r s) ∧
        MPVHypotheses (thm31_I (K := K) r s) thm31_support
            (thm31_componentExp r s) ∧
          (∀ q : ℕ, 1 ≤ q →
            symbolicPower (thm31_I (K := K) r s) q = thm31_I (K := K) r s ^ q ∧
              thm31_I (K := K) r s ^ q =
                ⨅ j : Fin 4, (thm31_component (K := K) r s j) ^ q) := by
  refine ⟨thm31_hasStdSymbolicFormula (K := K) r s hr hs,
    thm31_isSimis (K := K) r s hr hs,
    thm31_MPVHypotheses (K := K) r s hr hs, ?_⟩
  intro q hq
  refine ⟨thm31_symbolicPower_eq_pow (K := K) r s hr hs q hq, ?_⟩
  simpa [componentSymbolic] using
    (thm31_pow_eq_componentSymbolic (K := K) r s hr hs q)

/-- The radical and support-conclusion portion of Theorem 3.1. -/
theorem thm31_main_radical (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    (thm31_I (K := K) r s).radical = thm31_M (K := K) ∧
      supportComplex (thm31_I (K := K) r s) = supportComplex (thm31_M (K := K)) ∧
        SupportPreserving (thm31_I (K := K) r s) := by
  exact ⟨thm31_radical_eq_M (K := K) r s hr hs,
    thm31_supportComplex_eq_M (K := K) r s hr hs,
    thm31_supportPreserving (K := K) r s hr hs⟩

/-- The squarefree-root and MPV-conclusion portion of Theorem 3.1. -/
theorem thm31_main_root (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    (HasSqRoot (thm31_I (K := K) r s) ↔ r = s) ∧
      IsSimis (thm31_M (K := K)) ∧
        (MPVConc (thm31_I (K := K) r s) ↔ r = s) ∧
          (r ≠ s → ¬ MPVConc (thm31_I (K := K) r s)) ∧
            (r = s →
              IsSquarefreeMonomialIdeal (thm31_M (K := K)) ∧
                (∀ i, 0 < thm31_weight r i) ∧
                  diagonal (K := K) (thm31_weight r) (thm31_M (K := K)) =
                    thm31_I (K := K) r s ∧
                    (∀ {J : Ideal (MvPolynomial thm31_var K)} {d : thm31_var → ℕ},
                      IsSquarefreeMonomialIdeal J →
                        (∀ i, 0 < d i) →
                          diagonal (K := K) d J = thm31_I (K := K) r s →
                            J = thm31_M (K := K) ∧ d = thm31_weight r)) := by
  refine ⟨thm31_hasSqRoot_iff (K := K) r s hr hs,
    thm31_M_isSimis (K := K),
    thm31_MPVConc_iff (K := K) r s hr hs, ?_, ?_⟩
  · intro hrs hmpv
    exact hrs ((thm31_MPVConc_iff (K := K) r s hr hs).mp hmpv)
  · intro hrs
    subst s
    refine ⟨thm31_M_isSquarefree (K := K), thm31_weight_pos r hr,
      thm31_diagonal_M (K := K) r, ?_⟩
    intro J d hJs hd hdiag
    exact thm31_root_unique (K := K) r hr hJs hd hdiag

/-- Compact aggregate of Theorem 3.1. The detailed radical/height clauses are in
`thm31_main_decomposition`, and the detailed squarefree-root clauses are in `thm31_main_root`. -/
theorem thm31_main (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    IsIrredundantDecomp (thm31_I (K := K) r s) thm31_support
        (thm31_componentExp r s) ∧
      associatedPrimes (MvPolynomial thm31_var K)
          (MvPolynomial thm31_var K ⧸ thm31_I (K := K) r s) =
        Set.range (fun j : Fin 4 ↦
          (primeOf (K := K) (thm31_support j) : Ideal (MvPolynomial thm31_var K))) ∧
      (thm31_I (K := K) r s).minimalPrimes =
        Set.range (fun j : Fin 4 ↦
          (primeOf (K := K) (thm31_support j) : Ideal (MvPolynomial thm31_var K))) ∧
      associatedPrimes (MvPolynomial thm31_var K)
          (MvPolynomial thm31_var K ⧸ thm31_I (K := K) r s) =
        (thm31_I (K := K) r s).minimalPrimes ∧
      (∀ q : ℕ, 1 ≤ q →
        symbolicPower (thm31_I (K := K) r s) q = thm31_I (K := K) r s ^ q ∧
          thm31_I (K := K) r s ^ q =
            ⨅ j : Fin 4, (thm31_component (K := K) r s j) ^ q) ∧
      IsSimis (thm31_I (K := K) r s) ∧
      MPVHypotheses (thm31_I (K := K) r s) thm31_support
          (thm31_componentExp r s) ∧
      (thm31_I (K := K) r s).radical = thm31_M (K := K) ∧
      SupportPreserving (thm31_I (K := K) r s) ∧
      supportComplex (thm31_I (K := K) r s) = supportComplex (thm31_M (K := K)) ∧
      (HasSqRoot (thm31_I (K := K) r s) ↔ r = s) ∧
      IsSimis (thm31_M (K := K)) ∧
      (MPVConc (thm31_I (K := K) r s) ↔ r = s) := by
  rcases thm31_main_decomposition (K := K) r s hr hs with ⟨hdecomp, _, _, _, _⟩
  rcases thm31_main_primes (K := K) r s hr hs with ⟨hassoc, hminimal, heqPrimes⟩
  rcases thm31_main_symbolic (K := K) r s hr hs with ⟨_, hsimis, hMPV, hsymbolic⟩
  rcases thm31_main_radical (K := K) r s hr hs with ⟨hradical, hsupport, hpreserving⟩
  rcases thm31_main_root (K := K) r s hr hs with
    ⟨hsqroot, hMsimis, hMPVConc, _, _⟩
  exact ⟨hdecomp, hassoc, hminimal, heqPrimes, hsymbolic, hsimis, hMPV,
    hradical, hpreserving, hsupport, hsqroot, hMsimis, hMPVConc⟩
