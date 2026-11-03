/-
Lemma 4.2 (Bordoloi--Das--Kumar).

The proof uses the monomial witness of Equation (9).  The numbered declarations keep
the standard symbolic-power formula explicit as `HasStdSymbolicFormula`; the `_of_mpv`
wrappers discharge it using `Eq2_StandardSymbolic` from the MPV decomposition data.
-/
import SimisFormal.Defs
import SimisFormal.Eq2_StandardSymbolic

namespace SimisFormal
open MvPolynomial
open scoped BigOperators
variable {σ K ι : Type*} [Field K] [DecidableEq σ]
/-- The coordinatewise factor used in Equation (9) on \(F\cap G\). -/
def lem42Coord (r s : ℕ) : ℕ :=
  max (2 * min r s) (max r s)

theorem lem42Coord_comm (r s : ℕ) : lem42Coord r s = lem42Coord s r := by
  simp [lem42Coord, Nat.min_comm, Nat.max_comm]

theorem lem42Coord_le_left (r s : ℕ) : r ≤ lem42Coord r s := by
  exact (Nat.le_max_left r s).trans (Nat.le_max_right _ _)

theorem lem42Coord_le_right (r s : ℕ) : s ≤ lem42Coord r s := by
  exact (Nat.le_max_right r s).trans (Nat.le_max_right _ _)

theorem lem42Coord_le_add (r s : ℕ) : lem42Coord r s ≤ r + s := by
  have h₁ : 2 * min r s ≤ r + s := by
    have hleft := Nat.min_le_left r s
    have hright := Nat.min_le_right r s
    omega
  have h₂ : max r s ≤ r + s := by omega
  exact max_le h₁ h₂

/-- For distinct positive entries, their sum is strictly larger than the witness's
shared-coordinate exponent. -/
theorem lem42_add_not_le_coord {r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≠ s) :
    ¬ r + s ≤ lem42Coord r s := by
  rcases lt_or_gt_of_ne hrs with hlt | hgt
  · rw [lem42Coord, Nat.min_eq_left (Nat.le_of_lt hlt), Nat.max_eq_right (Nat.le_of_lt hlt)]
    omega
  · rw [lem42Coord, Nat.min_eq_right (Nat.le_of_lt hgt), Nat.max_eq_left (Nat.le_of_lt hgt)]
    omega

theorem lem42Coord_lt_of_add_le_of_ne {x y r s : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y)
    (hsum : x + y ≤ lem42Coord r s) :
    lem42Coord x y < lem42Coord r s := by
  have hstrict : lem42Coord x y < x + y := by
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · have hform : lem42Coord x y = max (2 * x) y := by
        simp [lem42Coord, Nat.min_eq_left (Nat.le_of_lt hlt),
          Nat.max_eq_right (Nat.le_of_lt hlt)]
      rw [hform]
      omega
    · have hform : lem42Coord x y = max (2 * y) x := by
        simp [lem42Coord, Nat.min_eq_right (Nat.le_of_lt hgt),
          Nat.max_eq_left (Nat.le_of_lt hgt)]
      rw [hform]
      omega
  exact hstrict.trans_le hsum

theorem lem42Coord_le_of_two_mul_le {w r s : ℕ}
    (hw : 2 * w ≤ lem42Coord r s) : lem42Coord r w ≤ lem42Coord r s := by
  apply max_le
  · exact (Nat.mul_le_mul_left 2 (Nat.min_le_right r w)).trans hw
  · apply max_le
    · exact lem42Coord_le_left r s
    · omega

theorem lem42Coord_lt_of_two_mul_le_of_lt {w r s : ℕ}
    (hw : 2 * w ≤ lem42Coord r s) (hrw : r < w) :
    lem42Coord r w < lem42Coord r s := by
  have hwT : w < lem42Coord r s := by omega
  have h₂rT : 2 * r < lem42Coord r s := by omega
  have hform : lem42Coord r w = max (2 * r) w := by
    simp [lem42Coord, Nat.min_eq_left (Nat.le_of_lt hrw),
      Nat.max_eq_right (Nat.le_of_lt hrw)]
  rw [hform]
  exact max_lt h₂rT hwT

/-- The exponent vector \(f\) of Equation (9).  Only the two finite supports are used,
so no global finiteness assumption on the variable type is needed. -/
noncomputable def lem42ObstructionExp (u v : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.onFinset (u.support ∪ v.support) (fun i =>
    if i ∈ u.support then
      if i ∈ v.support then lem42Coord (u i) (v i)
      else u i
    else v i) (by
      intro i hi
      by_cases hiu : i ∈ u.support
      · exact Finset.mem_union.mpr (Or.inl hiu)
      · by_cases hiv : i ∈ v.support
        · exact Finset.mem_union.mpr (Or.inr hiv)
        · have hv0 : v i = 0 := by simpa [Finsupp.mem_support_iff] using hiv
          exact (hi (by simp [hiu, hv0])).elim)

theorem lem42ObstructionExp_apply (u v : σ →₀ ℕ) (i : σ) :
    lem42ObstructionExp u v i =
      if i ∈ u.support then
        if i ∈ v.support then lem42Coord (u i) (v i)
        else u i
      else v i := by
  unfold lem42ObstructionExp
  rw [Finsupp.onFinset_apply]

theorem lem42ObstructionExp_comm (u v : σ →₀ ℕ) :
    lem42ObstructionExp u v = lem42ObstructionExp v u := by
  ext i
  rw [lem42ObstructionExp_apply, lem42ObstructionExp_apply]
  by_cases hiu : i ∈ u.support <;> by_cases hiv : i ∈ v.support
  · simp [hiu, hiv, lem42Coord_comm]
  · simp [hiu, hiv]
  · simp [hiu, hiv]
  · have hu0 : u i = 0 := by simpa [Finsupp.mem_support_iff] using hiu
    have hv0 : v i = 0 := by simpa [Finsupp.mem_support_iff] using hiv
    simp [hiu, hiv, hu0, hv0]

theorem lem42_mem_support_obstructionExp {u v : σ →₀ ℕ} {i : σ} :
    i ∈ (lem42ObstructionExp u v).support ↔ i ∈ u.support ∨ i ∈ v.support := by
  rw [Finsupp.mem_support_iff]
  by_cases hiu : i ∈ u.support <;> by_cases hiv : i ∈ v.support
  · rw [lem42ObstructionExp_apply, if_pos hiu, if_pos hiv]
    constructor
    · intro _
      exact Or.inl hiu
    · intro _
      have hup : 0 < u i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hiu)
      have hvp : 0 < v i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hiv)
      simp only [lem42Coord] at *
      omega
  · rw [lem42ObstructionExp_apply, if_pos hiu, if_neg hiv]
    constructor
    · intro _
      exact Or.inl hiu
    · intro _
      exact Finsupp.mem_support_iff.mp hiu
  · rw [lem42ObstructionExp_apply, if_neg hiu]
    constructor
    · intro _
      exact Or.inr hiv
    · intro _
      exact Finsupp.mem_support_iff.mp hiv
  · rw [lem42ObstructionExp_apply, if_neg hiu]
    have hv0 : v i = 0 := by simpa [Finsupp.mem_support_iff] using hiv
    constructor
    · intro h
      exact (h hv0).elim
    · intro h
      rcases h with h | h
      · exact (hiu h).elim
      · exact (hiv h).elim

theorem lem42_le_obstructionExp_left (u v : σ →₀ ℕ) :
    u ≤ lem42ObstructionExp u v := by
  rw [Finsupp.le_def]
  intro i
  by_cases hiu : i ∈ u.support
  · by_cases hiv : i ∈ v.support
    · rw [lem42ObstructionExp_apply, if_pos hiu, if_pos hiv]
      exact lem42Coord_le_left _ _
    · rw [lem42ObstructionExp_apply, if_pos hiu, if_neg hiv]
  · have hu0 : u i = 0 := by simpa [Finsupp.mem_support_iff] using hiu
    rw [lem42ObstructionExp_apply, if_neg hiu]
    simp [hu0]

theorem lem42_le_obstructionExp_right (u v : σ →₀ ℕ) :
    v ≤ lem42ObstructionExp u v := by
  rw [Finsupp.le_def]
  intro i
  by_cases hiv : i ∈ v.support
  · by_cases hiu : i ∈ u.support
    · rw [lem42ObstructionExp_apply, if_pos hiu, if_pos hiv]
      exact lem42Coord_le_right _ _
    · rw [lem42ObstructionExp_apply, if_neg hiu]
  · have hv0 : v i = 0 := by simpa [Finsupp.mem_support_iff] using hiv
    simp [lem42ObstructionExp_apply, hv0]

omit [DecidableEq σ] in
/-- Multiplication by a monomial preserves ideal membership. -/
theorem lem42_monomial_mem_of_le {J : Ideal (MvPolynomial σ K)}
    {z e : σ →₀ ℕ} (hz : z ≤ e)
    (hmem : (monomial z (1 : K) : MvPolynomial σ K) ∈ J) :
    (monomial e (1 : K) : MvPolynomial σ K) ∈ J := by
  let r : σ →₀ ℕ := e - z
  have hr : z + r = e := by
    ext i
    simpa [r] using Nat.add_sub_of_le (hz i)
  have heq : (monomial e (1 : K) : MvPolynomial σ K) =
      monomial r (1 : K) * monomial z (1 : K) := by
    rw [MvPolynomial.monomial_mul]
    simp only [one_mul]
    rw [add_comm r z, hr]
  rw [heq]
  exact Ideal.mul_mem_left J (monomial r (1 : K)) hmem

/-- A minimal generator of a radical monomial ideal is the squarefree support monomial. -/
theorem lem42_radical_minGen_eq_characteristic {I : Ideal (MvPolynomial σ K)}
    {e : σ →₀ ℕ} (he : e ∈ minGens I.radical) :
    e = characteristicExp e.support := by
  classical
  let c : σ →₀ ℕ := characteristicExp e.support
  let N : ℕ := e.sum fun _ n => n
  have hle : e ≤ N • c := by
    rw [Finsupp.le_def]
    intro j
    by_cases hj : j ∈ e.support
    · have hbound : e j ≤ e.sum (fun _ n => n) :=
        Finsupp.single_eval_le_sum e (g := fun n => n) (by rfl)
          (by intro n; exact Nat.zero_le n) j
      simpa [N, c, Finsupp.nsmul_apply, characteristicExp_apply, hj] using hbound
    · have hj0 : e j = 0 := by simpa [Finsupp.mem_support_iff] using hj
      simp [N, c, Finsupp.nsmul_apply, characteristicExp_apply, hj, hj0]
  have hce : c ≤ e := by
    rw [Finsupp.le_def]
    intro j
    by_cases hj : j ∈ e.support
    · have hjpos : 0 < e j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
      simp [c, characteristicExp_apply, hj, Nat.succ_le_iff]
      exact hjpos
    · simp [c, characteristicExp_apply, hj]
  let r : σ →₀ ℕ := N • c - e
  have hr : e + r = N • c := by
    ext j
    simpa [r] using Nat.add_sub_of_le (hle j)
  have heR : (monomial e (1 : K) : MvPolynomial σ K) ∈ I.radical := (mem_minGens.mp he).1
  have hmul : (monomial e (1 : K) : MvPolynomial σ K) * monomial r (1 : K) ∈ I.radical :=
    Ideal.mul_mem_right (monomial r (1 : K)) I.radical heR
  have hpow : (monomial c (1 : K) : MvPolynomial σ K) ^ N ∈ I.radical := by
    rw [MvPolynomial.monomial_pow]
    simpa [MvPolynomial.monomial_mul, hr] using hmul
  have hcR : (monomial c (1 : K) : MvPolynomial σ K) ∈ I.radical :=
    Ideal.mem_radical_of_pow_mem (m := N) hpow
  exact ((mem_minGens.mp he).2 c hcR hce).symm

/-- Support preservation makes the generator-support complex a clutter. -/
theorem lem42_isClutter_of_supportPreserving {I : Ideal (MvPolynomial σ K)}
    (hsp : SupportPreserving I) : IsClutter (supportComplex I) := by
  intro A hA B hB hAB
  have hAr : A ∈ supportComplex I.radical := hsp ▸ hA
  have hBr : B ∈ supportComplex I.radical := hsp ▸ hB
  rcases hAr with ⟨u, hu, huA⟩
  rcases hBr with ⟨v, hv, hvB⟩
  have hsub : u.support ⊆ v.support := by
    intro i hi
    have hiA : i ∈ A := by simpa [← huA] using hi
    have hiB : i ∈ B := hAB hiA
    simpa [← hvB] using hiB
  have huv : u ≤ v := by
    rw [lem42_radical_minGen_eq_characteristic hu,
      lem42_radical_minGen_eq_characteristic hv]
    rw [Finsupp.le_def]
    intro i
    by_cases hi : i ∈ u.support
    · have hi' : i ∈ v.support := hsub hi
      simp [characteristicExp_apply, hi, hi']
    · simp [characteristicExp_apply, hi]
  have heq : u = v := (mem_minGens.mp hv).2 u (mem_minGens.mp hu).1 huv
  calc
    A = u.support := huA.symm
    _ = v.support := congrArg Finsupp.support heq
    _ = B := hvB

/-- Any monomial ideal is generated by its minimal monomial generators. -/
theorem lem42_eq_minGens_of_isMonomialIdeal {I : Ideal (MvPolynomial σ K)}
    (hI : IsMonomialIdeal I) : I = monomialIdeal (minGens I) := by
  rcases hI with ⟨S, hS⟩
  rw [hS]
  apply monomialIdeal_eq_iff.mpr
  intro e
  constructor
  · rintro ⟨s, hsS, hse⟩
    rcases exists_minGens_le
        (I := (monomialIdeal S : Ideal (MvPolynomial σ K)))
        (monomial_mem_monomialIdeal.mpr ⟨s, hsS, le_rfl⟩) with ⟨u, hu, huse⟩
    exact ⟨u, hu, huse.trans hse⟩
  · rintro ⟨u, hu, hue⟩
    have huI : (monomial u (1 : K) : MvPolynomial σ K) ∈
        (monomialIdeal S : Ideal (MvPolynomial σ K)) := (mem_minGens.mp hu).1
    rcases monomial_mem_monomialIdeal.mp huI with ⟨s, hsS, hsu⟩
    exact ⟨s, hsS, hsu.trans hue⟩

omit [DecidableEq σ] in
/-- The join generators produced by a finite decomposition form a finite set. -/
theorem lem42_iInfGens_finite [Fintype ι] {A : ι → Finset σ} {a : ι → σ → ℕ} :
    (iInfGens (fun j : ι => {e : σ →₀ ℕ | ∃ i ∈ A j, e = Finsupp.single i (a j i)})).Finite := by
  classical
  let S : ι → Set (σ →₀ ℕ) :=
    fun j => {e : σ →₀ ℕ | ∃ i ∈ A j, e = Finsupp.single i (a j i)}
  have hSfin : ∀ j, (S j).Finite := by
    intro j
    have him := (A j).finite_toSet.image (fun i => Finsupp.single i (a j i))
    simpa [S, Set.image, eq_comm] using him
  have hchoices : {c : ι → (σ →₀ ℕ) | ∀ j, c j ∈ S j}.Finite :=
    Set.Finite.pi' hSfin
  have himg := hchoices.image (fun c : ι → (σ →₀ ℕ) => Finset.univ.sup c)
  simpa [iInfGens, S, Set.image, eq_comm] using himg

/-- Minimal generators with one fixed support form a finite set. -/
theorem lem42_minGens_fixedSupport_finite [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hcomp : HasComponents I A a) (F : Finset σ) :
    {e : σ →₀ ℕ | e ∈ minGens I ∧ e.support = F}.Finite := by
  classical
  let S : ι → Set (σ →₀ ℕ) :=
    fun j => {e : σ →₀ ℕ | ∃ i ∈ A j, e = Finsupp.single i (a j i)}
  have hIS : I = monomialIdeal (iInfGens S) := by
    exact hcomp.trans (by simpa [S, purePower] using (monomialIdeal_iInf (K := K) S))
  have hGfin : (iInfGens S).Finite := by
    simpa [S] using (lem42_iInfGens_finite (σ := σ) (A := A) (a := a))
  refine hGfin.subset ?_
  intro e he
  have heI : (monomial e (1 : K) : MvPolynomial σ K) ∈ I := (mem_minGens.mp he.1).1
  have heRep : (monomial e (1 : K) : MvPolynomial σ K) ∈ monomialIdeal (iInfGens S) := by
    simpa [hIS] using heI
  rcases monomial_mem_monomialIdeal.mp heRep with ⟨s, hsS, hse⟩
  have hsI : (monomial s (1 : K) : MvPolynomial σ K) ∈ I := by
    rw [hIS]
    exact monomial_mem_monomialIdeal.mpr ⟨s, hsS, le_rfl⟩
  have hseq : s = e := (mem_minGens.mp he.1).2 s hsI hse
  simpa [hseq] using hsS

/-- A finite irreducible decomposition gives a monomial generating system. -/
theorem lem42_isMonomialIdeal_of_hasComponents [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hcomp : HasComponents I A a) : IsMonomialIdeal I := by
  let S : ι → Set (σ →₀ ℕ) :=
    fun j => {e : σ →₀ ℕ | ∃ i ∈ A j, e = Finsupp.single i (a j i)}
  refine ⟨iInfGens S, hcomp.trans ?_⟩
  simpa [S, purePower] using (monomialIdeal_iInf (K := K) S)

/-- The Equation (9) witness belongs to the square of every component whenever \(u\)
and \(v\) are minimal generators of \(I\). -/
theorem lem42_obstructionExp_mem_componentSymbolic
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hcomp : HasComponents I A a) {u v : σ →₀ ℕ}
    (hu : u ∈ minGens I) (hv : v ∈ minGens I) :
    (monomial (lem42ObstructionExp u v) (1 : K) : MvPolynomial σ K) ∈
      componentSymbolic (fun j => (purePower (A j) (a j) : Ideal (MvPolynomial σ K))) 2 := by
  rw [componentSymbolic]
  refine Ideal.mem_iInf.mpr ?_
  intro j
  have huI : (monomial u (1 : K) : MvPolynomial σ K) ∈ I := (mem_minGens.mp hu).1
  have hvI : (monomial v (1 : K) : MvPolynomial σ K) ∈ I := (mem_minGens.mp hv).1
  have huInf : (monomial u (1 : K) : MvPolynomial σ K) ∈
      ⨅ k, (purePower (A k) (a k) : Ideal (MvPolynomial σ K)) := by
    rw [← hcomp]
    exact huI
  have hvInf : (monomial v (1 : K) : MvPolynomial σ K) ∈
      ⨅ k, (purePower (A k) (a k) : Ideal (MvPolynomial σ K)) := by
    rw [← hcomp]
    exact hvI
  rcases monomial_mem_purePower.mp (Ideal.mem_iInf.mp huInf j) with ⟨r, hrA, hrle⟩
  rcases monomial_mem_purePower.mp (Ideal.mem_iInf.mp hvInf j) with ⟨s, hsA, hsle⟩
  let x : σ →₀ ℕ := Finsupp.single r (a j r)
  let y : σ →₀ ℕ := Finsupp.single s (a j s)
  have hxQ : (monomial x (1 : K) : MvPolynomial σ K) ∈ purePower (A j) (a j) := by
    exact monomial_mem_purePower.mpr ⟨r, hrA, by simp [x]⟩
  have hyQ : (monomial y (1 : K) : MvPolynomial σ K) ∈ purePower (A j) (a j) := by
    exact monomial_mem_purePower.mpr ⟨s, hsA, by simp [y]⟩
  by_cases hrs : r = s
  · subst s
    have hx2mul : (monomial (x + x) (1 : K) : MvPolynomial σ K) ∈
        purePower (A j) (a j) * purePower (A j) (a j) := by
      simpa [MvPolynomial.monomial_mul] using Ideal.mul_mem_mul hxQ hxQ
    have hx2 : (monomial (x + x) (1 : K) : MvPolynomial σ K) ∈
        purePower (A j) (a j) ^ 2 := by
      simpa [pow_two] using hx2mul
    apply lem42_monomial_mem_of_le (z := x + x) (e := lem42ObstructionExp u v) ?_ hx2
    rw [Finsupp.le_def]
    intro t
    by_cases htr : t = r
    · subst t
      have hxcoef : (x + x) r = a j r + a j r := by simp [x]
      rw [hxcoef]
      by_cases hUr : r ∈ u.support <;> by_cases hVr : r ∈ v.support
      · rw [lem42ObstructionExp_apply, if_pos hUr, if_pos hVr]
        simp only [lem42Coord] at *
        omega
      · have hvr0 : v r = 0 := by simpa [Finsupp.mem_support_iff] using hVr
        rw [lem42ObstructionExp_apply, if_pos hUr, if_neg hVr]
        omega
      · have hur0 : u r = 0 := by simpa [Finsupp.mem_support_iff] using hUr
        rw [lem42ObstructionExp_apply, if_neg hUr]
        omega
      · have hur0 : u r = 0 := by simpa [Finsupp.mem_support_iff] using hUr
        have hvr0 : v r = 0 := by simpa [Finsupp.mem_support_iff] using hVr
        rw [lem42ObstructionExp_apply, if_neg hUr]
        omega
    · simp [x, htr]
  · have hxleu : x ≤ u := Finsupp.single_le_iff.mpr hrle
    have hylev : y ≤ v := Finsupp.single_le_iff.mpr hsle
    have hxleo : x ≤ lem42ObstructionExp u v :=
      hxleu.trans (lem42_le_obstructionExp_left u v)
    have hyleo : y ≤ lem42ObstructionExp u v :=
      hylev.trans (lem42_le_obstructionExp_right u v)
    have hprod : (monomial (x + y) (1 : K) : MvPolynomial σ K) ∈
        purePower (A j) (a j) * purePower (A j) (a j) := by
      simpa [MvPolynomial.monomial_mul] using Ideal.mul_mem_mul hxQ hyQ
    have hpow : (monomial (x + y) (1 : K) : MvPolynomial σ K) ∈
        purePower (A j) (a j) ^ 2 := by
      simpa [pow_two] using hprod
    apply lem42_monomial_mem_of_le (z := x + y) (e := lem42ObstructionExp u v) ?_ hpow
    rw [Finsupp.le_def]
    intro t
    by_cases htr : t = r
    · subst t
      have hsr : s ≠ r := fun h => hrs h.symm
      simpa [x, y, hsr] using hxleo r
    · by_cases hts : t = s
      · subst t
        simpa [x, y, hrs] using hyleo s
      · have hrt : r ≠ t := fun h => htr h.symm
        have hst : s ≠ t := fun h => hts h.symm
        simp [x, y, hrt, hst]

/-- Two distinct minimal generators cannot have the same support.  Choose a distinct
    pair minimizing the total size of the Equation (9) witness; its symbolic-square
    obstruction excludes every product of two same-support minimal generators. -/
theorem lem42_noTwo_minGens_sameSupport [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hcomp : HasComponents I A a)
    (hstd : HasStdSymbolicFormula I
      (fun j => (purePower (A j) (a j) : Ideal (MvPolynomial σ K))))
    (hsimis : IsSimis I) (hcl : IsClutter (supportComplex I))
    {u v : σ →₀ ℕ} (hu : u ∈ minGens I) (hv : v ∈ minGens I)
    (hsupp : u.support = v.support) : u = v := by
  classical
  by_contra huv
  let F : Finset σ := u.support
  let Mset : Set (σ →₀ ℕ) := {e | e ∈ minGens I ∧ e.support = F}
  have hMfinite : Mset.Finite := by
    simpa [Mset, F] using
      (lem42_minGens_fixedSupport_finite (K := K) hcomp u.support)
  let M : Finset (σ →₀ ℕ) := hMfinite.toFinset
  have memM {e : σ →₀ ℕ} : e ∈ M ↔ e ∈ Mset := by
    change e ∈ hMfinite.toFinset ↔ e ∈ Mset
    exact Set.Finite.mem_toFinset hMfinite
  have hF : F ∈ supportComplex I := ⟨u, hu, by simp [F]⟩
  have hFu : u.support = F := by simp [F]
  have hFv : v.support = F := by simpa [F] using hsupp.symm
  have huM : u ∈ M := memM.mpr ⟨hu, hFu⟩
  have hvM : v ∈ M := memM.mpr ⟨hv, hFv⟩
  let P : Finset ((σ →₀ ℕ) × (σ →₀ ℕ)) :=
    (M.product M).filter (fun p => p.1 ≠ p.2)
  have hPnon : P.Nonempty := by
    refine ⟨(u, v), ?_⟩
    simp [P, huM, hvM, huv]
  let measure : (σ →₀ ℕ) × (σ →₀ ℕ) → ℕ :=
    fun p => ∑ i ∈ F, lem42ObstructionExp p.1 p.2 i
  obtain ⟨p, hpP, hpmin⟩ := Finset.exists_min_image P measure hPnon
  have hpFilter := Finset.mem_filter.mp hpP
  have hpProd := Finset.mem_product.mp hpFilter.1
  let x : σ →₀ ℕ := p.1
  let y : σ →₀ ℕ := p.2
  have hxM : x ∈ M := by simpa [x] using hpProd.1
  have hyM : y ∈ M := by simpa [y] using hpProd.2
  have hxy : x ≠ y := by simpa [x, y] using hpFilter.2
  have hxSet : x ∈ minGens I ∧ x.support = F := memM.mp hxM
  have hySet : y ∈ minGens I ∧ y.support = F := memM.mp hyM
  have hx : x ∈ minGens I := hxSet.1
  have hy : y ∈ minGens I := hySet.1
  have hxSupp : x.support = F := hxSet.2
  have hySupp : y.support = F := hySet.2
  have hMin {r s : σ →₀ ℕ} (hrM : r ∈ M) (hsM : s ∈ M) (hrs : r ≠ s) :
      measure (x, y) ≤ measure (r, s) := by
    have hrsP : (r, s) ∈ P := by simp [P, hrM, hsM, hrs]
    simpa [x, y] using hpmin (r, s) hrsP
  let o : σ →₀ ℕ := lem42ObstructionExp x y
  have hoSupp : o.support = F := by
    ext i
    simpa [o, hxSupp, hySupp] using
      (lem42_mem_support_obstructionExp (u := x) (v := y) (i := i))
  have hoCoord (i : σ) (hi : i ∈ F) : o i = lem42Coord (x i) (y i) := by
    have hix : i ∈ x.support := by simpa [hxSupp] using hi
    have hiy : i ∈ y.support := by simpa [hySupp] using hi
    change lem42ObstructionExp x y i = lem42Coord (x i) (y i)
    rw [lem42ObstructionExp_apply]
    simp [hix, hiy]
  have hmeasureXY : measure (x, y) = ∑ i ∈ F, o i := by
    rfl
  have hnoSquare : ∀ w : σ →₀ ℕ, w ∈ M → ¬ w + w ≤ o := by
    intro w hwM hww
    have hwSet : w ∈ minGens I ∧ w.support = F := memM.mp hwM
    have hw : w ∈ minGens I := hwSet.1
    have hwSupp : w.support = F := hwSet.2
    have hwI : (monomial w (1 : K) : MvPolynomial σ K) ∈ I := (mem_minGens.mp hw).1
    have hwwCoord (i : σ) : 2 * w i ≤ o i := by
      simpa [two_mul] using hww i
    have hwlex : w ≤ x := by
      by_cases hwx : w = x
      · subst w
        exact le_rfl
      · have hpoint : ∀ i ∈ F, lem42ObstructionExp x w i ≤ o i := by
          intro i hi
          have hix : i ∈ x.support := by simpa [hxSupp] using hi
          have hiy : i ∈ y.support := by simpa [hySupp] using hi
          have hiw : i ∈ w.support := by simpa [hwSupp] using hi
          have hnew : lem42ObstructionExp x w i = lem42Coord (x i) (w i) := by
            rw [lem42ObstructionExp_apply]
            simp [hix, hiw]
          have hold := hoCoord i hi
          have htwo : 2 * w i ≤ lem42Coord (x i) (y i) := by simpa [hold] using hwwCoord i
          rw [hnew, hold]
          exact lem42Coord_le_of_two_mul_le htwo
        have hnoLt : ∀ i ∈ F, ¬ x i < w i := by
          intro i hi hlt
          have hix : i ∈ x.support := by simpa [hxSupp] using hi
          have hiy : i ∈ y.support := by simpa [hySupp] using hi
          have hiw : i ∈ w.support := by simpa [hwSupp] using hi
          have hnew : lem42ObstructionExp x w i = lem42Coord (x i) (w i) := by
            rw [lem42ObstructionExp_apply]
            simp [hix, hiw]
          have hold := hoCoord i hi
          have htwo : 2 * w i ≤ lem42Coord (x i) (y i) := by simpa [hold] using hwwCoord i
          have hstrict : lem42ObstructionExp x w i < o i := by
            rw [hnew, hold]
            exact lem42Coord_lt_of_two_mul_le_of_lt htwo hlt
          have hsumlt : (∑ j ∈ F, lem42ObstructionExp x w j) < ∑ j ∈ F, o j :=
            Finset.sum_lt_sum hpoint ⟨i, hi, hstrict⟩
          have hge := hMin hxM hwM (Ne.symm hwx)
          rw [hmeasureXY] at hge
          change (∑ j ∈ F, o j) ≤ ∑ j ∈ F, lem42ObstructionExp x w j at hge
          exact (not_lt_of_ge hge) hsumlt
        rw [Finsupp.le_def]
        intro i
        by_cases hi : i ∈ F
        · exact Nat.le_of_not_gt (hnoLt i hi)
        · have hnot : i ∉ w.support := by simpa [hwSupp] using hi
          have hw0 : w i = 0 := by simpa [Finsupp.mem_support_iff] using hnot
          simp [hw0]
    have hwley : w ≤ y := by
      by_cases hwy : w = y
      · subst w
        exact le_rfl
      · have hpoint : ∀ i ∈ F, lem42ObstructionExp y w i ≤ o i := by
          intro i hi
          have hix : i ∈ x.support := by simpa [hxSupp] using hi
          have hiy : i ∈ y.support := by simpa [hySupp] using hi
          have hiw : i ∈ w.support := by simpa [hwSupp] using hi
          have hnew : lem42ObstructionExp y w i = lem42Coord (y i) (w i) := by
            rw [lem42ObstructionExp_apply]
            simp [hiy, hiw]
          have hold := hoCoord i hi
          have htwoOld : 2 * w i ≤ lem42Coord (x i) (y i) := by
            simpa [hold] using hwwCoord i
          have htwo : 2 * w i ≤ lem42Coord (y i) (x i) :=
            htwoOld.trans_eq (lem42Coord_comm (x i) (y i))
          rw [hnew, hold]
          simpa [lem42Coord_comm] using
            (lem42Coord_le_of_two_mul_le (w := w i) (r := y i) (s := x i) htwo)
        have hnoLt : ∀ i ∈ F, ¬ y i < w i := by
          intro i hi hlt
          have hix : i ∈ x.support := by simpa [hxSupp] using hi
          have hiy : i ∈ y.support := by simpa [hySupp] using hi
          have hiw : i ∈ w.support := by simpa [hwSupp] using hi
          have hnew : lem42ObstructionExp y w i = lem42Coord (y i) (w i) := by
            rw [lem42ObstructionExp_apply]
            simp [hiy, hiw]
          have hold := hoCoord i hi
          have htwoOld : 2 * w i ≤ lem42Coord (x i) (y i) := by
            simpa [hold] using hwwCoord i
          have htwo : 2 * w i ≤ lem42Coord (y i) (x i) :=
            htwoOld.trans_eq (lem42Coord_comm (x i) (y i))
          have hstrict : lem42ObstructionExp y w i < o i := by
            rw [hnew, hold]
            simpa [lem42Coord_comm] using
              (lem42Coord_lt_of_two_mul_le_of_lt (w := w i) (r := y i) (s := x i)
                htwo hlt)
          have hsumlt : (∑ j ∈ F, lem42ObstructionExp y w j) < ∑ j ∈ F, o j :=
            Finset.sum_lt_sum hpoint ⟨i, hi, hstrict⟩
          have hge := hMin hyM hwM (Ne.symm hwy)
          rw [hmeasureXY] at hge
          change (∑ j ∈ F, o j) ≤ ∑ j ∈ F, lem42ObstructionExp y w j at hge
          exact (not_lt_of_ge hge) hsumlt
        rw [Finsupp.le_def]
        intro i
        by_cases hi : i ∈ F
        · exact Nat.le_of_not_gt (hnoLt i hi)
        · have hnot : i ∉ w.support := by simpa [hwSupp] using hi
          have hw0 : w i = 0 := by simpa [Finsupp.mem_support_iff] using hnot
          simp [hw0]
    have hweqx : w = x := by
      exact (mem_minGens.mp hx).2 w hwI hwlex
    have hweqy : w = y := by
      exact (mem_minGens.mp hy).2 w hwI hwley
    exact hxy (hweqx.symm.trans hweqy)
  have hmono : IsMonomialIdeal I := lem42_isMonomialIdeal_of_hasComponents hcomp
  have hminEq : I = monomialIdeal (minGens I) :=
    lem42_eq_minGens_of_isMonomialIdeal hmono
  have hnotI2 : (monomial o (1 : K) : MvPolynomial σ K) ∉ I ^ 2 := by
    intro hmem
    have hmemMul : (monomial o (1 : K) : MvPolynomial σ K) ∈ I * I := by
      simpa [pow_two] using hmem
    rw [hminEq] at hmemMul
    rw [monomialIdeal_mul] at hmemMul
    rcases monomial_mem_monomialIdeal.mp hmemMul with ⟨w, hwGens, hwo⟩
    rcases hwGens with ⟨r, hr, s, hs, hweq⟩
    subst w
    have hrle : r ≤ o := by
      rw [Finsupp.le_def]
      intro i
      have := hwo i
      simp only [Finsupp.add_apply] at this
      omega
    have hsle : s ≤ o := by
      rw [Finsupp.le_def]
      intro i
      have := hwo i
      simp only [Finsupp.add_apply] at this
      omega
    have hrSub : r.support ⊆ F := by
      simpa [hoSupp] using Finsupp.support_mono hrle
    have hsSub : s.support ⊆ F := by
      simpa [hoSupp] using Finsupp.support_mono hsle
    have hrH : r.support ∈ supportComplex I := ⟨r, hr, rfl⟩
    have hsH : s.support ∈ supportComplex I := ⟨s, hs, rfl⟩
    have hrSupp : r.support = F := hcl r.support hrH F hF hrSub
    have hsSupp : s.support = F := hcl s.support hsH F hF hsSub
    have hrM : r ∈ M := memM.mpr ⟨hr, hrSupp⟩
    have hsM : s ∈ M := memM.mpr ⟨hs, hsSupp⟩
    by_cases hrs : r = s
    · subst s
      exact hnoSquare r hrM hwo
    · have hpoint : ∀ i ∈ F, lem42ObstructionExp r s i ≤ o i := by
        intro i hi
        have hir : i ∈ r.support := by simpa [hrSupp] using hi
        have his : i ∈ s.support := by simpa [hsSupp] using hi
        have hnew : lem42ObstructionExp r s i = lem42Coord (r i) (s i) := by
          rw [lem42ObstructionExp_apply]
          simp [hir, his]
        have hold := hoCoord i hi
        have hadd : r i + s i ≤ lem42Coord (x i) (y i) := by
          simpa [hold] using hwo i
        rw [hnew, hold]
        exact (lem42Coord_le_add (r i) (s i)).trans hadd
      have hexDiff : ∃ i ∈ F, r i ≠ s i := by
        by_contra hnone
        apply hrs
        ext i
        by_cases hi : i ∈ F
        · by_contra hne
          exact hnone ⟨i, hi, hne⟩
        · have hrnot : i ∉ r.support := by simpa [hrSupp] using hi
          have hsnot : i ∉ s.support := by simpa [hsSupp] using hi
          have hr0 : r i = 0 := by simpa [Finsupp.mem_support_iff] using hrnot
          have hs0 : s i = 0 := by simpa [Finsupp.mem_support_iff] using hsnot
          omega
      rcases hexDiff with ⟨i, hiF, hidiff⟩
      have hir : i ∈ r.support := by simpa [hrSupp] using hiF
      have his : i ∈ s.support := by simpa [hsSupp] using hiF
      have hriPos : 0 < r i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hir)
      have hsiPos : 0 < s i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp his)
      have hnew : lem42ObstructionExp r s i = lem42Coord (r i) (s i) := by
        rw [lem42ObstructionExp_apply]
        simp [hir, his]
      have hold := hoCoord i hiF
      have hadd : r i + s i ≤ o i := by simpa using hwo i
      have hstrict : lem42ObstructionExp r s i < o i := by
        rw [hnew, hold]
        exact lem42Coord_lt_of_add_le_of_ne hriPos hsiPos hidiff
          ((by simpa [hold] using hadd))
      have hsumlt : (∑ j ∈ F, lem42ObstructionExp r s j) < ∑ j ∈ F, o j :=
        Finset.sum_lt_sum hpoint ⟨i, hiF, hstrict⟩
      have hge := hMin hrM hsM hrs
      rw [hmeasureXY] at hge
      change (∑ j ∈ F, o j) ≤ ∑ j ∈ F, lem42ObstructionExp r s j at hge
      exact (not_lt_of_ge hge) hsumlt
  have hCompMem := lem42_obstructionExp_mem_componentSymbolic hcomp hx hy
  have hpowEq : I ^ 2 =
      componentSymbolic (fun j => (purePower (A j) (a j) : Ideal (MvPolynomial σ K))) 2 := by
    calc
      I ^ 2 = symbolicPower I 2 := (hsimis 2 (by norm_num)).symm
      _ = componentSymbolic (fun j => (purePower (A j) (a j) : Ideal (MvPolynomial σ K))) 2 :=
        hstd 2 (by norm_num)
  apply hnotI2
  rw [hpowEq]
  simpa [o] using hCompMem

/-- Lemma 4.2(i): under the MPV hypotheses and support preservation, each facet of
    \(F(I)\) supports exactly one minimal monomial generator. -/
theorem lem42_oneGenerator [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hmpv : MPVHypotheses I A a) (hsp : SupportPreserving I)
    (hstd : HasStdSymbolicFormula I
      (fun j => (purePower (A j) (a j) : Ideal (MvPolynomial σ K)))) :
    ∀ F ∈ supportComplex I, ∃! e : σ →₀ ℕ, e ∈ minGens I ∧ e.support = F := by
  have hcl : IsClutter (supportComplex I) :=
    lem42_isClutter_of_supportPreserving hsp
  intro F hF
  rcases hF with ⟨u, hu, huF⟩
  refine ⟨u, ⟨hu, huF⟩, ?_⟩
  intro v hv
  exact lem42_noTwo_minGens_sameSupport
    (I := I) (A := A) (a := a) hmpv.1.1 hstd hmpv.2.2 hcl
    hv.1 hu (hv.2.trans huF.symm)

/-- Lemma 4.2(ii): an isolated pair has equal exponents at every shared variable.
    The proof is the Equation (9) monomial obstruction from the paper. -/
theorem lem42_isolatedEqualExponents [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hmpv : MPVHypotheses I A a) (hsp : SupportPreserving I)
    (hstd : HasStdSymbolicFormula I
      (fun j => (purePower (A j) (a j) : Ideal (MvPolynomial σ K))))
    {F G : Finset σ} (hF : F ∈ supportComplex I) (hG : G ∈ supportComplex I)
    (hFG : F ≠ G)
    (hIso : {E : Finset σ | E ∈ supportComplex I ∧ E ⊆ F ∪ G} = {F, G})
    {u v : σ →₀ ℕ} (hu : u ∈ minGens I) (hv : v ∈ minGens I)
    (hsuppU : u.support = F) (hsuppV : v.support = G)
    {i : σ} (hiF : i ∈ F) (hiG : i ∈ G) : u i = v i := by
  classical
  have hcomp : HasComponents I A a := hmpv.1.1
  have hsimis : IsSimis I := hmpv.2.2
  have hcl : IsClutter (supportComplex I) :=
    lem42_isClutter_of_supportPreserving hsp
  have hsame {r s : σ →₀ ℕ} (hr : r ∈ minGens I) (hs : s ∈ minGens I)
      (hsupp : r.support = s.support) : r = s :=
    lem42_noTwo_minGens_sameSupport hcomp hstd hsimis hcl hr hs hsupp
  by_contra hdiff
  have hFpriv : ∃ p, p ∈ F ∧ p ∉ G := by
    by_contra h
    have hsub : F ⊆ G := by
      intro x hx
      by_contra hxG
      exact h ⟨x, hx, hxG⟩
    exact hFG (hcl F hF G hG hsub)
  have hGpriv : ∃ q, q ∈ G ∧ q ∉ F := by
    by_contra h
    have hsub : G ⊆ F := by
      intro x hx
      by_contra hxF
      exact h ⟨x, hx, hxF⟩
    exact hFG (hcl G hG F hF hsub).symm
  rcases hFpriv with ⟨p, hpF, hpG⟩
  rcases hGpriv with ⟨q, hqG, hqF⟩
  let o : σ →₀ ℕ := lem42ObstructionExp u v
  have hoSupp : o.support = F ∪ G := by
    ext j
    simpa [o, hsuppU, hsuppV] using
      (lem42_mem_support_obstructionExp (u := u) (v := v) (i := j))
  have hnotUU : ¬ u + u ≤ o := by
    intro hle
    have hpU : p ∈ u.support := by simpa [hsuppU] using hpF
    have hpV : p ∉ v.support := by simpa [hsuppV] using hpG
    have hppos : 0 < u p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hpU)
    have hcoord : u p + u p ≤ u p := by
      simpa [o, lem42ObstructionExp_apply, hpU, hpV] using hle p
    omega
  have hnotVV : ¬ v + v ≤ o := by
    intro hle
    have hqV : q ∈ v.support := by simpa [hsuppV] using hqG
    have hqU : q ∉ u.support := by simpa [hsuppU] using hqF
    have hqpos : 0 < v q := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hqV)
    have hcoord : v q + v q ≤ v q := by
      simpa [o, lem42ObstructionExp_apply, hqU, hqV] using hle q
    omega
  have hnotUV : ¬ u + v ≤ o := by
    intro hle
    have hiU : i ∈ u.support := by simpa [hsuppU] using hiF
    have hiV : i ∈ v.support := by simpa [hsuppV] using hiG
    have hiuPos : 0 < u i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hiU)
    have hivPos : 0 < v i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hiV)
    have hcoord : u i + v i ≤ lem42Coord (u i) (v i) := by
      simpa [o, lem42ObstructionExp_apply, hiU, hiV] using hle i
    exact lem42_add_not_le_coord hiuPos hivPos hdiff hcoord
  have hmono : IsMonomialIdeal I := lem42_isMonomialIdeal_of_hasComponents hcomp
  have hminEq : I = monomialIdeal (minGens I) :=
    lem42_eq_minGens_of_isMonomialIdeal hmono
  have hnotI2 : (monomial o (1 : K) : MvPolynomial σ K) ∉ I ^ 2 := by
    intro hmem
    have hmemMul : (monomial o (1 : K) : MvPolynomial σ K) ∈ I * I := by
      simpa [pow_two] using hmem
    rw [hminEq] at hmemMul
    rw [monomialIdeal_mul] at hmemMul
    rcases monomial_mem_monomialIdeal.mp hmemMul with ⟨w, hwGens, hwo⟩
    rcases hwGens with ⟨r, hr, s, hs, hweq⟩
    subst w
    have hrle : r ≤ o := by
      rw [Finsupp.le_def]
      intro j
      have hj := hwo j
      simp only [Finsupp.add_apply] at hj
      omega
    have hsle : s ≤ o := by
      rw [Finsupp.le_def]
      intro j
      have hj := hwo j
      simp only [Finsupp.add_apply] at hj
      omega
    have hrSub : r.support ⊆ F ∪ G := by
      simpa [hoSupp] using Finsupp.support_mono hrle
    have hsSub : s.support ⊆ F ∪ G := by
      simpa [hoSupp] using Finsupp.support_mono hsle
    have hrSet : r.support ∈
        ({E : Finset σ | E ∈ supportComplex I ∧ E ⊆ F ∪ G} : Set (Finset σ)) :=
      ⟨⟨r, hr, rfl⟩, hrSub⟩
    have hsSet : s.support ∈
        ({E : Finset σ | E ∈ supportComplex I ∧ E ⊆ F ∪ G} : Set (Finset σ)) :=
      ⟨⟨s, hs, rfl⟩, hsSub⟩
    rw [hIso] at hrSet hsSet
    have hrCases : r.support = F ∨ r.support = G := by simpa using hrSet
    have hsCases : s.support = F ∨ s.support = G := by simpa using hsSet
    rcases hrCases with hrF | hrG
    · have hrequ : r = u := hsame hr hu (hrF.trans hsuppU.symm)
      rcases hsCases with hsF | hsG
      · have hsequ : s = u := hsame hs hu (hsF.trans hsuppU.symm)
        rw [hrequ, hsequ] at hwo
        exact hnotUU hwo
      · have hseqv : s = v := hsame hs hv (hsG.trans hsuppV.symm)
        rw [hrequ, hseqv] at hwo
        exact hnotUV hwo
    · have hreqv : r = v := hsame hr hv (hrG.trans hsuppV.symm)
      rcases hsCases with hsF | hsG
      · have hsequ : s = u := hsame hs hu (hsF.trans hsuppU.symm)
        rw [hreqv, hsequ] at hwo
        have hwo' : u + v ≤ o := by simpa [add_comm] using hwo
        exact hnotUV hwo'
      · have hseqv : s = v := hsame hs hv (hsG.trans hsuppV.symm)
        rw [hreqv, hseqv] at hwo
        exact hnotVV hwo
  have hCompMem := lem42_obstructionExp_mem_componentSymbolic hcomp hu hv
  have hpowEq : I ^ 2 =
      componentSymbolic (fun j => (purePower (A j) (a j) : Ideal (MvPolynomial σ K))) 2 := by
    calc
      I ^ 2 = symbolicPower I 2 := (hsimis 2 (by norm_num)).symm
      _ = componentSymbolic (fun j => (purePower (A j) (a j) : Ideal (MvPolynomial σ K))) 2 :=
        hstd 2 (by norm_num)
  apply hnotI2
  rw [hpowEq]
  simpa [o] using hCompMem

/-- Lemma 4.2, with both numbered assertions packaged as a single conjunction. -/
theorem lem42 [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hmpv : MPVHypotheses I A a) (hsp : SupportPreserving I)
    (hstd : HasStdSymbolicFormula I
      (fun j => (purePower (A j) (a j) : Ideal (MvPolynomial σ K)))) :
    (∀ F ∈ supportComplex I, ∃! e : σ →₀ ℕ, e ∈ minGens I ∧ e.support = F) ∧
      (∀ F G : Finset σ, F ∈ supportComplex I → G ∈ supportComplex I → F ≠ G →
        ({E : Finset σ | E ∈ supportComplex I ∧ E ⊆ F ∪ G} = {F, G}) →
        ∀ u v : σ →₀ ℕ, u ∈ minGens I → v ∈ minGens I →
          u.support = F → v.support = G →
          ∀ i : σ, i ∈ F → i ∈ G → u i = v i) := by
  constructor
  · exact lem42_oneGenerator hmpv hsp hstd
  · intro F G hF hG hFG hIso u v hu hv hsuppU hsuppV i hiF hiG
    exact lem42_isolatedEqualExponents hmpv hsp hstd hF hG hFG hIso
      hu hv hsuppU hsuppV hiF hiG

/-- Lemma 4.2(i), using the standard symbolic-power formula proved in
    `Eq2_StandardSymbolic` rather than taking it as a separate input. -/
theorem lem42_oneGenerator_of_mpv [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hmpv : MPVHypotheses I A a) (hsp : SupportPreserving I) :
    ∀ F ∈ supportComplex I, ∃! e : σ →₀ ℕ, e ∈ minGens I ∧ e.support = F := by
  have hstd : HasStdSymbolicFormula I
      (fun j => (purePower (A j) (a j) : Ideal (MvPolynomial σ K))) :=
    eq2_standardSymbolic (I := I) (A := A) (a := a) hmpv.1 hmpv.2.1
  exact lem42_oneGenerator hmpv hsp hstd

/-- Lemma 4.2(ii), using the standard symbolic-power formula proved in
    `Eq2_StandardSymbolic` rather than taking it as a separate input. -/
theorem lem42_isolatedEqualExponents_of_mpv [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hmpv : MPVHypotheses I A a) (hsp : SupportPreserving I)
    {F G : Finset σ} (hF : F ∈ supportComplex I) (hG : G ∈ supportComplex I)
    (hFG : F ≠ G)
    (hIso : {E : Finset σ | E ∈ supportComplex I ∧ E ⊆ F ∪ G} = {F, G})
    {u v : σ →₀ ℕ} (hu : u ∈ minGens I) (hv : v ∈ minGens I)
    (hsuppU : u.support = F) (hsuppV : v.support = G)
    {i : σ} (hiF : i ∈ F) (hiG : i ∈ G) : u i = v i := by
  have hstd : HasStdSymbolicFormula I
      (fun j => (purePower (A j) (a j) : Ideal (MvPolynomial σ K))) :=
    eq2_standardSymbolic (I := I) (A := A) (a := a) hmpv.1 hmpv.2.1
  exact lem42_isolatedEqualExponents hmpv hsp hstd hF hG hFG hIso
    hu hv hsuppU hsuppV hiF hiG

/-- Both parts of Lemma 4.2, with Equation (2) discharged by
    `Eq2_StandardSymbolic`. -/
theorem lem42_of_mpv [Fintype ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hmpv : MPVHypotheses I A a) (hsp : SupportPreserving I) :
    (∀ F ∈ supportComplex I, ∃! e : σ →₀ ℕ, e ∈ minGens I ∧ e.support = F) ∧
      (∀ F G : Finset σ, F ∈ supportComplex I → G ∈ supportComplex I → F ≠ G →
        ({E : Finset σ | E ∈ supportComplex I ∧ E ⊆ F ∪ G} = {F, G}) →
        ∀ u v : σ →₀ ℕ, u ∈ minGens I → v ∈ minGens I →
          u.support = F → v.support = G →
          ∀ i : σ, i ∈ F → i ∈ G → u i = v i) := by
  have hstd : HasStdSymbolicFormula I
      (fun j => (purePower (A j) (a j) : Ideal (MvPolynomial σ K))) :=
    eq2_standardSymbolic (I := I) (A := A) (a := a) hmpv.1 hmpv.2.1
  exact lem42 hmpv hsp hstd

end SimisFormal
