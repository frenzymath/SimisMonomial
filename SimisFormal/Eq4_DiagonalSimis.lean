import SimisFormal.Defs
import SimisFormal.Basic
import SimisFormal.Eq2_StandardSymbolic
import SimisFormal.Eq2_GroupedSymbolic
import SimisFormal.MonomialDecompExists

namespace SimisFormal
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [Field K] [DecidableEq σ] [Fintype σ]
noncomputable section
omit [DecidableEq σ] [Fintype σ] in
/-- Positive diagonal multiplication is inverted coordinatewise by floor division. -/
theorem eq4_floorDiv_diagExp {d : σ → ℕ} (hd : ∀ i, 0 < d i) (e : σ →₀ ℕ) :
    floorDiv d (diagExp d e) = e := by
  ext i
  simp only [floorDiv_apply, diagExp_apply]
  rw [Nat.mul_comm]
  exact Nat.mul_div_right (e i) (hd i)

omit [DecidableEq σ] [Fintype σ] in
/-- A diagonal map sends one pure-power generator to the correspondingly weighted generator. -/
theorem eq4_diagExp_single {d : σ → ℕ} (i : σ) (n : ℕ) :
    diagExp d (Finsupp.single i n) = Finsupp.single i (n * d i) := by
  ext k
  by_cases hki : k = i
  · subst k
    simp
  · simp [hki]

omit [DecidableEq σ] [Fintype σ] in
/-- Ordinary powers of a monomial ideal are monomial. -/
theorem eq4_isMonomialIdeal_pow {I : Ideal (MvPolynomial σ K)}
    (hI : IsMonomialIdeal I) (n : ℕ) : IsMonomialIdeal (I ^ n) := by
  rcases hI with ⟨S, hS⟩
  refine ⟨powGens S n, ?_⟩
  rw [hS]
  exact monomialIdeal_pow (K := K) S n

omit [DecidableEq σ] [Fintype σ] in
/-- Pure-power components are monomial. -/
theorem eq4_isMonomialIdeal_purePower (A : Finset σ) (a : σ → ℕ) :
    IsMonomialIdeal (purePower A a : Ideal (MvPolynomial σ K)) := by
  refine ⟨{e : σ →₀ ℕ | ∃ i ∈ A, e = Finsupp.single i (a i)}, rfl⟩

omit [Fintype σ] in
/-- A finite intersection of monomial ideals is monomial. -/
theorem eq4_isMonomialIdeal_iInf {ι : Type*} [Fintype ι]
    {I : ι → Ideal (MvPolynomial σ K)} (hI : ∀ j, IsMonomialIdeal (I j)) :
    IsMonomialIdeal (⨅ j, I j) := by
  classical
  choose S hS using hI
  refine ⟨iInfGens S, ?_⟩
  simpa only [hS] using (monomialIdeal_iInf (K := K) S)

omit [Fintype σ] in
/-- An intersection omitting one pure-power component is monomial. -/
theorem eq4_isMonomialIdeal_decompOmit {ι : Type*} [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ} (j : ι) :
    IsMonomialIdeal (decompOmit A a j : Ideal (MvPolynomial σ K)) := by
  classical
  unfold decompOmit
  exact eq4_isMonomialIdeal_iInf (fun k =>
    eq4_isMonomialIdeal_purePower (A k.1) (a k.1))

/-- A diagonal image of a monomial ideal is monomial. -/
theorem eq4_isMonomialIdeal_diagonal {I : Ideal (MvPolynomial σ K)}
    (d : σ → ℕ) (hI : IsMonomialIdeal I) : IsMonomialIdeal (diagonal d I) := by
  rcases hI with ⟨S, hS⟩
  refine ⟨diagExp d '' S, ?_⟩
  rw [hS]
  exact diagonal_monomialIdeal (K := K) d S

omit [Fintype σ] in
/-- Equality of monomial ideals is detected by membership of monic monomials. -/
theorem eq4_eq_of_monomial_mem {I J : Ideal (MvPolynomial σ K)}
    (hI : IsMonomialIdeal I) (hJ : IsMonomialIdeal J)
    (h : ∀ e : σ →₀ ℕ,
      (monomial e (1 : K) : MvPolynomial σ K) ∈ I ↔ monomial e (1 : K) ∈ J) :
    I = J := by
  rcases hI with ⟨S, hS⟩
  rcases hJ with ⟨T, hT⟩
  rw [hS, hT] at h ⊢
  rw [monomialIdeal_eq_iff]
  intro e
  simpa only [monomial_mem_monomialIdeal] using h e

/-- Positive diagonal weighting is injective on monomial ideals. -/
theorem eq4_diagonal_injective {d : σ → ℕ} (hd : ∀ i, 0 < d i)
    {I J : Ideal (MvPolynomial σ K)}
    (hI : IsMonomialIdeal I) (hJ : IsMonomialIdeal J)
    (hIJ : diagonal d I = diagonal d J) : I = J := by
  apply eq4_eq_of_monomial_mem hI hJ
  intro e
  constructor
  · intro he
    have hI' : (monomial (diagExp d e) (1 : K) : MvPolynomial σ K) ∈ diagonal d I :=
      (monomial_mem_diagonal (K := K) hI hd (e := diagExp d e)).mpr (by
        simpa only [eq4_floorDiv_diagExp hd e] using he)
    have hJ' : (monomial (diagExp d e) (1 : K) : MvPolynomial σ K) ∈ diagonal d J :=
      hIJ ▸ hI'
    have hfloor := (monomial_mem_diagonal (K := K) hJ hd (e := diagExp d e)).mp hJ'
    simpa only [eq4_floorDiv_diagExp hd e] using hfloor
  · intro he
    have hJ' : (monomial (diagExp d e) (1 : K) : MvPolynomial σ K) ∈ diagonal d J :=
      (monomial_mem_diagonal (K := K) hJ hd (e := diagExp d e)).mpr (by
        simpa only [eq4_floorDiv_diagExp hd e] using he)
    have hI' : (monomial (diagExp d e) (1 : K) : MvPolynomial σ K) ∈ diagonal d I :=
      hIJ.symm ▸ hJ'
    have hfloor := (monomial_mem_diagonal (K := K) hI hd (e := diagExp d e)).mp hI'
    simpa only [eq4_floorDiv_diagExp hd e] using hfloor

/-- Weighting a pure-power component multiplies its displayed exponents. -/
theorem eq4_diagonal_purePower (d : σ → ℕ) (A : Finset σ) (a : σ → ℕ) :
    diagonal d (purePower A a : Ideal (MvPolynomial σ K)) =
      purePower A (fun i => a i * d i) := by
  unfold purePower
  rw [diagonal_monomialIdeal]
  apply monomialIdeal_eq_iff.mpr
  intro e
  constructor
  · rintro ⟨z, ⟨u, ⟨i, hiA, rfl⟩, rfl⟩, hzle⟩
    refine ⟨Finsupp.single i (a i * d i), ⟨i, hiA, rfl⟩, ?_⟩
    simpa only [eq4_diagExp_single] using hzle
  · rintro ⟨v, ⟨i, hiA, rfl⟩, hvle⟩
    refine ⟨diagExp d (Finsupp.single i (a i)),
      ⟨Finsupp.single i (a i), ⟨i, hiA, rfl⟩, rfl⟩, ?_⟩
    simpa only [eq4_diagExp_single] using hvle

/-- Positive diagonal weighting commutes with finite intersections of monomial ideals,
and hence with the componentwise symbolic-power formula. -/
theorem eq4_diagonal_componentSymbolic {ι : Type*} [Fintype ι]
    {Q : ι → Ideal (MvPolynomial σ K)} (hQ : ∀ j, IsMonomialIdeal (Q j))
    {d : σ → ℕ} (hd : ∀ i, 0 < d i) (q : ℕ) :
    diagonal d (componentSymbolic Q q) =
      componentSymbolic (fun j => diagonal d (Q j)) q := by
  classical
  have hC : IsMonomialIdeal (componentSymbolic Q q) := by
    unfold componentSymbolic
    exact eq4_isMonomialIdeal_iInf (fun j => eq4_isMonomialIdeal_pow (hQ j) q)
  have hD : IsMonomialIdeal
      (componentSymbolic (fun j => diagonal d (Q j)) q) := by
    unfold componentSymbolic
    exact eq4_isMonomialIdeal_iInf (fun j =>
      eq4_isMonomialIdeal_pow (eq4_isMonomialIdeal_diagonal d (hQ j)) q)
  apply eq4_eq_of_monomial_mem (eq4_isMonomialIdeal_diagonal d hC) hD
  intro e
  rw [monomial_mem_diagonal (K := K) hC hd]
  simp only [componentSymbolic, Ideal.mem_iInf]
  constructor
  · intro h j
    have hpow : IsMonomialIdeal (Q j ^ q) := eq4_isMonomialIdeal_pow (hQ j) q
    have hm : (monomial e (1 : K) : MvPolynomial σ K) ∈ diagonal d (Q j ^ q) :=
      (monomial_mem_diagonal (K := K) hpow hd).mpr (h j)
    simpa only [diagonal, Ideal.map_pow] using hm
  · intro h j
    have hpow : IsMonomialIdeal (Q j ^ q) := eq4_isMonomialIdeal_pow (hQ j) q
    have hm : (monomial e (1 : K) : MvPolynomial σ K) ∈ diagonal d (Q j ^ q) := by
      simpa only [diagonal, Ideal.map_pow] using h j
    exact (monomial_mem_diagonal (K := K) hpow hd).mp hm

/-- Positive diagonal weighting commutes with a finite intersection of monomial ideals. -/
theorem eq4_diagonal_iInf {ι : Type*} [Fintype ι]
    {Q : ι → Ideal (MvPolynomial σ K)} (hQ : ∀ j, IsMonomialIdeal (Q j))
    {d : σ → ℕ} (hd : ∀ i, 0 < d i) :
    diagonal d (⨅ j, Q j) = ⨅ j, diagonal d (Q j) := by
  simpa only [componentSymbolic, pow_one] using
    (eq4_diagonal_componentSymbolic hQ hd 1)

/-- Positive diagonal weighting preserves and reflects inclusions of monomial ideals. -/
theorem eq4_diagonal_le_iff_le {d : σ → ℕ} (hd : ∀ i, 0 < d i)
    {I J : Ideal (MvPolynomial σ K)}
    (hI : IsMonomialIdeal I) (hJ : IsMonomialIdeal J) :
    diagonal d I ≤ diagonal d J ↔ I ≤ J := by
  constructor
  · intro hle
    rcases hI with ⟨S, hS⟩
    rcases hJ with ⟨T, hT⟩
    rw [hS, hT] at hle ⊢
    rw [monomialIdeal_le_iff]
    intro e he
    have heI : (monomial e (1 : K) : MvPolynomial σ K) ∈ monomialIdeal S :=
      monomial_mem_monomialIdeal.mpr he
    have hdiagI : (monomial (diagExp d e) (1 : K) : MvPolynomial σ K) ∈
        diagonal d (monomialIdeal S : Ideal (MvPolynomial σ K)) :=
      (monomial_mem_diagonal_monomialIdeal (K := K) hd S (e := diagExp d e)).mpr (by
        simpa only [eq4_floorDiv_diagExp hd e] using heI)
    have hdiagJ : (monomial (diagExp d e) (1 : K) : MvPolynomial σ K) ∈
        diagonal d (monomialIdeal T : Ideal (MvPolynomial σ K)) := hle hdiagI
    have hfloor :=
      (monomial_mem_diagonal_monomialIdeal (K := K) hd T (e := diagExp d e)).mp hdiagJ
    have heJ : (monomial e (1 : K) : MvPolynomial σ K) ∈ monomialIdeal T := by
      simpa only [eq4_floorDiv_diagExp hd e] using hfloor
    exact monomial_mem_monomialIdeal.mp heJ
  · intro hle
    simpa only [diagonal] using (Ideal.map_mono hle)

/-- Weighting commutes with the intersection omitting one component. -/
theorem eq4_diagonal_decompOmit {ι : Type*} [Fintype ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ} {d : σ → ℕ} (hd : ∀ i, 0 < d i) (j : ι) :
    diagonal d (decompOmit A a j : Ideal (MvPolynomial σ K)) =
      decompOmit A (fun j i => a j i * d i) j := by
  classical
  unfold decompOmit
  rw [eq4_diagonal_iInf (fun k : {k : ι // k ≠ j} =>
    eq4_isMonomialIdeal_purePower (A k.1) (a k.1)) hd]
  apply iInf_congr
  intro k
  exact eq4_diagonal_purePower d (A k.1) (a k.1)

/-- The external symbolic-power input needed for a short proof of Eq. (4). It says that all
relevant symbolic powers are monomial and that weighting commutes with them. -/
def Eq4SymbolicTransfer (J : Ideal (MvPolynomial σ K)) (d : σ → ℕ) : Prop :=
  (∀ q : ℕ, 1 ≤ q → IsMonomialIdeal (symbolicPower J q)) ∧
    (∀ q : ℕ, 1 ≤ q →
      diagonal d (symbolicPower J q) = symbolicPower (diagonal d J) q)

/-- Eq. (4), reduced to the two symbolic-power facts in `Eq4SymbolicTransfer`. -/
theorem eq4_isSimis_diagonal_iff {J : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hJ : IsMonomialIdeal J) (hd : ∀ i, 0 < d i) (ht : Eq4SymbolicTransfer J d) :
    IsSimis J ↔ IsSimis (diagonal d J) := by
  constructor
  · intro hJsim q hq
    calc
      symbolicPower (diagonal d J) q = diagonal d (symbolicPower J q) :=
        (ht.2 q hq).symm
      _ = diagonal d (J ^ q) := by rw [hJsim q hq]
      _ = diagonal d J ^ q := by
        simpa only [diagonal] using (Ideal.map_pow (diagHom (K := K) d) J q)
  · intro hDsim q hq
    apply eq4_diagonal_injective hd (ht.1 q hq) (eq4_isMonomialIdeal_pow hJ q)
    calc
      diagonal d (symbolicPower J q) = symbolicPower (diagonal d J) q := ht.2 q hq
      _ = diagonal d J ^ q := hDsim q hq
      _ = diagonal d (J ^ q) := by
        simpa only [diagonal] using (Ideal.map_pow (diagHom (K := K) d) J q).symm

/-- Eq. (4) when Eq. (2) has been supplied for both `J` and its positive diagonal image. -/
theorem eq4_isSimis_diagonal_iff_of_stdSymbolic {ι : Type*} [Fintype ι]
    {J : Ideal (MvPolynomial σ K)} {Q : ι → Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hJ : IsMonomialIdeal J) (hQ : ∀ j, IsMonomialIdeal (Q j))
    (hd : ∀ i, 0 < d i)
    (hstdJ : HasStdSymbolicFormula J Q)
    (hstdD : HasStdSymbolicFormula (diagonal d J) (fun j => diagonal d (Q j))) :
    IsSimis J ↔ IsSimis (diagonal d J) := by
  have hmonSym : ∀ q : ℕ, 1 ≤ q → IsMonomialIdeal (symbolicPower J q) := by
    intro q hq
    rw [hstdJ q hq]
    unfold componentSymbolic
    exact eq4_isMonomialIdeal_iInf (fun j => eq4_isMonomialIdeal_pow (hQ j) q)
  have hcomm : ∀ q : ℕ, 1 ≤ q →
      diagonal d (symbolicPower J q) = symbolicPower (diagonal d J) q := by
    intro q hq
    calc
      diagonal d (symbolicPower J q) = diagonal d (componentSymbolic Q q) := by
        rw [hstdJ q hq]
      _ = componentSymbolic (fun j => diagonal d (Q j)) q :=
        eq4_diagonal_componentSymbolic hQ hd q
      _ = symbolicPower (diagonal d J) q := (hstdD q hq).symm
  exact eq4_isSimis_diagonal_iff hJ hd ⟨hmonSym, hcomm⟩

/-- The form of Eq. (4) using an explicit irreducible-component family. The two
`HasStdSymbolicFormula` hypotheses are the formal counterpart of Eq. (2) before and after
weighting; together with positivity they discharge `Eq4SymbolicTransfer`. -/
theorem eq4_isSimis_diagonal_iff_of_stdPurePower {ι : Type*} [Fintype ι]
    {J : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} {d : σ → ℕ}
    (hJ : IsMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hstdJ : HasStdSymbolicFormula J (fun j => purePower (A j) (a j)))
    (hstdD : HasStdSymbolicFormula (diagonal d J)
      (fun j => purePower (A j) (fun i => a j i * d i))) :
    IsSimis J ↔ IsSimis (diagonal d J) := by
  have hQ : ∀ j, IsMonomialIdeal (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) := by
    intro j
    refine ⟨{e : σ →₀ ℕ | ∃ i ∈ A j, e = Finsupp.single i (a j i)}, rfl⟩
  have hstdD' : HasStdSymbolicFormula (diagonal d J)
      (fun j => diagonal d (purePower (A j) (a j) : Ideal (MvPolynomial σ K))) := by
    intro q hq
    simpa only [componentSymbolic, eq4_diagonal_purePower] using hstdD q hq
  exact eq4_isSimis_diagonal_iff_of_stdSymbolic hJ hQ hd hstdJ hstdD'

/-- Eq. (4) for a finite irredundant antichain decomposition. Equation (2) supplies the
symbolic formula before and after weighting; hence no symbolic formula is assumed here. -/
theorem eq4_isSimis_diagonal_iff_of_irredundantDecomp {ι : Type*} [Fintype ι]
    {J : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} {d : σ → ℕ}
    (hd : ∀ i, 0 < d i) (hdecomp : IsIrredundantDecomp J A a)
    (hanti : SupportsAntichain A a) :
    IsSimis J ↔ IsSimis (diagonal d J) := by
  rcases hdecomp with ⟨hcompJ, hirrJ⟩
  have hQ : ∀ j, IsMonomialIdeal (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) :=
    fun j => eq4_isMonomialIdeal_purePower (A j) (a j)
  have hJmon : IsMonomialIdeal J := by
    rw [hcompJ]
    exact eq4_isMonomialIdeal_iInf hQ
  have hstdJ : HasStdSymbolicFormula J (fun j => purePower (A j) (a j)) :=
    eq2_standardSymbolic (K := K) (show IsIrredundantDecomp J A a from ⟨hcompJ, hirrJ⟩) hanti
  have hcompD : HasComponents (diagonal d J) A (fun j i => a j i * d i) := by
    change diagonal d J = ⨅ j, (purePower (A j) (fun i => a j i * d i) :
      Ideal (MvPolynomial σ K))
    rw [hcompJ]
    rw [eq4_diagonal_iInf hQ hd]
    apply iInf_congr
    intro j
    exact eq4_diagonal_purePower d (A j) (a j)
  have hirrD : IsIrredundant (K := K) A (fun j i => a j i * d i) := by
    intro j hleD
    have hleDiag : diagonal d (decompOmit A a j : Ideal (MvPolynomial σ K)) ≤
        diagonal d (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) := by
      simpa only [eq4_diagonal_decompOmit hd, eq4_diagonal_purePower] using hleD
    have hleJ : (decompOmit A a j : Ideal (MvPolynomial σ K)) ≤ purePower (A j) (a j) :=
      (eq4_diagonal_le_iff_le
        (I := (decompOmit A a j : Ideal (MvPolynomial σ K)))
        (J := (purePower (A j) (a j) : Ideal (MvPolynomial σ K))) hd
        (eq4_isMonomialIdeal_decompOmit j) (eq4_isMonomialIdeal_purePower (A j) (a j))).mp
          hleDiag
    exact hirrJ j hleJ
  have hantiD : SupportsAntichain A (fun j i => a j i * d i) := by
    intro j k hsub
    exact hanti j k hsub
  have hstdD : HasStdSymbolicFormula (diagonal d J)
      (fun j => purePower (A j) (fun i => a j i * d i)) :=
    eq2_standardSymbolic (K := K)
      (show IsIrredundantDecomp (diagonal d J) A (fun j i => a j i * d i) from
        ⟨hcompD, hirrD⟩) hantiD
  exact eq4_isSimis_diagonal_iff_of_stdPurePower hJmon hd hstdJ hstdD

/-- A finite family of monomial components for which Eq. (2) holds both before and after
positive diagonal weighting. This is the precise existence input used below when embedded
primes are allowed. It is not proved here. An irredundant pure-power decomposition need not
have pairwise incomparable supports, so `eq2_standardSymbolic` cannot be applied directly to
one without first grouping and discarding nonminimal components. -/
def HasFiniteDiagonalStdSymbolicData (J : Ideal (MvPolynomial σ K)) (d : σ → ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (Q : ι → Ideal (MvPolynomial σ K)),
    (∀ j, IsMonomialIdeal (Q j)) ∧
      HasStdSymbolicFormula J Q ∧
        HasStdSymbolicFormula (diagonal d J) (fun j => diagonal d (Q j))

/-- Eq. (4) reduced to the clearly named existence of finite standard symbolic data.
This avoids asserting the false claim that every monomial ideal has a finite irredundant
pure-power decomposition whose supports form an antichain. -/
theorem eq4_isSimis_diagonal_iff_of_exists_stdSymbolic
    {J : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hJ : IsMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hdata : HasFiniteDiagonalStdSymbolicData J d) :
    IsSimis J ↔ IsSimis (diagonal d J) := by
  rcases hdata with ⟨ι, instι, Q, hQ, hstdJ, hstdD⟩
  let inst : Fintype ι := instι
  exact eq4_isSimis_diagonal_iff_of_stdSymbolic hJ hQ hd hstdJ hstdD

/-- Eq. (4) without an antichain assumption: Eq. (2) is supplied by the grouped version,
which permits repeated and embedded component radicals. -/
theorem eq4_isSimis_diagonal_iff_of_irredDecomp_grouped {ι : Type*} [Fintype ι]
    {J : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ} {d : σ → ℕ}
    (hd : ∀ i, 0 < d i) (hdecomp : IsIrredundantDecomp J A a) :
    IsSimis J ↔ IsSimis (diagonal d J) := by
  classical
  have hdecompJ : IsIrredundantDecomp J A a := hdecomp
  rcases hdecomp with ⟨hcompJ, hirrJ⟩
  have hQ : ∀ j, IsMonomialIdeal (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) :=
    fun j => eq4_isMonomialIdeal_purePower (A j) (a j)
  have hJmon : IsMonomialIdeal J := by
    rw [hcompJ]
    exact eq4_isMonomialIdeal_iInf hQ
  have hposJ : ∀ j i, i ∈ A j → 0 < a j i :=
    exponents_pos_of_irredundant (K := K) hirrJ
  have hcompD : HasComponents (diagonal d J) A (fun j i => a j i * d i) := by
    change diagonal d J = ⨅ j, (purePower (A j) (fun i => a j i * d i) :
      Ideal (MvPolynomial σ K))
    rw [hcompJ]
    rw [eq4_diagonal_iInf hQ hd]
    apply iInf_congr
    intro j
    exact eq4_diagonal_purePower d (A j) (a j)
  have hirrD : IsIrredundant (K := K) A (fun j i => a j i * d i) := by
    intro j hleD
    have hleDiag : diagonal d (decompOmit A a j : Ideal (MvPolynomial σ K)) ≤
        diagonal d (purePower (A j) (a j) : Ideal (MvPolynomial σ K)) := by
      simpa only [eq4_diagonal_decompOmit hd, eq4_diagonal_purePower] using hleD
    have hleJ : (decompOmit A a j : Ideal (MvPolynomial σ K)) ≤ purePower (A j) (a j) :=
      (eq4_diagonal_le_iff_le
        (I := (decompOmit A a j : Ideal (MvPolynomial σ K)))
        (J := (purePower (A j) (a j) : Ideal (MvPolynomial σ K))) hd
        (eq4_isMonomialIdeal_decompOmit j) (eq4_isMonomialIdeal_purePower (A j) (a j))).mp
          hleDiag
    exact hirrJ j hleJ
  have hdecompD : IsIrredundantDecomp (diagonal d J) A (fun j i => a j i * d i) :=
    ⟨hcompD, hirrD⟩
  have hposD : ∀ j i, i ∈ A j → 0 < a j i * d i :=
    exponents_pos_of_irredundant (K := K) hirrD
  have hradJ : J.radical = ⨅ j, (primeOf (A j) : Ideal (MvPolynomial σ K)) := by
    rw [hcompJ]
    exact radical_iInf_purePower_of_pos (K := K) hposJ
  have hradD : (diagonal d J).radical = ⨅ j, (primeOf (A j) : Ideal (MvPolynomial σ K)) := by
    rw [hcompD]
    exact radical_iInf_purePower_of_pos (K := K) hposD
  have hradEq : J.radical = (diagonal d J).radical := hradJ.trans hradD.symm
  have hminEq : J.minimalPrimes = (diagonal d J).minimalPrimes := by
    calc
      J.minimalPrimes = J.radical.minimalPrimes :=
        (Ideal.radical_minimalPrimes (I := J)).symm
      _ = (diagonal d J).radical.minimalPrimes := by rw [hradEq]
      _ = (diagonal d J).minimalPrimes :=
        Ideal.radical_minimalPrimes (I := diagonal d J)
  have hfinJ : J.minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial σ K) J
  let instMin : Fintype J.minimalPrimes := hfinJ.fintype
  let e : J.minimalPrimes ≃ (diagonal d J).minimalPrimes := Equiv.setCongr hminEq
  have hQgroup : ∀ P : J.minimalPrimes,
      IsMonomialIdeal (groupedComponents J A a P) :=
    fun P => groupedComponents_isMonomialIdeal (K := K) J A a P
  have hgroup : ∀ P : J.minimalPrimes,
      diagonal d (groupedComponents J A a P) =
        groupedComponents (diagonal d J) A (fun j i => a j i * d i) (e P) := by
    intro P
    let P' : (diagonal d J).minimalPrimes := ⟨P.1, by
      rw [← hminEq]
      exact P.2⟩
    have heq : e P = P' := by
      apply Subtype.ext
      rfl
    rw [heq]
    change diagonal d (⨅ j : {j : ι // primeOf (A j) = P.1},
        (purePower (A j.1) (a j.1) : Ideal (MvPolynomial σ K))) =
      ⨅ j : {j : ι // primeOf (A j) = P.1},
        (purePower (A j.1) (fun i => a j.1 i * d i) : Ideal (MvPolynomial σ K))
    rw [eq4_diagonal_iInf (fun j : {j : ι // primeOf (A j) = P.1} =>
      eq4_isMonomialIdeal_purePower (A j.1) (a j.1)) hd]
    apply iInf_congr
    intro j
    exact eq4_diagonal_purePower d (A j.1) (a j.1)
  have hreindex : ∀ q : ℕ,
      componentSymbolic (fun P : J.minimalPrimes => diagonal d (groupedComponents J A a P)) q =
        componentSymbolic (groupedComponents (diagonal d J) A (fun j i => a j i * d i)) q := by
    intro q
    unfold componentSymbolic
    calc
      (⨅ P : J.minimalPrimes, (diagonal d (groupedComponents J A a P)) ^ q) =
          ⨅ P : J.minimalPrimes,
            (groupedComponents (diagonal d J) A (fun j i => a j i * d i) (e P)) ^ q := by
        apply iInf_congr
        intro P
        rw [hgroup P]
      _ = ⨅ P : (diagonal d J).minimalPrimes,
            (groupedComponents (diagonal d J) A (fun j i => a j i * d i) P) ^ q :=
        Equiv.iInf_comp (g := fun P : (diagonal d J).minimalPrimes =>
          (groupedComponents (diagonal d J) A (fun j i => a j i * d i) P) ^ q) e
  have hstdJ : HasStdSymbolicFormula J (groupedComponents J A a) :=
    eq2_groupedSymbolic (K := K) hdecompJ
  have hstdD0 : HasStdSymbolicFormula (diagonal d J)
      (groupedComponents (diagonal d J) A (fun j i => a j i * d i)) :=
    eq2_groupedSymbolic (K := K) hdecompD
  have hstdD : HasStdSymbolicFormula (diagonal d J)
      (fun P : J.minimalPrimes => diagonal d (groupedComponents J A a P)) := by
    intro q hq
    calc
      symbolicPower (diagonal d J) q =
          componentSymbolic (groupedComponents (diagonal d J) A (fun j i => a j i * d i)) q :=
        hstdD0 q hq
      _ = componentSymbolic
          (fun P : J.minimalPrimes => diagonal d (groupedComponents J A a P)) q :=
        (hreindex q).symm
  exact eq4_isSimis_diagonal_iff_of_stdSymbolic hJmon hQgroup hd hstdJ hstdD

/-- Eq. (4) for every monomial ideal: the standard diagonal weighting preserves and
reflects the Simis property. Embedded primes are allowed. -/
theorem eq4_isSimis_diagonal_iff_of_isMonomialIdeal
    {J : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hJ : IsMonomialIdeal J) (hd : ∀ i, 0 < d i) :
    IsSimis J ↔ IsSimis (diagonal d J) := by
  rcases hasFiniteIrredundantDecomp_of_isMonomialIdeal (K := K) hJ with
    ⟨κ, instκ, A, a, hdecomp⟩
  let inst : Fintype κ := instκ
  exact eq4_isSimis_diagonal_iff_of_irredDecomp_grouped (K := K) hd hdecomp

end
end SimisFormal
