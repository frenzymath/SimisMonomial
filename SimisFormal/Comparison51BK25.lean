import SimisFormal.Defs
import SimisFormal.Comparison5_1
import SimisFormal.Eq2_StandardSymbolic
import SimisFormal.Eq4_DiagonalSimis
import SimisFormal.Cor5_3
import SimisFormal.Comparison51Unused

namespace SimisFormal
open MvPolynomial
variable {σ K ι : Type*} [Field K] [DecidableEq σ]
/-- Condition (13) gives the at-most-one-intervenor hypothesis for each mismatched pair. -/
theorem comparison51_bk25_atMostOneIntervenor_of_mismatch
    [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hcond : comparison51_Condition13 A a)
    {j k : ι}
    (hmis : ∃ i, i ∈ A j ∧ i ∈ A k ∧ a j i ≠ a k i) :
    _root_.thm52_AtMostOneIntervenor A j k := by
  classical
  rcases hmis with ⟨i, hiAj, hiAk, hne⟩
  have hjk : j ≠ k := by
    intro h
    subst k
    exact hne rfl
  have hNcomm : comparison51_N A j k = comparison51_N A k j := by
    ext r
    simp only [comparison51_N, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hrj, hrk, hsub⟩
      refine ⟨hrk, hrj, ?_⟩
      intro x hx
      rcases Finset.mem_union.mp (hsub hx) with hxj | hxk
      · exact Finset.mem_union.mpr (Or.inr hxj)
      · exact Finset.mem_union.mpr (Or.inl hxk)
    · rintro ⟨hrk, hrj, hsub⟩
      refine ⟨hrj, hrk, ?_⟩
      intro x hx
      rcases Finset.mem_union.mp (hsub hx) with hxk | hxj
      · exact Finset.mem_union.mpr (Or.inr hxk)
      · exact Finset.mem_union.mpr (Or.inl hxj)
  intro x y hx _hy
  have hxN : x ∈ comparison51_N A j k := by
    simpa [comparison51_N, _root_.thm52_isIntervenor] using hx
  rcases lt_or_gt_of_ne hjk with hlt | hgt
  · have hp : (j, k) ∈ prop21_XI A a :=
      ⟨hlt, ⟨i, hiAj, hiAk, hne⟩⟩
    have hN : comparison51_N A j k = ∅ := hcond (j, k) hp
    exfalso
    simp [hN] at hxN
  · have hp : (k, j) ∈ prop21_XI A a :=
      ⟨hgt, ⟨i, hiAk, hiAj, fun heq ↦ hne heq.symm⟩⟩
    have hN : comparison51_N A k j = ∅ := hcond (k, j) hp
    exfalso
    simp [hNcomm, hN] at hxN

/-- Under condition (13), equality of the second symbolic and ordinary powers forces
component exponents to agree at every shared variable. -/
theorem comparison51_bk25_exponentCoherence
    [Fintype σ] [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hdec : IsIrredundantDecomp I A a)
    (hanti : SupportsAntichain A a)
    (hcond : comparison51_Condition13 A a)
    (hsymbolic2 : symbolicPower I 2 = I ^ 2) :
    ∀ j k i, i ∈ A j → i ∈ A k → a j i = a k i := by
  classical
  have hpos : ∀ j i, i ∈ A j → 0 < a j i :=
    exponents_pos_of_irredundant (K := K) hdec.2
  have hsym : HasStdSymbolicFormula I
      (fun j ↦ (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K))) :=
    eq2_standardSymbolic (K := K) hdec hanti
  have hcomp : I ^ 2 =
      componentSymbolic (fun j ↦ (purePower (K := K) (A j) (a j) :
        Ideal (MvPolynomial σ K))) 2 :=
    hsymbolic2.symm.trans (hsym 2 (by norm_num))
  have hglobal :
      (⨅ j, (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K))) ^ 2 =
        ⨅ j, (purePower (K := K) (A j) (a j) : Ideal (MvPolynomial σ K)) ^ 2 := by
    rw [← hdec.1]
    simpa [componentSymbolic] using hcomp
  intro j k i hiAj hiAk
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hjk : j ≠ k := by
      intro h
      subst k
      exact hne rfl
    exact (_root_.thm52_lem51Obstruction_holds (K := K) A a hanti hpos hjk
      hiAj hiAk hlt
      (comparison51_bk25_atMostOneIntervenor_of_mismatch (A := A) (a := a)
        hcond (j := j) (k := k) ⟨i, hiAj, hiAk, hne⟩)) hglobal
  · have hkj : k ≠ j := by
      intro h
      subst j
      exact hne rfl
    exact (_root_.thm52_lem51Obstruction_holds (K := K) A a hanti hpos hkj
      hiAk hiAj hgt
      (comparison51_bk25_atMostOneIntervenor_of_mismatch (A := A) (a := a)
        hcond (j := k) (k := j) ⟨i, hiAk, hiAj, fun heq ↦ hne heq.symm⟩)) hglobal

/-- The BK25 comparison under the manuscript hypotheses.  The properness, nonzeroness, and
used-variable assumptions are not needed by the derivation and are retained only to match the
stated setting. -/
theorem comparison51_bk25_verified
    [Fintype σ] [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (hdec : IsIrredundantDecomp I A a)
    (hNoEmb : associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) = I.minimalPrimes)
    (hDistinct : ∀ j k, (primeOf (A j) : Ideal (MvPolynomial σ K)) =
      primeOf (A k) → j = k)
    (_hUsed : Finset.univ.biUnion A = Finset.univ)
    (hcond : comparison51_Condition13 A a) :
    IsSimis I ↔ MPVConc I := by
  classical
  have hanti : SupportsAntichain A a :=
    _root_.thm52_supportsAntichain_of_paperHypotheses (K := K)
      hdec hNoEmb hDistinct
  constructor
  · intro hsimis
    have hsymbolic2 : symbolicPower I 2 = I ^ 2 := hsimis 2 (by norm_num)
    have hcoh : ∀ j k i, i ∈ A j → i ∈ A k → a j i = a k i :=
      comparison51_bk25_exponentCoherence hdec hanti hcond hsymbolic2
    have hX : prop21_XI A a = ∅ := by
      ext p
      constructor
      · intro hp
        rcases p with ⟨j, k⟩
        rcases hp with ⟨_, ⟨i, hiAj, hiAk, hne⟩⟩
        exact (hne (hcoh j k i hiAj hiAk)).elim
      · intro hp
        cases hp
    have hroot : HasSqRoot I :=
      (prop21_hasSqRoot_iff_XI_eq_empty (K := K) hdec.1 hdec.2).mpr hX
    rcases hroot with ⟨J, d, hJsq, hd, hdiag⟩
    have hJmono : IsMonomialIdeal J := by
      rcases hJsq with ⟨H, hH⟩
      exact ⟨characteristicExp '' H, hH⟩
    have hJsim : IsSimis J :=
      (eq4_isSimis_diagonal_iff_of_isMonomialIdeal (K := K) (J := J) (d := d)
        hJmono hd).mpr (by simpa [hdiag] using hsimis)
    exact ⟨J, d, hJsq, hJsim, hd, hdiag⟩
  · rintro ⟨J, d, hJsq, hJsim, hd, hdiag⟩
    have hJmono : IsMonomialIdeal J := by
      rcases hJsq with ⟨H, hH⟩
      exact ⟨characteristicExp '' H, hH⟩
    have hdiagSimis : IsSimis (diagonal d J) :=
      (eq4_isSimis_diagonal_iff_of_isMonomialIdeal (K := K) (J := J) (d := d)
        hJmono hd).mp hJsim
    simpa [hdiag] using hdiagSimis

/-- Manuscript-shaped wrapper, including the standing nonzero and proper hypotheses. -/
theorem comparison51_bk25
    [Fintype σ] [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (_hI0 : I ≠ ⊥) (_hItop : I ≠ ⊤)
    (hdec : IsIrredundantDecomp I A a)
    (hNoEmb : associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) = I.minimalPrimes)
    (hDistinct : ∀ j k, (primeOf (A j) : Ideal (MvPolynomial σ K)) =
      primeOf (A k) → j = k)
    (_hUsed : Finset.univ.biUnion A = Finset.univ)
    (hcond : comparison51_Condition13 A a) :
    IsSimis I ↔ MPVConc I :=
  comparison51_bk25_verified (K := K) hdec hNoEmb hDistinct _hUsed hcond

/-- Height-two comparison with BK25: condition (11) is automatic for two-element supports. -/
theorem comparison51_bk25_heightTwo
    [Fintype σ] [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (_hI0 : I ≠ ⊥) (_hItop : I ≠ ⊤)
    (hdec : IsIrredundantDecomp I A a)
    (hNoEmb : associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I) = I.minimalPrimes)
    (hDistinct : ∀ j k, (primeOf (A j) : Ideal (MvPolynomial σ K)) =
      primeOf (A k) → j = k)
    (_hUsed : Finset.univ.biUnion A = Finset.univ)
    (hcard : ∀ j, (A j).card = 2) :
    IsSimis I ↔ MPVConc I := by
  classical
  have hanti : SupportsAntichain A a :=
    _root_.thm52_supportsAntichain_of_paperHypotheses (K := K)
      hdec hNoEmb hDistinct
  have hinc : _root_.thm52_IncidenceBound A :=
    _root_.thm52_IncidenceBound_of_card_eq_two hanti hcard
  constructor
  · intro hsimis
    have hcor := cor53_of_paperHypotheses (K := K)
      _hI0 _hItop hdec hNoEmb hDistinct hinc hsimis
    exact hcor.2.1
  · rintro ⟨J, d, hJsq, hJsimis, hd, hdiag⟩
    have hJmono : IsMonomialIdeal J := by
      rcases hJsq with ⟨H, hH⟩
      exact ⟨characteristicExp '' H, hH⟩
    have hdiagSimis : IsSimis (diagonal d J) :=
      (eq4_isSimis_diagonal_iff_of_isMonomialIdeal (K := K) (J := J) (d := d)
        hJmono hd).mp hJsimis
    simpa [hdiag] using hdiagSimis

/-- Unused variables do not let represented MPV examples escape the BK25 criterion. -/
theorem comparison51_representedMPV_noSeparation
    [Fintype σ] [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    {I : Ideal (MvPolynomial σ K)} {A : ι → Finset σ} {a : ι → σ → ℕ}
    (_hI0 : I ≠ ⊥) (_hItop : I ≠ ⊤)
    (hdec : IsIrredundantDecomp I A a)
    (hmpv : MPVConc I) :
    let U := comparison51_usedVariables A
    let A' := comparison51_restrictFinset U A
    let a' := comparison51_restrictWeight U a
    let I' := comparison51_restrictIdeal (K := K) U A a
    IsIrredundantDecomp I' A' a' ∧
      SupportsAntichain A' a' ∧
      Finset.univ.biUnion A' = Finset.univ ∧
      comparison51_Condition13 A' a' ∧
      associatedPrimes (MvPolynomial U K) (MvPolynomial U K ⧸ I') = I'.minimalPrimes ∧
      (∀ j k, (primeOf (A' j) : Ideal (MvPolynomial U K)) =
        primeOf (A' k) → j = k) ∧
      IsSimis I' ∧
      MPVConc I' ∧
      (IsSimis I' ↔ MPVConc I') ∧
      (IsSimis I ↔ IsSimis I') ∧
      (MPVConc I ↔ MPVConc I') := by
  classical
  have hroot : HasSqRoot I := by
    rcases hmpv with ⟨J, d, hJsq, _hJsimis, hd, hdiag⟩
    exact ⟨J, d, hJsq, hd, hdiag⟩
  let U := comparison51_usedVariables A
  let A' := comparison51_restrictFinset U A
  let a' := comparison51_restrictWeight U a
  let I' := comparison51_restrictIdeal (K := K) U A a
  change IsIrredundantDecomp I' A' a' ∧
    SupportsAntichain A' a' ∧
    Finset.univ.biUnion A' = Finset.univ ∧
    comparison51_Condition13 A' a' ∧
    associatedPrimes (MvPolynomial U K) (MvPolynomial U K ⧸ I') = I'.minimalPrimes ∧
    (∀ j k, (primeOf (A' j) : Ideal (MvPolynomial U K)) =
      primeOf (A' k) → j = k) ∧
    IsSimis I' ∧
    MPVConc I' ∧
    (IsSimis I' ↔ MPVConc I') ∧
    (IsSimis I ↔ IsSimis I') ∧
    (MPVConc I ↔ MPVConc I')
  have hp := comparison51_restrict_package (K := K) hdec hroot
  dsimp at hp
  rcases hp with ⟨hdec', hroot', hanti', hUsed, hsimIff, hmpvIff⟩
  have hmpv' : MPVConc I' := hmpvIff.mp hmpv
  have hsimis' : IsSimis I' := by
    rcases hmpv' with ⟨J, d, hJsq, hJsimis, hd, hdiag⟩
    have hJmono : IsMonomialIdeal J := by
      rcases hJsq with ⟨H, hH⟩
      exact ⟨characteristicExp '' H, hH⟩
    have hdiagSimis : IsSimis (diagonal d J) :=
      (eq4_isSimis_diagonal_iff_of_isMonomialIdeal (K := K) (J := J) (d := d)
        hJmono hd).mp hJsimis
    simpa [hdiag] using hdiagSimis
  have hcond' : comparison51_Condition13 A' a' :=
    comparison51_condition13_of_hasSqRoot (K := K) hdec'.1 hdec'.2 hroot'
  have hNoEmb' :
      associatedPrimes (MvPolynomial U K) (MvPolynomial U K ⧸ I') = I'.minimalPrimes :=
    prop21_associatedPrimes_eq_minimalPrimes_of_hasSqRoot (K := K)
      hdec'.1 hdec'.2 hroot'
  have hDistinct' : ∀ j k,
      (primeOf (A' j) : Ideal (MvPolynomial U K)) = primeOf (A' k) → j = k := by
    intro j k hEq
    apply hanti' j k
    intro x hx
    have hxmem :
        (monomial (Finsupp.single x (1 : ℕ)) (1 : K) : MvPolynomial U K) ∈
          (primeOf (A' j) : Ideal (MvPolynomial U K)) := by
      rw [monomial_mem_primeOf]
      exact ⟨x, hx, by simp⟩
    rw [hEq] at hxmem
    rcases monomial_mem_primeOf.mp hxmem with ⟨y, hy, hyle⟩
    have hyx : y = x := by
      by_contra hyne
      have hyzero : Finsupp.single x (1 : ℕ) y = 0 := by
        simp [hyne]
      simp [hyzero] at hyle
    rw [hyx] at hy
    exact hy
  have hBK' : IsSimis I' ↔ MPVConc I' :=
    comparison51_bk25_verified (K := K) hdec' hNoEmb' hDistinct' hUsed hcond'
  exact ⟨hdec', hanti', hUsed, hcond', hNoEmb', hDistinct',
    hsimis', hmpv', hBK', hsimIff, hmpvIff⟩

end SimisFormal
