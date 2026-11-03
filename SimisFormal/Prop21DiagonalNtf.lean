import SimisFormal.Defs
import SimisFormal.Basic
import SimisFormal.Prop2_1
import SimisFormal.DiagAssociatedPreserve

namespace SimisFormal
variable {σ K : Type*} [Field K] [DecidableEq σ]
/-- Unconditional diagonal invariance for monomial ideals and positive diagonal weights. -/
theorem prop21_NormallyTorsionFree_diagonal_iff_of_isMonomialIdeal
    [Fintype σ] {J : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hJ : IsMonomialIdeal J) (hd : ∀ i, 0 < d i) :
    prop21NormallyTorsionFree (diagonal d J) ↔ prop21NormallyTorsionFree J :=
  diagAssoc_normallyTorsionFree_diagonal_iff_of_monomial (K := K) hJ hd

/-- The monomial-invariance theorem specialized to squarefree monomial ideals. -/
theorem prop21_NormallyTorsionFree_diagonal_iff_of_isSquarefree
    [Fintype σ] {J : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hJ : IsSquarefreeMonomialIdeal J) (hd : ∀ i, 0 < d i) :
    prop21NormallyTorsionFree (diagonal d J) ↔ prop21NormallyTorsionFree J := by
  rcases hJ with ⟨H, hJrep⟩
  exact prop21_NormallyTorsionFree_diagonal_iff_of_isMonomialIdeal (K := K) (d := d)
    ⟨characteristicExp '' H, hJrep⟩ hd

/-- Transfer normal torsion-freeness to and from a positive squarefree diagonal root. -/
theorem prop21_NormallyTorsionFree_iff_of_sqRoot_of_fintype
    [Fintype σ] {I J : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hJ : IsSquarefreeMonomialIdeal J) (hd : ∀ i, 0 < d i)
    (hdiag : diagonal d J = I) :
    prop21NormallyTorsionFree I ↔ prop21NormallyTorsionFree J := by
  rw [← hdiag]
  exact prop21_NormallyTorsionFree_diagonal_iff_of_isSquarefree hJ hd

end SimisFormal
