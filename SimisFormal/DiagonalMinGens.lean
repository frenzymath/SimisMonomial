import SimisFormal.Defs
import SimisFormal.Eq4_DiagonalSimis

namespace SimisFormal
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [Field K] [DecidableEq σ]
noncomputable section
omit [DecidableEq σ] in
/-- Positive diagonal weighting preserves and reflects divisibility. -/
theorem diagExp_le_iff_le_of_pos [Fintype σ] {d : σ → ℕ} (hd : ∀ i, 0 < d i)
    (u v : σ →₀ ℕ) : diagExp d u ≤ diagExp d v ↔ u ≤ v := by
  rw [diagExp_le_iff_floor hd u (diagExp d v), eq4_floorDiv_diagExp hd v]

omit [DecidableEq σ] in
/-- Rounding down and then weighting recovers an exponent below the original one. -/
theorem diagExp_floorDiv_le_of_pos [Fintype σ] {d : σ → ℕ} (_hd : ∀ i, 0 < d i)
    (e : σ →₀ ℕ) : diagExp d (floorDiv d e) ≤ e := by
  rw [Finsupp.le_def]
  intro i
  simp only [diagExp_apply, floorDiv_apply]
  exact Nat.div_mul_le_self (e i) (d i)

/-- Positive diagonal weighting preserves the minimal monomial generators. -/
theorem diagonal_minGens [Fintype σ]
    {I : Ideal (MvPolynomial σ K)} {d : σ → ℕ}
    (hI : IsMonomialIdeal I) (hd : ∀ i, 0 < d i) :
    minGens (diagonal d I) = diagExp d '' minGens I := by
  ext e
  constructor
  · intro he
    rcases mem_minGens.mp he with ⟨heDiag, heMin⟩
    have hfloorI : (monomial (floorDiv d e) (1 : K) : MvPolynomial σ K) ∈ I :=
      (monomial_mem_diagonal (K := K) hI hd (e := e)).mp heDiag
    obtain ⟨u, huMin, hule⟩ := exists_minGens_le (I := I) (e := floorDiv d e) hfloorI
    have huI : (monomial u (1 : K) : MvPolynomial σ K) ∈ I :=
      (mem_minGens.mp huMin).1
    have hdiagMem : (monomial (diagExp d u) (1 : K) : MvPolynomial σ K) ∈ diagonal d I :=
      (monomial_mem_diagonal (K := K) hI hd (e := diagExp d u)).mpr (by
        simpa only [eq4_floorDiv_diagExp hd u] using huI)
    have hdiagLe : diagExp d u ≤ e := (diagExp_le_iff_floor hd u e).2 hule
    have heq : diagExp d u = e := heMin (diagExp d u) hdiagMem hdiagLe
    have hfloorEq : floorDiv d e = u := by
      rw [← heq]
      exact eq4_floorDiv_diagExp hd u
    have hfloorMin : floorDiv d e ∈ minGens I := by
      simpa only [hfloorEq] using huMin
    refine ⟨floorDiv d e, hfloorMin, ?_⟩
    rw [hfloorEq]
    exact heq
  · rintro ⟨u, huMin, rfl⟩
    rcases mem_minGens.mp huMin with ⟨huI, huMinimal⟩
    rw [mem_minGens]
    constructor
    · exact (monomial_mem_diagonal (K := K) hI hd (e := diagExp d u)).mpr (by
        simpa only [eq4_floorDiv_diagExp hd u] using huI)
    · intro z hzDiag hzle
      have hfloorI : (monomial (floorDiv d z) (1 : K) : MvPolynomial σ K) ∈ I :=
        (monomial_mem_diagonal (K := K) hI hd (e := z)).mp hzDiag
      have hdiagFloorLe : diagExp d (floorDiv d z) ≤ diagExp d u :=
        le_trans (diagExp_floorDiv_le_of_pos hd z) hzle
      have hfloorLe : floorDiv d z ≤ u := by
        have hfloorLe' : floorDiv d z ≤ floorDiv d (diagExp d u) :=
          (diagExp_le_iff_floor hd (floorDiv d z) (diagExp d u)).mp hdiagFloorLe
        simpa only [eq4_floorDiv_diagExp hd u] using hfloorLe'
      have hfloorEq : floorDiv d z = u :=
        huMinimal (floorDiv d z) hfloorI hfloorLe
      have hdiagULeZ : diagExp d u ≤ z := by
        simpa only [hfloorEq] using (diagExp_floorDiv_le_of_pos hd z)
      exact le_antisymm hzle hdiagULeZ

end
end SimisFormal
