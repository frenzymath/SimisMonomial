import SimisFormal.Defs
import SimisFormal.Prop6_1

namespace SimisFormal
variable {K : Type*} [Field K]
/-! The ambient polynomial rings in Proposition 6.1 form an infinite family.

The proposition gives examples indexed by \(m \ge 2\).  We record that their ambient rings are
pairwise nonisomorphic, since their Krull dimensions are \(6m\) and hence distinguish \(m\). -/
/-- The variable type of Proposition 6.1 has cardinality \(6m\). -/
theorem prop61_var_natCard (m : ℕ) : Nat.card (prop61_var m) = 6 * m := by
  let _ : Fintype (prop61_var m) := prop61_varFintype m
  rw [Nat.card_eq_fintype_card]
  simpa [prop61_var] using (show 3 * (2 * m) = 6 * m by ring)

/-- The ambient polynomial ring indexed by \(m\) has Krull dimension \(6m\). -/
theorem prop61_ringKrullDim (m : ℕ) :
    ringKrullDim (MvPolynomial (prop61_var m) K) = ((6 * m : ℕ) : WithBot ℕ∞) := by
  let _ : Fintype (prop61_var m) := prop61_varFintype m
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field K, prop61_var_natCard]
  simp

/-- Distinct parameters produce nonisomorphic ambient polynomial rings. -/
theorem prop61_ambientRings_pairwise_not_ringEquiv {m n : ℕ} (hmn : m ≠ n) :
    IsEmpty (MvPolynomial (prop61_var m) K ≃+* MvPolynomial (prop61_var n) K) := by
  refine ⟨fun e ↦ ?_⟩
  apply hmn
  have hdim := e.ringKrullDim
  rw [prop61_ringKrullDim (K := K), prop61_ringKrullDim (K := K)] at hdim
  have hcard : 6 * m = 6 * n := by
    exact_mod_cast hdim
  omega

/-- The manuscript's parameters \(m \ge 2\) give pairwise distinct ambient rings. -/
theorem prop61_ambientFamily_pairwiseDistinct :
    ∀ {m n : ℕ}, 2 ≤ m → 2 ≤ n → m ≠ n →
      IsEmpty (MvPolynomial (prop61_var m) K ≃+* MvPolynomial (prop61_var n) K) := by
  intro m n _ _ hmn
  exact prop61_ambientRings_pairwise_not_ringEquiv (K := K) hmn

end SimisFormal
