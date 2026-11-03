import SimisFormal.Defs
import SimisFormal.Basic

namespace SimisFormal
variable {σ : Type*} [DecidableEq σ]
/-- Every transversal contains an inclusion-minimal transversal. -/
theorem blocker_exists_minimal_transversal_subset
    {H : Set (Finset σ)} {W : Finset σ} (hW : IsTransversal H W) :
    ∃ T, T ⊆ W ∧ T ∈ blocker H := by
  classical
  let C : Finset (Finset σ) := W.powerset.filter (fun T ↦ IsTransversal H T)
  have hWmem : W ∈ C := by simp [C, hW]
  obtain ⟨T, hTC, hmin⟩ :=
    Finset.exists_min_image C (fun T ↦ T.card) ⟨W, hWmem⟩
  have hTC' := Finset.mem_filter.mp hTC
  have hTW : T ⊆ W := Finset.mem_powerset.mp hTC'.1
  have hTtrans : IsTransversal H T := hTC'.2
  refine ⟨T, hTW, hTtrans, ?_⟩
  intro U hUT hUtrans
  have hUW : U ⊆ W := hUT.1.trans hTW
  have hUC : U ∈ C := by simp [C, hUW, hUtrans]
  exact (not_lt_of_ge (hmin U hUC)) (Finset.card_lt_card hUT)

/-- The blocker of any set of finite sets is an antichain. -/
theorem blocker_isClutter (H : Set (Finset σ)) : IsClutter (blocker H) := by
  intro A hA B hB hAB
  by_contra hne
  have hss : A ⊂ B := Finset.ssubset_iff_subset_ne.mpr ⟨hAB, hne⟩
  exact hB.2 A hss hA.1

/-- Taking the blocker twice returns the original clutter, including degenerate cases. -/
theorem blocker_blocker_eq_self [Fintype σ] {H : Set (Finset σ)} (hH : IsClutter H) :
    blocker (blocker H) = H := by
  classical
  have hHsub : H ⊆ blocker (blocker H) := by
    intro E hE
    have hEtrans : IsTransversal (blocker H) E := by
      intro T hT
      simpa [Finset.inter_comm] using hT.1 E hE
    refine ⟨hEtrans, ?_⟩
    intro U hUE hUtrans
    let W : Finset σ := Finset.univ \ U
    have hWtrans : IsTransversal H W := by
      intro F hF
      by_contra hFW
      have hFU : F ⊆ U := by
        intro x hxF
        by_contra hxU
        have hxW : x ∈ W := by simp [W, hxU]
        exact hFW ⟨x, Finset.mem_inter.mpr ⟨hxF, hxW⟩⟩
      have hFE : F = E := hH F hF E hE (hFU.trans hUE.1)
      have hEU : E ⊆ U := by simpa [hFE] using hFU
      exact (ne_of_lt hUE) (Finset.Subset.antisymm hUE.1 hEU)
    obtain ⟨C, hCW, hCblock⟩ :=
      blocker_exists_minimal_transversal_subset (H := H) hWtrans
    rcases hUtrans C hCblock with ⟨x, hxCU⟩
    have hxCU' := Finset.mem_inter.mp hxCU
    have hxW : x ∈ W := hCW hxCU'.1
    have hxW' : x ∈ Finset.univ \ U := by simpa [W] using hxW
    exact (Finset.mem_sdiff.mp hxW').2 hxCU'.2
  apply Set.Subset.antisymm
  · intro T hT
    by_contra hTH
    have hnoEdgeSubset : ∀ E ∈ H, ¬ E ⊆ T := by
      intro E hE hET
      by_cases hEq : E = T
      · exact hTH (hEq ▸ hE)
      · have hss : E ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hET, hEq⟩
        exact hT.2 E hss (hHsub hE).1
    let W : Finset σ := Finset.univ \ T
    have hWtrans : IsTransversal H W := by
      intro E hE
      by_contra hEW
      have hET : E ⊆ T := by
        intro x hxE
        by_contra hxT
        have hxW : x ∈ W := by simp [W, hxT]
        exact hEW ⟨x, Finset.mem_inter.mpr ⟨hxE, hxW⟩⟩
      exact hnoEdgeSubset E hE hET
    obtain ⟨C, hCW, hCblock⟩ :=
      blocker_exists_minimal_transversal_subset (H := H) hWtrans
    rcases hT.1 C hCblock with ⟨x, hxCT⟩
    have hxCT' := Finset.mem_inter.mp hxCT
    have hxW : x ∈ W := hCW hxCT'.1
    have hxW' : x ∈ Finset.univ \ T := by simpa [W] using hxW
    exact (Finset.mem_sdiff.mp hxW').2 hxCT'.2
  · exact hHsub

end SimisFormal
