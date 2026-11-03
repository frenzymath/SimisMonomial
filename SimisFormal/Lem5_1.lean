import SimisFormal.Defs
import SimisFormal.Basic

namespace SimisFormal
open MvPolynomial
open scoped BigOperators
/-- The exponent vector with the three indicated coordinates. -/
noncomputable def lem51Exp3 (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.onFinset (Finset.univ : Finset (Fin 3))
    (fun i ↦ if i = 0 then a else if i = 1 then b else c)
    (by
      intro i _
      exact Finset.mem_univ i)

@[simp] theorem lem51Exp3_zero (a b c : ℕ) : lem51Exp3 a b c (0 : Fin 3) = a := by
  simp [lem51Exp3]

@[simp] theorem lem51Exp3_one (a b c : ℕ) : lem51Exp3 a b c (1 : Fin 3) = b := by
  simp [lem51Exp3]

@[simp] theorem lem51Exp3_two (a b c : ℕ) : lem51Exp3 a b c (2 : Fin 3) = c := by
  simp [lem51Exp3]

/-- Lemma 5.1, two-component form.  Thus equality of the square of the core with the
    intersection of the component squares is impossible when `0 < λ < μ`. -/
theorem lem51_twoComponents {K : Type*} [Field K]
    {l m a b : ℕ} (hl : 0 < l) (hlm : l < m) (ha : 0 < a) (hb : 0 < b) :
    let A : Ideal (MvPolynomial (Fin 3) K) :=
      purePower (K := K) ({0, 1} : Finset (Fin 3)) (![l, a, 0] : Fin 3 → ℕ)
    let B : Ideal (MvPolynomial (Fin 3) K) :=
      purePower (K := K) ({0, 2} : Finset (Fin 3)) (![m, 0, b] : Fin 3 → ℕ)
    (A ⊓ B) ^ 2 < A ^ 2 ⊓ B ^ 2 := by
  dsimp only
  let FA : Finset (Fin 3) := {0, 1}
  let FB : Finset (Fin 3) := {0, 2}
  let eA : Fin 3 → ℕ := ![l, a, 0]
  let eB : Fin 3 → ℕ := ![m, 0, b]
  let SA : Set (Fin 3 →₀ ℕ) := {e | ∃ i ∈ FA, e = Finsupp.single i (eA i)}
  let SB : Set (Fin 3 →₀ ℕ) := {e | ∃ i ∈ FB, e = Finsupp.single i (eB i)}
  let A : Ideal (MvPolynomial (Fin 3) K) := purePower (K := K) FA eA
  let B : Ideal (MvPolynomial (Fin 3) K) := purePower (K := K) FB eB
  change (A ⊓ B) ^ 2 < A ^ 2 ⊓ B ^ 2
  have hAeq : A = monomialIdeal (K := K) SA := by rfl
  have hBeq : B = monomialIdeal (K := K) SB := by rfl
  have hAB : A ⊓ B = monomialIdeal (K := K) (meetGens SA SB) := by
    change monomialIdeal (K := K) SA ⊓ monomialIdeal (K := K) SB = _
    exact monomialIdeal_inf SA SB
  let M : ℕ := max (l + l) m
  let f : Fin 3 →₀ ℕ := lem51Exp3 M 0 b
  have hM : M = max (l + l) m := rfl
  have hM_l : l + l ≤ M := by
    dsimp [M]
    exact Nat.le_max_left (l + l) m
  have hM_m : m ≤ M := by
    dsimp [M]
    exact Nat.le_max_right (l + l) m
  have hle : (A ⊓ B) ^ 2 ≤ A ^ 2 ⊓ B ^ 2 := by
    simp only [pow_two]
    refine le_inf ?_ ?_
    · exact Ideal.mul_mono inf_le_left inf_le_left
    · exact Ideal.mul_mono inf_le_right inf_le_right
  have hA2 : (monomial f (1 : K) : MvPolynomial (Fin 3) K) ∈ A ^ 2 := by
    rw [pow_two, hAeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
    refine ⟨Finsupp.single (0 : Fin 3) l + Finsupp.single (0 : Fin 3) l, ?_, ?_⟩
    · refine ⟨Finsupp.single (0 : Fin 3) l, ?_,
          Finsupp.single (0 : Fin 3) l, ?_, rfl⟩
      · exact ⟨0, by simp [FA], by simp [eA]⟩
      · exact ⟨0, by simp [FA], by simp [eA]⟩
    · rw [Finsupp.le_def]
      intro i
      fin_cases i
      · simpa [f] using hM_l
      · simp [f]
      · simp [f]
  have hB2 : (monomial f (1 : K) : MvPolynomial (Fin 3) K) ∈ B ^ 2 := by
    rw [pow_two, hBeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
    refine ⟨Finsupp.single (0 : Fin 3) m + Finsupp.single (2 : Fin 3) b, ?_, ?_⟩
    · refine ⟨Finsupp.single (0 : Fin 3) m, ?_,
          Finsupp.single (2 : Fin 3) b, ?_, rfl⟩
      · exact ⟨0, by simp [FB], by simp [eB]⟩
      · exact ⟨2, by simp [FB], by simp [eB]⟩
    · rw [Finsupp.le_def]
      intro i
      fin_cases i
      · simpa [f] using hM_m
      · simp [f]
      · simp [f]
  have hright : (monomial f (1 : K) : MvPolynomial (Fin 3) K) ∈ A ^ 2 ⊓ B ^ 2 :=
    ⟨hA2, hB2⟩
  have hnot : (monomial f (1 : K) : MvPolynomial (Fin 3) K) ∉ (A ⊓ B) ^ 2 := by
    rw [pow_two, hAB, monomialIdeal_mul, monomial_mem_monomialIdeal]
    rintro ⟨z, ⟨u, hu, v, hv, rfl⟩, hzle⟩
    have h0 := hzle (0 : Fin 3)
    have h2 := hzle (2 : Fin 3)
    simp [f] at h0 h2
    have hu_le : u ≤ f := by
      rw [Finsupp.le_def]
      intro i
      have hi := hzle i
      change u i + v i ≤ f i at hi
      omega
    have hv_le : v ≤ f := by
      rw [Finsupp.le_def]
      intro i
      have hi := hzle i
      change u i + v i ≤ f i at hi
      omega
    have classify : ∀ w : Fin 3 →₀ ℕ, w ∈ meetGens SA SB → w ≤ f →
        m ≤ w 0 ∨ (l ≤ w 0 ∧ b ≤ w 2) := by
      intro w hw hwf
      rcases hw with ⟨s, hs, t, ht, rfl⟩
      rcases hs with ⟨i, hi, rfl⟩
      rcases ht with ⟨j, hj, rfl⟩
      simp [FA] at hi
      rcases hi with rfl | rfl
      · simp [FB] at hj
        rcases hj with rfl | rfl
        · left
          simp [eA, eB, hlm.le]
        · right
          constructor <;> simp [eA, eB]
      · exfalso
        have hi1 := hwf (1 : Fin 3)
        simp [eA, f] at hi1
        omega
    rcases classify u hu hu_le with huP | ⟨huL, huB⟩
    · rcases classify v hv hv_le with hvP | ⟨hvL, hvB⟩
      · omega
      · omega
    · rcases classify v hv hv_le with hvP | ⟨hvL, hvB⟩
      · omega
      · omega
  refine lt_of_le_of_ne hle ?_
  intro heq
  apply hnot
  rw [heq]
  exact hright

/-- Exponent generators for the first two components of Lemma 5.1. -/
def lem51AGens (l a : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {e | ∃ i ∈ ({0, 1} : Finset (Fin 3)), e = Finsupp.single i ((![l, a, 0] : Fin 3 → ℕ) i)}

def lem51BGens (m b : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {e | ∃ i ∈ ({0, 2} : Finset (Fin 3)), e = Finsupp.single i ((![m, 0, b] : Fin 3 → ℕ) i)}

/-- The two possible shapes of the third component. -/
def lem51C2Gens (g d : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {e | ∃ i ∈ ({1, 2} : Finset (Fin 3)), e = Finsupp.single i ((![0, g, d] : Fin 3 → ℕ) i)}

def lem51C3Gens (t g d : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {e | ∃ i ∈ ({0, 1, 2} : Finset (Fin 3)),
    e = Finsupp.single i ((![t, g, d] : Fin 3 → ℕ) i)}

/-- The eight intersection-generator cases when the third component has no `y₀`-generator. -/
def lem51CoreCase (l m a b g d : ℕ) (w : Fin 3 →₀ ℕ) : Prop :=
  (m ≤ w 0 ∧ l ≤ w 0 ∧ g ≤ w 1) ∨
    (m ≤ w 0 ∧ l ≤ w 0 ∧ d ≤ w 2) ∨
      (l ≤ w 0 ∧ b ≤ w 2 ∧ g ≤ w 1) ∨
        (l ≤ w 0 ∧ b ≤ w 2 ∧ d ≤ w 2) ∨
          (m ≤ w 0 ∧ a ≤ w 1 ∧ g ≤ w 1) ∨
            (m ≤ w 0 ∧ a ≤ w 1 ∧ d ≤ w 2) ∨
              (a ≤ w 1 ∧ b ≤ w 2 ∧ g ≤ w 1) ∨
                (a ≤ w 1 ∧ b ≤ w 2 ∧ d ≤ w 2)

/-- Enumerate the joins for the three-generator core with `C = (y₁ᵍ,y₂ᵈ)`. -/
theorem lem51_coreCase_of_C2 {l m a b g d : ℕ} {w : Fin 3 →₀ ℕ}
    (hw : w ∈ meetGens (meetGens (lem51AGens l a) (lem51BGens m b)) (lem51C2Gens g d)) :
    lem51CoreCase l m a b g d w := by
  rcases hw with ⟨x, hx, z, hz, rfl⟩
  rcases hx with ⟨s, hs, t, ht, rfl⟩
  rcases hs with ⟨i, hi, rfl⟩
  rcases ht with ⟨j, hj, rfl⟩
  rcases hz with ⟨k, hk, rfl⟩
  simp at hi
  simp at hj
  simp at hk
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl <;>
    simp [lem51CoreCase]

/-- When a third `y₀`-generator has exponent above the first-coordinate bound, it cannot occur in
    a core generator below that bound. -/
theorem lem51_coreCase_of_C3_of_lt {l m a b t g d : ℕ} {w : Fin 3 →₀ ℕ}
    (hw : w ∈ meetGens (meetGens (lem51AGens l a) (lem51BGens m b)) (lem51C3Gens t g d))
    (hw0 : w 0 < t) : lem51CoreCase l m a b g d w := by
  rcases hw with ⟨x, hx, z, hz, rfl⟩
  rcases hz with ⟨k, hk, rfl⟩
  simp at hk
  rcases hk with rfl | rfl | rfl
  · exfalso
    have htle : t ≤ ((x ⊔ Finsupp.single (0 : Fin 3)
        ((![t, g, d] : Fin 3 → ℕ) 0)) : Fin 3 →₀ ℕ) 0 := by simp
    exact (not_lt_of_ge htle) hw0
  · exact lem51_coreCase_of_C2
      ⟨x, hx, Finsupp.single (1 : Fin 3) g, ⟨1, by simp, by simp⟩, rfl⟩
  · exact lem51_coreCase_of_C2
      ⟨x, hx, Finsupp.single (2 : Fin 3) d, ⟨2, by simp, by simp⟩, rfl⟩

/-- The four remaining cases for the small-exponent witness in the three-generator case. -/
def lem51SmallCase (l m b d t : ℕ) (w : Fin 3 →₀ ℕ) : Prop :=
  m ≤ w 0 ∨ (m ≤ w 0 ∧ d ≤ w 2) ∨
    (max l t ≤ w 0 ∧ b ≤ w 2) ∨ (l ≤ w 0 ∧ max b d ≤ w 2)

/-- Enumerate core generators that have zero second coordinate. -/
theorem lem51_smallCase_of_C3 {l m a b t g d : ℕ} (ha : 0 < a) (hg : 0 < g)
    {w : Fin 3 →₀ ℕ}
    (hw : w ∈ meetGens (meetGens (lem51AGens l a) (lem51BGens m b)) (lem51C3Gens t g d))
    (hw1 : w 1 = 0) : lem51SmallCase l m b d t w := by
  rcases hw with ⟨x, hx, z, hz, rfl⟩
  rcases hx with ⟨s, hs, q, hq, rfl⟩
  rcases hs with ⟨i, hi, rfl⟩
  rcases hq with ⟨j, hj, rfl⟩
  rcases hz with ⟨k, hk, rfl⟩
  simp at hi
  simp at hj
  simp at hk
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
    rcases hk with rfl | rfl | rfl <;> simp_all [lem51SmallCase]

/-- Lemma 5.1, three-component form with `C = (y₁ᵍ,y₂ᵈ)`.  The proof follows the paper's
    two-step witness argument: the first witness either obstructs equality directly or forces
    the inequalities needed for the second witness. -/
theorem lem51_threeComponents_C2 {K : Type*} [Field K]
    {l m a b g d : ℕ} (hl : 0 < l) (hlm : l < m) (ha : 0 < a) (hb : 0 < b)
    (hg : 0 < g) (hd : 0 < d) :
    let A : Ideal (MvPolynomial (Fin 3) K) :=
      purePower (K := K) ({0, 1} : Finset (Fin 3)) (![l, a, 0] : Fin 3 → ℕ)
    let B : Ideal (MvPolynomial (Fin 3) K) :=
      purePower (K := K) ({0, 2} : Finset (Fin 3)) (![m, 0, b] : Fin 3 → ℕ)
    let C : Ideal (MvPolynomial (Fin 3) K) :=
      purePower (K := K) ({1, 2} : Finset (Fin 3)) (![0, g, d] : Fin 3 → ℕ)
    (A ⊓ B ⊓ C) ^ 2 < A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2 := by
  dsimp only
  let A : Ideal (MvPolynomial (Fin 3) K) :=
    purePower (K := K) ({0, 1} : Finset (Fin 3)) (![l, a, 0] : Fin 3 → ℕ)
  let B : Ideal (MvPolynomial (Fin 3) K) :=
    purePower (K := K) ({0, 2} : Finset (Fin 3)) (![m, 0, b] : Fin 3 → ℕ)
  let C : Ideal (MvPolynomial (Fin 3) K) :=
    purePower (K := K) ({1, 2} : Finset (Fin 3)) (![0, g, d] : Fin 3 → ℕ)
  change (A ⊓ B ⊓ C) ^ 2 < A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2
  have hAeq : A = monomialIdeal (K := K) (lem51AGens l a) := by rfl
  have hBeq : B = monomialIdeal (K := K) (lem51BGens m b) := by rfl
  have hCeq : C = monomialIdeal (K := K) (lem51C2Gens g d) := by rfl
  have hAB : A ⊓ B = monomialIdeal (K := K) (meetGens (lem51AGens l a) (lem51BGens m b)) := by
    change monomialIdeal (K := K) (lem51AGens l a) ⊓ monomialIdeal (K := K) (lem51BGens m b) = _
    exact monomialIdeal_inf (K := K) (lem51AGens l a) (lem51BGens m b)
  have hK : A ⊓ B ⊓ C = monomialIdeal (K := K)
      (meetGens (meetGens (lem51AGens l a) (lem51BGens m b)) (lem51C2Gens g d)) := by
    rw [hAB, hCeq]
    exact monomialIdeal_inf (K := K)
      (meetGens (lem51AGens l a) (lem51BGens m b)) (lem51C2Gens g d)
  have hKA : A ⊓ B ⊓ C ≤ A := by
    exact le_trans (inf_le_left : A ⊓ B ⊓ C ≤ A ⊓ B) (inf_le_left : A ⊓ B ≤ A)
  have hKB : A ⊓ B ⊓ C ≤ B := by
    exact le_trans (inf_le_left : A ⊓ B ⊓ C ≤ A ⊓ B) (inf_le_right : A ⊓ B ≤ B)
  have hKC : A ⊓ B ⊓ C ≤ C := inf_le_right
  have hle : (A ⊓ B ⊓ C) ^ 2 ≤ A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2 := by
    simp only [pow_two]
    refine le_inf ?_ ?_
    · refine le_inf ?_ ?_
      · exact Ideal.mul_mono hKA hKA
      · exact Ideal.mul_mono hKB hKB
    · exact Ideal.mul_mono hKC hKC
  let Ahat : ℕ := max a g
  let Bhat : ℕ := max b d
  let F : Fin 3 →₀ ℕ := lem51Exp3 m Ahat Bhat
  have hAhatDef : Ahat = max a g := rfl
  have hBhatDef : Bhat = max b d := rfl
  have haHat : a ≤ Ahat := by
    dsimp [Ahat]
    exact Nat.le_max_left a g
  have hgHat : g ≤ Ahat := by
    dsimp [Ahat]
    exact Nat.le_max_right a g
  have hbHat : b ≤ Bhat := by
    dsimp [Bhat]
    exact Nat.le_max_left b d
  have hdHat : d ≤ Bhat := by
    dsimp [Bhat]
    exact Nat.le_max_right b d
  have hFA2 : (monomial F (1 : K) : MvPolynomial (Fin 3) K) ∈ A ^ 2 := by
    rw [pow_two, hAeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
    refine ⟨Finsupp.single (0 : Fin 3) l + Finsupp.single (1 : Fin 3) a, ?_, ?_⟩
    · refine ⟨Finsupp.single (0 : Fin 3) l, ?_,
          Finsupp.single (1 : Fin 3) a, ?_, rfl⟩
      · exact ⟨0, by simp, by simp⟩
      · exact ⟨1, by simp, by simp⟩
    · rw [Finsupp.le_def]
      intro i
      fin_cases i
      · simpa [F] using hlm.le
      · simpa [F] using haHat
      · simp [F]
  have hFB2 : (monomial F (1 : K) : MvPolynomial (Fin 3) K) ∈ B ^ 2 := by
    rw [pow_two, hBeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
    refine ⟨Finsupp.single (0 : Fin 3) m + Finsupp.single (2 : Fin 3) b, ?_, ?_⟩
    · refine ⟨Finsupp.single (0 : Fin 3) m, ?_,
          Finsupp.single (2 : Fin 3) b, ?_, rfl⟩
      · exact ⟨0, by simp, by simp⟩
      · exact ⟨2, by simp, by simp⟩
    · rw [Finsupp.le_def]
      intro i
      fin_cases i
      · simp [F]
      · simp [F]
      · simpa [F] using hbHat
  have hFC2 : (monomial F (1 : K) : MvPolynomial (Fin 3) K) ∈ C ^ 2 := by
    rw [pow_two, hCeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
    refine ⟨Finsupp.single (1 : Fin 3) g + Finsupp.single (2 : Fin 3) d, ?_, ?_⟩
    · refine ⟨Finsupp.single (1 : Fin 3) g, ?_,
          Finsupp.single (2 : Fin 3) d, ?_, rfl⟩
      · exact ⟨1, by simp, by simp⟩
      · exact ⟨2, by simp, by simp⟩
    · rw [Finsupp.le_def]
      intro i
      fin_cases i
      · simp [F]
      · simpa [F] using hgHat
      · simpa [F] using hdHat
  have hFright : (monomial F (1 : K) : MvPolynomial (Fin 3) K) ∈
      A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2 := ⟨⟨hFA2, hFB2⟩, hFC2⟩
  have hFcondition (hFsq : (monomial F (1 : K) : MvPolynomial (Fin 3) K) ∈
      (A ⊓ B ⊓ C) ^ 2) : l + l ≤ m ∧ g + g ≤ a ∧ b + b ≤ d := by
    rw [pow_two, hK, monomialIdeal_mul, monomial_mem_monomialIdeal] at hFsq
    rcases hFsq with ⟨z, ⟨u, hu, v, hv, rfl⟩, hzle⟩
    have h0 := hzle (0 : Fin 3)
    have h1 := hzle (1 : Fin 3)
    have h2 := hzle (2 : Fin 3)
    simp [F] at h0 h1 h2
    have huCase := lem51_coreCase_of_C2 hu
    have hvCase := lem51_coreCase_of_C2 hv
    rcases huCase with hu1 | hu2 | hu3 | hu4 | hu5 | hu6 | hu7 | hu8 <;>
      rcases hvCase with hv1 | hv2 | hv3 | hv4 | hv5 | hv6 | hv7 | hv8 <;> omega
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hFsq : (monomial F (1 : K) : MvPolynomial (Fin 3) K) ∈ (A ⊓ B ⊓ C) ^ 2 := by
    rw [heq]
    exact hFright
  by_cases hF : (monomial F (1 : K) : MvPolynomial (Fin 3) K) ∈ (A ⊓ B ⊓ C) ^ 2
  · rcases hFcondition hF with ⟨hll, hgg, hbb⟩
    let G : Fin 3 →₀ ℕ := lem51Exp3 l a d
    have hga : g ≤ a := by omega
    have hGA2 : (monomial G (1 : K) : MvPolynomial (Fin 3) K) ∈ A ^ 2 := by
      rw [pow_two, hAeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
      refine ⟨Finsupp.single (0 : Fin 3) l + Finsupp.single (1 : Fin 3) a, ?_, ?_⟩
      · refine ⟨Finsupp.single (0 : Fin 3) l, ?_,
            Finsupp.single (1 : Fin 3) a, ?_, rfl⟩
        · exact ⟨0, by simp, by simp⟩
        · exact ⟨1, by simp, by simp⟩
      · rw [Finsupp.le_def]
        intro i
        fin_cases i <;> simp [G]
    have hGB2 : (monomial G (1 : K) : MvPolynomial (Fin 3) K) ∈ B ^ 2 := by
      rw [pow_two, hBeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
      refine ⟨Finsupp.single (2 : Fin 3) b + Finsupp.single (2 : Fin 3) b, ?_, ?_⟩
      · refine ⟨Finsupp.single (2 : Fin 3) b, ?_,
            Finsupp.single (2 : Fin 3) b, ?_, rfl⟩
        · exact ⟨2, by simp, by simp⟩
        · exact ⟨2, by simp, by simp⟩
      · rw [Finsupp.le_def]
        intro i
        fin_cases i
        · simp [G]
        · simp [G]
        · simpa [G] using hbb
    have hGC2 : (monomial G (1 : K) : MvPolynomial (Fin 3) K) ∈ C ^ 2 := by
      rw [pow_two, hCeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
      refine ⟨Finsupp.single (1 : Fin 3) g + Finsupp.single (2 : Fin 3) d, ?_, ?_⟩
      · refine ⟨Finsupp.single (1 : Fin 3) g, ?_,
            Finsupp.single (2 : Fin 3) d, ?_, rfl⟩
        · exact ⟨1, by simp, by simp⟩
        · exact ⟨2, by simp, by simp⟩
      · rw [Finsupp.le_def]
        intro i
        fin_cases i
        · simp [G]
        · simpa [G] using hga
        · simp [G]
    have hGright : (monomial G (1 : K) : MvPolynomial (Fin 3) K) ∈
        A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2 := ⟨⟨hGA2, hGB2⟩, hGC2⟩
    have hGnot : (monomial G (1 : K) : MvPolynomial (Fin 3) K) ∉ (A ⊓ B ⊓ C) ^ 2 := by
      rw [pow_two, hK, monomialIdeal_mul, monomial_mem_monomialIdeal]
      rintro ⟨z, ⟨u, hu, v, hv, rfl⟩, hzle⟩
      have h0 := hzle (0 : Fin 3)
      have h1 := hzle (1 : Fin 3)
      have h2 := hzle (2 : Fin 3)
      simp [G] at h0 h1 h2
      have huCase := lem51_coreCase_of_C2 hu
      have hvCase := lem51_coreCase_of_C2 hv
      rcases huCase with hu1 | hu2 | hu3 | hu4 | hu5 | hu6 | hu7 | hu8 <;>
        rcases hvCase with hv1 | hv2 | hv3 | hv4 | hv5 | hv6 | hv7 | hv8 <;> omega
    apply hGnot
    rw [heq]
    exact hGright
  · exact hF hFsq

/-- Lemma 5.1, three-generator form in the regime `μ < θ`.  In this regime a core generator
    below the first witness cannot use the `y₀`-generator of `C`, reducing to the preceding
    eight-case argument. -/
theorem lem51_threeComponents_C3_large {K : Type*} [Field K]
    {l m a b t g d : ℕ} (hl : 0 < l) (hlm : l < m) (ha : 0 < a) (hb : 0 < b)
    (hg : 0 < g) (hd : 0 < d) (hmt : m < t) :
    let A : Ideal (MvPolynomial (Fin 3) K) :=
      purePower (K := K) ({0, 1} : Finset (Fin 3)) (![l, a, 0] : Fin 3 → ℕ)
    let B : Ideal (MvPolynomial (Fin 3) K) :=
      purePower (K := K) ({0, 2} : Finset (Fin 3)) (![m, 0, b] : Fin 3 → ℕ)
    let C : Ideal (MvPolynomial (Fin 3) K) :=
      purePower (K := K) ({0, 1, 2} : Finset (Fin 3)) (![t, g, d] : Fin 3 → ℕ)
    (A ⊓ B ⊓ C) ^ 2 < A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2 := by
  dsimp only
  let A : Ideal (MvPolynomial (Fin 3) K) :=
    purePower (K := K) ({0, 1} : Finset (Fin 3)) (![l, a, 0] : Fin 3 → ℕ)
  let B : Ideal (MvPolynomial (Fin 3) K) :=
    purePower (K := K) ({0, 2} : Finset (Fin 3)) (![m, 0, b] : Fin 3 → ℕ)
  let C : Ideal (MvPolynomial (Fin 3) K) :=
    purePower (K := K) ({0, 1, 2} : Finset (Fin 3)) (![t, g, d] : Fin 3 → ℕ)
  change (A ⊓ B ⊓ C) ^ 2 < A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2
  have hAeq : A = monomialIdeal (K := K) (lem51AGens l a) := by rfl
  have hBeq : B = monomialIdeal (K := K) (lem51BGens m b) := by rfl
  have hCeq : C = monomialIdeal (K := K) (lem51C3Gens t g d) := by rfl
  have hAB : A ⊓ B = monomialIdeal (K := K) (meetGens (lem51AGens l a) (lem51BGens m b)) := by
    change monomialIdeal (K := K) (lem51AGens l a) ⊓ monomialIdeal (K := K) (lem51BGens m b) = _
    exact monomialIdeal_inf (K := K) (lem51AGens l a) (lem51BGens m b)
  have hK : A ⊓ B ⊓ C = monomialIdeal (K := K)
      (meetGens (meetGens (lem51AGens l a) (lem51BGens m b)) (lem51C3Gens t g d)) := by
    rw [hAB, hCeq]
    exact monomialIdeal_inf (K := K)
      (meetGens (lem51AGens l a) (lem51BGens m b)) (lem51C3Gens t g d)
  have hKA : A ⊓ B ⊓ C ≤ A := by
    exact le_trans (inf_le_left : A ⊓ B ⊓ C ≤ A ⊓ B) (inf_le_left : A ⊓ B ≤ A)
  have hKB : A ⊓ B ⊓ C ≤ B := by
    exact le_trans (inf_le_left : A ⊓ B ⊓ C ≤ A ⊓ B) (inf_le_right : A ⊓ B ≤ B)
  have hKC : A ⊓ B ⊓ C ≤ C := inf_le_right
  have hle : (A ⊓ B ⊓ C) ^ 2 ≤ A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2 := by
    simp only [pow_two]
    refine le_inf ?_ ?_
    · refine le_inf ?_ ?_
      · exact Ideal.mul_mono hKA hKA
      · exact Ideal.mul_mono hKB hKB
    · exact Ideal.mul_mono hKC hKC
  let Ahat : ℕ := max a g
  let Bhat : ℕ := max b d
  let F : Fin 3 →₀ ℕ := lem51Exp3 m Ahat Bhat
  have hAhatDef : Ahat = max a g := rfl
  have hBhatDef : Bhat = max b d := rfl
  have haHat : a ≤ Ahat := by
    dsimp [Ahat]
    exact Nat.le_max_left a g
  have hgHat : g ≤ Ahat := by
    dsimp [Ahat]
    exact Nat.le_max_right a g
  have hbHat : b ≤ Bhat := by
    dsimp [Bhat]
    exact Nat.le_max_left b d
  have hdHat : d ≤ Bhat := by
    dsimp [Bhat]
    exact Nat.le_max_right b d
  have hFA2 : (monomial F (1 : K) : MvPolynomial (Fin 3) K) ∈ A ^ 2 := by
    rw [pow_two, hAeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
    refine ⟨Finsupp.single (0 : Fin 3) l + Finsupp.single (1 : Fin 3) a, ?_, ?_⟩
    · refine ⟨Finsupp.single (0 : Fin 3) l, ?_,
          Finsupp.single (1 : Fin 3) a, ?_, rfl⟩
      · exact ⟨0, by simp, by simp⟩
      · exact ⟨1, by simp, by simp⟩
    · rw [Finsupp.le_def]
      intro i
      fin_cases i
      · simpa [F] using hlm.le
      · simpa [F] using haHat
      · simp [F]
  have hFB2 : (monomial F (1 : K) : MvPolynomial (Fin 3) K) ∈ B ^ 2 := by
    rw [pow_two, hBeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
    refine ⟨Finsupp.single (0 : Fin 3) m + Finsupp.single (2 : Fin 3) b, ?_, ?_⟩
    · refine ⟨Finsupp.single (0 : Fin 3) m, ?_,
          Finsupp.single (2 : Fin 3) b, ?_, rfl⟩
      · exact ⟨0, by simp, by simp⟩
      · exact ⟨2, by simp, by simp⟩
    · rw [Finsupp.le_def]
      intro i
      fin_cases i
      · simp [F]
      · simp [F]
      · simpa [F] using hbHat
  have hFC2 : (monomial F (1 : K) : MvPolynomial (Fin 3) K) ∈ C ^ 2 := by
    rw [pow_two, hCeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
    refine ⟨Finsupp.single (1 : Fin 3) g + Finsupp.single (2 : Fin 3) d, ?_, ?_⟩
    · refine ⟨Finsupp.single (1 : Fin 3) g, ?_,
          Finsupp.single (2 : Fin 3) d, ?_, rfl⟩
      · exact ⟨1, by simp, by simp⟩
      · exact ⟨2, by simp, by simp⟩
    · rw [Finsupp.le_def]
      intro i
      fin_cases i
      · simp [F]
      · simpa [F] using hgHat
      · simpa [F] using hdHat
  have hFright : (monomial F (1 : K) : MvPolynomial (Fin 3) K) ∈
      A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2 := ⟨⟨hFA2, hFB2⟩, hFC2⟩
  have hFcondition (hFsq : (monomial F (1 : K) : MvPolynomial (Fin 3) K) ∈
      (A ⊓ B ⊓ C) ^ 2) : l + l ≤ m ∧ g + g ≤ a ∧ b + b ≤ d := by
    rw [pow_two, hK, monomialIdeal_mul, monomial_mem_monomialIdeal] at hFsq
    rcases hFsq with ⟨z, ⟨u, hu, v, hv, rfl⟩, hzle⟩
    have h0 := hzle (0 : Fin 3)
    have h1 := hzle (1 : Fin 3)
    have h2 := hzle (2 : Fin 3)
    simp [F] at h0 h1 h2
    have hu0 : u 0 < t := by omega
    have hv0 : v 0 < t := by omega
    have huCase := lem51_coreCase_of_C3_of_lt hu hu0
    have hvCase := lem51_coreCase_of_C3_of_lt hv hv0
    rcases huCase with hu1 | hu2 | hu3 | hu4 | hu5 | hu6 | hu7 | hu8 <;>
      rcases hvCase with hv1 | hv2 | hv3 | hv4 | hv5 | hv6 | hv7 | hv8 <;> omega
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hFsq : (monomial F (1 : K) : MvPolynomial (Fin 3) K) ∈ (A ⊓ B ⊓ C) ^ 2 := by
    rw [heq]
    exact hFright
  by_cases hF : (monomial F (1 : K) : MvPolynomial (Fin 3) K) ∈ (A ⊓ B ⊓ C) ^ 2
  · rcases hFcondition hF with ⟨hll, hgg, hbb⟩
    let G : Fin 3 →₀ ℕ := lem51Exp3 l a d
    have hga : g ≤ a := by omega
    have hGA2 : (monomial G (1 : K) : MvPolynomial (Fin 3) K) ∈ A ^ 2 := by
      rw [pow_two, hAeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
      refine ⟨Finsupp.single (0 : Fin 3) l + Finsupp.single (1 : Fin 3) a, ?_, ?_⟩
      · refine ⟨Finsupp.single (0 : Fin 3) l, ?_,
            Finsupp.single (1 : Fin 3) a, ?_, rfl⟩
        · exact ⟨0, by simp, by simp⟩
        · exact ⟨1, by simp, by simp⟩
      · rw [Finsupp.le_def]
        intro i
        fin_cases i <;> simp [G]
    have hGB2 : (monomial G (1 : K) : MvPolynomial (Fin 3) K) ∈ B ^ 2 := by
      rw [pow_two, hBeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
      refine ⟨Finsupp.single (2 : Fin 3) b + Finsupp.single (2 : Fin 3) b, ?_, ?_⟩
      · refine ⟨Finsupp.single (2 : Fin 3) b, ?_,
            Finsupp.single (2 : Fin 3) b, ?_, rfl⟩
        · exact ⟨2, by simp, by simp⟩
        · exact ⟨2, by simp, by simp⟩
      · rw [Finsupp.le_def]
        intro i
        fin_cases i
        · simp [G]
        · simp [G]
        · simpa [G] using hbb
    have hGC2 : (monomial G (1 : K) : MvPolynomial (Fin 3) K) ∈ C ^ 2 := by
      rw [pow_two, hCeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
      refine ⟨Finsupp.single (1 : Fin 3) g + Finsupp.single (2 : Fin 3) d, ?_, ?_⟩
      · refine ⟨Finsupp.single (1 : Fin 3) g, ?_,
            Finsupp.single (2 : Fin 3) d, ?_, rfl⟩
        · exact ⟨1, by simp, by simp⟩
        · exact ⟨2, by simp, by simp⟩
      · rw [Finsupp.le_def]
        intro i
        fin_cases i
        · simp [G]
        · simpa [G] using hga
        · simp [G]
    have hGright : (monomial G (1 : K) : MvPolynomial (Fin 3) K) ∈
        A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2 := ⟨⟨hGA2, hGB2⟩, hGC2⟩
    have hGnot : (monomial G (1 : K) : MvPolynomial (Fin 3) K) ∉ (A ⊓ B ⊓ C) ^ 2 := by
      rw [pow_two, hK, monomialIdeal_mul, monomial_mem_monomialIdeal]
      rintro ⟨z, ⟨u, hu, v, hv, rfl⟩, hzle⟩
      have h0 := hzle (0 : Fin 3)
      have h1 := hzle (1 : Fin 3)
      have h2 := hzle (2 : Fin 3)
      simp [G] at h0 h1 h2
      have hu0 : u 0 < t := by omega
      have hv0 : v 0 < t := by omega
      have huCase := lem51_coreCase_of_C3_of_lt hu hu0
      have hvCase := lem51_coreCase_of_C3_of_lt hv hv0
      rcases huCase with hu1 | hu2 | hu3 | hu4 | hu5 | hu6 | hu7 | hu8 <;>
        rcases hvCase with hv1 | hv2 | hv3 | hv4 | hv5 | hv6 | hv7 | hv8 <;> omega
    apply hGnot
    rw [heq]
    exact hGright
  · exact hF hFsq

/-- Lemma 5.1, three-generator form in the regime `0 < θ ≤ μ`.  Here the paper uses a
    two-variable witness, with its `y₂`-exponent chosen according to whether `2θ` exceeds
    `max(2λ,μ)`. -/
theorem lem51_threeComponents_C3_small {K : Type*} [Field K]
    {l m a b t g d : ℕ} (hl : 0 < l) (hlm : l < m) (ha : 0 < a) (hb : 0 < b)
    (ht : 0 < t) (hg : 0 < g) (hd : 0 < d) (htm : t ≤ m) :
    let A : Ideal (MvPolynomial (Fin 3) K) :=
      purePower (K := K) ({0, 1} : Finset (Fin 3)) (![l, a, 0] : Fin 3 → ℕ)
    let B : Ideal (MvPolynomial (Fin 3) K) :=
      purePower (K := K) ({0, 2} : Finset (Fin 3)) (![m, 0, b] : Fin 3 → ℕ)
    let C : Ideal (MvPolynomial (Fin 3) K) :=
      purePower (K := K) ({0, 1, 2} : Finset (Fin 3)) (![t, g, d] : Fin 3 → ℕ)
    (A ⊓ B ⊓ C) ^ 2 < A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2 := by
  dsimp only
  let A : Ideal (MvPolynomial (Fin 3) K) :=
    purePower (K := K) ({0, 1} : Finset (Fin 3)) (![l, a, 0] : Fin 3 → ℕ)
  let B : Ideal (MvPolynomial (Fin 3) K) :=
    purePower (K := K) ({0, 2} : Finset (Fin 3)) (![m, 0, b] : Fin 3 → ℕ)
  let C : Ideal (MvPolynomial (Fin 3) K) :=
    purePower (K := K) ({0, 1, 2} : Finset (Fin 3)) (![t, g, d] : Fin 3 → ℕ)
  change (A ⊓ B ⊓ C) ^ 2 < A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2
  have hAeq : A = monomialIdeal (K := K) (lem51AGens l a) := by rfl
  have hBeq : B = monomialIdeal (K := K) (lem51BGens m b) := by rfl
  have hCeq : C = monomialIdeal (K := K) (lem51C3Gens t g d) := by rfl
  have hAB : A ⊓ B = monomialIdeal (K := K) (meetGens (lem51AGens l a) (lem51BGens m b)) := by
    change monomialIdeal (K := K) (lem51AGens l a) ⊓ monomialIdeal (K := K) (lem51BGens m b) = _
    exact monomialIdeal_inf (K := K) (lem51AGens l a) (lem51BGens m b)
  have hK : A ⊓ B ⊓ C = monomialIdeal (K := K)
      (meetGens (meetGens (lem51AGens l a) (lem51BGens m b)) (lem51C3Gens t g d)) := by
    rw [hAB, hCeq]
    exact monomialIdeal_inf (K := K)
      (meetGens (lem51AGens l a) (lem51BGens m b)) (lem51C3Gens t g d)
  have hKA : A ⊓ B ⊓ C ≤ A := by
    exact le_trans (inf_le_left : A ⊓ B ⊓ C ≤ A ⊓ B) (inf_le_left : A ⊓ B ≤ A)
  have hKB : A ⊓ B ⊓ C ≤ B := by
    exact le_trans (inf_le_left : A ⊓ B ⊓ C ≤ A ⊓ B) (inf_le_right : A ⊓ B ≤ B)
  have hKC : A ⊓ B ⊓ C ≤ C := inf_le_right
  have hle : (A ⊓ B ⊓ C) ^ 2 ≤ A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2 := by
    simp only [pow_two]
    refine le_inf ?_ ?_
    · refine le_inf ?_ ?_
      · exact Ideal.mul_mono hKA hKA
      · exact Ideal.mul_mono hKB hKB
    · exact Ideal.mul_mono hKC hKC
  let M : ℕ := max (l + l) m
  have hMdef : M = max (l + l) m := rfl
  have hM_l : l + l ≤ M := by
    dsimp [M]
    exact Nat.le_max_left (l + l) m
  have hM_m : m ≤ M := by
    dsimp [M]
    exact Nat.le_max_right (l + l) m
  have htM : t ≤ M := le_trans htm hM_m
  have hmax_l : l ≤ max l t := Nat.le_max_left l t
  have hmax_b : b ≤ max b d := Nat.le_max_left b d
  have hmax_d : d ≤ max b d := Nat.le_max_right b d
  refine lt_of_le_of_ne hle ?_
  intro heq
  by_cases ht2 : t + t ≤ M
  · let H : Fin 3 →₀ ℕ := lem51Exp3 M 0 b
    have hHA2 : (monomial H (1 : K) : MvPolynomial (Fin 3) K) ∈ A ^ 2 := by
      rw [pow_two, hAeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
      refine ⟨Finsupp.single (0 : Fin 3) l + Finsupp.single (0 : Fin 3) l, ?_, ?_⟩
      · refine ⟨Finsupp.single (0 : Fin 3) l, ?_,
            Finsupp.single (0 : Fin 3) l, ?_, rfl⟩
        · exact ⟨0, by simp, by simp⟩
        · exact ⟨0, by simp, by simp⟩
      · rw [Finsupp.le_def]
        intro i
        fin_cases i
        · simpa [H] using hM_l
        · simp [H]
        · simp [H]
    have hHB2 : (monomial H (1 : K) : MvPolynomial (Fin 3) K) ∈ B ^ 2 := by
      rw [pow_two, hBeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
      refine ⟨Finsupp.single (0 : Fin 3) m + Finsupp.single (2 : Fin 3) b, ?_, ?_⟩
      · refine ⟨Finsupp.single (0 : Fin 3) m, ?_,
            Finsupp.single (2 : Fin 3) b, ?_, rfl⟩
        · exact ⟨0, by simp, by simp⟩
        · exact ⟨2, by simp, by simp⟩
      · rw [Finsupp.le_def]
        intro i
        fin_cases i
        · simpa [H] using hM_m
        · simp [H]
        · simp [H]
    have hHC2 : (monomial H (1 : K) : MvPolynomial (Fin 3) K) ∈ C ^ 2 := by
      rw [pow_two, hCeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
      refine ⟨Finsupp.single (0 : Fin 3) t + Finsupp.single (0 : Fin 3) t, ?_, ?_⟩
      · refine ⟨Finsupp.single (0 : Fin 3) t, ?_,
            Finsupp.single (0 : Fin 3) t, ?_, rfl⟩
        · exact ⟨0, by simp, by simp⟩
        · exact ⟨0, by simp, by simp⟩
      · rw [Finsupp.le_def]
        intro i
        fin_cases i
        · simpa [H] using ht2
        · simp [H]
        · simp [H]
    have hHright : (monomial H (1 : K) : MvPolynomial (Fin 3) K) ∈
        A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2 := ⟨⟨hHA2, hHB2⟩, hHC2⟩
    have hHnot : (monomial H (1 : K) : MvPolynomial (Fin 3) K) ∉ (A ⊓ B ⊓ C) ^ 2 := by
      rw [pow_two, hK, monomialIdeal_mul, monomial_mem_monomialIdeal]
      rintro ⟨z, ⟨u, hu, v, hv, rfl⟩, hzle⟩
      have h0 := hzle (0 : Fin 3)
      have h1 := hzle (1 : Fin 3)
      have h2 := hzle (2 : Fin 3)
      simp [H] at h0 h1 h2
      have hu1 : u 1 = 0 := by omega
      have hv1 : v 1 = 0 := by omega
      have huCase := lem51_smallCase_of_C3 ha hg hu hu1
      have hvCase := lem51_smallCase_of_C3 ha hg hv hv1
      rcases huCase with hu1 | hu2 | hu3 | hu4 <;>
        rcases hvCase with hv1 | hv2 | hv3 | hv4 <;> omega
    apply hHnot
    rw [heq]
    exact hHright
  · have ht2gt : M < t + t := Nat.lt_of_not_ge ht2
    have hlt : l < t := by omega
    have hmax_lt : max l t = t := Nat.max_eq_right hlt.le
    let Bhat : ℕ := max b d
    let H : Fin 3 →₀ ℕ := lem51Exp3 M 0 Bhat
    have hBhatDef : Bhat = max b d := rfl
    have hbHat : b ≤ Bhat := by
      dsimp [Bhat]
      exact Nat.le_max_left b d
    have hdHat : d ≤ Bhat := by
      dsimp [Bhat]
      exact Nat.le_max_right b d
    have hHA2 : (monomial H (1 : K) : MvPolynomial (Fin 3) K) ∈ A ^ 2 := by
      rw [pow_two, hAeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
      refine ⟨Finsupp.single (0 : Fin 3) l + Finsupp.single (0 : Fin 3) l, ?_, ?_⟩
      · refine ⟨Finsupp.single (0 : Fin 3) l, ?_,
            Finsupp.single (0 : Fin 3) l, ?_, rfl⟩
        · exact ⟨0, by simp, by simp⟩
        · exact ⟨0, by simp, by simp⟩
      · rw [Finsupp.le_def]
        intro i
        fin_cases i
        · simpa [H] using hM_l
        · simp [H]
        · simp [H]
    have hHB2 : (monomial H (1 : K) : MvPolynomial (Fin 3) K) ∈ B ^ 2 := by
      rw [pow_two, hBeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
      refine ⟨Finsupp.single (0 : Fin 3) m + Finsupp.single (2 : Fin 3) b, ?_, ?_⟩
      · refine ⟨Finsupp.single (0 : Fin 3) m, ?_,
            Finsupp.single (2 : Fin 3) b, ?_, rfl⟩
        · exact ⟨0, by simp, by simp⟩
        · exact ⟨2, by simp, by simp⟩
      · rw [Finsupp.le_def]
        intro i
        fin_cases i
        · simpa [H] using hM_m
        · simp [H]
        · simpa [H] using hbHat
    have hHC2 : (monomial H (1 : K) : MvPolynomial (Fin 3) K) ∈ C ^ 2 := by
      rw [pow_two, hCeq, monomialIdeal_mul, monomial_mem_monomialIdeal]
      refine ⟨Finsupp.single (0 : Fin 3) t + Finsupp.single (2 : Fin 3) d, ?_, ?_⟩
      · refine ⟨Finsupp.single (0 : Fin 3) t, ?_,
            Finsupp.single (2 : Fin 3) d, ?_, rfl⟩
        · exact ⟨0, by simp, by simp⟩
        · exact ⟨2, by simp, by simp⟩
      · rw [Finsupp.le_def]
        intro i
        fin_cases i
        · simpa [H] using htM
        · simp [H]
        · simpa [H] using hdHat
    have hHright : (monomial H (1 : K) : MvPolynomial (Fin 3) K) ∈
        A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2 := ⟨⟨hHA2, hHB2⟩, hHC2⟩
    have hHnot : (monomial H (1 : K) : MvPolynomial (Fin 3) K) ∉ (A ⊓ B ⊓ C) ^ 2 := by
      rw [pow_two, hK, monomialIdeal_mul, monomial_mem_monomialIdeal]
      rintro ⟨z, ⟨u, hu, v, hv, rfl⟩, hzle⟩
      have h0 := hzle (0 : Fin 3)
      have h1 := hzle (1 : Fin 3)
      have h2 := hzle (2 : Fin 3)
      simp [H] at h0 h1 h2
      have hu1 : u 1 = 0 := by omega
      have hv1 : v 1 = 0 := by omega
      have huCase := lem51_smallCase_of_C3 ha hg hu hu1
      have hvCase := lem51_smallCase_of_C3 ha hg hv hv1
      rw [lem51SmallCase] at huCase hvCase
      rw [hmax_lt] at huCase hvCase
      rcases huCase with hu1 | hu2 | hu3 | hu4 <;>
        rcases hvCase with hv1 | hv2 | hv3 | hv4 <;> omega
    apply hHnot
    rw [heq]
    exact hHright

/-- Lemma 5.1, three-component form with `C = (y₀ᵗ,y₁ᵍ,y₂ᵈ)`, for every `θ > 0`. -/
theorem lem51_threeComponents_C3 {K : Type*} [Field K]
    {l m a b t g d : ℕ} (hl : 0 < l) (hlm : l < m) (ha : 0 < a) (hb : 0 < b)
    (ht : 0 < t) (hg : 0 < g) (hd : 0 < d) :
    let A : Ideal (MvPolynomial (Fin 3) K) :=
      purePower (K := K) ({0, 1} : Finset (Fin 3)) (![l, a, 0] : Fin 3 → ℕ)
    let B : Ideal (MvPolynomial (Fin 3) K) :=
      purePower (K := K) ({0, 2} : Finset (Fin 3)) (![m, 0, b] : Fin 3 → ℕ)
    let C : Ideal (MvPolynomial (Fin 3) K) :=
      purePower (K := K) ({0, 1, 2} : Finset (Fin 3)) (![t, g, d] : Fin 3 → ℕ)
    (A ⊓ B ⊓ C) ^ 2 < A ^ 2 ⊓ B ^ 2 ⊓ C ^ 2 := by
  dsimp only
  by_cases hmt : m < t
  · exact lem51_threeComponents_C3_large (K := K) hl hlm ha hb hg hd hmt
  · exact lem51_threeComponents_C3_small (K := K) hl hlm ha hb ht hg hd
      (Nat.le_of_not_gt hmt)

end SimisFormal
