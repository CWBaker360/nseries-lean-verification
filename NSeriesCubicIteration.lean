import Mathlib

namespace BakerSeed

/-! The cubic majorant and its abstract iteration certificate. -/

noncomputable def bseq (D : ℝ) : ℕ → ℝ
  | 0 => D
  | (k + 1) => (bseq D k) ^ 3 / 3

@[simp] lemma bseq_zero (D : ℝ) :
    bseq D 0 = D := rfl

@[simp] lemma bseq_succ (D : ℝ) (k : ℕ) :
    bseq D (k + 1) = (bseq D k) ^ 3 / 3 := rfl

lemma bseq_nonneg {D : ℝ} (hD : 0 ≤ D) (k : ℕ) :
    0 ≤ bseq D k := by
  induction k with
  | zero => simpa using hD
  | succ n ih =>
      rw [bseq_succ]
      positivity

lemma bseq_le_half {D : ℝ}
    (hD0 : 0 ≤ D) (hD : D ≤ 1 / 2) (k : ℕ) :
    bseq D k ≤ 1 / 2 := by
  induction k with
  | zero => simpa using hD
  | succ n ih =>
      rw [bseq_succ]
      have hn : 0 ≤ bseq D n := bseq_nonneg hD0 n
      calc
        (bseq D n) ^ 3 / 3 ≤ ((1 / 2 : ℝ) ^ 3) / 3 := by
          gcongr
        _ ≤ 1 / 2 := by norm_num

theorem bseq_bounds {D : ℝ}
    (hD0 : 0 ≤ D) (hD : D ≤ 1 / 2) (k : ℕ) :
    0 ≤ bseq D k ∧ bseq D k ≤ 1 / 2 := by
  exact ⟨bseq_nonneg hD0 k, bseq_le_half hD0 hD k⟩

-- A locally recursive iterate, independent of the API for Function.iterate.
def cubicIter (F : ℝ → ℝ) (z : ℝ) : ℕ → ℝ
  | 0 => z
  | (k + 1) => F (cubicIter F z k)

@[simp] lemma cubicIter_zero (F : ℝ → ℝ) (z : ℝ) :
    cubicIter F z 0 = z := rfl

@[simp] lemma cubicIter_succ (F : ℝ → ℝ) (z : ℝ) (k : ℕ) :
    cubicIter F z (k + 1) = F (cubicIter F z k) := rfl

/-- Any map with the local cubic residual bound is bounded
    by the majorant at every iterate. -/
theorem cubicIter_bound
    (F : ℝ → ℝ) (D z : ℝ)
    (hF : ∀ x : ℝ, |x| ≤ 1 / 2 → |F x| ≤ |x| ^ 3 / 3)
    (hD0 : 0 ≤ D) (hD : D ≤ 1 / 2)
    (hz : |z| ≤ D) (k : ℕ) :
    |cubicIter F z k| ≤ bseq D k := by
  induction k with
  | zero =>
      simpa using hz
  | succ n ih =>
      rw [cubicIter_succ, bseq_succ]
      have hn : 0 ≤ bseq D n := bseq_nonneg hD0 n
      have hhalf : |cubicIter F z n| ≤ (1 / 2 : ℝ) :=
        le_trans ih (bseq_le_half hD0 hD n)
      calc
        |F (cubicIter F z n)| ≤ |cubicIter F z n| ^ 3 / 3 :=
          hF _ hhalf
        _ ≤ (bseq D n) ^ 3 / 3 := by
          gcongr

end BakerSeed

#print axioms BakerSeed.bseq_nonneg
#print axioms BakerSeed.bseq_le_half
#print axioms BakerSeed.bseq_bounds
#print axioms BakerSeed.cubicIter_bound
