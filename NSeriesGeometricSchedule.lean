/-
  Module C -- geometric specialization: Lemma 4.7's cubic bound fed into the
  abstract iteration certificate, plus the defect majorant.

  STATUS: NOT COMPILED.  This is the only module with unverified content, and
  it is deliberately short so that a failure is quick to diagnose.

  Imports Modules A and B, so neither the trigonometric proofs of Lemma 4.7 nor
  the abstract recurrence is rechecked.

  An axiom audit of `residual_bound_one_level` traverses the whole dependency
  graph, so the audit block at the foot of this file is sufficient evidence for
  the entire chain A + B + C -- there is no need to re-audit the upstream
  modules separately.
-/
import NSeriesSeedCubicBounds
import NSeriesCubicIteration

namespace BakerSeed

open Real

/-- `seedF` satisfies the hypothesis of `cubicIter_bound`: this is exactly
`abs_seedF_le` of Lemma 4.7, repackaged. -/
lemma seedF_cubic_bound : ∀ x : ℝ, |x| ≤ 1 / 2 → |seedF x| ≤ |x| ^ 3 / 3 :=
  fun _ hx => abs_seedF_le hx

/-- **The iteration bound at the geometric seed.**  Lemma 4.7's
single-application bound becomes the schedule's `|F^{k}(d)| <= b_k`. -/
theorem abs_seedF_iterate_le {D z : ℝ} (hD0 : 0 ≤ D) (hD1 : D ≤ 1 / 2)
    (hz : |z| ≤ D) (k : ℕ) : |cubicIter seedF z k| ≤ bseq D k :=
  cubicIter_bound seedF D z seedF_cubic_bound hD0 hD1 hz k

/-- Monotone form of `seedDefect_le`: a bound on `x` gives a bound on `d x`. -/
theorem seedDefect_le_of_le {x A : ℝ} (hx0 : 0 < x) (hxA : x ≤ A)
    (hA : A ≤ 3 / 2) : seedDefect x ≤ A ^ 3 / 81 := by
  have hx1 : x ≤ 3 / 2 := le_trans hxA hA
  have h := seedDefect_le hx0 hx1
  have hx0' : (0 : ℝ) ≤ x := le_of_lt hx0
  have hcube : x ^ 3 ≤ A ^ 3 := by gcongr
  linarith

/-- The defect of a level input is majorized by the rational `D` of
Remark 4.11, and that majorant is small enough for the iteration bound. -/
theorem defect_majorant {x A : ℝ} (hx0 : 0 < x) (hxA : x ≤ A)
    (hA0 : 0 < A) (hA : A ≤ 3 / 2) :
    |seedDefect x| ≤ A ^ 3 / 81 ∧ A ^ 3 / 81 ≤ 1 / 2 := by
  have hx1 : x ≤ 3 / 2 := le_trans hxA hA
  have hpos := seedDefect_pos hx0 hx1
  have hle := seedDefect_le_of_le hx0 hxA hA
  refine ⟨?_, ?_⟩
  · rw [abs_of_pos hpos]
    exact hle
  · have hA0' : (0 : ℝ) ≤ A := le_of_lt hA0
    have hcube : A ^ 3 ≤ (3 / 2 : ℝ) ^ 3 := by gcongr
    have hval : (3 / 2 : ℝ) ^ 3 = 27 / 8 := by norm_num
    rw [hval] at hcube
    linarith

/-- **One level of the schedule.**  If the level input is at most `A`, then after
`k` refinements the residual is bounded by the purely rational
`bseq (A^3/81) k`.

This is the form step (iii) consumes: pair it with the ladder bootstrap
`A = (16/5)/M_{i-1}` and the budget check `bseq D_i k_i <= tau/(L M_i)`. -/
theorem residual_bound_one_level {x A : ℝ} (hx0 : 0 < x) (hxA : x ≤ A)
    (hA0 : 0 < A) (hA : A ≤ 3 / 2) (k : ℕ) :
    |cubicIter seedF (seedDefect x) k| ≤ bseq (A ^ 3 / 81) k := by
  obtain ⟨hd, hD1⟩ := defect_majorant hx0 hxA hA0 hA
  have hD0 : (0 : ℝ) ≤ A ^ 3 / 81 := by positivity
  exact abs_seedF_iterate_le hD0 hD1 hd k

/-! ### Optional bridge to `Function.iterate`

For the record only, so the Lean statements can be quoted against the
manuscript's `F^{\circ k}`.  Nothing above depends on it, so a problem with
`Function.iterate_succ_apply'` costs one unused lemma and nothing else. -/

lemma cubicIter_eq_iterate (F : ℝ → ℝ) (z : ℝ) (k : ℕ) :
    cubicIter F z k = F^[k] z := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [cubicIter_succ, ih, Function.iterate_succ_apply']

end BakerSeed

/-! ## Axiom audit -- traverses A and B transitively -/
#print axioms BakerSeed.seedF_cubic_bound
#print axioms BakerSeed.abs_seedF_iterate_le
#print axioms BakerSeed.seedDefect_le_of_le
#print axioms BakerSeed.defect_majorant
#print axioms BakerSeed.residual_bound_one_level
#print axioms BakerSeed.cubicIter_eq_iterate
