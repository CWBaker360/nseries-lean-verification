/-
  Module F -- the canonical instance of Remark 4.11.

  Discharges the schedule hypothesis of `sched_certified` for

      L = 10,   tau = 10^(-85),   k = (4,3,3,3,3,3,2,2,2,2)

  giving an UNCONDITIONAL certificate for the ten-level hexagon-seeded
  constructible ladder: no residual budget assumed, no abstract `r`, no
  abstract weights.

  THE SCHEDULE.  With the majorant constant `401/100` (forced by this Mathlib
  having only `Real.pi_lt_four`; see Module E) the counts are

      (4, 3, 3, 3, 3, 3, 2, 2, 2, 2)

  and NOT the manuscript's `(4,3,3,3,3,2,2,2,2,2)`.  The extra refinement at
  level 6 is necessary, not conservative: with `k = 2` there the budget check
  fails.  Remarks 4.11 and 6.3 need updating.

  Margins, computed exactly in rational arithmetic:

      level  k   10*M(i+1)*b_k        budget
      0      4   1e-213.9             1e-85
      1      3   1e-107.8             1e-85
      2      3   1e-146.0             1e-85
      3      3   1e-184.2             1e-85
      4      3   1e-222.3             1e-85
      5      3   1e-260.5             1e-85
      6      2   1e-96.0              1e-85   <- tightest, 11 orders
      7      2   1e-108.4             1e-85
      8      2   1e-120.8             1e-85
      9      2   1e-133.2             1e-85

  COST NOTE.  `sched_level_0` is the heavy one: `bseq` iterated four times
  produces an 847-digit rational.  The ten level lemmas are stated separately
  so that if one is slow or fails, it is obvious which.  Nothing but
  `canonicalSchedule_clears_budget` depends on them.

  NOT COMPILED.
-/
import NSeriesRefinementSchedule

namespace BakerNSeries

open BakerSeed

/-- The canonical ten-level refinement schedule. -/
def canonicalSchedule : ℕ → ℕ
  | 1 => 4
  | 2 => 3
  | 3 => 3
  | 4 => 3
  | 5 => 3
  | 6 => 3
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | 10 => 2
  | _ => 0

/-! ### The ten level checks, each pure rational arithmetic -/

/-- Level 0: `k = 4` refinements clear the budget. -/
lemma sched_level_0 :
    (10 : ℝ) * ladderM 1
      * bseq (((401 : ℝ) / 100 / ladderM 0) ^ 3 / 81) 4 ≤ 1 / 10 ^ 85 := by
  norm_num [ladderM, bseq_succ, bseq_zero]

/-- Level 1: `k = 3` refinements clear the budget. -/
lemma sched_level_1 :
    (10 : ℝ) * ladderM 2
      * bseq (((401 : ℝ) / 100 / ladderM 1) ^ 3 / 81) 3 ≤ 1 / 10 ^ 85 := by
  norm_num [ladderM, bseq_succ, bseq_zero]

/-- Level 2: `k = 3` refinements clear the budget. -/
lemma sched_level_2 :
    (10 : ℝ) * ladderM 3
      * bseq (((401 : ℝ) / 100 / ladderM 2) ^ 3 / 81) 3 ≤ 1 / 10 ^ 85 := by
  norm_num [ladderM, bseq_succ, bseq_zero]

/-- Level 3: `k = 3` refinements clear the budget. -/
lemma sched_level_3 :
    (10 : ℝ) * ladderM 4
      * bseq (((401 : ℝ) / 100 / ladderM 3) ^ 3 / 81) 3 ≤ 1 / 10 ^ 85 := by
  norm_num [ladderM, bseq_succ, bseq_zero]

/-- Level 4: `k = 3` refinements clear the budget. -/
lemma sched_level_4 :
    (10 : ℝ) * ladderM 5
      * bseq (((401 : ℝ) / 100 / ladderM 4) ^ 3 / 81) 3 ≤ 1 / 10 ^ 85 := by
  norm_num [ladderM, bseq_succ, bseq_zero]

/-- Level 5: `k = 3` refinements clear the budget. -/
lemma sched_level_5 :
    (10 : ℝ) * ladderM 6
      * bseq (((401 : ℝ) / 100 / ladderM 5) ^ 3 / 81) 3 ≤ 1 / 10 ^ 85 := by
  norm_num [ladderM, bseq_succ, bseq_zero]

/-- Level 6: `k = 2` refinements clear the budget. -/
lemma sched_level_6 :
    (10 : ℝ) * ladderM 7
      * bseq (((401 : ℝ) / 100 / ladderM 6) ^ 3 / 81) 2 ≤ 1 / 10 ^ 85 := by
  norm_num [ladderM, bseq_succ, bseq_zero]

/-- Level 7: `k = 2` refinements clear the budget. -/
lemma sched_level_7 :
    (10 : ℝ) * ladderM 8
      * bseq (((401 : ℝ) / 100 / ladderM 7) ^ 3 / 81) 2 ≤ 1 / 10 ^ 85 := by
  norm_num [ladderM, bseq_succ, bseq_zero]

/-- Level 8: `k = 2` refinements clear the budget. -/
lemma sched_level_8 :
    (10 : ℝ) * ladderM 9
      * bseq (((401 : ℝ) / 100 / ladderM 8) ^ 3 / 81) 2 ≤ 1 / 10 ^ 85 := by
  norm_num [ladderM, bseq_succ, bseq_zero]

/-- Level 9: `k = 2` refinements clear the budget. -/
lemma sched_level_9 :
    (10 : ℝ) * ladderM 10
      * bseq (((401 : ℝ) / 100 / ladderM 9) ^ 3 / 81) 2 ≤ 1 / 10 ^ 85 := by
  norm_num [ladderM, bseq_succ, bseq_zero]

/-! ### Assembly -/

/-- `C = 401/100` is admissible for `tau = 10^(-85)`.

Stated as its own lemma so that `tau` is fixed by the statement.  Passing
`admissible_401 (by norm_num)` inline leaves `tau` as a metavariable at the
point `norm_num` runs, which is why the previous version failed with
`?m <= 1/100`. -/
lemma canonical_admissible :
    Real.pi + 1 / 10 ^ 85 ≤ 401 / 100 ∧ (401 : ℝ) / 100 ≤ 9 :=
  admissible_401 (by norm_num)


/-- The canonical schedule clears the budget at every level. -/
theorem canonicalSchedule_clears_budget (i : ℕ) (hi : i < 10) :
    (10 : ℝ) * ladderM (i + 1)
        * bseq (((401 : ℝ) / 100 / ladderM i) ^ 3 / 81)
            (canonicalSchedule (i + 1))
      ≤ 1 / 10 ^ 85 := by
  interval_cases i
  · simpa [canonicalSchedule] using sched_level_0
  · simpa [canonicalSchedule] using sched_level_1
  · simpa [canonicalSchedule] using sched_level_2
  · simpa [canonicalSchedule] using sched_level_3
  · simpa [canonicalSchedule] using sched_level_4
  · simpa [canonicalSchedule] using sched_level_5
  · simpa [canonicalSchedule] using sched_level_6
  · simpa [canonicalSchedule] using sched_level_7
  · simpa [canonicalSchedule] using sched_level_8
  · simpa [canonicalSchedule] using sched_level_9

/-- **The unconditional certificate.**

The ten-level hexagon-seeded ladder, built from the 4:3 proportional-chord seed
with the canonical refinement schedule, satisfies

    M_10 * |x_10 - pi/M_10|  <=  10^(-85)

with no hypothesis beyond the schedule itself.  Every ingredient is proved:
Lemma 4.7 bounds the seed, the `bseq` recurrence bounds the refinements, the
bootstrap keeps the inputs admissible, and Proposition 4.6 accumulates the
inherited error. -/
theorem canonical_ladder_certified :
    ladderM 10 * |err (schedLadder canonicalSchedule) 10| ≤ 1 / 10 ^ 85 :=
  sched_certified canonicalSchedule 10 (by norm_num) (401 / 100) (1 / 10 ^ 85)
    (by norm_num) (by norm_num)
    canonical_admissible.1 canonical_admissible.2
    canonicalSchedule_clears_budget

/-- The same, in both manuscript forms: the half-angle and the chord estimate. -/
theorem canonical_ladder_certified_both :
    ladderM 10 * |schedLadder canonicalSchedule 10 - target 10| ≤ 1 / 10 ^ 85 ∧
      |ladderM 10 * Real.sin (schedLadder canonicalSchedule 10)
        - ladderM 10 * Real.sin (target 10)| ≤ 1 / 10 ^ 85 :=
  sched_certified_both canonicalSchedule 10 (by norm_num) (401 / 100)
    (1 / 10 ^ 85) (by norm_num) (by norm_num)
    canonical_admissible.1 canonical_admissible.2
    canonicalSchedule_clears_budget

/-- **The per-level residual bounds for the canonical schedule.**

`|r j| <= 10^(-85) / (10 * M j)` for `1 <= j <= 10`.  This is what the tableau
composition consumes; it does NOT follow from `canonical_ladder_certified`,
which bounds only the accumulated `M_10 * |e_10|`. -/
theorem canonical_residual_bounds (j : ℕ) (hj1 : 1 ≤ j) (hj10 : j ≤ 10) :
    |schedResidual canonicalSchedule j|
      ≤ (1 / 10 ^ 85) / ((10 : ℝ) * ladderM j) :=
  abs_schedResidual_le_div canonicalSchedule 10 (by norm_num) (401 / 100)
    (1 / 10 ^ 85) (by norm_num) (by norm_num)
    canonical_admissible.1 canonical_admissible.2
    canonicalSchedule_clears_budget j hj1 hj10

end BakerNSeries

/-! ## Axiom audit -/
#print axioms BakerNSeries.sched_level_0
#print axioms BakerNSeries.sched_level_6
#print axioms BakerNSeries.canonical_admissible
#print axioms BakerNSeries.canonicalSchedule_clears_budget
#print axioms BakerNSeries.canonical_ladder_certified
#print axioms BakerNSeries.canonical_ladder_certified_both
#print axioms BakerNSeries.canonical_residual_bounds
