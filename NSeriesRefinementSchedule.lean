/-
  Module E -- step (iii), with the bootstrap constant PARAMETRIZED.

  The theorem now reads: for any majorant constant `C` with

      pi + tau <= C        and        C <= 9

  the scheduled hexagon-seeded ladder satisfies Theorem 4.9's conclusion
  unconditionally -- no residual budget assumed, only the rational schedule
  check against `C`.

  WHY PARAMETRIC.  The previous version hard-coded `C = 401/100`, which was
  forced by this Mathlib revision providing only `Real.pi_lt_four`; every tight
  numeric bound (`pi_lt_315`, `pi_lt_3141593`, `pi_lt_31415927`,
  `pi_lt_3141592654`, `pi_gt_314`, `pi_gt_3141592`) is absent, confirmed by
  `#check`.  Hard-coding it would publish a constant forced by one toolchain's
  lemma inventory: on a Mathlib with `pi_lt_315`, `C = 16/5` is admissible and
  the ten-level schedule is one refinement shorter.  Parametrizing confines the
  toolchain dependence to the instance, where it belongs.

      C = 401/100   needs only  pi < 4   ->  schedule (4,3,3,3,3,3,2,2,2,2)
      C = 16/5      needs       pi < 3.19 ->  schedule (4,3,3,3,3,2,2,2,2,2)

  `C <= 9` is what makes `C / M i <= 3/2` for every level, since `M i >= 6`.

  NEW IN THIS VERSION.  `schedResidual_le` and `abs_schedResidual_le_div`
  expose the PER-LEVEL residual bound.  These do not follow from
  `sched_certified`: a bound on `M_L |e_L|` says nothing about the individual
  `|r_i|`.  The per-level bounds come from the schedule's majorants, and the
  tableau composition needs them.

  Imports: Modules A, B, C and the ladder/tableau module.
  NOT COMPILED.
-/
import NSeriesSeedCubicBounds
import NSeriesCubicIteration
import NSeriesGeometricSchedule
import NSeriesLadderTableau

namespace BakerNSeries

open BakerSeed

/-! ## 1. Small arithmetic helpers -/

/-- Cancel a positive factor.  Built only from `div_le_div_of_nonneg_right` and
`field_simp`, both verified in `abs_err_le_div`. -/
lemma le_of_mul_le_mul_pos {a b c : ℝ} (hc : 0 < c) (h : c * a ≤ c * b) :
    a ≤ b := by
  have hdiv : (c * a) / c ≤ (c * b) / c :=
    div_le_div_of_nonneg_right h (le_of_lt hc)
  calc a = (c * a) / c := by field_simp
    _ ≤ (c * b) / c := hdiv
    _ = b := by field_simp

/-- `6 <= M i`, by a self-contained induction so that no `one_le_pow` name is
needed. -/
lemma ladderM_ge_six (i : ℕ) : (6 : ℝ) ≤ ladderM i := by
  unfold ladderM
  have h : (1 : ℝ) ≤ 3 ^ i := by
    induction i with
    | zero => norm_num
    | succ n ihn =>
        rw [pow_succ]
        nlinarith [ihn]
  nlinarith [h]

/-- `C = 401/100` is admissible on any Mathlib, needing only `Real.pi_lt_four`. -/
lemma admissible_401 {τ : ℝ} (hτ : τ ≤ 1 / 100) :
    Real.pi + τ ≤ 401 / 100 ∧ (401 : ℝ) / 100 ≤ 9 := by
  have h := Real.pi_lt_four
  exact ⟨by linarith, by norm_num⟩

/-! ## 2. The concrete scheduled ladder -/

/-- The hexagon-seeded ladder driven by a refinement schedule `k`: at each level
apply the 4:3 seed, then `k i` residual refinements. -/
noncomputable def schedLadder (k : ℕ → ℕ) : ℕ → ℝ
  | 0 => Real.pi / 6
  | (i + 1) =>
      schedLadder k i / 3
        + cubicIter seedF (seedDefect (schedLadder k i)) (k (i + 1))

/-- The residual actually produced at each level. -/
noncomputable def schedResidual (k : ℕ → ℕ) : ℕ → ℝ
  | 0 => 0
  | (i + 1) => cubicIter seedF (seedDefect (schedLadder k i)) (k (i + 1))

@[simp] lemma schedLadder_zero (k : ℕ → ℕ) :
    schedLadder k 0 = Real.pi / 6 := rfl

@[simp] lemma schedResidual_succ (k : ℕ → ℕ) (i : ℕ) :
    schedResidual k (i + 1)
      = cubicIter seedF (seedDefect (schedLadder k i)) (k (i + 1)) := rfl

/-- The scheduled ladder is a ladder in the sense of Section 4.3, so every
result of Proposition 4.6 and Theorem 4.9 applies. -/
lemma schedLadder_isLadder (k : ℕ → ℕ) :
    IsLadder (schedLadder k) (schedResidual k) := fun _ => rfl

/-- The hexagonal seed is exact, so the inherited term starts at zero. -/
lemma err_schedLadder_zero (k : ℕ → ℕ) : err (schedLadder k) 0 = 0 := by
  unfold err target
  rw [schedLadder_zero, ladderM_zero]
  ring

/-- The scaled level value, in the form the bootstrap uses. -/
lemma ladderM_mul_schedLadder (k : ℕ → ℕ) (i : ℕ) :
    ladderM i * schedLadder k i
      = Real.pi + ladderM i * err (schedLadder k) i := by
  have hne := ladderM_ne_zero i
  unfold err target
  field_simp
  ring

/-! ## 3. The bootstrap, for a general majorant constant -/

/-- `C / M n` is a legitimate majorant argument: positive, and at most `3/2`
because `M n >= 6` and `C <= 9`. -/
lemma bootstrapA_bounds {C : ℝ} (hC3 : 3 < C) (hC9 : C ≤ 9) (n : ℕ) :
    0 < C / ladderM n ∧ C / ladderM n ≤ 3 / 2 := by
  have hM := ladderM_pos n
  have h6 := ladderM_ge_six n
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hM]
  nlinarith [h6, hC9]

/-- The bootstrap proper: a scaled-error bound of `tau` puts the level input
strictly inside the admissible range `(0, C / M n]`. -/
lemma bootstrap_input {k : ℕ → ℕ} {C τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 100)
    (hC : Real.pi + τ ≤ C) (n : ℕ)
    (hn : ladderM n * |err (schedLadder k) n| ≤ τ) :
    0 < schedLadder k n ∧ schedLadder k n ≤ C / ladderM n := by
  have hM := ladderM_pos n
  have hMx := ladderM_mul_schedLadder k n
  have habs : |ladderM n * err (schedLadder k) n| ≤ τ := by
    rw [abs_mul, abs_of_pos hM]
    exact hn
  have hub : ladderM n * err (schedLadder k) n ≤ τ := (abs_le.mp habs).2
  have hlb : -τ ≤ ladderM n * err (schedLadder k) n := (abs_le.mp habs).1
  have hpi3 := Real.pi_gt_three
  constructor
  · have hgt : 0 < ladderM n * schedLadder k n := by
      rw [hMx]; linarith
    have hq : 0 < (ladderM n * schedLadder k n) / ladderM n := div_pos hgt hM
    calc (0 : ℝ) < (ladderM n * schedLadder k n) / ladderM n := hq
      _ = schedLadder k n := by field_simp
  · have hle : ladderM n * schedLadder k n ≤ C := by
      rw [hMx]; linarith
    have hdiv : (ladderM n * schedLadder k n) / ladderM n ≤ C / ladderM n :=
      div_le_div_of_nonneg_right hle (le_of_lt hM)
    calc schedLadder k n = (ladderM n * schedLadder k n) / ladderM n := by
          field_simp
      _ ≤ C / ladderM n := hdiv

/-- `C > 3` follows from admissibility, since `pi > 3` and `tau > 0`. -/
lemma C_gt_three {C τ : ℝ} (hτ0 : 0 < τ) (hC : Real.pi + τ ≤ C) : 3 < C := by
  have := Real.pi_gt_three
  linarith

/-! ## 4. Step (iii) -/

/-- **The schedule invariant.**  `L * (M i * |e i|) <= i * tau` for every
`i <= L`, by an induction in which the bootstrap and the budget advance
together.  The schedule hypothesis is purely rational. -/
theorem sched_budget_invariant
    (k : ℕ → ℕ) (L : ℕ) (hL : 0 < L) (C τ : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 100)
    (hC : Real.pi + τ ≤ C) (hC9 : C ≤ 9)
    (hsched : ∀ i, i < L →
      (L : ℝ) * ladderM (i + 1)
          * bseq ((C / ladderM i) ^ 3 / 81) (k (i + 1)) ≤ τ) :
    ∀ i, i ≤ L →
      (L : ℝ) * (ladderM i * |err (schedLadder k) i|) ≤ (i : ℝ) * τ := by
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hC3 := C_gt_three hτ0 hC
  intro i
  induction i with
  | zero =>
      intro _
      rw [err_schedLadder_zero]
      simp
  | succ n ih =>
      intro hiL
      have hnL : n < L := by omega
      have hn := ih (by omega)
      have hMn := ladderM_pos n
      have hMn1 := ladderM_pos (n + 1)
      have hnT : ladderM n * |err (schedLadder k) n| ≤ τ := by
        refine le_of_mul_le_mul_pos hLR ?_
        have hnLR : (n : ℝ) ≤ (L : ℝ) := by exact_mod_cast le_of_lt hnL
        nlinarith [hn, hτ0, hLR, hnLR]
      obtain ⟨hx0, hxA⟩ := bootstrap_input hτ0 hτ1 hC n hnT
      obtain ⟨hA0, hA32⟩ := bootstrapA_bounds hC3 hC9 n
      have hres : |schedResidual k (n + 1)|
          ≤ bseq ((C / ladderM n) ^ 3 / 81) (k (n + 1)) := by
        rw [schedResidual_succ]
        exact residual_bound_one_level hx0 hxA hA0 hA32 (k (n + 1))
      have hbud : (L : ℝ) * ladderM (n + 1) * |schedResidual k (n + 1)| ≤ τ := by
        have hmono :
            (L : ℝ) * ladderM (n + 1) * |schedResidual k (n + 1)|
              ≤ (L : ℝ) * ladderM (n + 1)
                  * bseq ((C / ladderM n) ^ 3 / 81) (k (n + 1)) := by
          have hpos : (0 : ℝ) ≤ (L : ℝ) * ladderM (n + 1) := by positivity
          exact mul_le_mul_of_nonneg_left hres hpos
        exact le_trans hmono (hsched n hnL)
      have hstep := err_succ (schedLadder k) (schedResidual k)
        (schedLadder_isLadder k) n
      have hMsucc := ladderM_succ n
      have htri : ladderM (n + 1) * |err (schedLadder k) (n + 1)|
          ≤ ladderM n * |err (schedLadder k) n|
            + ladderM (n + 1) * |schedResidual k (n + 1)| := by
        rw [hstep, hMsucc]
        have hsplit : |err (schedLadder k) n / 3 + schedResidual k (n + 1)|
            ≤ |err (schedLadder k) n| / 3 + |schedResidual k (n + 1)| := by
          calc |err (schedLadder k) n / 3 + schedResidual k (n + 1)|
              ≤ |err (schedLadder k) n / 3| + |schedResidual k (n + 1)| :=
                abs_add_le _ _
            _ = |err (schedLadder k) n| / 3 + |schedResidual k (n + 1)| := by
                rw [abs_div]
                norm_num
        nlinarith [hsplit, hMn, abs_nonneg (err (schedLadder k) n),
          abs_nonneg (schedResidual k (n + 1))]
      push_cast
      nlinarith [htri, hn, hbud, hLR, hMn1,
        abs_nonneg (err (schedLadder k) (n + 1)),
        abs_nonneg (schedResidual k (n + 1))]

/-- **Step (iii), the conclusion.**  The scheduled geometric ladder satisfies
Theorem 4.9's conclusion unconditionally. -/
theorem sched_certified
    (k : ℕ → ℕ) (L : ℕ) (hL : 0 < L) (C τ : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 100)
    (hC : Real.pi + τ ≤ C) (hC9 : C ≤ 9)
    (hsched : ∀ i, i < L →
      (L : ℝ) * ladderM (i + 1)
          * bseq ((C / ladderM i) ^ 3 / 81) (k (i + 1)) ≤ τ) :
    ladderM L * |err (schedLadder k) L| ≤ τ := by
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have h := sched_budget_invariant k L hL C τ hτ0 hτ1 hC hC9 hsched L le_rfl
  refine le_of_mul_le_mul_pos hLR ?_
  nlinarith [h, hτ0, hLR]

/-- The angular and chord forms together. -/
theorem sched_certified_both
    (k : ℕ → ℕ) (L : ℕ) (hL : 0 < L) (C τ : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 100)
    (hC : Real.pi + τ ≤ C) (hC9 : C ≤ 9)
    (hsched : ∀ i, i < L →
      (L : ℝ) * ladderM (i + 1)
          * bseq ((C / ladderM i) ^ 3 / 81) (k (i + 1)) ≤ τ) :
    ladderM L * |schedLadder k L - target L| ≤ τ ∧
      |ladderM L * Real.sin (schedLadder k L)
        - ladderM L * Real.sin (target L)| ≤ τ := by
  have hangle : ladderM L * |schedLadder k L - target L| ≤ τ := by
    have h := sched_certified k L hL C τ hτ0 hτ1 hC hC9 hsched
    unfold err at h
    exact h
  exact ⟨hangle,
    le_trans (sin_ladder_dist_le L (schedLadder k L) (target L)) hangle⟩

/-! ## 5. The per-level residual bounds

These do NOT follow from `sched_certified`: a bound on `M_L * |e_L|` says
nothing about the individual `|r_i|`.  They come from the schedule's majorants
together with the bootstrap, and the tableau composition consumes them. -/

/-- The residual at each level is bounded by its rational majorant. -/
theorem schedResidual_le
    (k : ℕ → ℕ) (L : ℕ) (hL : 0 < L) (C τ : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 100)
    (hC : Real.pi + τ ≤ C) (hC9 : C ≤ 9)
    (hsched : ∀ i, i < L →
      (L : ℝ) * ladderM (i + 1)
          * bseq ((C / ladderM i) ^ 3 / 81) (k (i + 1)) ≤ τ)
    (i : ℕ) (hi : i < L) :
    |schedResidual k (i + 1)| ≤ bseq ((C / ladderM i) ^ 3 / 81) (k (i + 1)) := by
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hC3 := C_gt_three hτ0 hC
  have hinv :=
    sched_budget_invariant k L hL C τ hτ0 hτ1 hC hC9 hsched i (le_of_lt hi)
  have hnT : ladderM i * |err (schedLadder k) i| ≤ τ := by
    refine le_of_mul_le_mul_pos hLR ?_
    have hiLR : (i : ℝ) ≤ (L : ℝ) := by exact_mod_cast le_of_lt hi
    nlinarith [hinv, hτ0, hLR, hiLR]
  obtain ⟨hx0, hxA⟩ := bootstrap_input hτ0 hτ1 hC i hnT
  obtain ⟨hA0, hA32⟩ := bootstrapA_bounds hC3 hC9 i
  rw [schedResidual_succ]
  exact residual_bound_one_level hx0 hxA hA0 hA32 (k (i + 1))

/-- The per-level residual bound in the divided form the tableau results use:
`|r j| <= tau / (L * M j)` for `1 <= j <= L`. -/
theorem abs_schedResidual_le_div
    (k : ℕ → ℕ) (L : ℕ) (hL : 0 < L) (C τ : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 100)
    (hC : Real.pi + τ ≤ C) (hC9 : C ≤ 9)
    (hsched : ∀ i, i < L →
      (L : ℝ) * ladderM (i + 1)
          * bseq ((C / ladderM i) ^ 3 / 81) (k (i + 1)) ≤ τ)
    (j : ℕ) (hj1 : 1 ≤ j) (hjL : j ≤ L) :
    |schedResidual k j| ≤ τ / ((L : ℝ) * ladderM j) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < L := by omega
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hMj := ladderM_pos (i + 1)
  have hd : (0 : ℝ) < (L : ℝ) * ladderM (i + 1) := by positivity
  have hres := schedResidual_le k L hL C τ hτ0 hτ1 hC hC9 hsched i hi
  have hmul : ((L : ℝ) * ladderM (i + 1)) * |schedResidual k (i + 1)| ≤ τ := by
    have hstep :
        ((L : ℝ) * ladderM (i + 1)) * |schedResidual k (i + 1)|
          ≤ ((L : ℝ) * ladderM (i + 1))
              * bseq ((C / ladderM i) ^ 3 / 81) (k (i + 1)) :=
      mul_le_mul_of_nonneg_left hres (le_of_lt hd)
    exact le_trans hstep (hsched i hi)
  have hdiv :
      (((L : ℝ) * ladderM (i + 1)) * |schedResidual k (i + 1)|)
          / ((L : ℝ) * ladderM (i + 1))
        ≤ τ / ((L : ℝ) * ladderM (i + 1)) :=
    div_le_div_of_nonneg_right hmul (le_of_lt hd)
  calc |schedResidual k (i + 1)|
      = (((L : ℝ) * ladderM (i + 1)) * |schedResidual k (i + 1)|)
          / ((L : ℝ) * ladderM (i + 1)) := by field_simp
    _ ≤ τ / ((L : ℝ) * ladderM (i + 1)) := hdiv

end BakerNSeries

/-! ## Axiom audit -/
#print axioms BakerNSeries.le_of_mul_le_mul_pos
#print axioms BakerNSeries.ladderM_ge_six
#print axioms BakerNSeries.admissible_401
#print axioms BakerNSeries.schedLadder_isLadder
#print axioms BakerNSeries.err_schedLadder_zero
#print axioms BakerNSeries.ladderM_mul_schedLadder
#print axioms BakerNSeries.bootstrapA_bounds
#print axioms BakerNSeries.bootstrap_input
#print axioms BakerNSeries.C_gt_three
#print axioms BakerNSeries.sched_budget_invariant
#print axioms BakerNSeries.sched_certified
#print axioms BakerNSeries.sched_certified_both
#print axioms BakerNSeries.schedResidual_le
#print axioms BakerNSeries.abs_schedResidual_le_div
