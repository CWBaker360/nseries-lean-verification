import Mathlib

/-
N-Series Stage 7: manuscript-form eleven-input budget corollary.

Cumulative standalone source. Stage 6 is included unchanged except for this
additional theorem. Stage 6 was compiled by the user with exit code 0 and
standard axiom dependencies. Stage 7 must still be compiled and audited.

This theorem specializes the budget hypothesis to the paper's formula
  tau = Bcon / (sum_{j=0}^{10} |w_j|).
It still assumes the eleven weights have sum 1. Identification of the
weights with the concrete Lagrange/Richardson vector remains a separate task.
-/
/-
  N-Series constructible ladder, stage 2.

  Standalone (imports only Mathlib), cumulative in the style of the A24 ellipse
  stages.  Stage 1 is reproduced verbatim from the VERIFIED v4 file, which
  compiled with exit code 0 and audited to
  [propext, Classical.choice, Quot.sound].

  Stage 1 (verified):
    err_succ                         Proposition 4.6, local form
    ladderM_mul_err                  Proposition 4.6, telescoped
    ladderM_mul_err_of_exact_start   the e₀ = 0 specialization
    err_zero_of_hex_start            the hexagonal seed is exact
    abs_ladderM_mul_err_le           per-level budget ⇒ bound at every level

  New in stage 2 (NOT yet compiled):
    abs_sin_sub_sin_le'              sin is 1-Lipschitz, elementary form
    sin_ladder_dist_le               Lemma 4.4, scaled by the panel count
    finite_target_ladder             Theorem 4.9, both conclusions, at every
                                     level j ≤ L rather than only at L
    abs_err_le_div                   the manuscript's divided form of (24)

  Two changes to the verified stage-1 text, both cosmetic:
    * dropped the `<;> ring` after `field_simp` in `hcancel` — it was the
      source of all three unreachable-tactic lint warnings;
    * extended the audit block to every declaration.

  The budget hypothesis is kept in the manuscript's division form
  `|r i| ≤ τ / (L * M i)`, since v4 proved it in that form.  No bridge lemma
  is needed and the Lean statement is the paper's statement.

  The one name I am least sure of is `Real.lipschitzWith_sin`; fallbacks are
  noted at its use site.
-/

namespace BakerNSeries

open Finset

/-! ## Stage 1 — verified in v4 -/

/-- Panel count at level `i` of the hexagon-seeded tripling ladder: `6 * 3 ^ i`. -/
noncomputable def ladderM (i : ℕ) : ℝ := 6 * 3 ^ i

@[simp] lemma ladderM_zero : ladderM 0 = 6 := by
  simp [ladderM]

lemma ladderM_pos (i : ℕ) : 0 < ladderM i := by
  unfold ladderM
  positivity

lemma ladderM_ne_zero (i : ℕ) : ladderM i ≠ 0 :=
  ne_of_gt (ladderM_pos i)

lemma ladderM_succ (i : ℕ) : ladderM (i + 1) = 3 * ladderM i := by
  unfold ladderM
  rw [pow_succ]
  ring

/-- The exact half-angle at level `i`, namely `π / M i`. -/
noncomputable def target (i : ℕ) : ℝ := Real.pi / ladderM i

/-- The targets telescope: each exact half-angle is one third of its parent.
This is the only property of `target` used below. -/
lemma target_succ (i : ℕ) : target (i + 1) = target i / 3 := by
  unfold target
  rw [ladderM_succ]
  field_simp

variable (xhat r : ℕ → ℝ)

/-- `IsLadder xhat r` says that `xhat` is produced by seeding the parent
half-angle and adding the refinement residual, which is exactly the
recurrence (23) of the manuscript. -/
def IsLadder : Prop := ∀ i : ℕ, xhat (i + 1) = xhat i / 3 + r (i + 1)

/-- Signed angular error of the ladder against the exact target. -/
noncomputable def err (i : ℕ) : ℝ := xhat i - target i

/-- **Proposition 4.6, local form.**  The inherited error is divided by three
and the fresh residual is added.  Note what this does *not* say: `r (i+1)` is
not applied to `err xhat i`, which is the whole content of the obstruction in
Proposition 4.8. -/
theorem err_succ (h : IsLadder xhat r) (i : ℕ) :
    err xhat (i + 1) = err xhat i / 3 + r (i + 1) := by
  unfold err
  rw [h i, target_succ]
  ring

/-- **Proposition 4.6, telescoped form.** -/
theorem ladderM_mul_err (h : IsLadder xhat r) (L : ℕ) :
    ladderM L * err xhat L
      = ladderM 0 * err xhat 0
        + ∑ i ∈ range L, ladderM (i + 1) * r (i + 1) := by
  induction L with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih, err_succ xhat r h n,
        ladderM_succ n]
      ring

/-- With an exactly constructible hexagonal start the inherited term vanishes,
so the scaled error is exactly the weighted residual sum. -/
theorem ladderM_mul_err_of_exact_start
    (h : IsLadder xhat r) (h0 : err xhat 0 = 0) (L : ℕ) :
    ladderM L * err xhat L = ∑ i ∈ range L, ladderM (i + 1) * r (i + 1) := by
  rw [ladderM_mul_err xhat r h L, h0, mul_zero, zero_add]

/-- The hexagonal seed `xhat 0 = π / 6` is an exact start. -/
lemma err_zero_of_hex_start (hx : xhat 0 = Real.pi / 6) : err xhat 0 = 0 := by
  unfold err target
  rw [hx, ladderM_zero]
  ring

/-- If each residual obeys `|r i| ≤ τ / (L * M i)` then every level `j ≤ L`
satisfies `M j * |err j| ≤ τ`.  Stated with `j ≤ L` on purpose: Corollary 6.2
reads the bound off all eleven levels of one ladder. -/
theorem abs_ladderM_mul_err_le
    (h : IsLadder xhat r) (h0 : err xhat 0 = 0)
    (L : ℕ) (hL : 0 < L) (τ : ℝ)
    (hr : ∀ i, 1 ≤ i → i ≤ L → |r i| ≤ τ / (L * ladderM i))
    (j : ℕ) (hj : j ≤ L) :
    ladderM j * |err xhat j| ≤ τ := by
  have key : ladderM j * |err xhat j|
      = |∑ i ∈ range j, ladderM (i + 1) * r (i + 1)| := by
    rw [← abs_of_pos (ladderM_pos j), ← abs_mul,
      ladderM_mul_err_of_exact_start xhat r h h0 j]
  rw [key]
  calc |∑ i ∈ range j, ladderM (i + 1) * r (i + 1)|
      ≤ ∑ i ∈ range j, |ladderM (i + 1) * r (i + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range j, τ / L := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hiL : i + 1 ≤ L := by
          have := Finset.mem_range.mp hi
          omega
        have hM := ladderM_pos (i + 1)
        rw [abs_mul, abs_of_pos hM]
        have := hr (i + 1) (by omega) hiL
        calc ladderM (i + 1) * |r (i + 1)|
            ≤ ladderM (i + 1) * (τ / (L * ladderM (i + 1))) := by
              exact mul_le_mul_of_nonneg_left this (le_of_lt hM)
          _ = τ / L := by
              field_simp
    _ = (j : ℝ) * (τ / L) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ τ := by
        have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
        have hden : (0 : ℝ) < (L : ℝ) * ladderM 1 :=
          mul_pos hLpos (ladderM_pos 1)
        have h1 := hr 1 le_rfl hL
        have hτdiv : 0 ≤ τ / ((L : ℝ) * ladderM 1) :=
          le_trans (abs_nonneg (r 1)) h1
        have hprod :
            0 ≤ (τ / ((L : ℝ) * ladderM 1)) * ((L : ℝ) * ladderM 1) :=
          mul_nonneg hτdiv (le_of_lt hden)
        have hcancel :
            (τ / ((L : ℝ) * ladderM 1)) * ((L : ℝ) * ladderM 1) = τ := by
          field_simp [ne_of_gt hden, ne_of_gt (ladderM_pos 1), ne_of_gt hLpos]
        have hτ : 0 ≤ τ := by
          rw [hcancel] at hprod
          exact hprod
        have hjL : (j : ℝ) ≤ (L : ℝ) := by exact_mod_cast hj
        have hscaled : (j : ℝ) * τ ≤ (L : ℝ) * τ :=
          mul_le_mul_of_nonneg_right hjL hτ
        have hdivide :
            ((j : ℝ) * τ) / (L : ℝ) ≤ ((L : ℝ) * τ) / (L : ℝ) :=
          div_le_div_of_nonneg_right hscaled (le_of_lt hLpos)
        calc
          (j : ℝ) * (τ / (L : ℝ)) = ((j : ℝ) * τ) / (L : ℝ) := by ring
          _ ≤ ((L : ℝ) * τ) / (L : ℝ) := hdivide
          _ = τ := by field_simp [ne_of_gt hLpos]

/-! ## Stage 2 — Theorem 4.9

The sine step is isolated first so that a lemma-name problem there is easy to
localize. -/

/-- `sin` is 1-Lipschitz, in the elementary form needed here.

If `Real.lipschitzWith_sin` is not the current name, fallbacks in order of
preference:
  * `Real.abs_sin_sub_sin_le a b`, if your Mathlib has it directly;
  * `Real.sin_sub_sin a b` rewrites the difference as
    `2 * sin ((a - b) / 2) * cos ((a + b) / 2)`, after which the bound follows
    from `Real.abs_sin_le` (or `Real.abs_sin_lt_abs_of_pos`) together with
    `Real.abs_cos_le_one`;
  * failing both, `Real.lipschitzWith_sin` may be stated for `Complex.sin` in
    your version — then use the mean value inequality for `Real.sin` with
    `|cos| ≤ 1`. -/
lemma abs_sin_sub_sin_le' (a b : ℝ) : |Real.sin a - Real.sin b| ≤ |a - b| := by
  have h := Real.lipschitzWith_sin.dist_le_mul a b
  simpa [Real.dist_eq] using h

/-- The sine transfer step, scaled by the panel count.  This is Lemma 4.4 of
the manuscript in the form Theorem 4.9 uses. -/
lemma sin_ladder_dist_le (j : ℕ) (a b : ℝ) :
    |ladderM j * Real.sin a - ladderM j * Real.sin b|
      ≤ ladderM j * |a - b| := by
  have hM := ladderM_pos j
  calc |ladderM j * Real.sin a - ladderM j * Real.sin b|
      = ladderM j * |Real.sin a - Real.sin b| := by
        rw [← mul_sub, abs_mul, abs_of_pos hM]
    _ ≤ ladderM j * |a - b| :=
        mul_le_mul_of_nonneg_left (abs_sin_sub_sin_le' a b) (le_of_lt hM)

/-- **Theorem 4.9 (finite-target certified ladder).**

Under the per-level budget both manuscript conclusions hold, and they hold at
*every* level `j ≤ L` rather than only at the target level — which is exactly
what Corollary 6.2 needs in order to certify all eleven tableau inputs from a
single ladder. -/
theorem finite_target_ladder
    (h : IsLadder xhat r) (h0 : err xhat 0 = 0)
    (L : ℕ) (hL : 0 < L) (τ : ℝ)
    (hr : ∀ i, 1 ≤ i → i ≤ L → |r i| ≤ τ / (L * ladderM i))
    (j : ℕ) (hj : j ≤ L) :
    ladderM j * |xhat j - target j| ≤ τ ∧
      |ladderM j * Real.sin (xhat j) - ladderM j * Real.sin (target j)| ≤ τ := by
  have hangle : ladderM j * |xhat j - target j| ≤ τ := by
    have hb := abs_ladderM_mul_err_le xhat r h h0 L hL τ hr j hj
    unfold err at hb
    exact hb
  exact ⟨hangle, le_trans (sin_ladder_dist_le j (xhat j) (target j)) hangle⟩

/-- The manuscript writes the first conclusion of Theorem 4.9 as
`|x̂_j − π/M_j| ≤ τ/M_j`.  Division-free in its reasoning: it divides a proved
inequality rather than inverting one, reusing the `div_le_div_of_nonneg_right`
step that already compiled above. -/
lemma abs_err_le_div {τ : ℝ} (j : ℕ) (h : ladderM j * |err xhat j| ≤ τ) :
    |err xhat j| ≤ τ / ladderM j := by
  have hM := ladderM_pos j
  have hdiv : (ladderM j * |err xhat j|) / ladderM j ≤ τ / ladderM j :=
    div_le_div_of_nonneg_right h (le_of_lt hM)
  calc |err xhat j|
      = (ladderM j * |err xhat j|) / ladderM j := by
        field_simp
    _ ≤ τ / ladderM j := hdiv

end BakerNSeries

/-! Stage 5: the finite Richardson tableau perturbation bound.
This stage is deliberately independent of the sine/asin estimates of Lemma 4.7.
The hypotheses `hinput` capture the Lipschitz transfer |sin(xhat)-sin(target)|
that will be established in a separate analytic module.
-/
namespace BakerNSeries

/-- Corollary 6.2, abstract weighted perturbation bound. Every one of the
`L+1` input errors is at most `τ`, so the weighted tableau error is at most
`τ * ∑ |w j|`. -/
theorem weighted_tableau_error_le
    (L : ℕ) (w p q : ℕ → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (hinput : ∀ j, j ≤ L → |q j - p j| ≤ τ) :
    |(∑ j ∈ Finset.range (L + 1), w j * q j) -
      (∑ j ∈ Finset.range (L + 1), w j * p j)| ≤
      τ * (∑ j ∈ Finset.range (L + 1), |w j|) := by
  have hrewrite :
      (∑ j ∈ Finset.range (L + 1), w j * q j) -
        (∑ j ∈ Finset.range (L + 1), w j * p j) =
      ∑ j ∈ Finset.range (L + 1), w j * (q j - p j) := by
    calc
      (∑ j ∈ Finset.range (L + 1), w j * q j) -
          (∑ j ∈ Finset.range (L + 1), w j * p j) =
          ∑ j ∈ Finset.range (L + 1), (w j * q j - w j * p j) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ j ∈ Finset.range (L + 1), w j * (q j - p j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
  rw [hrewrite]
  calc
    |∑ j ∈ Finset.range (L + 1), w j * (q j - p j)| ≤
        ∑ j ∈ Finset.range (L + 1), |w j * (q j - p j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (L + 1), |w j| * τ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (hinput j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) (abs_nonneg _)
    _ = τ * (∑ j ∈ Finset.range (L + 1), |w j|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Corollary 6.2, budget form: assuming that the weight sum times the
per-input tolerance is at most `Bcon`, the entire tableau perturbation is
at most `Bcon`. -/
theorem weighted_tableau_error_budget
    (L : ℕ) (w p q : ℕ → ℝ) (τ Bcon : ℝ) (hτ : 0 ≤ τ)
    (hinput : ∀ j, j ≤ L → |q j - p j| ≤ τ)
    (hbudget : τ * (∑ j ∈ Finset.range (L + 1), |w j|) ≤ Bcon) :
    |(∑ j ∈ Finset.range (L + 1), w j * q j) -
      (∑ j ∈ Finset.range (L + 1), w j * p j)| ≤ Bcon := by
  exact (weighted_tableau_error_le L w p q τ hτ hinput).trans hbudget

end BakerNSeries


/-! ## Stage 6 — full constructive-to-tableau bridge

Unlike the abstract weighted lemma, this theorem *derives* the sine-input
bound from the ladder recurrence and its residual hypothesis.
The finite-target budget hypotheses are exactly those of Theorem 4.9.
-/
namespace BakerNSeries

/-- Corollary 6.2, derived form. Every input of the weighted tableau is
actually `M_j * sin(xhat j)`; the ideal input is `M_j * sin(target j)`.
The hypothesis on the residuals is *not* replaced by an assumed input bound. -/
theorem constructible_tableau_from_ladder
    (xhat r w : ℕ → ℝ)
    (h : IsLadder xhat r) (h0 : err xhat 0 = 0)
    (L : ℕ) (hL : 0 < L) (τ Bcon : ℝ) (hτ : 0 ≤ τ)
    (hr : ∀ i, 1 ≤ i → i ≤ L → |r i| ≤ τ / (L * ladderM i))
    (hbudget : τ * (∑ j ∈ Finset.range (L + 1), |w j|) ≤ Bcon) :
    |(∑ j ∈ Finset.range (L + 1),
        w j * (ladderM j * Real.sin (xhat j))) -
      (∑ j ∈ Finset.range (L + 1),
        w j * (ladderM j * Real.sin (target j)))| ≤ Bcon := by
  apply weighted_tableau_error_budget L w
      (fun j => ladderM j * Real.sin (target j))
      (fun j => ladderM j * Real.sin (xhat j)) τ Bcon hτ
  · intro j hj
    exact (finite_target_ladder xhat r h h0 L hL τ hr j hj).2
  · exact hbudget

/-- The eleven-input canonical instance (`j = 0, ..., 10`). -/
theorem constructible_tableau_eleven_inputs
    (xhat r w : ℕ → ℝ)
    (h : IsLadder xhat r) (h0 : err xhat 0 = 0)
    (τ Bcon : ℝ) (hτ : 0 ≤ τ)
    (hr : ∀ i, 1 ≤ i → i ≤ 10 → |r i| ≤ τ / (10 * ladderM i))
    (hbudget : τ * (∑ j ∈ Finset.range 11, |w j|) ≤ Bcon) :
    |(∑ j ∈ Finset.range 11,
        w j * (ladderM j * Real.sin (xhat j))) -
      (∑ j ∈ Finset.range 11,
        w j * (ladderM j * Real.sin (target j)))| ≤ Bcon := by
  exact constructible_tableau_from_ladder xhat r w h h0 10 (by omega)
    τ Bcon hτ hr hbudget

end BakerNSeries

/-! ## Axiom audit: original plus new derived claims -/
#print axioms BakerNSeries.err_succ
#print axioms BakerNSeries.ladderM_mul_err
#print axioms BakerNSeries.ladderM_mul_err_of_exact_start
#print axioms BakerNSeries.abs_ladderM_mul_err_le
#print axioms BakerNSeries.abs_sin_sub_sin_le'
#print axioms BakerNSeries.sin_ladder_dist_le
#print axioms BakerNSeries.finite_target_ladder
#print axioms BakerNSeries.abs_err_le_div
#print axioms BakerNSeries.weighted_tableau_error_le
#print axioms BakerNSeries.weighted_tableau_error_budget
#print axioms BakerNSeries.constructible_tableau_from_ladder
#print axioms BakerNSeries.constructible_tableau_eleven_inputs

namespace BakerNSeries

/-- Manuscript Corollary 6.2, with `τ = Bcon / ∑ |w_j|` inserted explicitly.
The normalization condition ensures that the denominator is positive. -/
theorem constructible_tableau_eleven_allowance
    (xhat r w : ℕ → ℝ)
    (h : IsLadder xhat r) (h0 : err xhat 0 = 0)
    (Bcon : ℝ) (hBcon : 0 < Bcon)
    (hweights : (∑ j ∈ Finset.range 11, w j) = 1)
    (hr : ∀ i, 1 ≤ i → i ≤ 10 →
      |r i| ≤ (Bcon / (∑ j ∈ Finset.range 11, |w j|)) /
        (10 * ladderM i)) :
    |(∑ j ∈ Finset.range 11,
        w j * (ladderM j * Real.sin (xhat j))) -
      (∑ j ∈ Finset.range 11,
        w j * (ladderM j * Real.sin (target j)))| ≤ Bcon := by
  let S : ℝ := ∑ j ∈ Finset.range 11, |w j|
  have hSge : (1 : ℝ) ≤ S := by
    have htriangle :
        |∑ j ∈ Finset.range 11, w j| ≤ S := by
      exact Finset.abs_sum_le_sum_abs _ _
    rw [hweights, abs_one] at htriangle
    exact htriangle
  have hSpos : 0 < S := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hSge
  have hSnonzero : S ≠ 0 := ne_of_gt hSpos
  have hτ : 0 ≤ Bcon / S := div_nonneg (le_of_lt hBcon) (le_of_lt hSpos)
  have hbudget : (Bcon / S) * S ≤ Bcon := by
    field_simp [hSnonzero] <;> norm_num
  exact constructible_tableau_eleven_inputs xhat r w h h0
    (Bcon / S) Bcon hτ (by simpa only [S] using hr)
    (by simpa only [S] using hbudget)

end BakerNSeries

#print axioms BakerNSeries.constructible_tableau_eleven_allowance


/-! ## Stage 8 — the canonical eleven Richardson weights

Closes the remaining abstractness in Corollary 6.2: Stage 6 and Stage 7 hold for
*arbitrary* weights `w`, so nothing yet tied them to the canonical Richardson
vector of Theorem 6.1.  This stage supplies that vector explicitly, bounds its
absolute-weight sum by `13/10`, and specializes the Stage 6 bridge to it.

Design notes.

* Only an **upper bound** on `∑ |w j|` is needed.  The exact value is
  `4506376289742420050495113657881073 / 3506332999261206519449485758693376`
  `= 1.2852105862996828...`, whose denominator is 34 digits; `13/10` is a
  comfortable majorant and makes the arithmetic cheap.  With
  `τ = (10/13) * Bcon` the budget closes as
  `τ * ∑|w j| ≤ (10/13) * Bcon * (13/10) = Bcon`.

* The weights are stated over `ℚ` so that every bound is exact rational
  arithmetic, then cast to `ℝ` for the bridge.

* **Do not use `native_decide` anywhere in this file.**  It would introduce
  `Lean.ofReduceBool` into the axiom audit and break the clean-axiom record.
  Every arithmetic step below is `norm_num`.

* The signs alternate as `(-1)^i`, which is why `canonicalWeightAbs` can be
  given by positive literals and matched against `|canonicalWeight i|`
  index by index.
-/

namespace BakerNSeries

open Finset

/-- The canonical Richardson weights for the eleven tripling levels
`M j = 6 * 3 ^ j`, as exact rationals. -/
def canonicalWeight : ℕ → ℚ
  | 0  => (1 : ℚ) / 26675946836622770539385872686850599297942028288000000
  | 1  => (-9 : ℚ) / 61204694701795202569762266199999287132160000
  | 2  => (729 : ℚ) / 12638401240524007097892513356185600000
  | 3  => (-531441 : ℚ) / 213738842427517756690074173440000
  | 4  => (3486784401 : ℚ) / 293149945039255224765644800000
  | 5  => (-205891132094649 : ℚ) / 32571725791581255667548160000
  | 6  => (109418989131512359209 : ℚ) / 293149945039255224765644800000
  | 7  => (-523347633027360537213511521 : ℚ) / 213738842427517756690074173440000
  | 8  => (22528399544939174411840147874772641 : ℚ) / 12638401240524007097892513356185600000
  | 9  => (-8727963568087712425891397479476727340041449 : ℚ) / 61204694701795202569762266199999287132160000
  | 10 => (30432527221704537086371993251530170531786747066637049 : ℚ) / 26675946836622770539385872686850599297942028288000000
  | _ => 0

/-- Absolute values of `canonicalWeight`, as positive literals. -/
def canonicalWeightAbs : ℕ → ℚ
  | 0  => (1 : ℚ) / 26675946836622770539385872686850599297942028288000000
  | 1  => (9 : ℚ) / 61204694701795202569762266199999287132160000
  | 2  => (729 : ℚ) / 12638401240524007097892513356185600000
  | 3  => (531441 : ℚ) / 213738842427517756690074173440000
  | 4  => (3486784401 : ℚ) / 293149945039255224765644800000
  | 5  => (205891132094649 : ℚ) / 32571725791581255667548160000
  | 6  => (109418989131512359209 : ℚ) / 293149945039255224765644800000
  | 7  => (523347633027360537213511521 : ℚ) / 213738842427517756690074173440000
  | 8  => (22528399544939174411840147874772641 : ℚ) / 12638401240524007097892513356185600000
  | 9  => (8727963568087712425891397479476727340041449 : ℚ) / 61204694701795202569762266199999287132160000
  | 10 => (30432527221704537086371993251530170531786747066637049 : ℚ) / 26675946836622770539385872686850599297942028288000000
  | _ => 0

/-- `canonicalWeightAbs` really is the absolute value, index by index. -/
lemma abs_canonicalWeight (i : ℕ) (hi : i < 11) :
    |canonicalWeight i| = canonicalWeightAbs i := by
  interval_cases i <;>
    simp only [canonicalWeight, canonicalWeightAbs] <;>
    norm_num

/-- The weights are normalized: `∑ w j = 1`.  This is the condition
`Stage 7`'s allowance theorem needs. -/
lemma canonicalWeight_sum : (∑ i ∈ Finset.range 11, canonicalWeight i) = 1 := by
  norm_num [Finset.sum_range_succ, canonicalWeight]

/-- **The absolute-weight bound.**  Exact value `1.28521...`, majorized by
`13/10`. -/
lemma canonicalWeight_abs_sum_le :
    (∑ i ∈ Finset.range 11, |canonicalWeight i|) ≤ 13 / 10 := by
  have hcongr : (∑ i ∈ Finset.range 11, |canonicalWeight i|)
      = ∑ i ∈ Finset.range 11, canonicalWeightAbs i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact abs_canonicalWeight i (Finset.mem_range.mp hi)
  rw [hcongr]
  norm_num [Finset.sum_range_succ, canonicalWeightAbs]

/-- The real-valued form used by the Stage 6 bridge. -/
lemma canonicalWeightR_abs_sum_le :
    (∑ j ∈ Finset.range 11, |((canonicalWeight j : ℚ) : ℝ)|) ≤ 13 / 10 := by
  have hq := canonicalWeight_abs_sum_le
  have hcast : (∑ j ∈ Finset.range 11, |((canonicalWeight j : ℚ) : ℝ)|)
      = (((∑ i ∈ Finset.range 11, |canonicalWeight i|) : ℚ) : ℝ) := by
    push_cast
    rfl
  rw [hcast]
  have : (((∑ i ∈ Finset.range 11, |canonicalWeight i|) : ℚ) : ℝ)
      ≤ ((13 / 10 : ℚ) : ℝ) := by exact_mod_cast hq
  simpa using this

/-- **Corollary 6.2, canonical instance.**

The weights are no longer abstract: they are the explicit Richardson vector of
`canonicalWeight`.  Choosing `τ = (10/13) * Bcon` discharges the budget
hypothesis from `canonicalWeight_abs_sum_le`, so the only remaining hypothesis
is the residual budget on the ladder. -/
theorem canonical_constructible_tableau
    (xhat r : ℕ → ℝ)
    (h : IsLadder xhat r) (h0 : err xhat 0 = 0)
    (Bcon : ℝ) (hBcon : 0 ≤ Bcon)
    (hr : ∀ i, 1 ≤ i → i ≤ 10 →
      |r i| ≤ ((10 / 13) * Bcon) / (10 * ladderM i)) :
    |(∑ j ∈ Finset.range 11,
        ((canonicalWeight j : ℚ) : ℝ) * (ladderM j * Real.sin (xhat j))) -
      (∑ j ∈ Finset.range 11,
        ((canonicalWeight j : ℚ) : ℝ) * (ladderM j * Real.sin (target j)))|
      ≤ Bcon := by
  have hτ : (0 : ℝ) ≤ (10 / 13) * Bcon := by positivity
  have hbudget :
      ((10 / 13) * Bcon) *
          (∑ j ∈ Finset.range 11, |((canonicalWeight j : ℚ) : ℝ)|) ≤ Bcon := by
    calc ((10 / 13) * Bcon) *
            (∑ j ∈ Finset.range 11, |((canonicalWeight j : ℚ) : ℝ)|)
        ≤ ((10 / 13) * Bcon) * (13 / 10) :=
          mul_le_mul_of_nonneg_left canonicalWeightR_abs_sum_le hτ
      _ = Bcon := by ring
  exact constructible_tableau_eleven_inputs xhat r
    (fun j => ((canonicalWeight j : ℚ) : ℝ)) h h0 ((10 / 13) * Bcon) Bcon hτ hr
    hbudget

/-! ### Identification with the manuscript's Lagrange formula

The manuscript defines the weights as `w i = ∏_{k ≠ i} x k / (x k - x i)` at the
nodes `x j = (6 * 3 ^ j)⁻²`.  The product over `k ≠ i` is written with an `if`
rather than `Finset.erase`, which is the same product and evaluates far more
predictably.

This section is independent of everything above: the bound and the bridge do
not depend on it.  It is also the expensive part — eleven goals, each a
ten-factor product of rationals with ~50-digit denominators — so if it is slow
or fails, the results above still stand and this can be iterated on separately.
-/

/-- The manuscript's interpolation nodes `x j = (6 * 3 ^ j)⁻²`. -/
def canonicalNode (j : ℕ) : ℚ := 1 / (6 * 3 ^ j) ^ 2

/-- The manuscript's Lagrange weight at the origin,
`w i = ∏_{k ≠ i} x k / (x k - x i)`. -/
def lagrangeWeight (i : ℕ) : ℚ :=
  ∏ k ∈ Finset.range 11,
    (if k = i then 1 else canonicalNode k / (canonicalNode k - canonicalNode i))

/-- The explicit literals of `canonicalWeight` are the manuscript's Lagrange
weights.  This is what makes the canonical instance above an instance of
Theorem 6.1's tableau rather than an unrelated rational vector. -/
lemma canonicalWeight_eq_lagrangeWeight (i : ℕ) (hi : i < 11) :
    canonicalWeight i = lagrangeWeight i := by
  interval_cases i <;>
    norm_num [canonicalWeight, lagrangeWeight, canonicalNode,
      Finset.prod_range_succ]

end BakerNSeries

/-! ## Stage 8 axiom audit -/
#print axioms BakerNSeries.abs_canonicalWeight
#print axioms BakerNSeries.canonicalWeight_sum
#print axioms BakerNSeries.canonicalWeight_abs_sum_le
#print axioms BakerNSeries.canonicalWeightR_abs_sum_le
#print axioms BakerNSeries.canonical_constructible_tableau
#print axioms BakerNSeries.canonicalWeight_eq_lagrangeWeight
