/-
  Lemma 4.7 of the N-Series manuscript: the elementary seed and cubic bounds
  for the 4:3 proportional-chord construction.

      0 < d(x) ≤ x³/81,     sgn F(z) = -sgn z,     |F(z)| ≤ |z|³/3

  NOT COMPILED — no Lean toolchain where this was written.

  ---------------------------------------------------------------------------
  TWO SIMPLIFICATIONS over the manuscript's proof
  ---------------------------------------------------------------------------

  1.  `F z = -(seedDefect (3*z))`, exactly (`F_eq_neg_seedDefect` below).  Since
      `d(3z) ≤ (3z)³/81 = z³/3`, both `F` claims are corollaries of the `d`
      claims at `x = 3z`.  The manuscript proves them by a separate Taylor
      argument on `[0,1/2]`; that is not needed.

  2.  The `d` bound is proved on `(0, 3/2]` rather than `(0, π/6]`.  Numerically
      the worst ratio `d(x)/(x³/81)` on `(0,3/2]` is `0.2452`, attained at the
      right endpoint, so there is a factor of four to spare.  Proving it there
      is what lets simplification 1 reach the manuscript's full range
      `|z| ≤ 1/2`, since `3·(1/2) = 3/2`.

  So the whole lemma rests on two sine inequalities on `(0, 3/2]`:

      (A)  sin (x/3) < (4/3) * sin (x/4)
      (B)  (4/3) * sin (x/4) ≤ sin (x/3 + x³/81)

  plus one `arcsin` monotonicity step.

  ---------------------------------------------------------------------------
  WHERE THE MATHLIB RISK IS
  ---------------------------------------------------------------------------

  All uncertainty about Mathlib names is deliberately confined to the three
  helper lemmas of §1 (`sin_lower`, `sin_upper`, `arcsin_le_of_le_sin`) and
  `arcsin_lt_of_sin_lt`.  Everything after §1 is polynomial arithmetic and
  should go through unchanged once those four are fixed.  Fallbacks are given
  at each use site.
-/
import Mathlib

namespace BakerSeed

open Real

/-! ## 1. Helpers — the only places Mathlib names are in question -/

/-- Two-sided cubic Taylor bound for `sin` on `[0,1]`, lower half.

Primary route is `Real.sin_bound : |x| ≤ 1 → |sin x - (x - x^3/6)| ≤ |x|^4 * (5/96)`.
If that name or shape differs, alternatives:
  * `Real.sin_bound` may be stated for `Complex.sin`; there is a real version in
    `Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`;
  * a weaker but very stable substitute is
    `Real.sin_gt_sub_cube : 0 < x → x ≤ 1 → x - x^3/4 < sin x`.
    **Warning:** the `x³/4` constant is NOT strong enough for lemma (B) below;
    it gives `d(x) ≤ x³/54`, which is weaker than `x³/81`.  If you must fall
    back to it, the manuscript's `x³/81` has to be relaxed accordingly, and
    then `|F(z)| ≤ 2|z|³/3` replaces `|z|³/3` and the `b ↦ b³/3` recurrence of
    Remark 4.11 becomes `b ↦ 2b³/3`.  Prefer fixing `sin_bound`. -/
lemma sin_lower {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t - t ^ 3 / 6 - 5 / 96 * t ^ 4 ≤ Real.sin t := by
  have habs : |t| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have hb := Real.sin_bound habs
  rw [abs_le] at hb
  rw [abs_of_nonneg h0] at hb
  have hpow : t ^ 5 ≤ t ^ 4 := by
    nlinarith [mul_nonneg (pow_nonneg h0 4) (sub_nonneg.mpr h1)]
  nlinarith [hb.1]

/-- Two-sided cubic Taylor bound for `sin` on `[0,1]`, upper half. -/
lemma sin_upper {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Real.sin t ≤ t - t ^ 3 / 6 + 5 / 96 * t ^ 4 := by
  have habs : |t| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have hb := Real.sin_bound habs
  rw [abs_le] at hb
  rw [abs_of_nonneg h0] at hb
  have hpow : t ^ 5 ≤ t ^ 4 := by
    nlinarith [mul_nonneg (pow_nonneg h0 4) (sub_nonneg.mpr h1)]
  nlinarith [hb.2]

/-- `arcsin w ≤ θ` whenever `w ≤ sin θ` and `θ` is in the principal range.

Primary route: monotonicity of `arcsin` plus `Real.arcsin_sin`.  If
`Real.arcsin_le_arcsin` has a different signature, alternatives:
  * `Real.arcsin_le_iff_le_sin`, if present, gives this directly;
  * `Real.monotone_arcsin` or `Real.arcsin_mono` in place of
    `Real.arcsin_le_arcsin`. -/
lemma arcsin_le_of_le_sin {w θ : ℝ} (hw : -1 ≤ w) (hθl : -(π / 2) ≤ θ)
    (hθu : θ ≤ π / 2) (h : w ≤ Real.sin θ) : Real.arcsin w ≤ θ := by
  have hmono : Real.arcsin w ≤ Real.arcsin (Real.sin θ) :=
    Real.arcsin_le_arcsin h
  rwa [Real.arcsin_sin hθl hθu] at hmono

/-- Strict version, for the strict positivity of the defect.

If `Real.arcsin_lt_arcsin` is unavailable, `Real.strictMonoOn_arcsin` applied on
`Set.Icc (-1) 1` serves, or derive it from `arcsin_le_of_le_sin` plus
injectivity. -/
lemma arcsin_lt_of_sin_lt {w θ : ℝ} (hθl : -(π / 2) ≤ θ) (hθu : θ ≤ π / 2)
    (hw : w ≤ 1) (h : Real.sin θ < w) : θ < Real.arcsin w := by
  have hmono : Real.arcsin (Real.sin θ) < Real.arcsin w :=
    Real.arcsin_lt_arcsin (by linarith [Real.neg_one_le_sin θ]) h hw
  rwa [Real.arcsin_sin hθl hθu] at hmono

/-! ## 2. The construction -/

/-- The 4:3 proportional-chord seed, in half-angle form:
`s x = arcsin ((4/3) * sin (x/4))`, equal to `D(2x)/2` for the manuscript's `D`. -/
noncomputable def seedS (x : ℝ) : ℝ := Real.arcsin (4 / 3 * Real.sin (x / 4))

/-- The local defect of the seed, `d x = s x - x/3`. -/
noncomputable def seedDefect (x : ℝ) : ℝ := seedS x - x / 3

/-- The residual-transfer map `F z = z - s (3z)`. -/
noncomputable def seedF (z : ℝ) : ℝ := z - seedS (3 * z)

/-- **The identity that collapses the `F` half of Lemma 4.7.** -/
lemma F_eq_neg_seedDefect (z : ℝ) : seedF z = -seedDefect (3 * z) := by
  unfold seedF seedDefect
  ring

/-! ## 3. The two sine inequalities

Both are stated on `(0, 3/2]`, which is what simplification 2 above needs. -/

/-- Inequality (A): `sin (x/3) < (4/3) * sin (x/4)` on `(0, 3/2]`.

This is the strict decrease of `sin t / t`, specialized to the ratio `4/3`.
Proved from the two-sided cubic bounds: writing `b = x/4`, the gap is at least
`(28/162) b³ - (5/96)(4/3 + 256/81) b⁴`, which is positive for `b < 0.738`,
and `b ≤ 3/8` here. -/
lemma sin_third_lt_seed {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 3 / 2) :
    Real.sin (x / 3) < 4 / 3 * Real.sin (x / 4) := by
  have h3l : (0 : ℝ) ≤ x / 3 := by linarith
  have h3u : x / 3 ≤ 1 := by linarith
  have h4l : (0 : ℝ) ≤ x / 4 := by linarith
  have h4u : x / 4 ≤ 1 := by linarith
  have hup := sin_upper h3l h3u
  have hlo := sin_lower h4l h4u
  have hx4 : x ^ 4 ≤ (3 / 2 : ℝ) * x ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg (le_of_lt hx0) 3) (sub_nonneg.mpr hx1)]
  nlinarith [hup, hlo, hx4, pow_pos hx0 3]

/-- Inequality (B): `(4/3) * sin (x/4) ≤ sin (x/3 + x³/81)` on `(0, 3/2]`.

At the right endpoint the two sides are `0.4897` and `≥ 0.5107`, so the margin
is about `0.021`; the slack grows as `x` decreases. -/
lemma seed_le_sin_shift {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 3 / 2) :
    4 / 3 * Real.sin (x / 4) ≤ Real.sin (x / 3 + x ^ 3 / 81) := by
  have h4l : (0 : ℝ) ≤ x / 4 := by linarith
  have hsin : Real.sin (x / 4) ≤ x / 4 := Real.sin_le h4l
  have hx2 : x ^ 2 ≤ (9 / 4 : ℝ) := by nlinarith [sq_nonneg (3 / 2 - x)]
  have hx3 : x ^ 3 ≤ (9 / 4 : ℝ) * x := by
    nlinarith [mul_nonneg (le_of_lt hx0) (sub_nonneg.mpr hx2)]
  have hθl : (0 : ℝ) ≤ x / 3 + x ^ 3 / 81 := by positivity
  have hθu : x / 3 + x ^ 3 / 81 ≤ 1 := by nlinarith [hx3]
  have hθratio : x / 3 + x ^ 3 / 81 ≤ (3 / 8 : ℝ) * x := by
    nlinarith [hx3]
  have hθcube : (x / 3 + x ^ 3 / 81) ^ 3 ≤ ((3 / 8 : ℝ) * x) ^ 3 := by
    gcongr
  have hθfifth : (x / 3 + x ^ 3 / 81) ^ 5 ≤ ((3 / 8 : ℝ) * x) ^ 5 := by
    gcongr
  have hx5 : x ^ 5 ≤ (9 / 4 : ℝ) * x ^ 3 := by
    nlinarith [mul_nonneg (pow_nonneg (le_of_lt hx0) 3) (sub_nonneg.mpr hx2)]
  have hlo := sin_lower hθl hθu
  -- The rational cubic margin now dominates both Taylor remainders.
  nlinarith [hlo, hsin, hθcube, hθfifth, hx5, pow_pos hx0 3]

/-! ## 4. Range facts needed for the `arcsin` transfer -/

lemma seed_arg_le_one {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 3 / 2) :
    4 / 3 * Real.sin (x / 4) ≤ 1 := by
  have h4l : (0 : ℝ) ≤ x / 4 := by linarith
  have hsin : Real.sin (x / 4) ≤ x / 4 := Real.sin_le h4l
  nlinarith [hsin, hx1]

lemma seed_arg_nonneg {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 3 / 2) :
    (0 : ℝ) ≤ 4 / 3 * Real.sin (x / 4) := by
  have : (0 : ℝ) ≤ Real.sin (x / 4) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> nlinarith [Real.pi_gt_three]
  linarith

lemma third_in_range {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 3 / 2) :
    -(π / 2) ≤ x / 3 ∧ x / 3 ≤ π / 2 := by
  constructor
  · nlinarith [Real.pi_gt_three]
  · nlinarith [Real.pi_gt_three]

lemma shift_in_range {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 3 / 2) :
    -(π / 2) ≤ x / 3 + x ^ 3 / 81 ∧ x / 3 + x ^ 3 / 81 ≤ π / 2 := by
  have hx2 : x ^ 2 ≤ (9 / 4 : ℝ) := by nlinarith [sq_nonneg (3 / 2 - x)]
  have hx3 : x ^ 3 ≤ (9 / 4 : ℝ) * x := by
    nlinarith [mul_nonneg (le_of_lt hx0) (sub_nonneg.mpr hx2)]
  have hθu : x / 3 + x ^ 3 / 81 ≤ 1 := by nlinarith [hx3]
  constructor
  · nlinarith [Real.pi_gt_three, pow_pos hx0 3]
  · nlinarith [Real.pi_gt_three, hθu]

/-! ## 5. Lemma 4.7, the defect half -/

/-- `0 < d x` on `(0, 3/2]`.  This is what makes every `r_i` strictly negative
in Proposition 4.8. -/
theorem seedDefect_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 3 / 2) :
    0 < seedDefect x := by
  have hrange := third_in_range hx0 hx1
  have hlt := sin_third_lt_seed hx0 hx1
  have hle1 := seed_arg_le_one hx0 hx1
  have : x / 3 < seedS x :=
    arcsin_lt_of_sin_lt hrange.1 hrange.2 hle1 hlt
  unfold seedDefect
  linarith

/-- `d x ≤ x³/81` on `(0, 3/2]`. -/
theorem seedDefect_le {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 3 / 2) :
    seedDefect x ≤ x ^ 3 / 81 := by
  have hrange := shift_in_range hx0 hx1
  have hle := seed_le_sin_shift hx0 hx1
  have hnn := seed_arg_nonneg hx0 hx1
  have : seedS x ≤ x / 3 + x ^ 3 / 81 :=
    arcsin_le_of_le_sin (by linarith) hrange.1 hrange.2 hle
  unfold seedDefect
  linarith

/-! ## 6. Lemma 4.7, the `F` half — corollaries of §5 via the identity -/

/-- `F z < 0` for `0 < z ≤ 1/2`. -/
theorem seedF_neg {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1 / 2) : seedF z < 0 := by
  have h := seedDefect_pos (x := 3 * z) (by linarith) (by linarith)
  rw [F_eq_neg_seedDefect]
  linarith

/-- `F` is odd, so the sign statement extends to negative arguments. -/
lemma seedS_odd (x : ℝ) : seedS (-x) = -seedS x := by
  unfold seedS
  rw [show (-x) / 4 = -(x / 4) by ring, Real.sin_neg,
    show 4 / 3 * -Real.sin (x / 4) = -(4 / 3 * Real.sin (x / 4)) by ring,
    Real.arcsin_neg]

lemma seedF_odd (z : ℝ) : seedF (-z) = -seedF z := by
  unfold seedF
  rw [show 3 * -z = -(3 * z) by ring, seedS_odd]
  ring

/-- `F z > 0` for `-1/2 ≤ z < 0`. -/
theorem seedF_pos_of_neg {z : ℝ} (hz0 : z < 0) (hz1 : -(1 / 2) ≤ z) :
    0 < seedF z := by
  have h := seedF_neg (z := -z) (by linarith) (by linarith)
  rw [seedF_odd] at h
  linarith

/-- **`|F z| ≤ |z|³/3` for `|z| ≤ 1/2`.**  The manuscript's bound, obtained
from `seedDefect_le` at `x = 3z` since `(3z)³/81 = z³/3`. -/
theorem abs_seedF_le {z : ℝ} (hz : |z| ≤ 1 / 2) :
    |seedF z| ≤ |z| ^ 3 / 3 := by
  rcases lt_trichotomy z 0 with hneg | hzero | hpos
  · -- negative: use oddness
    have hz' : |(-z)| ≤ 1 / 2 := by rwa [abs_neg]
    have h3z : (0 : ℝ) < 3 * (-z) := by linarith
    have h3z' : 3 * (-z) ≤ 3 / 2 := by
      have := (abs_le.mp hz).1
      linarith
    have hd := seedDefect_le (x := 3 * (-z)) h3z h3z'
    have hdp := seedDefect_pos (x := 3 * (-z)) h3z h3z'
    have hF : seedF (-z) = -seedDefect (3 * (-z)) := F_eq_neg_seedDefect _
    have habsF : |seedF z| = seedDefect (3 * (-z)) := by
      rw [← abs_neg, ← seedF_odd, hF, abs_neg, abs_of_pos hdp]
    have habsz : |z| = -z := abs_of_neg hneg
    rw [habsF, habsz]
    nlinarith [hd]
  · simp [hzero, seedF, seedS]
  · have h3z : (0 : ℝ) < 3 * z := by linarith
    have h3z' : 3 * z ≤ 3 / 2 := by
      have := (abs_le.mp hz).2
      linarith
    have hd := seedDefect_le (x := 3 * z) h3z h3z'
    have hdp := seedDefect_pos (x := 3 * z) h3z h3z'
    have hF : seedF z = -seedDefect (3 * z) := F_eq_neg_seedDefect z
    have habsF : |seedF z| = seedDefect (3 * z) := by
      rw [hF, abs_neg, abs_of_pos hdp]
    have habsz : |z| = z := abs_of_pos hpos
    rw [habsF, habsz]
    nlinarith [hd]

/-- The manuscript's `0 < d(x) ≤ x³/81` on its stated range `(0, π/6]`, which is
contained in `(0, 3/2]` since `π < 9/2`. -/
theorem seedDefect_bounds_on_pi_div_six {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ π / 6) :
    0 < seedDefect x ∧ seedDefect x ≤ x ^ 3 / 81 := by
  have hpi : π < 9 / 2 := by linarith [Real.pi_lt_four]
  have hx : x ≤ 3 / 2 := by linarith
  exact ⟨seedDefect_pos hx0 hx, seedDefect_le hx0 hx⟩

end BakerSeed

/-! ## Axiom audit -/
#print axioms BakerSeed.sin_lower
#print axioms BakerSeed.sin_upper
#print axioms BakerSeed.arcsin_le_of_le_sin
#print axioms BakerSeed.arcsin_lt_of_sin_lt
#print axioms BakerSeed.F_eq_neg_seedDefect
#print axioms BakerSeed.sin_third_lt_seed
#print axioms BakerSeed.seed_le_sin_shift
#print axioms BakerSeed.seedDefect_pos
#print axioms BakerSeed.seedDefect_le
#print axioms BakerSeed.seedF_neg
#print axioms BakerSeed.seedF_pos_of_neg
#print axioms BakerSeed.abs_seedF_le
#print axioms BakerSeed.seedDefect_bounds_on_pi_div_six
