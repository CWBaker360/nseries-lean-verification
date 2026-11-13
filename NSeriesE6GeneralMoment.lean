/-
  E6 — Theorem 7.1 (general moment cancellation), explicit-bound form.
  Indexing: `r` here is the number of cancelled even-power terms
  (the paper's r − 1); the scale set `s` is any finite index set.
-/
import Mathlib

namespace BakerNSeries

open Finset

/-- If q(M) = Q + Σ_{j<r} C_j / M^(2(j+1)) up to an error B / M^(2(r+1)), and the
    weights sum to 1 and annihilate the first r even moments, then the weighted
    multi-scale combination is within Σ |w_i| · B / (m_i N)^(2(r+1)) of Q. -/
theorem general_moment_cancellation
    {ι : Type*} (s : Finset ι) (w m : ι → ℝ) (r : ℕ)
    (q : ℝ → ℝ) (Q B N : ℝ) (C : ℕ → ℝ)
    (hN : 0 < N) (hm : ∀ i ∈ s, 0 < m i)
    (hw : ∑ i ∈ s, w i = 1)
    (hmom : ∀ j ∈ range r, ∑ i ∈ s, w i / m i ^ (2 * (j + 1)) = 0)
    (hq : ∀ M : ℝ, 0 < M →
      |q M - Q - ∑ j ∈ range r, C j / M ^ (2 * (j + 1))|
        ≤ B / M ^ (2 * (r + 1))) :
    |∑ i ∈ s, w i * q (m i * N) - Q|
      ≤ ∑ i ∈ s, |w i| * (B / (m i * N) ^ (2 * (r + 1))) := by
  -- the weighted model part collapses to Q
  have hmodel :
      ∑ i ∈ s, w i * (Q + ∑ j ∈ range r, C j / (m i * N) ^ (2 * (j + 1))) = Q := by
    calc
      ∑ i ∈ s, w i * (Q + ∑ j ∈ range r, C j / (m i * N) ^ (2 * (j + 1)))
          = ∑ i ∈ s, (w i * Q
              + ∑ j ∈ range r, w i * (C j / (m i * N) ^ (2 * (j + 1)))) := by
            apply sum_congr rfl
            intro i _
            rw [mul_add, mul_sum]
      _ = (∑ i ∈ s, w i) * Q
            + ∑ j ∈ range r, ∑ i ∈ s, w i * (C j / (m i * N) ^ (2 * (j + 1))) := by
            rw [sum_add_distrib, ← sum_mul]
            congr 1
            exact sum_comm
      _ = Q + ∑ j ∈ range r, (0 : ℝ) := by
            rw [hw, one_mul]
            congr 1
            apply sum_congr rfl
            intro j hj
            have hfactor :
                ∑ i ∈ s, w i * (C j / (m i * N) ^ (2 * (j + 1)))
                  = C j / N ^ (2 * (j + 1))
                      * ∑ i ∈ s, w i / m i ^ (2 * (j + 1)) := by
              rw [mul_sum]
              apply sum_congr rfl
              intro i _
              ring
            rw [hfactor, hmom j hj, mul_zero]
      _ = Q := by simp
  -- split the combination into remainder part + model part
  have hsum :
      ∑ i ∈ s, w i * q (m i * N)
        = ∑ i ∈ s, w i * (q (m i * N) - Q
              - ∑ j ∈ range r, C j / (m i * N) ^ (2 * (j + 1)))
          + ∑ i ∈ s, w i * (Q + ∑ j ∈ range r, C j / (m i * N) ^ (2 * (j + 1))) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  have hsplit :
      ∑ i ∈ s, w i * q (m i * N) - Q
        = ∑ i ∈ s, w i * (q (m i * N) - Q
              - ∑ j ∈ range r, C j / (m i * N) ^ (2 * (j + 1))) := by
    rw [hsum, hmodel]
    ring
  rw [hsplit]
  calc
    |∑ i ∈ s, w i * (q (m i * N) - Q
          - ∑ j ∈ range r, C j / (m i * N) ^ (2 * (j + 1)))|
        ≤ ∑ i ∈ s, |w i * (q (m i * N) - Q
            - ∑ j ∈ range r, C j / (m i * N) ^ (2 * (j + 1)))| :=
          abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, |w i| * (B / (m i * N) ^ (2 * (r + 1))) := by
          apply sum_le_sum
          intro i hi
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (hq (m i * N) (mul_pos (hm i hi) hN)) (abs_nonneg _)

end BakerNSeries

#print axioms BakerNSeries.general_moment_cancellation
