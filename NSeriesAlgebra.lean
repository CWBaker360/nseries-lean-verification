/-
  Baker N-series π acceleration — Module A: exact algebra
  Covers: Thm 3.1 (two-scale, exact model form), Thm 6.1 weight identities,
          Cor 6.2 (k = 2 weights), Sec. 10 chord-trisection cubic.
  NOT YET COMPILED — written without a local Mathlib build.
-/
import Mathlib

namespace BakerNSeries

/-! ## Two-scale operator (Theorem 3.1) -/

/-- The two-scale operator is the weighted combination (k²·Q_{kN} − Q_N)/(k² − 1). -/
theorem two_scale_weights (qN qkN k : ℝ) (hk : 1 < k) :
    qkN + (qkN - qN) / (k ^ 2 - 1) = (k ^ 2 * qkN - qN) / (k ^ 2 - 1) := by
  have h1 : k ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < k ^ 2 - 1).ne'
  field_simp
  ring

/-- On the truncated model Q + C₂/N² + C₄/N⁴ the N⁻² term cancels exactly and the
    residual is −C₄/(k²N⁴) (the coefficient used in Corollary 3.2). -/
theorem two_scale_model (Q C₂ C₄ k N : ℝ) (hk : 1 < k) (hN : 0 < N) :
    (Q + C₂ / (k * N) ^ 2 + C₄ / (k * N) ^ 4)
      + ((Q + C₂ / (k * N) ^ 2 + C₄ / (k * N) ^ 4) - (Q + C₂ / N ^ 2 + C₄ / N ^ 4))
          / (k ^ 2 - 1)
      = Q - C₄ / (k ^ 2 * N ^ 4) := by
  have hk0 : k ≠ 0 := (by linarith : (0 : ℝ) < k).ne'
  have hN0 : N ≠ 0 := hN.ne'
  have h1 : k ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < k ^ 2 - 1).ne'
  field_simp
  ring

/-! ## Three-scale weights (Theorem 6.1) -/

noncomputable def wa (k : ℝ) : ℝ := 1 / ((k ^ 2 - 1) ^ 2 * (k ^ 2 + 1))
noncomputable def wb (k : ℝ) : ℝ := -k ^ 2 / (k ^ 2 - 1) ^ 2
noncomputable def wc (k : ℝ) : ℝ := k ^ 6 / ((k ^ 2 - 1) ^ 2 * (k ^ 2 + 1))

/-- a + b + c = 1 : the limit is preserved. -/
theorem w_sum (k : ℝ) (hk : 1 < k) : wa k + wb k + wc k = 1 := by
  have h1 : k ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < k ^ 2 - 1).ne'
  have h2 : k ^ 2 + 1 ≠ 0 := (by positivity : (0 : ℝ) < k ^ 2 + 1).ne'
  unfold wa wb wc
  field_simp
  ring

/-- a + b/k² + c/k⁴ = 0 : the N⁻² term is cancelled. -/
theorem w_moment2 (k : ℝ) (hk : 1 < k) :
    wa k + wb k / k ^ 2 + wc k / k ^ 4 = 0 := by
  have hk0 : k ≠ 0 := (by linarith : (0 : ℝ) < k).ne'
  have h1 : k ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < k ^ 2 - 1).ne'
  have h2 : k ^ 2 + 1 ≠ 0 := (by positivity : (0 : ℝ) < k ^ 2 + 1).ne'
  unfold wa wb wc
  field_simp
  ring

/-- a + b/k⁴ + c/k⁸ = 0 : the N⁻⁴ term is cancelled. -/
theorem w_moment4 (k : ℝ) (hk : 1 < k) :
    wa k + wb k / k ^ 4 + wc k / k ^ 8 = 0 := by
  have hk0 : k ≠ 0 := (by linarith : (0 : ℝ) < k).ne'
  have h1 : k ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < k ^ 2 - 1).ne'
  have h2 : k ^ 2 + 1 ≠ 0 := (by positivity : (0 : ℝ) < k ^ 2 + 1).ne'
  unfold wa wb wc
  field_simp
  ring

/-- Corollary 6.2: the dyadic weights are 1/45, −4/9, 64/45. -/
theorem w_dyadic : wa 2 = 1 / 45 ∧ wb 2 = -(4 / 9) ∧ wc 2 = 64 / 45 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [wa, wb, wc]

/-! ## Chord-trisection cubic (Section 10) -/

/-- u = sin(x/3) satisfies 4u³ − 3u + sin x = 0; with x = π/N this is
    4u³ − 3u + c_N = 0, u = c_{3N}. -/
theorem trisection_cubic (x : ℝ) :
    4 * Real.sin (x / 3) ^ 3 - 3 * Real.sin (x / 3) + Real.sin x = 0 := by
  have h := Real.sin_three_mul (x / 3)
  rw [show 3 * (x / 3) = x by ring] at h
  linarith

end BakerNSeries
