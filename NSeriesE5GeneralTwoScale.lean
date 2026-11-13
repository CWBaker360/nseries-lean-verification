/-
  E5 — Theorem 3.1 for a general sequence (explicit-bound form):
  if |q(M) − Q − C/M²| ≤ B/M⁴ at every scale, the two-scale operator
  removes the M⁻² term and leaves an N⁻⁴ error with explicit constant.
  NOT YET COMPILED (written without a local Mathlib build).
-/
import NSeriesB5ActualBound

namespace BakerNSeries

theorem two_scale_general_bound
    (q : Real → Real) (Q C B N k : Real) (hN : 0 < N) (hk : 1 < k)
    (hq : ∀ M : Real, 0 < M → abs (q M - Q - C / M^2) ≤ B / M^4) :
    abs ((k^2 * q (k * N) - q N) / (k^2 - 1) - Q)
      ≤ (k^2 * (B / (k * N)^4) + B / N^4) / (k^2 - 1) := by
  have hkpos : 0 < k := by linarith
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hk0 : k ≠ 0 := ne_of_gt hkpos
  have hdenpos : 0 < k^2 - 1 := by
    nlinarith [sq_nonneg (k - 1)]
  have hden0 : k^2 - 1 ≠ 0 := ne_of_gt hdenpos
  have hid :
      (k^2 * q (k * N) - q N) / (k^2 - 1) - Q
        = (k^2 * (q (k * N) - Q - C / (k * N)^2) - (q N - Q - C / N^2))
            / (k^2 - 1) := by
    field_simp [hN0, hk0, hden0]
    ring
  rw [hid]
  exact two_scale_error_budget k (q N - Q - C / N^2) (q (k * N) - Q - C / (k * N)^2)
    (B / N^4) (B / (k * N)^4) hk (hq N hN) (hq (k * N) (mul_pos hkpos hN))

/-- The bound above is exactly B·(k² + 1)/(k²·(k² − 1)) · N⁻⁴. -/
theorem two_scale_general_constant (B N k : Real) (hN : 0 < N) (hk : 1 < k) :
    (k^2 * (B / (k * N)^4) + B / N^4) / (k^2 - 1)
      = B * (k^2 + 1) / (k^2 * (k^2 - 1)) / N^4 := by
  have hkpos : 0 < k := by linarith
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hk0 : k ≠ 0 := ne_of_gt hkpos
  have hdenpos : 0 < k^2 - 1 := by
    nlinarith [sq_nonneg (k - 1)]
  have hden0 : k^2 - 1 ≠ 0 := ne_of_gt hdenpos
  field_simp [hN0, hk0, hden0]
  ring

end BakerNSeries

#print axioms BakerNSeries.two_scale_general_bound
#print axioms BakerNSeries.two_scale_general_constant
