/-
  E7 — Remark 7.2 (Vandermonde structure): for distinct nodes x_i (the paper's
  x_i = m_i⁻²), weights are uniquely determined by their first n moments.
-/
import Mathlib

namespace BakerNSeries

/-- Two weight vectors with the same moments Σ w_i · x_i^j (j < n) at distinct
    nodes are equal. -/
theorem moment_weights_unique {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x)
    (w w' : Fin n → ℝ)
    (h : ∀ j : Fin n, ∑ i, w i * x i ^ (j : ℕ) = ∑ i, w' i * x i ^ (j : ℕ)) :
    w = w' := by
  have hdet : (Matrix.vandermonde x).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.2 hx
  have hz : Matrix.vecMul (w - w') (Matrix.vandermonde x) = 0 := by
    funext j
    have hj := h j
    simp only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply,
      Pi.sub_apply, Pi.zero_apply, sub_mul, Finset.sum_sub_distrib]
    linarith
  exact sub_eq_zero.1 (Matrix.eq_zero_of_vecMul_eq_zero hdet hz)

end BakerNSeries

#print axioms BakerNSeries.moment_weights_unique
