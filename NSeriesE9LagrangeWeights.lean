import Mathlib

namespace BakerNSeries

open Polynomial

theorem lagrange_weights_moments {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) (j : ℕ) (hj : j < n) :
    ∑ i, (Lagrange.basis Finset.univ x i).eval 0 * x i ^ j = (0 : ℝ) ^ j := by
  have hdeg : ((X : ℝ[X]) ^ j).degree
      < ((Finset.univ : Finset (Fin n)).card : WithBot ℕ) := by
    rw [degree_X_pow, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast hj
  have h := Lagrange.eq_interpolate (s := (Finset.univ : Finset (Fin n)))
    (v := x) (hx.injOn) hdeg
  have h0 : (0 : ℝ) ^ j
      = ∑ i, x i ^ j * (Lagrange.basis Finset.univ x i).eval 0 := by
    have he := congrArg (Polynomial.eval 0) h
    have heval : ∀ s : Finset (Fin n),
        Polynomial.eval 0 (∑ i ∈ s, (C (x i) ^ j) * Lagrange.basis Finset.univ x i)
          = ∑ i ∈ s, Polynomial.eval 0 ((C (x i) ^ j) * Lagrange.basis Finset.univ x i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s his ih => simp [his, Polynomial.eval_add, ih]
    simpa [Lagrange.interpolate_apply, heval Finset.univ] using he
  rw [h0]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem lagrange_weight_formula {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (Lagrange.basis Finset.univ x i).eval 0
      = ∏ k ∈ Finset.univ.erase i, (-x k) / (x i - x k) := by
  simp [Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod,
    div_eq_inv_mul]

end BakerNSeries

#print axioms BakerNSeries.lagrange_weights_moments
#print axioms BakerNSeries.lagrange_weight_formula
