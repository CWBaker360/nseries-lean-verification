/-
  E8 — Existence of moment weights at distinct nodes (Vandermonde invertibility),
  combined with E7 into existence-and-uniqueness for the N-series moment system.
  Candidate: not compiled.
-/
import NSeriesE7Vandermonde

namespace BakerNSeries

/-- At distinct nodes, any prescribed first-n moments are attained by some weights. -/
theorem moment_weights_exist {n : ℕ} (x : Fin n → ℝ) (hx : Function.Injective x)
    (b : Fin n → ℝ) :
    ∃ w : Fin n → ℝ, ∀ j : Fin n, ∑ i, w i * x i ^ (j : ℕ) = b j := by
  have hdet : IsUnit (Matrix.vandermonde x).det :=
    isUnit_iff_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 hx)
  have hex : ∃ w : Fin n → ℝ, Matrix.vecMul w (Matrix.vandermonde x) = b := by
    refine ⟨Matrix.vecMul b (Matrix.vandermonde x)⁻¹, ?_⟩
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
  obtain ⟨w, hw⟩ := hex
  refine ⟨w, fun j => ?_⟩
  have hj := congrFun hw j
  simp only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply] at hj
  exact hj

/-- The N-series moment system (zeroth moment 1, higher moments 0) has exactly
    one solution at distinct nodes. -/
theorem nseries_weights_existsUnique {n : ℕ} (x : Fin n → ℝ)
    (hx : Function.Injective x) :
    ∃! w : Fin n → ℝ, ∀ j : Fin n,
      ∑ i, w i * x i ^ (j : ℕ) = if (j : ℕ) = 0 then 1 else 0 := by
  obtain ⟨w, hw⟩ :=
    moment_weights_exist x hx (fun j => if (j : ℕ) = 0 then 1 else 0)
  refine ⟨w, hw, fun w' hw' => ?_⟩
  exact moment_weights_unique x hx w' w (fun j => (hw' j).trans (hw j).symm)

/-- Distinct positive scales m_i give distinct nodes x_i = (m_i²)⁻¹. -/
theorem scale_nodes_injective {n : ℕ} (m : Fin n → ℝ)
    (hpos : ∀ i, 0 < m i) (hm : Function.Injective m) :
    Function.Injective (fun i => (m i ^ 2)⁻¹) := by
  intro i j h
  have hsq : m i ^ 2 = m j ^ 2 := inv_injective h
  have hfac : (m i - m j) * (m i + m j) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.1 hfac with h1 | h2
  · exact hm (sub_eq_zero.1 h1)
  · exfalso
    linarith [hpos i, hpos j]

end BakerNSeries

#print axioms BakerNSeries.moment_weights_exist
#print axioms BakerNSeries.nseries_weights_existsUnique
#print axioms BakerNSeries.scale_nodes_injective
