import NSeriesD3Foundation
import NSeriesD3Witness

namespace BakerNSeries

theorem canonicalRootWitness_ne_one (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    canonicalRootWitness n ≠ 1 := by
  intro hw
  have hc : canonicalPolygonStep n = 1 := by
    have h := congrArg (fun w : rootsOfUnity n ℂ => ((w.1 : ℂˣ) : ℂ)) hw
    simpa [canonicalRootWitness_coe_complex] using h
  have hp : canonicalPolygonStep n ^ 1 = 1 := by simpa using hc
  have hdvd : n ∣ 1 :=
    (canonicalPolygonStep_pow_eq_one_iff n 1 NeZero.out).1 hp
  have hle : n ≤ 1 := Nat.le_of_dvd (by omega) hdvd
  omega

theorem canonicalRootWitness_mem_nontrivialRoots (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    canonicalRootWitness n ∈ nontrivialRoots n := by
  simp only [nontrivialRoots, Finset.mem_filter, Finset.mem_univ, true_and]
  intro h
  apply canonicalRootWitness_ne_one n hn
  apply Subtype.ext
  apply Units.ext
  simpa [canonicalRootWitness_coe_complex] using h

theorem rootChordLengths_nonempty (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    (rootChordLengths n).Nonempty := by
  refine ⟨dist (1 : ℂ) (((canonicalRootWitness n).1 : ℂˣ) : ℂ), ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨canonicalRootWitness n, canonicalRootWitness_mem_nontrivialRoots n hn, rfl⟩

theorem rootChordLengths_pos (n : ℕ) [NeZero n] (hn : 3 ≤ n) {x : ℝ}
    (hx : x ∈ rootChordLengths n) : 0 < x := by
  rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
  rw [nontrivialRoots, Finset.mem_filter] at hz
  exact dist_pos.mpr (Ne.symm hz.2)

theorem minimumRootChord_pos (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (h : (rootChordLengths n).Nonempty) : 0 < minimumRootChord n h := by
  apply rootChordLengths_pos n hn
  exact Finset.min'_mem _ h

end BakerNSeries

#print axioms BakerNSeries.canonicalRootWitness_ne_one
#print axioms BakerNSeries.canonicalRootWitness_mem_nontrivialRoots
#print axioms BakerNSeries.rootChordLengths_nonempty
#print axioms BakerNSeries.rootChordLengths_pos
#print axioms BakerNSeries.minimumRootChord_pos
