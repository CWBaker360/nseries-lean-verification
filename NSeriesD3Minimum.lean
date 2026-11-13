import NSeriesD3RootEnumeration
import NSeriesD3ChordComparison
import NSeriesD3Positive

namespace BakerNSeries

/-- The canonical adjacent chord belongs to the intrinsic finite chord set. -/
theorem canonicalPolygonStep_chord_mem_rootChordLengths
    (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    dist (1 : ℂ) (canonicalPolygonStep n) ∈ rootChordLengths n := by
  apply Finset.mem_image.mpr
  refine ⟨canonicalRootWitness n, canonicalRootWitness_mem_nontrivialRoots n hn, ?_⟩
  rw [canonicalRootWitness_coe_complex]

/-- The canonical adjacent chord is no longer than every intrinsic root chord. -/
theorem canonicalPolygonStep_chord_le_rootChord
    (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (d : ℝ) (hd : d ∈ rootChordLengths n) :
    dist (1 : ℂ) (canonicalPolygonStep n) ≤ d := by
  rcases Finset.mem_image.mp hd with ⟨z, hz, rfl⟩
  have hz' : ((z.1 : ℂˣ) : ℂ) ≠ 1 := (Finset.mem_filter.mp hz).2
  obtain ⟨k, hk1, hkn, hk⟩ := nontrivialRoot_exists_canonical_pow n z hz'
  rw [hk]
  exact canonicalPolygonStep_chord_le_pow_chord n k hn hk1 hkn

/-- The intrinsic shortest nonzero root-of-unity chord is the adjacent canonical chord. -/
theorem minimumRootChord_eq_canonicalPolygonStep_chord
    (n : ℕ) [NeZero n] (hn : 3 ≤ n)
    (h : (rootChordLengths n).Nonempty) :
    minimumRootChord n h = dist (1 : ℂ) (canonicalPolygonStep n) := by
  unfold minimumRootChord
  apply le_antisymm
  · exact Finset.min'_le _ _ (canonicalPolygonStep_chord_mem_rootChordLengths n hn)
  · apply Finset.le_min'
    intro d hd
    exact canonicalPolygonStep_chord_le_rootChord n hn d hd

end BakerNSeries

#print axioms BakerNSeries.canonicalPolygonStep_chord_mem_rootChordLengths
#print axioms BakerNSeries.canonicalPolygonStep_chord_le_rootChord
#print axioms BakerNSeries.minimumRootChord_eq_canonicalPolygonStep_chord
