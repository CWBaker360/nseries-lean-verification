import NSeriesD3Witness

namespace BakerNSeries

/-- Every `n`th root of unity is a canonical-step power with exponent below `n`. -/
theorem rootOfUnity_exists_canonical_pow
    (n : ℕ) [NeZero n] (z : rootsOfUnity n ℂ) :
    ∃ k : ℕ, k < n ∧ ((z.1 : ℂˣ) : ℂ) = canonicalPolygonStep n ^ k := by
  let hcan : IsPrimitiveRoot (canonicalPolygonStep n) n :=
    canonicalPolygonStep_isPrimitiveRoot n NeZero.out
  let ζ : ℂˣ := (hcan.isUnit NeZero.out).unit
  have hζ : IsPrimitiveRoot ζ n := hcan.isUnit_unit NeZero.out
  have hmem : (z.1 : ℂˣ) ∈ Subgroup.zpowers ζ := by
    rw [hζ.zpowers_eq]
    exact z.2
  let zz : Subgroup.zpowers ζ := ⟨z.1, hmem⟩
  let a : ZMod n := hζ.zmodEquivZPowers.symm (Additive.ofMul zz)
  refine ⟨a.val, ZMod.val_lt a, ?_⟩
  have hsub : zz = ⟨ζ ^ a.val, a.val, rfl⟩ := by
    have ha : hζ.zmodEquivZPowers a = Additive.ofMul zz := by
      dsimp [a]
      exact hζ.zmodEquivZPowers.apply_symm_apply _
    have happly := hζ.zmodEquivZPowers_apply_natCast a.val
    rw [ZMod.natCast_zmod_val] at happly
    exact congrArg Additive.toMul (ha.symm.trans happly)
  have hu : (z.1 : ℂˣ) = ζ ^ a.val := congrArg Subtype.val hsub
  apply_fun (fun u : ℂˣ => (u : ℂ)) at hu
  simpa [ζ] using hu

/-- A nonidentity `n`th root uses a nonzero canonical-step exponent. -/
theorem nontrivialRoot_exists_canonical_pow
    (n : ℕ) [NeZero n] (z : rootsOfUnity n ℂ)
    (hz : ((z.1 : ℂˣ) : ℂ) ≠ 1) :
    ∃ k : ℕ, 1 ≤ k ∧ k < n ∧
      ((z.1 : ℂˣ) : ℂ) = canonicalPolygonStep n ^ k := by
  obtain ⟨k, hklt, hk⟩ := rootOfUnity_exists_canonical_pow n z
  refine ⟨k, ?_, hklt, hk⟩
  by_contra hkpos
  have hkzero : k = 0 := by omega
  apply hz
  rw [hk, hkzero, pow_zero]

end BakerNSeries

#print axioms BakerNSeries.rootOfUnity_exists_canonical_pow
#print axioms BakerNSeries.nontrivialRoot_exists_canonical_pow
