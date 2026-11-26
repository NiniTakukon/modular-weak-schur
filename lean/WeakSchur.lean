import WeakSchur.Threshold
import WeakSchur.Witness

namespace WeakSchur

/-- The original one-colour congruence on the integers 1,...,n. -/
def ModularWitness (m l n : Nat) : Prop :=
  ∃ (xs : List Nat) (y : Nat), xs.length = l ∧
    (xs.Nodup ∧ ∀ x ∈ xs, 0 < x ∧ x ≤ n) ∧
    y ∉ xs ∧ 0 < y ∧ y ≤ n ∧ xs.sum % m = y % m

theorem hasSolution_iff_modularWitness {m l n : Nat} :
    HasSolution m l n ↔ ModularWitness m l n := by
  constructor
  · rintro ⟨z, hs, hd⟩
    obtain ⟨xs, y, len, valid, fresh, hy, hle, rfl⟩ := signed_iff_witness.mp hs
    have h := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hd)
    rw [← Int.ofNat_emod, ← Int.ofNat_emod] at h
    exact ⟨xs, y, len, valid, fresh, hy, hle, Int.ofNat_inj.mp h⟩
  · rintro ⟨xs, y, len, valid, fresh, hy, hle, hmod⟩
    have h : (xs.sum : Int) % m = (y : Int) % m := by
      rw [← Int.ofNat_emod, ← Int.ofNat_emod, hmod]
    exact ⟨_, signed_iff_witness.mpr ⟨xs, y, len, valid, fresh, hy, hle, rfl⟩,
      Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h)⟩

/-- The formula characterizes every solution-free initial interval. -/
theorem one_colour_threshold {m l n : Nat} (hm : 0 < m) (hl : 0 < l) :
    ¬ ModularWitness m l n ↔ n ≤ weakSchur m l := by
  rw [← hasSolution_iff_modularWitness, safe_iff hm hl]

/-- The formula is itself attainable and is the greatest such n. -/
theorem weakSchur_isGreatest {m l : Nat} (hm : 0 < m) (hl : 0 < l) :
    (¬ ModularWitness m l (weakSchur m l)) ∧
    ∀ n, (¬ ModularWitness m l n) → n ≤ weakSchur m l :=
  ⟨(one_colour_threshold hm hl).mpr (Nat.le_refl _),
    fun _ h => (one_colour_threshold hm hl).mp h⟩

end WeakSchur
