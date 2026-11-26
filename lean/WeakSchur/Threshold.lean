import WeakSchur.Spectrum

namespace WeakSchur

def HasSolution (m l n : Nat) : Prop :=
  ∃ z : Int, Signed n l z ∧ (m : Int) ∣ z

def boundaryHit (m l : Nat) : Bool :=
  (List.range (l+1)).any fun j =>
    ((tri l : Int) - (l+1 : Nat) + 2*(j : Int)) % (m : Int) == 0

def roomCut (m l : Nat) : Nat :=
  let r := (tri l - 1) % m
  max (l+2) (min (r+1) (l + (m-r+l-1)/l))

def firstBad (m l : Nat) : Nat :=
  if l = 1 then m+1 else if boundaryHit m l then l+1 else roomCut m l

def weakSchur (m l : Nat) : Nat := firstBad m l - 1

private theorem boundary_iff {m l : Nat} (hl : 2 ≤ l) :
    boundaryHit m l = true ↔ HasSolution m l (l+1) := by
  simp only [boundaryHit, List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨_, (spectrum_tight hl).2 ⟨j, by omega, rfl⟩, Int.dvd_of_emod_eq_zero h⟩
  · rintro ⟨z,hs,hd⟩
    obtain ⟨j, hj, rfl⟩ := (spectrum_tight hl).1 hs
    exact ⟨j, by omega, Int.emod_eq_zero_of_dvd hd⟩

/-- The lower adjacent multiple is c - c % m, and the next is m units above it. -/
private theorem multiple_in_interval {m c a b : Int} (hm : 0 < m) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∃ z : Int, c-a ≤ z ∧ z ≤ c+b ∧ m ∣ z) ↔ c%m ≤ a ∨ m-c%m ≤ b := by
  have decomp := Int.emod_add_ediv c m
  have r0 := Int.emod_nonneg c (by omega : m ≠ 0)
  have rlt := Int.emod_lt_of_pos c hm
  have next : m*(c/m+1) = m*(c/m)+m := by rw [Int.mul_add, Int.mul_one]
  constructor
  · rintro ⟨_, hlo, hhi, ⟨q, rfl⟩⟩
    by_cases hq : q ≤ c/m
    · have h := Int.mul_le_mul_of_nonneg_left hq (by omega : 0 ≤ m)
      exact Or.inl (by omega)
    · have h := Int.mul_le_mul_of_nonneg_left (show c/m+1 ≤ q by omega) (by omega : 0 ≤ m)
      rw [next] at h
      exact Or.inr (by omega)
  · rintro (h | h)
    · exact ⟨m*(c/m), by omega, by omega, ⟨_, rfl⟩⟩
    · exact ⟨m*(c/m+1), by omega, by omega, ⟨_, rfl⟩⟩

private theorem ceil_le {u l d : Nat} (hl : 0 < l) :
    (u+l-1)/l ≤ d ↔ u ≤ l*d := by
  have h := Nat.div_lt_iff_lt_mul (x := u+l-1) (y := d+1) hl
  rw [Nat.succ_mul, Nat.mul_comm d l] at h
  omega

private theorem room_iff {m l n : Nat} (hm : 0 < m) (hl : 2 ≤ l) (hn : l+2 ≤ n) :
    HasSolution m l n ↔ roomCut m l ≤ n := by
  let c := tri l - 1
  let r := c % m
  have hc : (c : Int) = (tri l : Int) - 1 := by
    have := tri_pos (l := l) (by omega)
    dsimp [c]; omega
  have hr : (r : Int) = (c : Int) % (m : Int) := Int.ofNat_emod _ _
  have hrlt : r < m := Nat.mod_lt c hm
  have hmul : (↑(l*(n-l)) : Int) = (l : Int)*((n : Int)-l) := by
    rw [Int.natCast_mul, Int.ofNat_sub (show l ≤ n by omega)]
  have interval : HasSolution m l n ↔
      ∃ z : Int, (c : Int) - (↑(n-1) : Int) ≤ z ∧
        z ≤ (c : Int) + ↑(l*(n-l)) ∧ (m : Int) ∣ z := by
    constructor
    · rintro ⟨z, hs, hd⟩
      obtain ⟨lo,hi⟩ := (spectrum_room hl hn).1 hs
      exact ⟨z, by omega, by omega, hd⟩
    · rintro ⟨z, lo, hi, hd⟩
      exact ⟨z, (spectrum_room hl hn).2 ⟨by omega, by omega⟩, hd⟩
  rw [interval, multiple_in_interval (by omega) (by omega) (by omega), ← hr]
  have hceil := ceil_le (u := m-r) (d := n-l) (l := l) (by omega)
  change _ ↔ max (l+2) (min (r+1) (l + (m-r+l-1)/l)) ≤ n
  omega

private theorem one_iff {m n : Nat} (hm : 0 < m) :
    HasSolution m 1 n ↔ m+1 ≤ n := by
  constructor
  · rintro ⟨z,hs,hd⟩
    obtain ⟨hnz, hlo, hhi⟩ := spectrum_one.1 hs
    by_cases hz : 0 < z
    · have := Int.le_of_dvd hz hd
      omega
    · have hneg : (m : Int) ∣ -z := Int.dvd_neg.mpr hd
      have := Int.le_of_dvd (show 0 < -z by omega) hneg
      omega
  · intro h
    exact ⟨m, spectrum_one.2 ⟨by omega, by omega, by omega⟩, Int.dvd_refl _⟩

theorem hasSolution_iff_firstBad {m l n : Nat} (hm : 0 < m) (hl : 0 < l) :
    HasSolution m l n ↔ firstBad m l ≤ n := by
  by_cases one : l = 1
  · subst l; simpa [firstBad] using (one_iff (n := n) hm)
  have hl2 : 2 ≤ l := by omega
  have hcut : l+2 ≤ roomCut m l := Nat.le_max_left _ _
  by_cases hit : boundaryHit m l = true
  · simp only [firstBad, if_neg one, hit, if_true]
    constructor
    · rintro ⟨z,hs,_⟩
      by_cases h : l+1 ≤ n
      · exact h
      · exact False.elim (spectrum_small (by omega) hs)
    · intro h
      obtain ⟨z,hs,hd⟩ := (boundary_iff hl2).1 hit
      exact ⟨z, signed_mono hs h, hd⟩
  · simp only [firstBad, if_neg one, if_neg hit]
    by_cases hn : l+2 ≤ n
    · exact room_iff hm hl2 hn
    · constructor
      · intro sol
        by_cases b : n = l+1
        · subst n
          exact False.elim (hit ((boundary_iff hl2).2 sol))
        · obtain ⟨z,hs,_⟩ := sol
          exact False.elim (spectrum_small (by omega) hs)
      · omega

theorem safe_iff {m l n : Nat} (hm : 0 < m) (hl : 0 < l) :
    ¬ HasSolution m l n ↔ n ≤ weakSchur m l := by
  have pos : 0 < firstBad m l := by
    unfold firstBad
    split
    · omega
    · split
      · omega
      · have hcut : l+2 ≤ roomCut m l := Nat.le_max_left _ _
        omega
  rw [hasSolution_iff_firstBad hm hl]
  unfold weakSchur
  omega

end WeakSchur
