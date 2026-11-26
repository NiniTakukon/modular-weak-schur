import WeakSchur.Model

namespace WeakSchur

private def top (n k : Nat) : Int :=
  (tri k : Int) + (k : Int) * ((n : Int) - k)

private theorem tri_step (k : Nat) : (tri (k+1) : Int) = (tri k : Int) + k + 1 := by
  simp [tri, Int.add_assoc]

private theorem top_step (n k : Nat) : top (n+1) k = top n k + k := by
  unfold top
  rw [show (↑(n+1) : Int) - k = ((n : Int) - k) + 1 by omega, Int.mul_add, Int.mul_one]
  omega

private theorem top_diag (n k : Nat) : top (n+1) (k+1) = top n k + (n+1 : Nat) := by
  unfold top
  rw [show (↑(n+1) : Int) - ↑(k+1) = (n : Int) - k by omega, tri_step,
      show (↑(k+1) : Int) = (k : Int)+1 by omega, Int.add_mul, Int.one_mul]
  omega

private theorem pos_bounds {n k s} (h : Pos n k s) :
    k ≤ n ∧ (tri k : Int) ≤ s ∧ s ≤ top n k := by
  induction h with
  | empty => decide
  | skip h ih => rw [top_step]; omega
  | take h ih => rw [top_diag, tri_step]; omega

private theorem bounds {n k s} (h : Signed n k s) :
    k+1 ≤ n ∧ (tri k : Int) - n ≤ s ∧ s ≤ top n k - 1 := by
  induction h with
  | skip h ih => rw [top_step]; omega
  | plus h ih => rw [top_diag, tri_step]; omega
  | minus h => have b := pos_bounds h; rw [top_step]; omega

theorem spectrum_small {n l : Nat} {z : Int} (h : n ≤ l) : ¬ Signed n l z := by
  intro hs
  have b := bounds hs
  omega

private theorem fullPos (k : Nat) : Pos k k (tri k) := by
  induction k with
  | zero => exact .empty
  | succ k ih => simpa [tri] using Pos.take ih

private theorem pos_mono {n k s} (h : Pos n k s) {N : Nat} (hn : n ≤ N) : Pos N k s := by
  induction hn with
  | refl => exact h
  | step _ ih => exact .skip ih

theorem signed_mono {n k s} (h : Signed n k s) {N : Nat} (hn : n ≤ N) :
    Signed N k s := by
  induction hn with
  | refl => exact h
  | step _ ih => exact .skip ih

private theorem minimum {n k : Nat} (hn : k+1 ≤ n) : Signed n k ((tri k : Int)-n) := by
  cases n with
  | zero => omega
  | succ n => exact .minus (pos_mono (fullPos k) (by omega))

private theorem maximum {n k : Nat} (hn : k+1 ≤ n) : Signed n k (top n k - 1) := by
  induction k generalizing n with
  | zero =>
    have h : Signed 1 0 (-1) := Signed.minus Pos.empty
    simpa [top, tri] using signed_mono h hn
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have h := Signed.plus (ih (n := n) (by omega))
      rw [top_diag]
      exact (show top n k - 1 + (↑(n+1) : Int) = top n k + ↑(n+1) - 1 by omega) ▸ h

private theorem tight_forward {n k s} (h : Signed n k s) (hn : n = k+1) :
    ∃ j : Nat, j ≤ k ∧ s = (tri k : Int) - (k+1 : Nat) + 2*(j : Int) := by
  induction h with
  | skip h _ => have b := bounds h; omega
  | @plus n k s h ih =>
    obtain ⟨j, hj, hs⟩ := ih (by omega)
    refine ⟨j+1, by omega, ?_⟩
    rw [tri_step]
    omega
  | @minus n k s h =>
    have e : n = k := by omega
    subst n
    obtain ⟨_,hl,hu⟩ := pos_bounds h
    simp [top] at hu
    exact ⟨0, by omega, by omega⟩

private theorem tight_backward (k j : Nat) (hj : j ≤ k) :
    Signed (k+1) k ((tri k : Int) - (k+1 : Nat) + 2*(j : Int)) := by
  induction k generalizing j with
  | zero =>
    have : j = 0 := by omega
    subst j
    exact Signed.minus (fullPos 0)
  | succ k ih =>
    cases j with
    | zero => simpa using Signed.minus (fullPos (k+1))
    | succ j =>
      have h := Signed.plus (ih j (by omega))
      rw [tri_step]
      rw [show (tri k : Int) + k + 1 - ↑(k+1+1) + 2*↑(j+1) =
        ((tri k : Int) - ↑(k+1) + 2*(j : Int)) + ↑(k+1+1) by omega]
      exact h

theorem spectrum_tight {l : Nat} {z : Int} (_h : 2 ≤ l) :
    Signed (l+1) l z ↔ ∃ j : Nat, j ≤ l ∧ z = (tri l : Int) - (l+1 : Nat) + 2*(j : Int) := by
  constructor
  · intro h; exact tight_forward h rfl
  · rintro ⟨j, hj, rfl⟩; exact tight_backward l j hj

/- Prepend a position to the interval. It can be left unused or chosen
positively; all old positions increase by one. -/
private theorem pos_prepend {a e n k s} (p : Pos 1 e a) (h : Pos n k s) :
    Pos (n+1) (e+k) (a+s+(k : Int)) := by
  induction h with
  | empty => simpa using p
  | skip h ih => exact .skip ih
  | @take n k s h ih =>
    rw [show a + (s + ↑(n+1)) + (↑(k+1) : Int) =
        (a+s+↑k) + ↑(n+1+1) by omega]
    exact .take ih

private theorem signed_prepend {a e n k s} (p : Pos 1 e a) (h : Signed n k s) :
    Signed (n+1) (e+k) (a+s+(k : Int)-1) := by
  induction h with
  | skip h ih => exact .skip ih
  | @plus n k s h ih =>
    rw [show a + (s + ↑(n+1)) + (↑(k+1) : Int) - 1 =
        (a+s+↑k-1) + ↑(n+1+1) by omega]
    exact .plus ih
  | @minus n k s h =>
    rw [show a + (s - ↑(n+1)) + (k : Int) - 1 =
        (a+s+↑k) - ↑(n+1+1) by omega]
    exact .minus (pos_prepend p h)

private theorem shift {n k s} (h : Signed n k s) : Signed (n+1) k (s+k-1) := by
  simpa using signed_prepend (Pos.skip Pos.empty) h

private theorem add_first {n k s} (h : Signed n k s) : Signed (n+1) (k+1) (s+k) := by
  have h' := signed_prepend (Pos.take Pos.empty) h
  change Signed (n+1) (1+k) (1+s+↑k-1) at h'
  rw [show 1+k = k+1 by omega, show (1:Int)+s+↑k-1 = s+k by omega] at h'
  exact h'

private theorem four_two {z : Int} (lo : -1 ≤ z) (hi : z ≤ 6) : Signed 4 2 z := by
  have a : Signed 3 2 0 := tight_backward 2 0 (by decide)
  have b : Signed 3 2 2 := tight_backward 2 1 (by decide)
  have c : Signed 3 2 4 := tight_backward 2 2 (by decide)
  have hz : z = -1 ∨ z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 := by omega
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact minimum (by decide)
  · exact .skip a
  · exact shift a
  · exact .skip b
  · exact shift b
  · exact .skip c
  · exact shift c
  · exact maximum (by decide)

private theorem dense_two {n : Nat} (hn : 4 ≤ n) {z : Int}
    (lo : (tri 2 : Int)-n ≤ z) (hi : z ≤ top n 2 - 1) : Signed n 2 z := by
  induction hn generalizing z with
  | refl => exact four_two lo hi
  | @step n hn ih =>
    have hn4 : 4 ≤ n := hn
    by_cases a : z < (tri 2 : Int)-n
    · have hz : (tri 2 : Int)-↑(n+1) = z := by omega
      exact hz ▸ minimum (n := n+1) (k := 2) (by omega)
    by_cases b : z ≤ top n 2 - 1
    · exact .skip (ih (by omega) b)
    by_cases c : z = top (n+1) 2 - 1
    · exact c ▸ maximum (n := n+1) (k := 2) (by omega)
    rw [top_step] at hi c
    have hz : (top n 2 - 1) + (2 : Nat) - 1 = z := by omega
    exact hz ▸ shift (maximum (n := n) (k := 2) (by omega))

private theorem dense {k : Nat} (hk : 2 ≤ k) {n : Nat} (hn : k+2 ≤ n) {z : Int}
    (lo : (tri k : Int)-n ≤ z) (hi : z ≤ top n k - 1) : Signed n k z := by
  induction hk generalizing n z with
  | refl => exact dense_two hn lo hi
  | @step k hk ih =>
    have hk2 : 2 ≤ k := hk
    cases n with
    | zero => omega
    | succ n =>
      rw [tri_step] at lo
      rw [top_diag] at hi
      by_cases h : z ≤ top n k - 1 + k
      · have prior := ih (n := n) (z := z-k) (by omega) (by omega) (by omega)
        exact (show (z-k) + (k : Int) = z by omega) ▸ add_first prior
      · have nonneg : 0 ≤ (k : Int)*((n : Int)-k) := Int.mul_nonneg (by omega) (by omega)
        have below : (tri k : Int) + (k : Int)*((n : Int)-k) - 1 + ↑k < z :=
          Int.lt_of_not_ge h
        have bottom : (tri k : Int)-n ≤ z-↑(n+1) := by
          omega
        have prior := ih (n := n) (z := z-↑(n+1)) (by omega) bottom (by omega)
        exact (show (z-↑(n+1)) + (↑(n+1) : Int) = z by omega) ▸ Signed.plus prior

theorem spectrum_room {n l : Nat} {z : Int} (hl : 2 ≤ l) (hn : l+2 ≤ n) :
    Signed n l z ↔ (tri l : Int) - n ≤ z ∧ z ≤ (tri l : Int) - 1 + (l : Int)*((n : Int)-l) := by
  constructor
  · intro h
    obtain ⟨_,lo,hi⟩ := bounds h
    unfold top at hi
    exact ⟨lo, by omega⟩
  · rintro ⟨lo,hi⟩
    apply dense hl hn lo
    unfold top
    omega

private theorem one_nonzero {n k s} (h : Signed n k s) (hk : k = 1) : s ≠ 0 := by
  induction h with
  | skip _ ih => exact ih hk
  | @plus n k s h _ =>
    have e : k = 0 := by omega
    subst k
    have b := (bounds h).2.1
    change (0 : Int) - n ≤ s at b
    omega
  | @minus n k s h =>
    subst k
    have b := (pos_bounds h).2.2
    simp [top, tri] at b
    omega

theorem spectrum_one {n : Nat} {z : Int} :
    Signed n 1 z ↔ z ≠ 0 ∧ -(n : Int) < z ∧ z < (n : Int) := by
  constructor
  · intro h
    have b := bounds h
    simp [top, tri] at b
    exact ⟨one_nonzero h rfl, by omega, by omega⟩
  · rintro ⟨hz,lo,hi⟩
    by_cases hp : 0 < z
    · have h := maximum (n := z.toNat+1) (k := 1) (by omega)
      have eq : top (z.toNat+1) 1 - 1 = z := by simp [top, tri]; omega
      exact signed_mono (eq ▸ h) (by omega)
    · have h := minimum (n := (-z).toNat+1) (k := 1) (by omega)
      have eq : (tri 1 : Int) - ↑((-z).toNat+1) = z := by change 1-↑((-z).toNat+1) = z; omega
      exact signed_mono (eq ▸ h) (by omega)

end WeakSchur
