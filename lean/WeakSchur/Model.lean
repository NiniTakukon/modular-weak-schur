import Std

namespace WeakSchur

/-- Choose k distinct entries of 1,...,n, with ordinary sum s. -/
inductive Pos : Nat → Nat → Int → Prop where
  | empty : Pos 0 0 0
  | skip {n k s} : Pos n k s → Pos (n+1) k s
  | take {n k s} : Pos n k s → Pos (n+1) (k+1) (s + (↑(n+1) : Int))

/-- Exactly one entry has weight -1, exactly k have weight +1.
The constructors process the entries from left to right, using each at most once. -/
inductive Signed : Nat → Nat → Int → Prop where
  | skip {n k s} : Signed n k s → Signed (n+1) k s
  | plus {n k s} : Signed n k s → Signed (n+1) (k+1) (s + (↑(n+1) : Int))
  | minus {n k s} : Pos n k s → Signed (n+1) k (s - (↑(n+1) : Int))

def tri : Nat → Nat
  | 0 => 0
  | n+1 => tri n + (n+1)

theorem tri_pos {l : Nat} (h : 0 < l) : 0 < tri l := by
  cases l with
  | zero => omega
  | succ l => simp only [tri]; omega

theorem tri_closed (n : Nat) : tri n = n*(n+1)/2 := by
  have twice (k : Nat) : 2*tri k = k*(k+1) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      calc
        2*tri (k+1) = 2*tri k + 2*(k+1) := Nat.mul_add 2 _ _
        _ = (k+2)*(k+1) := by rw [ih, Nat.add_mul]
        _ = (k+1)*(k+1+1) := Nat.mul_comm _ _
  have h := twice n
  omega

end WeakSchur
