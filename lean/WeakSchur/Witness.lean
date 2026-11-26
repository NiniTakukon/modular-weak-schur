import WeakSchur.Model

namespace WeakSchur

/-- An ordered list of distinct positive summands and a separate right-hand side in 1,...,n. -/
def SignedWitness (n l : Nat) (z : Int) : Prop :=
  ∃ (xs : List Nat) (y : Nat), xs.length = l ∧
    (xs.Nodup ∧ ∀ x ∈ xs, 0 < x ∧ x ≤ n) ∧
    y ∉ xs ∧ 0 < y ∧ y ≤ n ∧ (xs.sum : Int) - y = z

private abbrev ValidList (n : Nat) (xs : List Nat) : Prop :=
  xs.Nodup ∧ ∀ x ∈ xs, 0 < x ∧ x ≤ n

private theorem top_fresh {n xs} (h : ValidList n xs) : n + 1 ∉ xs := by
  intro hmem
  have := (h.2 _ hmem).2
  omega

private theorem valid_skip {n xs} (h : ValidList n xs) : ValidList (n + 1) xs :=
  ⟨h.1, fun x hx => ⟨(h.2 x hx).1, Nat.le_succ_of_le (h.2 x hx).2⟩⟩

private theorem valid_cons {n xs} (h : ValidList n xs) : ValidList (n + 1) ((n + 1) :: xs) := by
  refine ⟨List.nodup_cons.mpr ⟨top_fresh h, h.1⟩, ?_⟩
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨Nat.zero_lt_succ _, Nat.le_refl _⟩
  · exact (valid_skip h).2 x hx

private theorem list_of_pos {n l s} (h : Pos n l s) :
    ∃ xs : List Nat, xs.length = l ∧ ValidList n xs ∧ (xs.sum : Int) = s := by
  induction h with
  | empty => exact ⟨[], rfl, ⟨by simp, by simp⟩, rfl⟩
  | skip _ ih =>
    obtain ⟨xs, hlen, hv, hsum⟩ := ih
    exact ⟨xs, hlen, valid_skip hv, hsum⟩
  | @take n l s _ ih =>
    obtain ⟨xs, hlen, hv, hsum⟩ := ih
    refine ⟨(n + 1) :: xs, by simp [hlen], valid_cons hv, ?_⟩
    simp only [List.sum_cons, Int.natCast_add]
    omega

private theorem witness_of_signed {n l z} (h : Signed n l z) : SignedWitness n l z := by
  induction h with
  | skip _ ih =>
    obtain ⟨xs, y, hlen, hv, hnot, hypos, hyle, hz⟩ := ih
    exact ⟨xs, y, hlen, valid_skip hv, hnot, hypos, Nat.le_succ_of_le hyle, hz⟩
  | @plus n l z _ ih =>
    obtain ⟨xs, y, hlen, hv, hnot, hypos, hyle, hz⟩ := ih
    refine ⟨(n + 1) :: xs, y, by simp [hlen], valid_cons hv, ?_, hypos,
      Nat.le_succ_of_le hyle, ?_⟩
    · intro hmem
      rcases List.mem_cons.mp hmem with heq | htail
      · omega
      · exact hnot htail
    · simp only [List.sum_cons, Int.natCast_add]
      omega
  | @minus n l s hpos =>
    obtain ⟨xs, hlen, hv, hsum⟩ := list_of_pos hpos
    exact ⟨xs, n + 1, hlen, valid_skip hv, top_fresh hv, Nat.zero_lt_succ _,
      Nat.le_refl _, by rw [hsum]⟩

/-- Reconstruct the positive derivation and the signed one for each admissible right-hand side. -/
private theorem realize_list {n xs} (h : ValidList n xs) :
    Pos n xs.length (xs.sum : Int) ∧
    ∀ y : Nat, y ∉ xs → 0 < y → y ≤ n → Signed n xs.length ((xs.sum : Int) - y) := by
  induction n generalizing xs with
  | zero =>
    have hempty : xs = [] := List.eq_nil_iff_forall_not_mem.mpr (by
      intro x hx
      obtain ⟨hxpos, hxle⟩ := h.2 x hx
      omega)
    subst xs
    exact ⟨Pos.empty, fun y _ hypos hyle => by omega⟩
  | succ n ih =>
    let rest := xs.erase (n + 1)
    have hrest : ValidList n rest := by
      refine ⟨h.1.erase _, ?_⟩
      intro x hx
      obtain ⟨hne, hmem⟩ := h.1.mem_erase_iff.mp hx
      obtain ⟨hxpos, hxle⟩ := h.2 x hmem
      exact ⟨hxpos, by omega⟩
    obtain ⟨pos, signed⟩ := ih hrest
    by_cases htop : n + 1 ∈ xs
    · have perm : xs.Perm ((n + 1) :: rest) := List.perm_cons_erase htop
      have hlen : xs.length = rest.length + 1 := perm.length_eq
      have hsum : xs.sum = (n + 1) + rest.sum :=
        perm.foldr_eq' (f := Nat.add) (fun x _ y _ t => Nat.add_left_comm y x t) 0
      have hcast : (xs.sum : Int) = (rest.sum : Int) + (↑(n + 1) : Int) := by omega
      rw [hlen, hcast]
      refine ⟨Pos.take pos, ?_⟩
      intro y hnot hypos hyle
      have hne : y ≠ n + 1 := fun heq => hnot (heq ▸ htop)
      have hnotRest : y ∉ rest := fun hy => hnot (List.mem_of_mem_erase hy)
      have hs := signed y hnotRest hypos (by omega)
      rw [show (rest.sum : Int) + (↑(n + 1) : Int) - y =
               ((rest.sum : Int) - y) + (↑(n + 1) : Int) by omega]
      exact Signed.plus hs
    · have heq : rest = xs := List.erase_of_not_mem htop
      rw [heq] at pos signed
      refine ⟨Pos.skip pos, ?_⟩
      intro y hnot hypos hyle
      by_cases hy : y = n + 1
      · subst y
        exact Signed.minus pos
      · exact Signed.skip (signed y hnot hypos (by omega))

/-- The signed recurrence represents exactly the bounded, pairwise distinct witnesses. -/
theorem signed_iff_witness {n l : Nat} {z : Int} : Signed n l z ↔ SignedWitness n l z := by
  constructor
  · exact witness_of_signed
  · rintro ⟨xs, y, rfl, hv, hnot, hypos, hyle, rfl⟩
    exact (realize_list hv).2 y hnot hypos hyle

end WeakSchur
