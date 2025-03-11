
import Mathlib.Tactic


theorem sum_finset_union (s1 s2 : Finset ℕ) (f : ℕ → ℕ) :
  ∑ i ∈ s1 ∪ s2, f i = ∑ i ∈ s1, f i + ∑ i ∈ s2, f i := by
  apply Finset.sum_union


theorem sum_choose_exp (n : ℕ) : ∑ i ∈ Finset.range (n + 1), n.choose i = 2^n := by
  induction n with
  | zero => simp
  | succ n' ih =>
    let newRange := Finset.range (n'+ 1 + 1) \ {0}
    have h_union : Finset.range (n'+ 1 + 1) = newRange ∪ {0} := by simp [newRange]
    rw [h_union]
    have h_one_plus : ∑ i ∈ newRange ∪ {0}, (n'+ 1).choose i =
        ∑ i ∈ newRange, (n'+ 1).choose i + ∑ i ∈ {0}, (n' + 1).choose i := by
        have h_disjoint : Disjoint newRange {0} := by simp [newRange]
        apply (Finset.sum_union h_disjoint)
    rw [h_one_plus]
    simp

    have h_newRange : newRange ∪ {0} = Finset.range (n' + 1 + 1) := by
      simp [newRange]
