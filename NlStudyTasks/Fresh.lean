
import Mathlib.Tactic



theorem sum_shift (n : ℕ) (f : ℕ → ℕ) :
  ∑ (i ∈ Finset.range (n + 1)), f i = f 0 + ∑ (i ∈ Finset.range n), f (i + 1) := by
  induction n with
  | zero => simp [Finset.range]
  | succ n' ih =>
    have h_range_union_1 : Finset.range (n' + 1) = Finset.range n' ∪ {n'} := by
      apply Finset.range_add
    have h_range_union_2 : Finset.range (n' + 1 + 1) = Finset.range (n' + 1) ∪ {n' + 1} := by
      apply Finset.range_add
    have h_disjoint_1 : Disjoint (Finset.range n') {n'} := by simp
    have h_disjoint_2 : Disjoint (Finset.range (n' + 1)) {n' + 1} := by simp
    rw [h_range_union_1]
    rw [Finset.sum_union h_disjoint_1]
    rw [h_range_union_2]
    rw [Finset.sum_union h_disjoint_2]
    simp
    rw [ih]
    omega


theorem sum_choose_shift (n : ℕ) :
  ∑ i ∈ Finset.range (n + 1), n.choose i =
  1 + ∑ i ∈ Finset.range (n + 1), n.choose (i + 1) := by
  have h_shift := sum_shift n (fun i => n.choose i)
  rw [Nat.choose_zero_right] at h_shift
  have heq : ∑ i ∈ Finset.range (n + 1), n.choose (i + 1) = ∑ i ∈ Finset.range n, n.choose (i + 1) := by
    have h_range_union_1 : Finset.range (n + 1) = Finset.range n ∪ {n} := by
      apply Finset.range_add
    have h_disjoint_1 : Disjoint (Finset.range n) {n} := by simp
    rw [h_range_union_1]
    rw [Finset.sum_union h_disjoint_1]
    simp
  rw [heq]
  assumption



theorem sum_choose_exp (n : ℕ) : ∑ i ∈ Finset.range (n + 1), n.choose i = 2^n := by
  induction n with
  | zero => simp
  | succ n' ih =>
    rw [sum_choose_shift (n' + 1)]
    simp [Nat.choose]
    rw [Finset.sum_add_distrib]
    have h_range_union : Finset.range (n' + 1 + 1) = Finset.range (n' + 1) ∪ {n' + 1} := by
      apply Finset.range_add
    rw [h_range_union]
    have h_disjoint : Disjoint (Finset.range (n' + 1)) {n' + 1} := by simp
    rw [Finset.sum_union h_disjoint]
    rw [ih]
    simp
    rw [Finset.sum_union h_disjoint]
    simp
    have h_choose : n'.choose (n' + 1 + 1)  = 0 := by rw [Nat.choose_eq_zero_iff]; omega;
    rw [h_choose]
    simp
    rw [← Nat.add_assoc]
    have h_add : (1 + 2^ n' = 2^n' + 1) := by omega
    rw [h_add]
    rw [Nat.add_assoc]
    rw [← sum_choose_shift]
    rw [ih]
    omega


theorem sum_choose_exp' (n : ℕ) : ∑ i ∈ Finset.range (n + 1), n.choose i = 2^n := by
  have finsetn : ∃ f : Finset ℕ, n = f.card := by
    exists Finset.range n
    simp
  obtain ⟨f, hf⟩ := finsetn
  rw [hf]
  rw [← Finset.card_powerset f]
  rw [Finset.powerset_card_disjiUnion]
  rw [Finset.card_disjiUnion]
  simp
