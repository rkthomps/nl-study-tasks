
-- Should we include mathlib?
-- That would kind of test how well the user can look for
-- lemmas which is not really what we are studying.

-- Maybe the LLMs should know about the lemmas?

-- Binomial thoerem:
-- (a + b)^n = ∑_{k=0}^{n} (n choose k) * a^(n-k) * b^k


import Mathlib.Tactic

def fac : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fac n

notation n "!" => fac n

@[simp]
def shiftRange (r : Finset ℕ) (s : ℕ) : Finset ℕ :=
  r.map ⟨λ i => i + s, by simp[Function.Injective]⟩

-- range from s to e inclusive
@[simp]
def range (s e : ℕ) : Finset ℕ :=
  shiftRange (Finset.range (e - s + 1)) s


example (x y : Set α) (H : x ⊆ y) : x ∩ y = x := by
  apply Set.ext
  intro z
  simp
  simp [Set.subset_def] at H





theorem sum_break_range (s b e : ℕ) (f : ℕ → ℕ) :
  ∑ i ∈ range s e, f i = ∑ i ∈ range s b, f i + ∑ i ∈ range (b + 1) e, f i := by
  have h_union : range s e = range s b ∪ range (b + 1) e := by
    simp



theorem sum_shift (n : ℕ) : ∑ i ∈ range 0 n, n.choose i = 1 + ∑ i ∈ range 1 n, n.choose i := by
  induction n with
  | zero => simp
  | succ n' ih =>




theorem binom_theorem (a b n : Nat) :
  (a + b) ^ n = ∑ i ∈ Finset.range (n + 1), Nat.choose n i * (a ^ i) * (b ^ (n - i)):= by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ∑ i ∈ Finset.range (n + 1 + 1), (n + 1).choose i * a ^ i * b ^ (n + 1 - i) =
