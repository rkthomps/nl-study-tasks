
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

def shiftRange (r : Finset ℕ) (s : ℕ) : Finset ℕ :=
  r.map ⟨λ i => i + s, by simp[Function.Injective]⟩

-- range from s to e inclusive
@[simp]
def range (s e : ℕ) : Finset ℕ :=
  shiftRange (Finset.range (e - s + 1)) s

theorem shift_sum (s : Finset ℕ) (shift : ℕ) (f : ℕ → ℕ) :
  ∑ i ∈ range 0 n

theorem sum_shift (n : ℕ) : ∑ i ∈ range 0 n, n.choose i = 1 + ∑ i ∈ range 1 n, n.choose i := by
  induction n with
  | zero => simp
  | succ n' ih =>


theorem powerset_card (n : ℕ) :
  ∑ i ∈ range 0 n, Nat.choose n i = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n' ih =>
    -- ∑_i=0^{n+1} (n+1 choose i) = 1 + ∑_i=1^{n+1} (n+1 choose i)
    have h1: ∑ i ∈ range 0 (n' + 1), Nat.choose (n' + 1) i = 1 + ∑ i ∈ range 1 (n' + 1), Nat.choose (n' + 1) i := by
      ring_nf



theorem binom_theorem (a b n : Nat) :
  (a + b) ^ n = ∑ i ∈ Finset.range (n + 1), Nat.choose n i * (a ^ i) * (b ^ (n - i)):= by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ∑ i ∈ Finset.range (n + 1 + 1), (n + 1).choose i * a ^ i * b ^ (n + 1 - i) =
