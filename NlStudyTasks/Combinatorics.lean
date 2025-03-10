
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

-- def choose (n k : Nat) : Nat := (n)! / ((k)! * (n - k)!)

-- range from 1 to 1000
def y := Finset.range 1000
#eval ∑ i ∈ y, i

theorem binom_theorem (a b n : Nat) :
  (a + b) ^ n = ∑ i ∈ Finset.range (n + 1), Nat.choose n i * (a ^ i) * (b ^ (n - i)):= by
  induction n with
  | zero => simp
  | succ n ih => sorry
