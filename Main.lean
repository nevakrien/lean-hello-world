import LeanHelloWorld
import Mathlib.Algebra.Ring.Parity


def main : IO Unit :=
  IO.println s!"Hello, {hello}!"


def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

theorem fact_even (n : Nat) : n ≥ 2 → Even (fact n) := by
  intro h
  rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
  induction k with
  | zero =>
      simp [fact]
  | succ k ih =>
      have hk : 2 + k ≥ 2 := by
        exact Nat.le_add_right 2 k
      have h₂ : Even (fact (2 + k)) := ih hk
      simpa [fact, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using h₂.mul_left (k + 3)
