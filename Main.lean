import LeanHelloWorld
import Mathlib.Algebra.Ring.Parity


def main : IO Unit :=
  IO.println s!"Hello, {hello}!"


def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fact n

theorem fact_succ_pred (m : Nat) (hm : m > 0) :
  fact m = m * fact (m - 1) := by
  cases m with
  | zero => cases hm
  | succ t => simp [fact]

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

theorem fact_dvd (m n : Nat) (hm : m > 0) : n ≥ m → m ∣ fact n := by
  intro h
  rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
  induction k with
  | zero =>
      have h1 := fact_succ_pred m hm
      have h2 : m ∣ m * fact (m - 1) :=
        dvd_mul_right m (fact (m - 1))
      rw [Nat.add_zero, h1]
      exact h2
  | succ k ih =>
      have hk : m + k ≥ m := Nat.le_add_right m k
      have h₂ : m ∣ fact (m + k) := ih hk
      simpa [fact, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using dvd_mul_of_dvd_right h₂ (m + k + 1)
