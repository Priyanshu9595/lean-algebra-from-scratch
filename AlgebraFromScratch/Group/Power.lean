/-
# Natural-number powers in a group

`a ^ n` is defined by recursion: `a ^ 0 = 1`, `a ^ (n+1) = a ^ n * a`.
We prove the exponent laws by induction.
-/
import AlgebraFromScratch.Group.Basic

namespace AlgebraFromScratch

universe u

namespace Group

variable {G : Type u} [Group G]

/-- Repeated multiplication. -/
def npow (a : G) : Nat → G
  | 0 => 1
  | n + 1 => npow a n * a

instance : HPow G Nat G := ⟨npow⟩

variable (a b : G) (m n : Nat)

@[simp] theorem pow_zero : a ^ (0 : Nat) = 1 := rfl

theorem pow_succ : a ^ (n + 1) = a ^ n * a := rfl

@[simp] theorem pow_one : a ^ (1 : Nat) = a := by
  rw [pow_succ, pow_zero, one_mul]

/-- `a` commutes with its own powers. -/
theorem pow_mul_comm : a ^ n * a = a * a ^ n := by
  induction n with
  | zero => rw [pow_zero, one_mul, mul_one]
  | succ k ih =>
    rw [pow_succ, mul_assoc, ih, ← mul_assoc, ← ih, ← pow_succ]
    -- goal: a ^ (k+1) * a = a * (a ^ k * a)
    rw [pow_succ, ← mul_assoc, ih]

theorem pow_succ' : a ^ (n + 1) = a * a ^ n := by
  rw [pow_succ, pow_mul_comm]

@[simp] theorem one_pow : (1 : G) ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [pow_succ, ih, one_mul]

/-- First exponent law: `a ^ (m + n) = a ^ m * a ^ n`. -/
theorem pow_add : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, pow_zero, mul_one]
  | succ k ih => rw [← Nat.add_assoc, pow_succ, ih, pow_succ, mul_assoc]

/-- Powers of the same element commute. -/
theorem pow_mul_pow_comm : a ^ m * a ^ n = a ^ n * a ^ m := by
  rw [← pow_add, ← pow_add, Nat.add_comm]

/-- Second exponent law: `a ^ (m * n) = (a ^ m) ^ n`. -/
theorem pow_mul : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => rw [Nat.mul_zero, pow_zero, pow_zero]
  | succ k ih => rw [Nat.mul_succ, pow_add, ih, pow_succ]

/-- `(a⁻¹) ^ n = (a ^ n)⁻¹`. -/
theorem inv_pow : a⁻¹ ^ n = (a ^ n)⁻¹ := by
  induction n with
  | zero => rw [pow_zero, pow_zero, inv_one]
  | succ k ih => rw [pow_succ, ih, pow_succ', mul_inv_rev]

/-- If `a` and `b` commute then `b` commutes with every power of `a`. -/
theorem pow_mul_comm_of_comm {a b : G} (h : a * b = b * a) (n : Nat) :
    a ^ n * b = b * a ^ n := by
  induction n with
  | zero => rw [pow_zero, one_mul, mul_one]
  | succ k ih =>
    rw [pow_succ, mul_assoc, h, ← mul_assoc, ih, mul_assoc]

/-- For commuting elements, `(a * b) ^ n = a ^ n * b ^ n`. -/
theorem mul_pow_of_comm {a b : G} (h : a * b = b * a) (n : Nat) :
    (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, one_mul]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ, pow_succ]
    -- a^k * b^k * (a * b) = a^k * a * (b^k * b)
    have hb : b ^ k * a = a * b ^ k := (pow_mul_comm_of_comm h.symm k)
    calc a ^ k * b ^ k * (a * b)
        = a ^ k * ((b ^ k * a) * b) := by simp only [mul_assoc]
      _ = a ^ k * ((a * b ^ k) * b) := by rw [hb]
      _ = a ^ k * a * (b ^ k * b) := by simp only [mul_assoc]

end Group

end AlgebraFromScratch
