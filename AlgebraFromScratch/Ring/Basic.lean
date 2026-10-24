/-
# Rings from axioms

A ring is an abelian group under `+` with an associative, unital `*` that
distributes over `+`. From the axioms alone we derive the "obvious" facts
that school algebra takes for granted:

* `a * 0 = 0` and `0 * a = 0`,
* `(-a) * b = -(a * b)`, `a * (-b) = -(a * b)`,
* **`(-a) * (-b) = a * b`** — "minus times minus is plus",
* `(-1) * a = -a`,
* if `1 = 0` the ring has only one element.
-/

namespace AlgebraFromScratch

universe u

class Ring (R : Type u) extends Add R, Mul R, Neg R, Zero R, One R where
  add_assoc : ∀ a b c : R, a + b + c = a + (b + c)
  zero_add : ∀ a : R, 0 + a = a
  neg_add_cancel : ∀ a : R, -a + a = 0
  add_comm : ∀ a b : R, a + b = b + a
  mul_assoc : ∀ a b c : R, a * b * c = a * (b * c)
  one_mul : ∀ a : R, 1 * a = a
  mul_one : ∀ a : R, a * 1 = a
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

namespace Ring

variable {R : Type u} [Ring R] (a b c : R)

/-! ## The additive group -/

theorem add_zero : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel : a + -a = 0 := by rw [add_comm, neg_add_cancel]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  calc b = -a + a + b := by rw [neg_add_cancel, zero_add]
    _ = -a + (a + b) := add_assoc _ _ _
    _ = -a + (a + c) := by rw [h]
    _ = c := by rw [← add_assoc, neg_add_cancel, zero_add]

theorem add_right_cancel {a b c : R} (h : b + a = c + a) : b = c := by
  rw [add_comm b, add_comm c] at h
  exact add_left_cancel h

/-- Additive inverses are unique. -/
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  apply add_left_cancel (a := a)
  rw [add_neg_cancel, h]

@[simp] theorem neg_neg : -(-a) = a :=
  neg_eq_of_add_eq_zero (neg_add_cancel a)

@[simp] theorem neg_zero : -(0 : R) = 0 :=
  neg_eq_of_add_eq_zero (add_zero 0)

theorem neg_add : -(a + b) = -a + -b := by
  apply neg_eq_of_add_eq_zero
  calc a + b + (-a + -b) = (a + -a) + (b + -b) := by
        rw [add_assoc, ← add_assoc b, add_comm b, add_assoc, ← add_assoc]
    _ = 0 := by rw [add_neg_cancel, add_neg_cancel, add_zero]

/-! ## Multiplication by zero -/

/-- `a * 0 = 0`. Not an axiom: it follows from distributivity. -/
@[simp] theorem mul_zero : a * 0 = 0 := by
  apply add_left_cancel (a := a * 0)
  rw [← left_distrib, add_zero, add_zero]

@[simp] theorem zero_mul : 0 * a = 0 := by
  apply add_left_cancel (a := 0 * a)
  rw [← right_distrib, add_zero, add_zero]

/-! ## Sign rules -/

theorem neg_mul : -a * b = -(a * b) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← right_distrib, add_neg_cancel, zero_mul]

theorem mul_neg : a * -b = -(a * b) := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [← left_distrib, add_neg_cancel, mul_zero]

/-- **Minus times minus is plus.** -/
theorem neg_mul_neg : -a * -b = a * b := by
  rw [neg_mul, mul_neg, neg_neg]

theorem neg_one_mul : -1 * a = -a := by
  rw [neg_mul, one_mul]

theorem mul_neg_one : a * -1 = -a := by
  rw [mul_neg, mul_one]

theorem neg_one_mul_neg_one : (-1 : R) * -1 = 1 := by
  rw [neg_mul_neg, one_mul]

/-! ## Squares -/

/-- `(a + b)² = a² + ab + ba + b²` in any (not necessarily commutative) ring. -/
theorem add_mul_self :
    (a + b) * (a + b) = a * a + a * b + (b * a + b * b) := by
  rw [right_distrib, left_distrib, left_distrib, add_assoc]

/-! ## The zero ring -/

/-- If `1 = 0` then every element is `0`. -/
theorem eq_zero_of_one_eq_zero (h : (1 : R) = 0) : a = 0 := by
  rw [← one_mul a, h, zero_mul]

end Ring

/-- A commutative ring. -/
class CommRing (R : Type u) extends Ring R where
  mul_comm : ∀ a b : R, a * b = b * a

namespace CommRing

variable {R : Type u} [CommRing R] (a b : R)

/-- In a commutative ring, `(a + b)² = a² + 2ab + b²` (written without `2`). -/
theorem add_sq :
    (a + b) * (a + b) = a * a + (a * b + a * b) + b * b := by
  rw [Ring.add_mul_self, mul_comm b a]
  simp only [Ring.add_assoc]

/-- Difference of squares: `(a + b)(a - b) = a² - b²`. -/
theorem mul_self_sub_mul_self :
    (a + b) * (a + -b) = a * a + -(b * b) := by
  rw [Ring.left_distrib, Ring.right_distrib, Ring.right_distrib, Ring.mul_neg,
    Ring.mul_neg, mul_comm b a, Ring.add_assoc, ← Ring.add_assoc (a * b),
    Ring.add_neg_cancel, Ring.zero_add]

end CommRing

end AlgebraFromScratch
