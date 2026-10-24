/-
# Boolean rings

A ring is **Boolean** if every element is idempotent: `a * a = a`.

Classic theorem: every Boolean ring
1. has characteristic 2 (`a + a = 0`), and
2. is **commutative**.

The proof is a nice exercise in expanding `(x + y)²` and cancelling.
-/
import AlgebraFromScratch.Ring.Basic

namespace AlgebraFromScratch

universe u

namespace Ring

variable {R : Type u} [Ring R]

/-- Step 1: in a Boolean ring, `a + a = 0`. -/
theorem add_self_eq_zero_of_idem (h : ∀ x : R, x * x = x) (a : R) : a + a = 0 := by
  -- (a + a)² = a + a, and expanding gives (a + a) + (a + a).
  have expand := add_mul_self a a
  simp only [h] at expand
  -- expand : a + a = a + a + (a + a)
  have : (a + a) + 0 = (a + a) + (a + a) := by
    rw [add_zero]
    exact expand
  exact (add_left_cancel this).symm

/-- In a Boolean ring every element is its own negative. -/
theorem neg_eq_self_of_idem (h : ∀ x : R, x * x = x) (a : R) : -a = a :=
  neg_eq_of_add_eq_zero (add_self_eq_zero_of_idem h a)

/-- Step 2: **every Boolean ring is commutative.** -/
theorem mul_comm_of_idem (h : ∀ x : R, x * x = x) (a b : R) : a * b = b * a := by
  -- (a + b)² = a + b; expanding: a + ab + (ba + b) = a + b
  have expand := add_mul_self a b
  rw [h, h, h] at expand
  -- cancel a on the left and b on the right to get ab + ba = 0
  have key : a * b + b * a = 0 := by
    have e1 : a + (a * b + (b * a + b)) = a + (0 + b) := by
      rw [zero_add, expand, add_assoc]
    have e2 : a * b + (b * a + b) = 0 + b := add_left_cancel e1
    have e3 : (a * b + b * a) + b = 0 + b := by rw [add_assoc]; exact e2
    exact add_right_cancel e3
  -- so ab = -(ba) = ba
  calc a * b = -(b * a) := (neg_eq_of_add_eq_zero (by rw [add_comm]; exact key)).symm
    _ = b * a := neg_eq_self_of_idem h _

/-- Package the theorem: a Boolean ring is a commutative ring. -/
def CommRing.ofIdem (h : ∀ x : R, x * x = x) : CommRing R :=
  { (inferInstance : Ring R) with mul_comm := mul_comm_of_idem h }

end Ring

end AlgebraFromScratch
