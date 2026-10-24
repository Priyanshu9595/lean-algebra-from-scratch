/-
# Abelian groups and commutativity criteria

Two classic textbook exercises:

1. If every element is its own inverse (`a * a = 1`), the group is abelian.
2. `(a * b)² = a² * b²` holds exactly when `a` and `b` commute.
-/
import AlgebraFromScratch.Group.Power

namespace AlgebraFromScratch

universe u

/-- A commutative (abelian) group. -/
class CommGroup (G : Type u) extends Group G where
  mul_comm : ∀ a b : G, a * b = b * a

namespace Group

variable {G : Type u} [Group G]

/-- **Exercise 1.** A group in which every element squares to `1` is abelian. -/
theorem comm_of_mul_self_eq_one (h : ∀ x : G, x * x = 1) (a b : G) :
    a * b = b * a := by
  have self_inv : ∀ x : G, x⁻¹ = x := fun x => (inv_eq_self_iff x).2 (h x)
  calc a * b = (a * b)⁻¹ := (self_inv _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [self_inv, self_inv]

/-- Package Exercise 1 as an instance-builder. -/
def CommGroup.ofMulSelfEqOne (h : ∀ x : G, x * x = 1) : CommGroup G :=
  { (inferInstance : Group G) with mul_comm := comm_of_mul_self_eq_one h }

/-- **Exercise 2.** `(ab)(ab) = (aa)(bb)` iff `ab = ba`. -/
theorem mul_self_mul_eq_iff_comm (a b : G) :
    (a * b) * (a * b) = (a * a) * (b * b) ↔ a * b = b * a := by
  constructor
  · intro h
    -- rewrite both sides as `a * (_ * b)` and cancel `a` on the left, `b` on the right
    have h' : a * ((b * a) * b) = a * ((a * b) * b) := by
      simpa only [mul_assoc] using h
    exact (mul_right_cancel (mul_left_cancel h')).symm
  · intro h
    calc (a * b) * (a * b) = a * ((b * a) * b) := by simp only [mul_assoc]
      _ = a * ((a * b) * b) := by rw [h]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]

/-- Same statement, phrased with powers. -/
theorem sq_mul_eq_iff_comm (a b : G) :
    (a * b) ^ (2 : Nat) = a ^ (2 : Nat) * b ^ (2 : Nat) ↔ a * b = b * a := by
  have sq : ∀ x : G, x ^ (2 : Nat) = x * x := fun x => by
    rw [pow_succ, pow_one]
  rw [sq, sq, sq]
  exact mul_self_mul_eq_iff_comm a b

/-- In an abelian group the inverse map is a homomorphism. -/
theorem inv_mul_of_comm {a b : G} (h : a * b = b * a) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  rw [h, mul_inv_rev]

end Group

namespace CommGroup

variable {G : Type u} [CommGroup G]

theorem mul_pow (a b : G) (n : Nat) : (a * b) ^ n = a ^ n * b ^ n :=
  Group.mul_pow_of_comm (mul_comm a b) n

theorem mul_inv (a b : G) : (a * b)⁻¹ = a⁻¹ * b⁻¹ :=
  Group.inv_mul_of_comm (mul_comm a b)

end CommGroup

end AlgebraFromScratch
