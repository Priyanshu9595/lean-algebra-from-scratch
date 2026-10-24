/-
# Concrete instances

The abstract theory above is not vacuous: here are concrete models,
and the general theorems applied to them.
-/
import AlgebraFromScratch.Group.Abelian
import AlgebraFromScratch.Group.Hom
import AlgebraFromScratch.Ring.Boolean

namespace AlgebraFromScratch

/-! ## The integers form a commutative ring -/

instance : CommRing Int where
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  neg_add_cancel := Int.add_left_neg
  add_comm := Int.add_comm
  mul_assoc := Int.mul_assoc
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  mul_comm := Int.mul_comm

/-- Our abstract sign rule, specialised to `Int`. -/
example (a b : Int) : -a * -b = a * b := Ring.neg_mul_neg a b

/-! ## `ℤ/2` as a group, via `Bool` and exclusive-or -/

/-- `ℤ/2ℤ` modelled as `Bool` with `xor` as the group operation. -/
def Z2 := Bool

instance : Group Z2 where
  mul a b := Bool.xor a b
  one := false
  inv a := a
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  inv_mul_cancel a := by cases a <;> rfl

theorem Z2.mul_self (a : Z2) : a * a = 1 := by
  cases a <;> rfl

/-- `ℤ/2` is abelian — derived from the general theorem, not checked by hand. -/
instance : CommGroup Z2 := Group.CommGroup.ofMulSelfEqOne Z2.mul_self

/-- The parity map `ℤ/2 × ℤ/2 → ℤ/2`-style example: the identity is a
homomorphism with trivial kernel, hence injective. -/
example : ∀ a b : Z2, (Hom.id Z2) a = (Hom.id Z2) b → a = b :=
  (Hom.injective_iff_ker_trivial (Hom.id Z2)).2 (fun _ hx => hx)

/-! ## `Bool` as a Boolean ring (`xor` is `+`, `&&` is `*`) -/

/-- The two-element Boolean ring. -/
def B2 := Bool

instance : Ring B2 where
  add a b := Bool.xor a b
  mul a b := a && b
  neg a := a
  zero := false
  one := true
  add_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  zero_add a := by cases a <;> rfl
  neg_add_cancel a := by cases a <;> rfl
  add_comm a b := by cases a <;> cases b <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  left_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl
  right_distrib a b c := by cases a <;> cases b <;> cases c <;> rfl

theorem B2.idem (a : B2) : a * a = a := by cases a <;> rfl

/-- Commutativity of `B2` obtained from the Boolean-ring theorem. -/
instance : CommRing B2 := Ring.CommRing.ofIdem B2.idem

/-- …and characteristic 2. -/
example (a : B2) : a + a = 0 := Ring.add_self_eq_zero_of_idem B2.idem a

end AlgebraFromScratch
