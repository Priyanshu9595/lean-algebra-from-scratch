/-
# Groups from minimal axioms

We define a group using the *weakest* standard axiom set:

* associativity,
* a **left** identity `1 * a = a`,
* a **left** inverse `a⁻¹ * a = 1`.

The right-handed versions (`a * 1 = a`, `a * a⁻¹ = 1`) are *not* assumed —
they are theorems, proved below. Everything else in this file is derived from
these three axioms alone; no Mathlib is used.
-/

namespace AlgebraFromScratch

universe u

/-- A group, axiomatised with a left identity and left inverses only. -/
class Group (G : Type u) extends Mul G, One G, Inv G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

namespace Group

variable {G : Type u} [Group G] (a b c : G)

/-! ## Recovering the right-handed axioms -/

/-- The left inverse is also a right inverse.

Classical trick: write `1` on the left as `(a⁻¹)⁻¹ * a⁻¹` and re-associate. -/
theorem mul_inv_cancel : a * a⁻¹ = 1 := by
  calc a * a⁻¹
      = 1 * (a * a⁻¹) := (one_mul _).symm
    _ = ((a⁻¹)⁻¹ * a⁻¹) * (a * a⁻¹) := by rw [inv_mul_cancel]
    _ = (a⁻¹)⁻¹ * ((a⁻¹ * a) * a⁻¹) := by rw [mul_assoc, ← mul_assoc a⁻¹ a]
    _ = (a⁻¹)⁻¹ * a⁻¹ := by rw [inv_mul_cancel, one_mul]
    _ = 1 := inv_mul_cancel _

/-- The left identity is also a right identity. -/
theorem mul_one : a * 1 = a := by
  calc a * 1
      = a * (a⁻¹ * a) := by rw [inv_mul_cancel]
    _ = (a * a⁻¹) * a := (mul_assoc _ _ _).symm
    _ = a := by rw [mul_inv_cancel, one_mul]

/-! ## Cancellation -/

theorem mul_left_cancel {a b c : G} (h : a * b = a * c) : b = c := by
  calc b = 1 * b := (one_mul b).symm
    _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel]
    _ = a⁻¹ * (a * b) := mul_assoc _ _ _
    _ = a⁻¹ * (a * c) := by rw [h]
    _ = (a⁻¹ * a) * c := (mul_assoc _ _ _).symm
    _ = c := by rw [inv_mul_cancel, one_mul]

theorem mul_right_cancel {a b c : G} (h : b * a = c * a) : b = c := by
  calc b = b * 1 := (mul_one b).symm
    _ = b * (a * a⁻¹) := by rw [mul_inv_cancel]
    _ = (b * a) * a⁻¹ := (mul_assoc _ _ _).symm
    _ = (c * a) * a⁻¹ := by rw [h]
    _ = c * (a * a⁻¹) := mul_assoc _ _ _
    _ = c := by rw [mul_inv_cancel, mul_one]

theorem mul_left_cancel_iff : a * b = a * c ↔ b = c :=
  ⟨mul_left_cancel, fun h => by rw [h]⟩

theorem mul_right_cancel_iff : b * a = c * a ↔ b = c :=
  ⟨mul_right_cancel, fun h => by rw [h]⟩

/-! ## Uniqueness of the identity and of inverses -/

/-- Any left identity equals `1`. -/
theorem eq_one_of_left_id {e : G} (h : ∀ x : G, e * x = x) : e = 1 := by
  calc e = e * 1 := (mul_one e).symm
    _ = 1 := h 1

/-- Any right identity equals `1`. -/
theorem eq_one_of_right_id {e : G} (h : ∀ x : G, x * e = x) : e = 1 := by
  calc e = 1 * e := (one_mul e).symm
    _ = 1 := h 1

/-- A right inverse of `a` must be `a⁻¹`. -/
theorem eq_inv_of_mul_eq_one {a b : G} (h : a * b = 1) : b = a⁻¹ := by
  calc b = 1 * b := (one_mul b).symm
    _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel]
    _ = a⁻¹ * (a * b) := mul_assoc _ _ _
    _ = a⁻¹ := by rw [h, mul_one]

/-- A left inverse of `b` must be `b⁻¹`. -/
theorem eq_inv_of_mul_eq_one_left {a b : G} (h : a * b = 1) : a = b⁻¹ := by
  calc a = a * 1 := (mul_one a).symm
    _ = a * (b * b⁻¹) := by rw [mul_inv_cancel]
    _ = (a * b) * b⁻¹ := (mul_assoc _ _ _).symm
    _ = b⁻¹ := by rw [h, one_mul]

/-! ## Algebra of inverses -/

@[simp] theorem inv_inv : (a⁻¹)⁻¹ = a :=
  (eq_inv_of_mul_eq_one (inv_mul_cancel a)).symm

@[simp] theorem inv_one : (1 : G)⁻¹ = 1 :=
  (eq_inv_of_mul_eq_one (mul_one (1 : G))).symm

/-- "Socks and shoes": the inverse of a product reverses the order. -/
theorem mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  refine (eq_inv_of_mul_eq_one ?_).symm
  calc a * b * (b⁻¹ * a⁻¹)
      = a * ((b * b⁻¹) * a⁻¹) := by rw [mul_assoc, ← mul_assoc b]
    _ = 1 := by rw [mul_inv_cancel, one_mul, mul_inv_cancel]

theorem inv_injective {a b : G} (h : a⁻¹ = b⁻¹) : a = b := by
  rw [← inv_inv a, h, inv_inv]

theorem inv_inj : a⁻¹ = b⁻¹ ↔ a = b :=
  ⟨inv_injective, fun h => by rw [h]⟩

theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
  ⟨eq_inv_of_mul_eq_one_left, fun h => by rw [h, inv_mul_cancel]⟩

theorem eq_of_mul_inv_eq_one {a b : G} (h : a * b⁻¹ = 1) : a = b := by
  have := eq_inv_of_mul_eq_one_left h
  rwa [inv_inv] at this

theorem inv_eq_self_iff : a⁻¹ = a ↔ a * a = 1 := by
  constructor
  · intro h
    calc a * a = a * a⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel a
  · intro h
    exact (eq_inv_of_mul_eq_one h).symm

/-! ## Linear equations have unique solutions -/

/-- `a * x = b` has the unique solution `x = a⁻¹ * b`. -/
theorem mul_left_eq_iff {a b x : G} : a * x = b ↔ x = a⁻¹ * b := by
  constructor
  · intro h
    rw [← h, ← mul_assoc, inv_mul_cancel, one_mul]
  · intro h
    rw [h, ← mul_assoc, mul_inv_cancel, one_mul]

/-- `x * a = b` has the unique solution `x = b * a⁻¹`. -/
theorem mul_right_eq_iff {a b x : G} : x * a = b ↔ x = b * a⁻¹ := by
  constructor
  · intro h
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]
  · intro h
    rw [h, mul_assoc, inv_mul_cancel, mul_one]

/-! ## Conjugation -/

/-- Conjugation by `g`. -/
def conj (g x : G) : G := g * x * g⁻¹

theorem conj_mul (g x y : G) : conj g (x * y) = conj g x * conj g y := by
  unfold conj
  calc g * (x * y) * g⁻¹
      = g * x * (1 * y) * g⁻¹ := by rw [one_mul, mul_assoc g x y]
    _ = g * x * ((g⁻¹ * g) * y) * g⁻¹ := by rw [inv_mul_cancel]
    _ = g * x * g⁻¹ * (g * y * g⁻¹) := by
          simp only [mul_assoc]

theorem conj_one (g : G) : conj g 1 = 1 := by
  unfold conj; rw [mul_one, mul_inv_cancel]

theorem conj_inv (g x : G) : conj g x⁻¹ = (conj g x)⁻¹ := by
  unfold conj
  rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]

end Group

end AlgebraFromScratch
