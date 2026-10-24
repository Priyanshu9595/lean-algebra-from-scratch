/-
# Group homomorphisms

A homomorphism only has to preserve multiplication; preserving `1` and `⁻¹`
are consequences.

Contents:
* `map_one`, `map_inv`, `map_pow`,
* identity and composition,
* the kernel is a **normal** subgroup, the image is a subgroup,
* **a homomorphism is injective iff its kernel is trivial.**
-/
import AlgebraFromScratch.Group.Power
import AlgebraFromScratch.Group.Subgroup

namespace AlgebraFromScratch

universe u v w

open Group

structure Hom (G : Type u) (H : Type v) [Group G] [Group H] where
  toFun : G → H
  map_mul : ∀ a b : G, toFun (a * b) = toFun a * toFun b

namespace Hom

variable {G : Type u} {H : Type v} {K : Type w} [Group G] [Group H] [Group K]

instance : CoeFun (Hom G H) (fun _ => G → H) := ⟨Hom.toFun⟩

variable (f : Hom G H)

theorem map_mul' (a b : G) : f (a * b) = f a * f b := f.map_mul a b

/-- Homomorphisms send `1` to `1`. -/
theorem map_one : f 1 = 1 := by
  apply mul_right_cancel (a := f 1)
  rw [← f.map_mul', one_mul, one_mul]

/-- Homomorphisms commute with inverses. -/
theorem map_inv (a : G) : f a⁻¹ = (f a)⁻¹ := by
  apply eq_inv_of_mul_eq_one
  rw [← f.map_mul', mul_inv_cancel, map_one]

theorem map_pow (a : G) (n : Nat) : f (a ^ n) = (f a) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, map_one]
  | succ k ih => rw [pow_succ, f.map_mul', ih, pow_succ]

/-- The identity homomorphism. -/
def id (G : Type u) [Group G] : Hom G G where
  toFun x := x
  map_mul _ _ := rfl

/-- Composition `g ∘ f`. -/
def comp (g : Hom H K) (f : Hom G H) : Hom G K where
  toFun x := g (f x)
  map_mul a b := by
    show g.toFun (f.toFun (a * b)) = g.toFun (f.toFun a) * g.toFun (f.toFun b)
    rw [f.map_mul, g.map_mul]

/-- The kernel `{x | f x = 1}`. -/
def ker : Subgroup G where
  carrier x := f x = 1
  one_mem := f.map_one
  mul_mem {a b} ha hb := by
    show f (a * b) = 1
    rw [f.map_mul', show f a = 1 from ha, show f b = 1 from hb, one_mul]
  inv_mem {a} ha := by
    show f a⁻¹ = 1
    rw [f.map_inv, show f a = 1 from ha, inv_one]

/-- The kernel of a homomorphism is a normal subgroup. -/
theorem ker_isNormal : f.ker.IsNormal := by
  intro g n hn
  show f (g * n * g⁻¹) = 1
  rw [f.map_mul', f.map_mul', show f n = 1 from hn, mul_one, ← f.map_mul',
    mul_inv_cancel, f.map_one]

/-- The image `{y | ∃ x, f x = y}`. -/
def range : Subgroup H where
  carrier y := ∃ x, f x = y
  one_mem := ⟨1, f.map_one⟩
  mul_mem := fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x * y, by rw [f.map_mul', hx, hy]⟩
  inv_mem := fun ⟨x, hx⟩ => ⟨x⁻¹, by rw [f.map_inv, hx]⟩

/-- **A homomorphism is injective iff its kernel is trivial.** -/
theorem injective_iff_ker_trivial :
    (∀ a b : G, f a = f b → a = b) ↔ (∀ x : G, f x = 1 → x = 1) := by
  constructor
  · intro hinj x hx
    exact hinj x 1 (by rw [hx, f.map_one])
  · intro hker a b hab
    apply eq_of_mul_inv_eq_one
    apply hker
    rw [f.map_mul', f.map_inv, hab, mul_inv_cancel]

/-- Composition of injective homomorphisms has trivial kernel. -/
theorem comp_ker_trivial (g : Hom H K) (f : Hom G H)
    (hg : ∀ y, g y = 1 → y = 1) (hf : ∀ x, f x = 1 → x = 1) :
    ∀ x, comp g f x = 1 → x = 1 :=
  fun x hx => hf x (hg (f x) hx)

/-- Conjugation by a fixed element is a homomorphism (an inner automorphism). -/
def conjHom (g : G) : Hom G G where
  toFun := conj g
  map_mul := conj_mul g

end Hom

end AlgebraFromScratch
