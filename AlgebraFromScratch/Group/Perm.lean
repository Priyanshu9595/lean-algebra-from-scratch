/-
# Permutation groups

Bijections `α → α` (recorded with an explicit inverse) form a group under
composition. We use this to exhibit a concrete **non-abelian** group:
permutations of a three-element set.
-/
import AlgebraFromScratch.Group.Abelian

namespace AlgebraFromScratch

universe u

/-- A permutation of `α`, stored with its inverse. -/
structure Perm (α : Type u) where
  toFun : α → α
  invFun : α → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ x, toFun (invFun x) = x

namespace Perm

variable {α : Type u}

/-- Two permutations are equal as soon as their forward maps agree:
the inverse is determined by the forward map. -/
theorem ext {σ τ : Perm α} (h : ∀ x, σ.toFun x = τ.toFun x) : σ = τ := by
  obtain ⟨f, g, lf, rf⟩ := σ
  obtain ⟨f', g', lf', rf'⟩ := τ
  have hf : f = f' := funext h
  subst hf
  have hg : g = g' := funext fun x => by
    calc g x = g (f (g' x)) := by rw [rf']
      _ = g' x := lf _
  subst hg
  rfl

/-- Group structure: `σ * τ` means "first `τ`, then `σ`". -/
instance : Group (Perm α) where
  mul σ τ :=
    { toFun := fun x => σ.toFun (τ.toFun x)
      invFun := fun x => τ.invFun (σ.invFun x)
      left_inv := fun x => by simp only [σ.left_inv, τ.left_inv]
      right_inv := fun x => by simp only [σ.right_inv, τ.right_inv] }
  one := { toFun := fun x => x, invFun := fun x => x,
           left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  inv σ := { toFun := σ.invFun, invFun := σ.toFun,
             left_inv := σ.right_inv, right_inv := σ.left_inv }
  mul_assoc _ _ _ := ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
  inv_mul_cancel σ := ext fun x => σ.left_inv x

/-- Build a permutation from a self-inverse function (an involution). -/
def ofInvolution (f : α → α) (hf : ∀ x, f (f x) = x) : Perm α :=
  ⟨f, f, hf, hf⟩

end Perm

/-! ## A non-abelian group: permutations of `Fin 3` -/

namespace S3

/-- Swap `0 ↔ 1`. -/
def swap01 : Perm (Fin 3) :=
  Perm.ofInvolution (fun x => if x = 0 then 1 else if x = 1 then 0 else x)
    (by decide)

/-- Swap `1 ↔ 2`. -/
def swap12 : Perm (Fin 3) :=
  Perm.ofInvolution (fun x => if x = 1 then 2 else if x = 2 then 1 else x)
    (by decide)

/-- `swap01 * swap12 ≠ swap12 * swap01`: evaluate both at `0`. -/
theorem swaps_dont_commute : swap01 * swap12 ≠ swap12 * swap01 := by
  intro h
  have h0 := congrArg (fun σ : Perm (Fin 3) => σ.toFun 0) h
  revert h0
  decide

/-- **`Perm (Fin 3)` is not abelian**, so `CommGroup` really is extra structure. -/
theorem not_comm : ¬ ∀ σ τ : Perm (Fin 3), σ * τ = τ * σ :=
  fun h => swaps_dont_commute (h _ _)

/-- Consequently some element of `Perm (Fin 3)` does not square to `1`
(contrapositive of `Group.comm_of_mul_self_eq_one`). -/
theorem exists_mul_self_ne_one : ¬ ∀ σ : Perm (Fin 3), σ * σ = 1 :=
  fun h => not_comm (Group.comm_of_mul_self_eq_one h)

end S3

end AlgebraFromScratch
