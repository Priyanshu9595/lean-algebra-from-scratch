/-
# Subgroups

A subgroup is a predicate on `G` closed under `1`, `*` and `⁻¹`.

Contents:
* the trivial subgroup and the whole group,
* intersection of two subgroups,
* the **one-step subgroup test**: a nonempty subset closed under `a * b⁻¹`
  is a subgroup,
* the **center** `Z(G)` is a subgroup,
* normal subgroups.
-/
import AlgebraFromScratch.Group.Basic

namespace AlgebraFromScratch

universe u

open Group

structure Subgroup (G : Type u) [Group G] where
  carrier : G → Prop
  one_mem : carrier 1
  mul_mem : ∀ {a b : G}, carrier a → carrier b → carrier (a * b)
  inv_mem : ∀ {a : G}, carrier a → carrier a⁻¹

namespace Subgroup

variable {G : Type u} [Group G]

instance : Membership G (Subgroup G) := ⟨fun H x => H.carrier x⟩

theorem mem_def {H : Subgroup G} {x : G} : x ∈ H ↔ H.carrier x := Iff.rfl

/-- The trivial subgroup `{1}`. -/
def bot : Subgroup G where
  carrier x := x = 1
  one_mem := rfl
  mul_mem ha hb := by rw [ha, hb, one_mul]
  inv_mem ha := by rw [ha, inv_one]

/-- The whole group. -/
def top : Subgroup G where
  carrier _ := True
  one_mem := trivial
  mul_mem _ _ := trivial
  inv_mem _ := trivial

/-- The intersection of two subgroups is a subgroup. -/
def inter (H K : Subgroup G) : Subgroup G where
  carrier x := H.carrier x ∧ K.carrier x
  one_mem := ⟨H.one_mem, K.one_mem⟩
  mul_mem ha hb := ⟨H.mul_mem ha.1 hb.1, K.mul_mem ha.2 hb.2⟩
  inv_mem ha := ⟨H.inv_mem ha.1, K.inv_mem ha.2⟩

theorem inv_mem_iff (H : Subgroup G) (x : G) : H.carrier x⁻¹ ↔ H.carrier x :=
  ⟨fun h => by simpa only [inv_inv] using H.inv_mem h, H.inv_mem⟩

/-- **One-step subgroup test.** A subset that contains some element and is
closed under `(a, b) ↦ a * b⁻¹` is a subgroup. -/
def ofDiv (S : G → Prop) (nonempty : ∃ x, S x)
    (div_mem : ∀ {a b : G}, S a → S b → S (a * b⁻¹)) : Subgroup G :=
  have one_mem : S 1 := by
    obtain ⟨x, hx⟩ := nonempty
    have := div_mem hx hx
    rwa [mul_inv_cancel] at this
  have inv_mem : ∀ {a : G}, S a → S a⁻¹ := fun {a} ha => by
    have := div_mem one_mem ha
    rwa [one_mul] at this
  { carrier := S
    one_mem := one_mem
    inv_mem := inv_mem
    mul_mem := fun {a b} ha hb => by
      have := div_mem ha (inv_mem hb)
      rwa [inv_inv] at this }

/-- The **center** of `G`: elements commuting with everything. -/
def center (G : Type u) [Group G] : Subgroup G where
  carrier g := ∀ x : G, g * x = x * g
  one_mem x := by rw [one_mul, mul_one]
  mul_mem {a b} ha hb x := by
    calc a * b * x = a * (b * x) := mul_assoc _ _ _
      _ = a * (x * b) := by rw [hb]
      _ = (a * x) * b := (mul_assoc _ _ _).symm
      _ = (x * a) * b := by rw [ha]
      _ = x * (a * b) := mul_assoc _ _ _
  inv_mem {g} hg x := by
    -- g⁻¹ x = g⁻¹ x (g g⁻¹) = g⁻¹ (x g) g⁻¹ = g⁻¹ (g x) g⁻¹ = x g⁻¹
    calc g⁻¹ * x = g⁻¹ * x * (g * g⁻¹) := by rw [mul_inv_cancel, mul_one]
      _ = g⁻¹ * (x * g) * g⁻¹ := by simp only [mul_assoc]
      _ = g⁻¹ * (g * x) * g⁻¹ := by rw [hg]
      _ = (g⁻¹ * g) * x * g⁻¹ := by simp only [mul_assoc]
      _ = x * g⁻¹ := by rw [inv_mul_cancel, one_mul]

/-- A subgroup is normal if it is closed under conjugation. -/
def IsNormal (N : Subgroup G) : Prop :=
  ∀ (g : G) {n : G}, N.carrier n → N.carrier (g * n * g⁻¹)

theorem center_isNormal : (center G).IsNormal := by
  intro g n hn x
  -- n is central, so g n g⁻¹ = n
  have : g * n * g⁻¹ = n := by
    rw [← hn g, mul_assoc, mul_inv_cancel, mul_one]
  rw [this]
  exact hn x

theorem bot_isNormal : (bot : Subgroup G).IsNormal := by
  intro g n hn
  show g * n * g⁻¹ = 1
  rw [show n = 1 from hn, mul_one, mul_inv_cancel]

theorem top_isNormal : (top : Subgroup G).IsNormal := fun _ _ _ => trivial

theorem inter_isNormal {N M : Subgroup G} (hN : N.IsNormal) (hM : M.IsNormal) :
    (inter N M).IsNormal :=
  fun g _ h => ⟨hN g h.1, hM g h.2⟩

end Subgroup

end AlgebraFromScratch
