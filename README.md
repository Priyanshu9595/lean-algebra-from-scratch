# Algebra from Scratch in Lean 4

Formalization of introductory abstract algebra (groups and rings) in **Lean 4**, built **from the axioms up without Mathlib**. Every structure is defined here and every result is proved from those definitions using only core Lean.

![Lean](https://img.shields.io/badge/Lean-4.24.0-blue) ![sorry-free](https://img.shields.io/badge/sorry-0-brightgreen) ![deps](https://img.shields.io/badge/dependencies-none-lightgrey)

## Why no Mathlib?

Mathlib already contains all of this. The point here is to work through the foundations yourself:

- Groups are axiomatized with **only a left identity and left inverses**. That `a * 1 = a` and `a * a⁻¹ = 1` also hold is proved, not assumed.
- Rings do **not** assume `a * 0 = 0` or any sign rules. These are derived from distributivity.

## Contents

| File | What's proved |
|---|---|
| `Group/Basic.lean` | Right identity and right inverse from the left-only axioms, cancellation laws, uniqueness of identity and inverses, `(a⁻¹)⁻¹ = a`, `(ab)⁻¹ = b⁻¹a⁻¹`, unique solutions of `ax = b` and `xa = b`, conjugation |
| `Group/Power.lean` | `aⁿ` by recursion, `a^(m+n) = aᵐaⁿ`, `a^(mn) = (aᵐ)ⁿ`, `(a⁻¹)ⁿ = (aⁿ)⁻¹`, `(ab)ⁿ = aⁿbⁿ` for commuting `a, b` |
| `Group/Abelian.lean` | If every `x² = 1` then G is abelian; `(ab)² = a²b² ↔ ab = ba` |
| `Group/Subgroup.lean` | Subgroups, intersections, the **one-step subgroup test**, the **center** `Z(G)` is a normal subgroup |
| `Group/Hom.lean` | Homomorphisms preserve `1`, `⁻¹` and powers; composition; kernel is a **normal** subgroup; image is a subgroup; **injective ⇔ trivial kernel** |
| `Group/Perm.lean` | Permutations of a type form a group; `Perm (Fin 3)` is **non-abelian** |
| `Ring/Basic.lean` | `a·0 = 0`, `(-a)b = -(ab)`, **`(-a)(-b) = ab`**, `(-1)a = -a`, `1 = 0 ⇒` trivial ring, `(a+b)²` expansion, difference of squares |
| `Ring/Boolean.lean` | Every **Boolean ring** (`x² = x`) has characteristic 2 and is **commutative** |
| `Examples.lean` | `ℤ` is a commutative ring, `ℤ/2` as a group, the two-element Boolean ring, with the general theorems applied to each |

About 80 theorems in total, with zero `sorry`s. `#print axioms` on the main results shows either no axioms at all or only Lean's standard `propext` and `Quot.sound`.

## Highlights

**Left axioms imply right axioms.** The proof expresses `1` as `(a⁻¹)⁻¹ * a⁻¹` and re-associates:

```lean
theorem mul_inv_cancel : a * a⁻¹ = 1 := by
  calc a * a⁻¹
      = 1 * (a * a⁻¹) := (one_mul _).symm
    _ = ((a⁻¹)⁻¹ * a⁻¹) * (a * a⁻¹) := by rw [inv_mul_cancel]
    _ = (a⁻¹)⁻¹ * ((a⁻¹ * a) * a⁻¹) := by rw [mul_assoc, ← mul_assoc a⁻¹ a]
    _ = (a⁻¹)⁻¹ * a⁻¹ := by rw [inv_mul_cancel, one_mul]
    _ = 1 := inv_mul_cancel _
```

**Boolean rings are commutative.** Expand `(a+b)² = a+b`, cancel to get `ab + ba = 0`, then use `x = -x`.

**Injective ⇔ trivial kernel.**

```lean
theorem injective_iff_ker_trivial :
    (∀ a b : G, f a = f b → a = b) ↔ (∀ x : G, f x = 1 → x = 1)
```

## Build

You need [elan](https://github.com/leanprover/elan) installed.

```bash
git clone <this-repo>
cd lean-algebra-from-scratch
lake build
```

There are no dependencies, so the build takes a few seconds. CI runs `lake build` on every push.

## Roadmap

- [ ] Lagrange's theorem (cosets, index)
- [ ] Quotient groups and the First Isomorphism Theorem
- [ ] Cyclic groups and orders of elements
- [ ] Ideals and quotient rings
- [ ] Port statements to Mathlib's API and compare proofs
