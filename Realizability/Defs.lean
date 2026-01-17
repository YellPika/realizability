module

import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation

public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Data.PFun
public import Mathlib.Computability.Partrec

/-!
This module contains basic definitions about (semi)computable functions.
-/

public section

namespace Realizability

variable {A B : Type*} [Encodable A] [Encodable B]

/--
A natural number `n` _realizes_ an element `x` of an `Encodable` type `A` if
`Encodable.decode n = some x`.
-/
infix:80 " ⊢ " => fun n x ↦ Encodable.decode n = some x

/--
A partial function `f : A →. B` is _semicomputable_ if there exists a partial
recursive function `φ : ℕ →. ℕ` such that the following conditions hold for all
`k : ℕ` and `x : ℕ`:
1. If `k ⊢ x` and `f x` terminates, then `φ x` terminates and `φ k ⊢ f x`.
2. If `k ⊢ x` and `f x` does not terminate, then neither does `φ k`.
-/
inductive Semicomputable (f : A →. B) : Prop
| intro (φ : ℕ →. ℕ) :
    -- φ is semicomputable
    Nat.Partrec φ →

    -- If `k ⊢ x` and `f x` terminates, then `φ x` terminates and `φ k ⊢ f x`.
    (∀ (k : ℕ) (x : A) (y : B),
      k ⊢ x →             -- "`k` represents `x`"
      f x = .some y →     -- "`y` is the result of `f x`"
      ∃k',
        φ k = .some k' ∧  -- "some `k'` is the result of `φ k`"
        k' ⊢ y) →         -- "`k'` represents `y`"

    -- If `k ⊢ x` and `f x` does not terminate, then neither does `φ k`.
    (∀ (k : ℕ) (x : A),
      k ⊢ x →             -- "`k` represents `x`"
      f x = Part.none →   -- "`f x` does not terminate"
      φ k = Part.none) →  -- "`φ k` does not terminate"

    Semicomputable f

/--
A function `f : A → B` is _computable_ if, as a partial function, `f` is
semicomputable.
-/
@[expose, fun_prop]
def Computable (f : A → B) : Prop :=
  Semicomputable (f : A →. B)

/-- `ComputableHom A B` is the type of computable functions from `A` to `B`. -/
structure ComputableHom (A B : Type*) [Encodable A] [Encodable B] where
  toFun : A → B
  computable' : Computable toFun := by fun_prop

namespace ComputableHom

instance : FunLike (ComputableHom A B) A B where
  coe := toFun
  coe_injective' f g := by
    cases f
    cases g
    simp only [mk.injEq, imp_self]

/-- A simps projection for function coercion. -/
def Simps.coe (f : ComputableHom A B) : A → B := f

initialize_simps_projections ComputableHom (toFun → coe)

/--
Copy of a `ComputableHom` with a new `toFun` equal to the old one.
Useful to fix definitional equalities.
-/
@[expose, simps!]
protected def copy (f : ComputableHom A B) (f' : A → B) (h : f' = ⇑f) : ComputableHom A B where
  toFun := f'
  computable' := h.symm ▸ f.computable'

instance : Encodable (ComputableHom A B) where
  encode := sorry
  decode := sorry
  encodek := sorry

end ComputableHom

end Realizability
