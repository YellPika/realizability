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

notation:80 n:80 " ⊢ " x:80 => Encodable.decode n = some x

inductive Semicomputable (f : A →. B) : Prop
| intro (φ : ℕ →. ℕ) :
    -- φ is semicomputable
    Nat.Partrec φ →

    -- If `k ⊢ x` and `f x` terminates, then `φ x` terminates and `φ k ⊢ f x`.
    (∀ (k : ℕ) (x : A) (y : B),
      k ⊢ x →     -- "`k` represents `x`"
      y ∈ f x →   -- "`y` is the result of `f x`"
      ∃k' ∈ φ k,  -- "some `k'` is the result of `φ k`"
        k' ⊢ y) → -- "`k'` represents `y`"

    -- If `k ⊢ x` and `f x` does not terminate, then neither does `φ k`.
    (∀ (k : ℕ) (x : A),
      k ⊢ x →             -- "`k` represents `x`"
      f x = Part.none →   -- "`f x` does not terminate"
      φ k = Part.none) →  -- "`φ k` does not terminate"

    Semicomputable f

@[expose, fun_prop]
def Computable (f : A → B) : Prop :=
  Semicomputable (f : A →. B)

end Realizability
