module

import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation

public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Data.PFun
public import Mathlib.Computability.Partrec
public import Mathlib.Computability.PartrecCode

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

lemma computable_iff_exists
    (f : A → B)
    : Computable f
    ↔ ∃φ : ℕ →. ℕ, Nat.Partrec φ ∧ ∀k x, k ⊢ x → ∃k', φ k = .some k' ∧ k' ⊢ f x := by
  apply Iff.intro
  · rintro ⟨φ, h₁, h₂, h₃⟩
    simp only [PFun.coe_val, Part.some_inj, forall_apply_eq_imp_iff] at h₂
    use φ
  · rintro ⟨φ, h₁, h₂⟩
    use φ
    · intro k x y hkx hfx
      simp only [PFun.coe_val, Part.some_inj] at hfx
      grind
    · simp only [PFun.coe_val, Part.some_ne_none, IsEmpty.forall_iff, implies_true]

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

noncomputable def encode (f : ComputableHom A B) : ℕ :=
  let φ := ((computable_iff_exists f).1 f.computable').choose
  have hφ : Nat.Partrec φ := ((computable_iff_exists f).1 f.computable').choose_spec.1
  have hφ' : ∃c : Nat.Partrec.Code, c.eval = φ := Nat.Partrec.Code.exists_code.1 hφ
  Encodable.encode hφ'.choose

noncomputable def decode (n : ℕ) : Option (ComputableHom A B) :=
  (Encodable.decode n : Option Nat.Partrec.Code).bind fun c ↦
    open Classical in
    if hc : ∃f : A → B, ∀k x, k ⊢ x → ∃k', c.eval k = .some k' ∧ k' ⊢ f x
    then .some {
      toFun := hc.choose
      computable' := by
        use c.eval
        · have := Nat.Partrec.Code.exists_code (f := c.eval)
          simp only [exists_apply_eq_apply, iff_true] at this
          exact this
        · simp only [PFun.coe_val, Part.some_inj, forall_apply_eq_imp_iff] at ⊢ hc
          grind
        · simp only [PFun.coe_val, Part.some_ne_none, IsEmpty.forall_iff, implies_true]
    }
    else .none

noncomputable instance : Encodable (ComputableHom A B) where
  encode := encode
  decode := decode
  encodek f := by
    simp only [
      decode, encode, Denumerable.decode_eq_ofNat, Denumerable.ofNat_encode,
      Option.bind_some, Option.dite_none_right_eq_some, Option.some.injEq]
    have lem₁ := (computable_iff_exists f).1 f.computable'
    have lem₂ := Nat.Partrec.Code.exists_code.1 lem₁.choose_spec.1
    have lem₃ : ∃ g : A → B, ∀ (k : ℕ) (x : A),
        Encodable.decode k = some x →
        ∃ k',
          lem₂.choose.eval k = Part.some k' ∧
          Encodable.decode k' = some (g x) := by
      rcases f with ⟨f, φ, h₁, h₂, h₃⟩
      use f
      intro k x hkx
      simp only [lem₂.choose_spec]
      apply lem₁.choose_spec.2 k x hkx
    have lem₄ : Computable lem₃.choose := by
      have := lem₃.choose_spec
      simp only [lem₂.choose_spec] at this
      use lem₁.choose
      · exact lem₁.choose_spec.1
      · simp only [PFun.coe_val, Part.some_inj, forall_apply_eq_imp_iff]
        intro k x hkx
        obtain h := lem₃.choose_spec k x hkx
        simp only [lem₂.choose_spec] at h
        exact h
      · simp only [PFun.coe_val, Part.some_ne_none, IsEmpty.forall_iff, implies_true]
    use lem₃
    change ⟨lem₃.choose, lem₄⟩ = f
    rcases f with ⟨f, hf⟩
    simp only [mk.injEq]
    ext x
    obtain ⟨k, hk₁, hk₂⟩ := lem₃.choose_spec (Encodable.encode x) x (by simp only [Encodable.encodek])
    simp only [lem₂.choose_spec] at hk₁
    obtain ⟨h₁, h₂⟩ := lem₁.choose_spec
    obtain ⟨i, hi₁, hi₂⟩ := h₂ (Encodable.encode x) x (by simp only [Encodable.encodek])
    dsimp only [DFunLike.coe] at hi₂
    simp only [hi₁, Part.some_inj] at hk₁
    subst hk₁
    simp only [hk₂, Option.some.injEq] at hi₂
    exact hi₂

end ComputableHom

end Realizability
