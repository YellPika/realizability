import Mathlib.Tactic.TypeStar
import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Encodable.Basic
import Mathlib.Computability.Partrec

namespace Realizability

variable {A B C : Type*} [Encodable A] [Encodable B] [Encodable C]

notation:80 n:80 " ⊢ " x:80 => Encodable.decode n = some x

inductive Semicomputable (f : A →. B) : Prop
| intro (φ : ℕ →. ℕ) :
    -- φ is semicomputable
    Nat.Partrec φ →

    -- If `k ⊢ x` and `f x` terminates, then `φ x` terminates and `φ k ⊢ f x`.
    (∀ (k : ℕ) (x : A) (y : B),
      k ⊢ x →     -- "`x` is represented by `k`"
      y ∈ f x →   -- "`y` is the result of `f x`"
      ∃k' ∈ φ k,  -- "some `k'` is the result of `φ k`"
        k' ⊢ y) → -- "`k'` represents `y`"

    -- If `k ⊢ x` and `f x` does not terminate, then neither does `φ k`.
    (∀ (k : ℕ) (x : A),
      k ⊢ x →           -- "`x` is rpresented by `k`"
      f x = Part.none → -- "`f x` does not terminate"
      φ k = Part.none) →  -- "`φ k` does not terminate"

    Semicomputable f

@[fun_prop]
def Computable (f : A → B) : Prop :=
  Semicomputable (f : A →. B)

@[fun_prop]
lemma computable_id : Computable (id : A → A) := by
  use Part.some
  · apply Nat.Partrec.some
  · simp only [
      PFun.coe_val, id_eq, Part.mem_some_iff, exists_eq_left,
      forall_eq_apply_imp_iff, imp_self, implies_true]
  · simp only [PFun.coe_val, id_eq, Part.some_ne_none, imp_self, implies_true]

@[fun_prop]
lemma computable_comp
    {f : B → C} (hf : Computable f)
    {g : A → B} (hg : Computable g)
    : Computable (f ∘ g) := by
  sorry

@[fun_prop]
lemma Prod.computable_mk
    {f : A → B} (hf : Computable f)
    {g : A → C} (hg : Computable g)
    : Computable (fun x ↦ (f x, g x)) := by
  sorry

@[fun_prop]
lemma Prod.computable_fst : Computable (Prod.fst : A × B → A) := by
  sorry

@[fun_prop]
lemma Prod.computable_snd : Computable (Prod.snd : A × B → B) := by
  sorry

example : Computable (fun x : A ↦ (x, x, x, x, x)) := by
  fun_prop

lemma semicomputable_of_computable
    {f : A → B} (hf : Computable f)
    : Semicomputable (f : A →. B) :=
  hf

lemma semicomputable_id : Semicomputable (PFun.id A) := by
  apply semicomputable_of_computable
  fun_prop

lemma semicomputable_comp
    {f : B →. C} (hf : Semicomputable f)
    {g : A →. B} (hg : Semicomputable g)
    : Semicomputable (f.comp g) := by
  sorry

lemma Prod.semicomputable_mk
    {f : A →. B} (hf : Semicomputable f)
    {g : A →. C} (hg : Semicomputable g)
    : Semicomputable (PFun.prodLift f g) := by
  sorry

lemma Prod.semicomputable_fst : Semicomputable (↑(Prod.fst : A × B → A) : A × B →. A) := by
  apply semicomputable_of_computable
  fun_prop

lemma Prod.semicomputable_snd : Semicomputable (↑(Prod.snd : A × B → B) : A × B →. B) := by
  apply semicomputable_of_computable
  fun_prop

end Realizability
