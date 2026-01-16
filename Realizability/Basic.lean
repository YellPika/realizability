module

public import Realizability.Defs
public import Mathlib.Logic.Encodable.Basic

/-!
This module contains basic theorems about (semi)computable functions.
-/

public section

namespace Realizability

variable {A B C : Type*} [Encodable A] [Encodable B] [Encodable C]

lemma semicomputable_of_computable
    {f : A → B} (hf : Computable f)
    : Semicomputable (f : A →. B) :=
  hf

lemma semicomputable_id : Semicomputable (PFun.id A) := by
  use Part.some
  · apply Nat.Partrec.some
  · simp only [
      PFun.id_apply, Part.mem_some_iff, exists_eq_left,
      forall_eq_apply_imp_iff, imp_self, implies_true]
  · simp only [PFun.id_apply, Part.some_ne_none, imp_self, implies_true]

@[fun_prop]
lemma computable_id : Computable (id : A → A) := by
  exact semicomputable_id

lemma semicomputable_comp
    {f : B →. C} (hf : Semicomputable f)
    {g : A →. B} (hg : Semicomputable g)
    : Semicomputable (f.comp g) := by
  sorry

@[fun_prop]
lemma computable_comp
    {f : B → C} (hf : Computable f)
    {g : A → B} (hg : Computable g)
    : Computable (f ∘ g) := by
  sorry

namespace Prod

lemma semicomputable_mk
    {f : A →. B} (hf : Semicomputable f)
    {g : A →. C} (hg : Semicomputable g)
    : Semicomputable (PFun.prodLift f g) := by
  sorry

@[fun_prop]
lemma computable_mk
    {f : A → B} (hf : Computable f)
    {g : A → C} (hg : Computable g)
    : Computable (fun x ↦ (f x, g x)) := by
  sorry

lemma semicomputable_fst : Semicomputable (↑(Prod.fst : A × B → A) : A × B →. A) := by
  sorry

@[fun_prop]
lemma computable_fst : Computable (Prod.fst : A × B → A) := by
  exact semicomputable_fst

lemma semicomputable_snd : Semicomputable (↑(Prod.snd : A × B → B) : A × B →. B) := by
  sorry

@[fun_prop]
lemma computable_snd : Computable (Prod.snd : A × B → B) := by
  exact semicomputable_snd

end Prod

end Realizability
