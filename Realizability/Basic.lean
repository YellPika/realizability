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

lemma semicomputable_const (x : B) : Semicomputable fun _ : A ↦ .some x := by
  use fun _ ↦ Encodable.encode x
  · simp only [Part.coe_some]
    sorry
  · simp only [
      Part.mem_some_iff, Part.coe_some, exists_eq_left, Encodable.encodek,
      Option.some.injEq, forall_eq_apply_imp_iff, implies_true]
  · simp only [Part.some_ne_none, Part.coe_some, imp_self, implies_true]

@[fun_prop]
lemma computable_const (x : B) : Computable fun _ : A ↦ x := by
  apply semicomputable_const

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

namespace ComputableHom

@[ext]
lemma ext {f g : ComputableHom A B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

@[simp]
lemma coe_mk {f : A → B} (hf : Computable f) : ⇑(mk f hf) = f := rfl

@[simp]
lemma eta (f : ComputableHom A B) : mk f f.computable' = f := rfl

@[simp]
lemma toFun_eq_coe (f : ComputableHom A B) : toFun f = ⇑f := rfl

@[simp, fun_prop]
lemma computable_coe (f : ComputableHom A B) : Computable ⇑f := f.computable'

@[local fun_prop, simp]
lemma computable_eval : Computable (fun p : ComputableHom A B × A ↦ p.1 p.2) := by
  sorry

@[fun_prop]
lemma computable_eval'
    {f : A → ComputableHom B C} (hf : Computable f)
    {g : A → B} (hg : Computable g)
    : Computable (fun x ↦ f x (g x)) := by
  apply computable_comp (f := fun x ↦ x.1 x.2) (g := fun x ↦ (f x, g x))
  · simp only [computable_eval]
  · fun_prop

@[fun_prop]
lemma computable_mk
    {f : A → B → C} (hf : Computable (fun x : A × B ↦ f x.1 x.2))
    : Computable (fun x ↦ mk (f x) (by fun_prop)) := by
  sorry

@[simp]
lemma computable_iff (f : A → ComputableHom B C) : Computable f ↔ Computable (fun x : A × B ↦ f x.1 x.2) := by
  apply Iff.intro
  · intro hf
    fun_prop
  · intro hf
    apply computable_mk hf

/-- Currying for `ComputableHom`s. -/
@[expose, simps coe]
def curry (f : ComputableHom (A × B) C) : ComputableHom A (ComputableHom B C) where
  toFun x := { toFun y := f (x, y) }

/-- Uncurrying for `ComputableHom`s. -/
@[expose, simps coe]
def uncurry (f : ComputableHom A (ComputableHom B C)) : ComputableHom (A × B) C where
  toFun x := f x.1 x.2

@[simp]
lemma curry_uncurry (f : ComputableHom A (ComputableHom B C)) : curry (uncurry f) = f := rfl

@[simp]
lemma uncurry_curry (f : ComputableHom (A × B) C) : uncurry (curry f) = f := rfl

end ComputableHom

end Realizability
