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
      PFun.id_apply, Part.some_inj, exists_eq_left',
      forall_apply_eq_imp_iff, imp_self, implies_true]
  · simp only [PFun.id_apply, Part.some_ne_none, imp_self, implies_true]

@[fun_prop]
lemma computable_id : Computable (id : A → A) := by
  exact semicomputable_id

lemma const_is_rec (n : ℕ) : Nat.Partrec fun _ => n := by
  induction n with
  | zero => apply Nat.Partrec.zero
  | succ n ind =>
    have : (fun _ : ℕ ↦ .some (n + 1)) = PFun.comp (Nat.succ : ℕ →. ℕ) (fun x ↦ .some n) := by
      ext n1 n2
      simp only [Part.mem_some_iff, PFun.comp_apply, Part.bind_some, PFun.coe_val,
        Nat.succ_eq_add_one]
    simp only [Part.coe_some, this]
    apply Nat.Partrec.comp
    · apply Nat.Partrec.succ
    · apply ind

lemma semicomputable_const (x : B) : Semicomputable fun _ : A ↦ .some x := by
  use fun _ ↦ Encodable.encode x
  · simp only [Part.coe_some]
    apply const_is_rec
  · simp only [
      Part.some_inj, Part.coe_some, exists_eq_left', Encodable.encodek,
      Option.some.injEq, imp_self, implies_true]
  · simp only [Part.some_ne_none, Part.coe_some, imp_self, implies_true]

@[fun_prop]
lemma computable_const (x : B) : Computable fun _ : A ↦ x := by
  apply semicomputable_const

lemma semicomputable_comp
    {f : B →. C} (hf : Semicomputable f)
    {g : A →. B} (hg : Semicomputable g)
    : Semicomputable (f.comp g) := by
  rcases hf with ⟨φf , h1f, h2f, h3f⟩
  rcases hg with ⟨φg , h1g, h2g, h3g⟩
  use φf.comp φg
  · use Nat.Partrec.comp h1f h1g
  · simp only [PFun.comp_apply]
    intro n a c hc hfga
    cases hga : g a using Part.induction_on with
    | hnone => simp only [hga, Part.bind_none, Part.none_ne_some] at hfga
    | hsome b =>
      simp only [hga, Part.bind_some] at hfga
      obtain ⟨m, hm₁, hm₂⟩ := h2g n a b hc hga
      obtain ⟨k', hk'₁, hk'₂⟩ := h2f m b c hm₂ hfga
      use k'
      simp only [hm₁, Part.bind_some, hk'₁, hk'₂, and_self]
  · intro n a h31 h32
    simp only [PFun.comp_apply]
    cases hga : g a using Part.induction_on with
    | hnone =>
      specialize h3g n a h31 hga
      simp only [h3g, Part.bind_none]
    | hsome b =>
      obtain ⟨m, hm₁, hm₂⟩ := h2g n a b h31 hga
      simp only [hm₁, Part.bind_some]
      apply h3f m b hm₂
      simp only [PFun.comp_apply, hga, Part.bind_some] at h32
      exact h32

@[fun_prop]
lemma computable_comp
    {f : B → C} (hf : Computable f)
    {g : A → B} (hg : Computable g)
    : Computable (f ∘ g) := by
  have hc := semicomputable_comp
      (semicomputable_of_computable hf)
      (semicomputable_of_computable hg)
  simp only [Computable]
  have : (f : B →. C).comp g = (↑(f∘g) : A →.C) := by
    ext
    simp only [PFun.comp_apply, PFun.coe_val, Part.bind_some, Part.mem_some_iff,
      Function.comp_apply]
  grind

namespace Prod

@[simp]
private lemma apply_eq_bind
    {A B : Type u}
    (f : Part (A → B)) (x : Part A)
    : f <*> x = Part.bind f fun f' ↦ Part.map f' x := by
  rfl

@[simp]
private lemma bind_none
    (x : Part A)
    : Part.bind x (fun _ ↦ Part.none) = (Part.none : Part B) := by
  cases x using Part.induction_on <;> simp

lemma semicomputable_mk
    {f : A →. B} (hf : Semicomputable f)
    {g : A →. C} (hg : Semicomputable g)
    : Semicomputable (PFun.prodLift f g) := by
  rcases hf with ⟨φf , h1f, h2f, h3f⟩
  rcases hg with ⟨φg , h1g, h2g, h3g⟩
  let ff := fun n => Nat.pair <$> φf n <*> φg n
  use ff
  · apply Nat.Partrec.pair h1f h1g
  · intro k a ⟨p1,p2⟩  h1 h2
    simp only [PFun.prodLift_apply] at h2
    cases h : f a using Part.induction_on with
    | hnone =>
      replace h2 := congr_arg Part.Dom h2
      simp [h] at h2
    | hsome a' =>
      simp only [Encodable.decode_prod_val]
      cases h' : g a using Part.induction_on with
      | hnone =>
        replace h2 := congr_arg Part.Dom h2
        simp only [h', Part.not_none_dom, and_false, Part.some_dom, eq_iff_iff, iff_true] at h2
      | hsome a'' =>
        rw [h] at h2
        rw [h'] at h2
        simp only [Part.get_some] at h2
        let h22 := h2f k a a' h1 h
        rcases h22 with ⟨n, ha, hb⟩
        let h23 := h2g k a a'' h1 h'
        rcases h23 with ⟨m, hc, hd⟩
        use Nat.pair n m
        simp only [Nat.unpair_pair]
        apply And.intro
        · simp only [Part.map_eq_map, apply_eq_bind, Part.bind_map, ha, hc, Part.map_some,
          Part.bind_some, ff]
        · simp only [hb, hd, Option.map_some, Option.bind_some, Option.some.injEq, Prod.mk.injEq]
          simp only [Part.ext_iff, Part.mem_mk_iff, Part.some_dom, and_self, exists_const,
            Part.mem_some_iff, Prod.forall, Prod.mk.injEq] at h2
          let hhh := h2 a' a''
          simp only [← hhh, and_self]
  · intro k a h h2
    have h3f1 := h3f k a h
    have h3g1 := h3g k a h
    cases j:f a using Part.induction_on with
    | hnone =>
      have t1 := h3f1 j
      simp only [Part.map_eq_map, apply_eq_bind, Part.bind_map, t1, Part.bind_none, ff]
    | hsome a' =>
      simp only [Part.map_eq_map, apply_eq_bind, Part.bind_map, ff]
      cases j':g a using Part.induction_on with
      | hnone =>
        have t1' := h3g1 j'
        simp only [t1', Part.map_none, bind_none]
      | hsome a'' =>
        simp only [PFun.prodLift_apply] at h2
        replace h2 := congr_arg Part.Dom h2
        simp only [j', Part.some_dom, and_true, Part.not_none_dom, eq_iff_iff, iff_false] at h2
        simp only [j, Part.some_dom, not_true_eq_false] at h2

@[fun_prop]
lemma computable_mk
    {f : A → B} (hf : Computable f)
    {g : A → C} (hg : Computable g)
    : Computable (fun x ↦ (f x, g x)) := by
  have hc := semicomputable_mk hf hg
  simp only [Computable]
  have : ((↑f : A →. B).prodLift ↑g) =  PFun.lift (fun (x : A) => (f x, g x)) := by
    ext
    simp only [PFun.prodLift_apply, PFun.coe_val, Part.get_some, Part.mem_mk_iff, Part.some_dom,
      and_self, exists_const, Part.mem_some_iff]
    grind
  grind

lemma semicomputable_fst : Semicomputable (↑(Prod.fst : A × B → A) : A × B →. A) := by
  let ff := PFun.lift fun n => (Nat.unpair n).fst
  use ff
  · apply Nat.Partrec.left
  · intro n ab a h h2
    simp only [PFun.lift, Part.some_inj] at h2
    simp only [PFun.coe_val, Part.some_inj, exists_eq_left', ff]
    subst h2
    simp only [Encodable.decode_prod_val] at h
    cases h3:(Encodable.decode (Nat.unpair n).1 : Option A) with
    | none => simp only [h3, Option.bind_none, reduceCtorEq] at h
    | some val =>
      simp only [h3, Option.bind_some, Option.map_eq_some_iff] at h
      simp only [Option.some.injEq]
      grind
  · intro n ab h h2
    simp only [PFun.coe_val, Part.some_ne_none] at h2

@[fun_prop]
lemma computable_fst : Computable (Prod.fst : A × B → A) := by
  exact semicomputable_fst

lemma semicomputable_snd : Semicomputable (↑(Prod.snd : A × B → B) : A × B →. B) := by
  let ff := PFun.lift fun n => (Nat.unpair n).snd
  use ff
  · apply Nat.Partrec.right
  · intro n ab a h h2
    simp only [PFun.lift, Part.some_inj] at h2
    simp only [PFun.coe_val, Part.some_inj, exists_eq_left', ff]
    subst h2
    simp only [Encodable.decode_prod_val] at h
    cases h3:(Encodable.decode (Nat.unpair n).1 : Option A) with
    | none => simp only [h3, Option.bind_none, reduceCtorEq] at h
    | some val =>
      simp only [h3, Option.bind_some, Option.map_eq_some_iff] at h
      grind
  · intro n ab h h2
    simp only [PFun.coe_val, Part.some_ne_none] at h2

@[fun_prop]
lemma computable_snd : Computable (Prod.snd : A × B → B) := by
  exact semicomputable_snd

end Prod

namespace Sum

@[simp]
lemma semicomputable_inl : Semicomputable (↑(Sum.inl : A → A ⊕ B) : A →. A ⊕ B) := by
  use ↑(fun x ↦ 2 * x : ℕ → ℕ)
  · sorry -- This is hard!
  · sorry
  · sorry

@[fun_prop, simp]
lemma computable_inl : Computable (Sum.inl : A → A ⊕ B) := by
  apply semicomputable_inl

@[simp]
lemma semicomputable_inr : Semicomputable (↑(Sum.inr : B → A ⊕ B) : B →. A ⊕ B) := by
  use ↑(fun x ↦ 2 * x + 1 : ℕ → ℕ)
  · sorry -- This is hard!
  · sorry
  · sorry

@[fun_prop, simp]
lemma computable_inr : Computable (Sum.inr : B → A ⊕ B) := by
  apply semicomputable_inr

end Sum

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
