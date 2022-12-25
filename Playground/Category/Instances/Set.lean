import Playground.Category.Basic
import Playground.Category.Instances.MetaSet
import Playground.Category.EpiMono
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.PushNeg

namespace Category.Instances
section
  -- Here we define Set, the category of all types, as a math object, hence in a fixed universe
  universe u in
  instance : Category (Type u) where
    hom := MetaSet.hom
    comp := MetaSet.comp
    id := MetaSet.id
    id_comp := MetaSet.id_comp
    comp_id := MetaSet.comp_id
    assoc := MetaSet.assoc

  universe u in
  instance {X Y : Type u} : Coe (X ⟶ Y) (X → Y) where coe x := x

end
end Category.Instances

section
  open Category

  universe u
  variable {X Y : Type u}

  def Function.Injective.of_monomorphism (f : X ↣ Y) : (f : X → Y).Injective := 
    λ x y h =>
    have := (f.property.1 (λ _ : X => x) (λ _ : X => y) (funext λ _ => h))
    congrFun this x

  def Category.Monomorphism.of_Injective (f : X → Y) (hf : f.Injective) : X ↣ Y :=
    ⟨f, ⟨λ _ _ p => funext λ x => hf ((congrFun p) x)⟩⟩

  def Function.Surjective.of_epimorphism (f : X ↠ Y) : (f : X → Y).Surjective := 
    open Classical in
    let this := propDecidable
    byContradiction <| by
      intro (c : ¬∀ _, _)
      push_neg at c
      let ⟨y₀, c⟩ := c
      let g : Y ⟶ ULift Bool := λ _ => ULift.up <| true
      let h : Y ⟶ ULift Bool := λ y => ULift.up <| if y = y₀ then false else true
      have : g ≠ h := by
        intro d
        have : true = ite .. := congrArg ULift.down (congrFun d y₀)
        rw [if_pos rfl] at this
        exact ne_true_of_eq_false this rfl
      exact this <| f.property.1 g h <| by
        funext x
        show ULift.up true = ULift.up (ite ..)
        apply congrArg ULift.up
        exact if hx : f.val x = y₀ then by
          rw [if_pos hx]; exact False.elim <| c x hx
        else by rw [if_neg hx]

  def Category.Epimorphism.of_Surjective (f : X → Y) (hf : f.Surjective) : X ↠ Y :=
    ⟨f, ⟨λ _ _ p => funext λ y => let ⟨x, hx⟩ := hf y; hx ▸ congrFun p x⟩⟩

end