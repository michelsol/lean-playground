import Playground.Category.EpiMono
import Playground.Category.Functor.Universal
import Playground.Category.Construction.Terminal
import Playground.Category.Construction.Pullback

namespace Category
open Construction

structure Subobject {C} [Category C] (X : C) where
  {object : C}
  mono : object ↣ X

structure SubobjectClassifier (C) [Category C] [Terminals C] where
  Ω : C
  τ : terminal.object ⟶ Ω
  χ {X : C} (U : Subobject X) : X ⟶ Ω
  comm : ∀ ⦃X⦄ (U : Subobject X), U.mono ≫ χ U = (terminal.existence ⟨U.object⟩).choose ≫ τ
  property : 
    let pullbackDiagram {X : C} (U : Subobject X) : Pullback.Data (χ U) τ := {
        commutative := comm U
      }
    ∀ ⦃X⦄ (U : Subobject X), Functor.Universal.Property (pullbackDiagram U)
  -- intuitively a subobject classifer is a χ and an element τ of some truth universe Ω 
  -- such that U is the most general solution to the χ U = τ problem iow, 
  -- U = { x | χ U (x) = true } = (χ U)⁻¹(True)

section
  variable {C} [Category C] [Terminals C] (s : SubobjectClassifier C)
  namespace SubobjectClassifier
  noncomputable def pullbackOfSubobject {X} (U : Subobject X) : Pullback (s.χ U) s.τ := {
      toProperty := s.property U
      commutative := s.comm U
    }
  end SubobjectClassifier
end

section
  def Sub.{u,v} (C) [Category.{u,v} C] [Pullbacks C] : Cᵒᵖ ⥤ Type _ where
    obj_map | op X => Subobject X
    hom_map := λ {d} {c} => match d, c with | op d, op c => λ
      | (op f), { object := t, mono := { val := i, property := hi }} => {
      object := (i ̲× f).object
      mono := {
        val := (i ̲× f).morphism₂
        property := by
          constructor
          intro Z a b h
          apply (i ̲× f).uniqueness {
              morphism₁ := a ≫ (i ̲× f).morphism₁
              morphism₂ := a ≫ (i ̲× f).morphism₂
              commutative := by rw [assoc, (i ̲× f).commutative, ←assoc] }
          . simp [Functor.Universal.FactorsThroughVia]
          . have : _ ≫ _ = _ ≫ _ := congrArg (. ≫ f) h
            rw [assoc, assoc, ←(i ̲× f).commutative, ←assoc, ←assoc] at this
            have h' := hi.mono _ _ this
            simp [Functor.Universal.FactorsThroughVia, h, h']
      }
    }
    hom_map_comp _ _ := sorry
    hom_map_id _ := sorry
end

end Category