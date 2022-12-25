import Playground.Category.Functor.Hom
import Playground.Category.Instances.Set

namespace Category.Functor
section

  structure PreAdjunction (C) [Category C] (D) [Category D] where
    left : D ⥤ C
    right : C ⥤ D

  def PreAdjunction.homLeft.{u,v,w,t} {C} [Category.{u,v} C] {D} [Category.{w,t} D] (p : PreAdjunction C D)
  : Bi Cᵒᵖ D (Type _) := (𝟭 C).opp.prod p.left ⋙ hom C ⋙ ulift.{v,t}

  def PreAdjunction.homRight.{u,v,w,t} {C} [Category.{u,v} C] {D} [Category.{w,t} D] (p : PreAdjunction C D)
  : Bi Cᵒᵖ D (Type _) := p.right.opp.prod (𝟭 D) ⋙ hom D ⋙ ulift.{t,v}

  structure Adjunction (C) [Category C] (D) [Category D] extends PreAdjunction C D where
    isomorphism : toPreAdjunction.homLeft ≅ toPreAdjunction.homRight

  def Adjunction.isomorphismAt.{u,v,w,t} {C} [Category.{u,v} C] {D} [Category.{w,t} D]
    (a : Adjunction C D) (X : C) (Y : D)
    : ULift.{t,v} (X ⟶ a.left Y) ≅ ULift.{v,t} (a.right X ⟶ Y) :=
    isom_images_of_isom_functors a.isomorphism ⟨op X, Y⟩


end
end Category.Functor