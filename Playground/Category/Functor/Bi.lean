import Playground.Category.Instances.Set
import Playground.Category.Instances.Product
import Playground.Category.Functor.Category

namespace Category.Functor

section
  open Natural_Transformation

  section
    abbrev Bi (C D E) [Category C] [Category D] [Category E] := (C × D) ⥤ E
  end
  
  namespace Bi
  section

    def swap {C D E} [Category C] [Category D] [Category E]
      (F : Bi C D E) : Bi D C E where
      obj_map := λ ⟨Y, X⟩ => F ⟨X, Y⟩
      hom_map := λ ⟨g, f⟩ => F.hom_map ⟨f, g⟩
      hom_map_comp := λ ⟨g₁, f₁⟩ ⟨g₂, f₂⟩ => by
        show F.hom_map (_, _ ≫ _) = F.hom_map _ ≫ F.hom_map _ 
        rw [←hom_map_comp]
        show F.hom_map (_, _ ≫ _) = F.hom_map ((_ ≫ _), (_ ≫ _))
        simp
      hom_map_id := λ Y => by
        show F.hom_map (𝟙 _) = 𝟙 _ 
        simp

    def fixLeft {C D E} [Category C] [Category D] [Category E]
      (F : Bi C D E) (X : C) : D ⥤ E where
      obj_map := λ Y => F ⟨X, Y⟩
      hom_map := @λ Y₁ Y₂ g => 
        show F ⟨X, Y₁⟩ ⟶ F ⟨X, Y₂⟩ from
        F.hom_map ⟨𝟙 _, g⟩
      hom_map_comp := λ {Y₁ Y₂ Y₃} g₁ g₂ => by
        show F.hom_map (_, _ ≫ _) = F.hom_map _ ≫ F.hom_map _ 
        rw [←hom_map_comp]
        show F.hom_map (_, _ ≫ _) = F.hom_map ((_ ≫ _), (_ ≫ _))
        simp
      hom_map_id := λ Y => by
        show F.hom_map (𝟙 _) = 𝟙 _ 
        simp

    def fixRight {C D E} [Category C] [Category D] [Category E]
      (F : Bi C D E) (Y : D) : C ⥤ E := F.swap.fixLeft Y

    def curry {C D E} [Category C] [Category D] [Category E]
      (F : Bi C D E) : C ⥤ D ⥤ E where
      obj_map := F.fixLeft
      hom_map {X₁ X₂} f := {
        component := λ Y => F.hom_map (f, 𝟙 Y)
        naturality := λ {Y₁ Y₂} g => by
          show F.hom_map _ ≫ F.hom_map _ = F.hom_map _ ≫ F.hom_map _
          rw [←hom_map_comp, ←hom_map_comp]
          apply congrArg F.hom_map
          show (_ ≫ _, _ ≫ _) = (_ ≫ _, _ ≫ _)
          simp
      }
      hom_map_comp {X₁ X₂ X₃} f₁ f₂ := by
        apply eq_of_component_eq
        funext Y
        show F.hom_map _ = F.hom_map _ ≫ F.hom_map _
        rw [←hom_map_comp]
        apply congrArg F.hom_map
        show _ = (_ ≫ _, _ ≫ _)
        simp
      hom_map_id X := by
        apply eq_of_component_eq
        funext Y
        show F.hom_map (𝟙 _) = 𝟙 _ 
        simp
  end
  end Bi

  section
    def asLHSofBi {C D E} [Category C] [Category D] [Category E]
      (F : C ⥤ E) : Bi C D E where
      obj_map := λ ⟨X, _⟩ => F X
      hom_map := λ ⟨f, _⟩ => F.hom_map f
      hom_map_comp _ _ := by simp
      hom_map_id _ := by simp

    def asRHSofBi {C D E} [Category C] [Category D] [Category E]
      (F : D ⥤ E) : Bi C D E where
      obj_map := λ ⟨_, Y⟩ => F Y
      hom_map := λ ⟨_, f⟩ => F.hom_map f
      hom_map_comp _ _ := by simp
      hom_map_id _ := by simp

    def pack {C D₁ D₂} [Category C] [Category D₁] [Category D₂] 
      (F₁ : C ⥤ D₁) (F₂ : C ⥤ D₂) : C ⥤ D₁ × D₂ where
      obj_map X := ⟨F₁ X, F₂ X⟩
      hom_map f := ⟨F₁.hom_map f, F₂.hom_map f⟩
      hom_map_comp f g := by simp; rfl
      hom_map_id X := by simp; rfl

    def prod {C D E₁ E₂} [Category C] [Category D] [Category E₁] [Category E₂]
      (F₁ : C ⥤ E₁) (F₂ : D ⥤ E₂) : Bi C D (E₁ × E₂) :=
      F₁.asLHSofBi.pack F₂.asRHSofBi
  end

  section
    def fixLeft {C D E} [Category C] [Category D] [Category E]
      (F : C ⥤ D ⥤ E) (X : C) : D ⥤ E := F X

    def fixRight {C D E} [Category C] [Category D] [Category E]
      (F : C ⥤ D ⥤ E) (Y : D) : C ⥤ E where
      obj_map := λ X => F X Y
      hom_map := λ {X₁ X₂} f => (F.hom_map f).component Y
      hom_map_comp := by simp
      hom_map_id X := by simp; rfl

    def uncurry {C D E} [Category C] [Category D] [Category E]
      (F : C ⥤ D ⥤ E) : Bi C D E where
      obj_map := λ ⟨X, Y⟩ => F X Y
      hom_map := @λ ⟨X₁, Y₁⟩ ⟨X₂, Y₂⟩ ⟨f, g⟩ => 
        show F X₁ Y₁ ⟶ F X₂ Y₂ from
        (F X₁).hom_map g ≫ (F.fixRight Y₂).hom_map f
      hom_map_comp := @λ ⟨X₁, Y₁⟩ ⟨X₂, Y₂⟩ ⟨X₃, Y₃⟩ ⟨f₁, g₁⟩ ⟨f₂, g₂⟩ => by
        simp [fixRight]
        rw [assoc ((F X₁).hom_map g₁), ←assoc ((F X₁).hom_map g₂)]
        rw [naturality, assoc, assoc]
      hom_map_id _ := by simp; rfl

    def swap {C D E} [Category C] [Category D] [Category E]
      (F : C ⥤ D ⥤ E) : D ⥤ C ⥤ E := F.uncurry.swap.curry
  end

  section
    namespace Bi
    -- define the evaluation bifunctor : X, F ↦ F X
    def evaluation (C D) [Category C] [Category D] : Bi C (C ⥤ D) D :=
      (𝟭 (C ⥤ D)).uncurry.swap

    --
    -- def ofLeftAndRightFunctors {C D E} [Category C] [Category D] [Category E]
    --   (F : C ⥤ E)
    --   : Bi C D E := sorry

    end Bi
  end

  section
    def isom_images_of_isom_functors {C D} [Category C] [Category D] {F G : C ⥤ D} (α : F ≅ G) (X : C) 
      : F X ≅ G X :=
      ((Bi.evaluation C D).fixLeft X).isom_images_of_isom_objects α

    -- example {C D} [Category C] [Category D] {F G : C ⥤ D} (h : ∀ X, F X ≅ G X) : F ≅ G :=
    --   sorry

  end
end

end Category.Functor
