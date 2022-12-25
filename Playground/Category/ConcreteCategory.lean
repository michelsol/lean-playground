import Playground.Category.Functor.Basic
import Playground.Category.Instances.Set

namespace Category

class Concrete (C) extends Category C where
  toType : C ⥤ Type
export Concrete (toType)

end Category