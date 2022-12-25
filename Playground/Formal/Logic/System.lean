import Playground.Formal.System
import Playground.Formal.Logic.Language

namespace Formal.Logic

class System (L) [Language L] extends System L where
  map : Formula L → Judgment

end Formal.Logic
