/-
  Łukasiewicz / MV-algebra formalization — library root.

  Importing this module pulls in the entire MV-algebra development as a single
  dependency-ordered chain (no code duplication):

      Base → Lattice → Distance → BooleanCenter → MVLemmas → BooleanAlgebra
           → Ideals → Subalgebras → IdealOperations → Instances → Quotient → Correspondence → SecondIso → CRT → IsoBasics → IdealLattice

  The propositional-logic developments (`Residuation`, `Soundness`,
  `Equivalence`, `DeductionBL`) are deliberately *not* imported here: each is a
  self-contained module that redeclares the `MVAlgebra` class for standalone
  checking, so importing them alongside `Base` would clash. Check those four
  with `lake env lean Lukasiewicz/<Name>.lean` (or plain `lean <file>`).
-/

import Lukasiewicz.Base
import Lukasiewicz.Lattice
import Lukasiewicz.Distance
import Lukasiewicz.BooleanCenter
import Lukasiewicz.MVLemmas
import Lukasiewicz.BooleanAlgebra
import Lukasiewicz.Ideals
import Lukasiewicz.Subalgebras
import Lukasiewicz.IdealOperations
import Lukasiewicz.Instances
import Lukasiewicz.Quotient
import Lukasiewicz.Correspondence
import Lukasiewicz.SecondIso
import Lukasiewicz.CRT
import Lukasiewicz.IsoBasics
import Lukasiewicz.IdealLattice
