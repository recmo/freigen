import Freigen.ITree.PFunctor
import Freigen.ITree.Basic
import Freigen.ITree.Eutt
import Freigen.Free
import Freigen.Ast.Basic
import Freigen.Ast.Sexp
import Freigen.Reflect.Attributes
import Freigen.Reflect.Sound
import Freigen.Reflect.Registry
import Freigen.Reflect.Basic
import Freigen.Compile
import Freigen.Examples.Circuit.Basic
import Freigen.Examples.Storage
import Freigen.Examples.Recursion
import Freigen.Examples.FirstClass

/-!
# Freigen

`import Freigen` exposes the unified implementation:

* `Freigen.Free` is the higher-order free syntax over an `ITree.HSig`. Operations may contain
  dynamically bound blocks; ordinary effects are operations with no branches.
* `Freigen.ITree` provides higher-order signatures, interaction trees, recursion, interpretation,
  and relational weak bisimulation.
* `Freigen.Ast` provides the `Tp`-indexed PHOAS syntax, its denotation, source locations, and the
  S-expression serializer.
* `Freigen.Reflect` provides explicit representation/signature registries, structural soundness
  lemmas, and the two-pass `reflect%`, `reflect_def`, and `#reflect_plan` elaborators.
* `Freigen.Compile` provides `#compile program => "path"` for the `:prog` Lake facet.

The former first-order/scoped implementation and all version-suffixed modules have been removed.
-/
