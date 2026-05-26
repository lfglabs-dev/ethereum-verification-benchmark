/-
  Benchmark.Grindset.Attr — registers the `grind_norm` simp attribute.

  Kept in a separate file because Lean 4 does not allow using an attribute in
  the same file where it is registered.
-/

import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand

/-- Simp set for the Verity grindset. Unfolds the `Contract` monad
    scaffolding (`bind`, `pure`, `Contract.run`, `ContractResult.snd`,
    `ContractResult.fst`) and the primitive `*_run` reductions so that a
    benchmark task goal of shape

      ((Contract.f args).run s).snd.storage n = v

    collapses to plain record-update reasoning over `s`. Usage:

    ```
    simp only [grind_norm]
    ```

    Members are registered across `Benchmark.Grindset.Monad` and
    `Benchmark.Grindset.Core`. -/
register_simp_attr grind_norm
