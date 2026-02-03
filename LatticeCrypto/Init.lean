-- TODO: Switch to the module system
import Mathlib.Init
import Mathlib.Tactic.Common

/--
  Defines the `fact` and `corollary` macros as syntactic sugars for `theorem` with a more readable syntax.

  * `mods:declModifiers`: This captures everything that comes before the keyword, including doc strings (`/-- ... -/`), attributes (`@[simp]`, `@[instance]`), and visibility modifiers (`private`, `protected`).

  * `n:declId`: Captures the name of your declaration (e.g., `my_fact`).

  * `sig:declSig`: Captures the type signature and arguments (e.g., `(p q : Prop) : p → q`).

  * `val:declVal`: Captures the value/proof (e.g., `:= by ...`).
-/
-- Define the macro for 'fact'
macro mods:declModifiers "fact" n:declId sig:declSig val:declVal : command =>
  `($mods:declModifiers theorem $n $sig $val)

-- Define the macro for 'corollary'
macro mods:declModifiers "corollary" n:declId sig:declSig val:declVal : command =>
  `($mods:declModifiers theorem $n $sig $val)
