import Lean

/-!
# Build-time axiom checks

* `#assert_axioms foo` fails unless `foo` depends only on `propext`,
  `Classical.choice` and `Quot.sound`.  An unfinished proof depends on
  `sorryAx` and is therefore rejected.
* `#assert_axioms foo allowing [a, b]` additionally permits the listed axioms.
* `#assert_project_axioms [a, b]` fails unless the axioms declared in
  `ThreeDecomposition.*` modules are exactly `a, b`.
-/

namespace ThreeDecomposition.Audit

open Lean Elab Command

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

syntax (name := assertAxioms) "#assert_axioms " ident (" allowing " "[" ident,* "]")? : command

@[command_elab assertAxioms]
def elabAssertAxioms : CommandElab
  | `(#assert_axioms $id:ident $[allowing [$extra,*]]?) => do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let extraNames ← match extra with
      | some xs => xs.getElems.toList.mapM fun (x : Ident) =>
          liftCoreM <| realizeGlobalConstNoOverloadWithInfo x.raw
      | none => pure []
    let axs ← liftCoreM <| collectAxioms n
    let allowed := standardAxioms ++ extraNames
    let bad := axs.toList.filter (· ∉ allowed)
    unless bad.isEmpty do
      throwError "{n} depends on disallowed axioms: {bad}"
  | _ => throwUnsupportedSyntax

syntax (name := assertProjectAxioms) "#assert_project_axioms " "[" ident,* "]" : command

@[command_elab assertProjectAxioms]
def elabAssertProjectAxioms : CommandElab
  | `(#assert_project_axioms [$ids,*]) => do
    let expected ← ids.getElems.toList.mapM fun (x : Ident) =>
      liftCoreM <| realizeGlobalConstNoOverloadWithInfo x.raw
    let env ← getEnv
    let found := env.constants.fold (init := ([] : List Name)) fun acc n ci =>
      match ci with
      | .axiomInfo _ =>
        match env.getModuleIdxFor? n with
        | some idx =>
          if (`ThreeDecomposition).isPrefixOf env.header.moduleNames[idx.toNat]! then
            n :: acc
          else acc
        | none => acc
      | _ => acc
    let unexpected := found.filter (· ∉ expected)
    let missing := expected.filter (· ∉ found)
    unless unexpected.isEmpty && missing.isEmpty do
      throwError "project axioms changed: unexpected {unexpected}, no longer present {missing}"
  | _ => throwUnsupportedSyntax

end ThreeDecomposition.Audit
