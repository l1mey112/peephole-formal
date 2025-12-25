import Lean

open Lean Meta

/- initialize iNInst : SimpExtension ←
  registerSimpAttr `iN_unwrap_inst
    "simp lemmas unwrapping instructions" -/

initialize simpIN : SimpExtension ←
  registerSimpAttr `simp_iN
    "simp lemmas unwrapping instructions"

initialize simpINBitvec : SimpExtension ←
  registerSimpAttr `simp_iN_bitvec
    "simp lemmas unwrapping instructions"

initialize validInstructions : SimplePersistentEnvExtension (Name) (List Name) ←
  let addEntryFn | m, name => name :: m

  registerSimplePersistentEnvExtension {
    name := `valid_instructions
    addImportedFn := mkStateFromImportedEntries addEntryFn {}
    addEntryFn
  }

initialize instAttr : Unit ←
  registerBuiltinAttribute {
    name  := `inst
    descr := "tags definitions to be used as valid instructions"
    applicationTime := .afterCompilation
    add   := fun declName stx _attrKind => do

      let info ← getConstInfo declName
      match info with
      | .defnInfo _ => pure ()
      | _ => throwErrorAt stx "@[inst] is only allowed on definitions"

      modifyEnv fun env =>
         validInstructions.addEntry env declName
  }
