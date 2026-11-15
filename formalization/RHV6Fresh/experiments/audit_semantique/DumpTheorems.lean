/-
Copyright © 2026 Charles S. Tous droits réservés.
Enveloppe Soleau INPI n° DSO2026044645, déposée le 15/11/2026. Voir COPYRIGHT.md et THIRD_PARTY_NOTICES.md à la racine du dépôt.
-/

import Lean
open Lean Meta Elab

/-- Usage: lean --run DumpTheorems.lean <ownRootsCSV> <baseRootsCSV> <outPrefix> <moduleListFile> -/

def rootOf (n : Name) : String := n.getRoot.toString

def isSkippableName (n : Name) : Bool :=
  if n.isInternal then true else
  let s := n.toString
  let last := n.componentsRev.headD .anonymous |>.toString
  (s.splitOn "_proof_").length > 1 || (s.splitOn "match_").length > 1 ||
  (s.splitOn ".proof_").length > 1 || (s.splitOn "_sunfold").length > 1 ||
  (s.splitOn "_cstage").length > 1 || (s.splitOn "_unsafe_rec").length > 1 ||
  last == "injEq" || last == "inj" || last == "sizeOf_spec" || last == "eq_def" ||
  last == "eq_1" || (last.startsWith "eq_" && (last.drop 3).all Char.isDigit) ||
  (last.startsWith "_" ) || last == "noConfusion" || last == "noConfusionType" ||
  last == "below" || last == "brecOn" || last == "binductionOn" || last == "casesOn" ||
  last == "recOn" || last == "rec" || last == "ibelow" || last == "ndrec" || last == "ndrecOn" ||
  last == "mk.injEq" || last == "ctorIdx" || last == "toCtorIdx"

def constDeps (ci : ConstantInfo) : Array Name :=
  let a := ci.type.getUsedConstants
  match ci with
  | .thmInfo v => a ++ v.value.getUsedConstants
  | .defnInfo v => a ++ v.value.getUsedConstants
  | .opaqueInfo v => a ++ v.value.getUsedConstants
  | _ => a

def stdAx : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Axioms of every constant reachable, memoized, iterative DFS. -/
def axiomsOf (env : Environment) (memo : IO.Ref (Std.HashMap Name (Array Name))) (root : Name) : IO (Array Name) := do
  let mut stack : Array (Name × Bool) := #[(root, false)]
  let mut inprog : Std.HashSet Name := {}
  while !stack.isEmpty do
    let (n, expanded) := stack.back!
    stack := stack.pop
    let m ← memo.get
    if m.contains n then continue
    match env.find? n with
    | none => memo.modify (·.insert n #[])
    | some ci =>
      if !expanded then
        if ci matches .axiomInfo _ then
          memo.modify (·.insert n #[n]); continue
        if inprog.contains n then continue
        inprog := inprog.insert n
        stack := stack.push (n, true)
        for d in constDeps ci do
          unless m.contains d || inprog.contains d do stack := stack.push (d, false)
      else
        let m ← memo.get
        let mut acc : Array Name := #[]
        for d in constDeps ci do
          if let some s := m.get? d then
            for a in s do unless acc.contains a do acc := acc.push a
        memo.modify (·.insert n acc)
        inprog := inprog.erase n
  return ((← memo.get).get? root).getD #[]

unsafe def main (args : List String) : IO UInt32 := do
  let own := (args[0]!).splitOn ","
  let base := if (args[1]!).isEmpty then [] else (args[1]!).splitOn ","
  let outPre := args[2]!
  let mods := (← IO.FS.readFile (args[3]!)).splitOn "\n" |>.filter (· ≠ "") |>.map String.toName
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules (mods.toArray.map fun m => ({ module := m } : Import)) {} (trustLevel := 0) (loadExts := true)
  IO.eprintln s!"imported {mods.length} modules"
  let modNames := env.header.moduleNames
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).map fun i => modNames[i.toNat]!
  let inRoots (roots : List String) (n : Name) : Bool :=
    match modOf n with | some m => roots.contains (rootOf m) | none => false
  let opts : Options := ((({} : Options).setBool `pp.fullNames false).set `format.width (400:Nat)).setBool `pp.unicode.fun true
  let ctx : Core.Context := { fileName := "<dump>", fileMap := default, maxHeartbeats := 0, options := opts }
  let coreSt : IO.Ref Core.State ← IO.mkRef { env := env }
  let memo ← IO.mkRef ({} : Std.HashMap Name (Array Name))
  let hT ← IO.FS.Handle.mk (outPre ++ ".jsonl") .write
  let hD ← IO.FS.Handle.mk (outPre ++ "_defs.jsonl") .write
  let mut consts : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₁.toList do
    if inRoots own n && (match modOf n with | some m => mods.contains m | none => false) && !isSkippableName ((privateToUserName? n).getD n) then consts := consts.push (n, ci)
  consts := consts.qsort (fun a b => a.1.toString < b.1.toString)
  IO.eprintln s!"{consts.size} candidate constants"
  let mut cnt := 0
  for (n, ci) in consts do
    let isThm := ci matches .thmInfo _
    let isDef := ci matches .defnInfo _ || ci matches .inductInfo _ || ci matches .opaqueInfo _ || ci matches .axiomInfo _
    unless isThm || isDef do continue
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
      | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom" | _ => "other"
    let modn := (modOf n).getD .anonymous
    let file := (modn.toString.replace "." "/") ++ ".lean"
    let act : MetaM (String × Nat) := do
      let ty := ci.type
      let s ← try pure (toString (← ppExpr ty)) catch e => pure s!"<pp error: {← e.toMessageData.toString}>"
      let s := if s.length > 4000 then (s.take 4000).toString ++ "…[truncated]" else s
      let hc ← try
          forallTelescope ty fun xs _ => do
            let mut k := 0
            for x in xs do
              let d ← x.fvarId!.getDecl
              if d.binderInfo.isExplicit && (← isProp d.type) then k := k + 1
            pure k
        catch _ => pure 0
      pure (s, hc)
    let (tyStr, hc) ← try
        let st ← coreSt.get
        let ((r), _) ← (act.run' {} {}).toIO ctx st
        pure r
      catch e => pure (s!"<error {e.toString}>", 0)
    let docS ← (do
      let r ← (Lean.findDocString? env n : IO (Option String)) |>.toBaseIO
      match r with | .ok v => pure v | .error _ => pure none)
    let line : Option Nat := (declRangeExt.find? env n).map fun r => r.range.pos.line
    if isThm then
      let axs ← axiomsOf env memo n
      let deps := ((constDeps ci).toList.eraseDups).filter (fun d => d != n)
      let dp := deps.filter (inRoots own) |>.map toString
      let db := deps.filter (inRoots base) |>.map toString
      let j := Json.mkObj [("name", toString ((privateToUserName? n).getD n)), ("private", decide (isPrivateName n)), ("full_name", toString n), ("module", toString modn), ("file", file),
        ("line", match line with | some l => Json.num l | none => Json.null),
        ("kind", kind), ("type", tyStr), ("docstring", match docS with | some d => Json.str d | none => Json.null),
        ("deps_project", toJson dp), ("deps_base", toJson db),
        ("axioms", toJson (axs.map toString)),
        ("uses_sorry", axs.contains `sorryAx),
        ("nonstandard_axioms", toJson ((axs.filter (fun a => !stdAx.contains a && a != `sorryAx)).map toString)),
        ("mentions_RH", decide ((tyStr.splitOn "RiemannHypothesis").length > 1)),
        ("hyp_count", hc)]
      hT.putStrLn j.compress
    else
      let j := Json.mkObj [("name", toString ((privateToUserName? n).getD n)), ("private", decide (isPrivateName n)), ("full_name", toString n), ("module", toString modn), ("file", file),
        ("line", match line with | some l => Json.num l | none => Json.null),
        ("kind", kind), ("type", tyStr), ("docstring", match docS with | some d => Json.str d | none => Json.null)]
      hD.putStrLn j.compress
    cnt := cnt + 1
    if cnt % 500 == 0 then IO.eprintln s!"{cnt}"
  hT.flush; hD.flush
  return 0

