/-
The declaration-level dependency cone of `riemannHypothesis`, computed from the compiled
environment by a native program (the same computation as `cut.sh`, which runs it in the
interpreter and is far slower).

Build (in this directory):   lake build cut
Run (from the archive root, so that LEAN_PATH points at the built archive):
    lake env /path/to/cut/.lake/build/bin/cut <output-directory>

Outputs: cut-result.txt (summary and membership tests), cut-modules.txt (project modules that
contain a declaration of the cone), cut-hub.txt (literature-hub theorems, in or out).
-/
import Lean
open Lean

def valOf : ConstantInfo → Option Expr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

def extraOf : ConstantInfo → List Name
  | .inductInfo v => v.ctors
  | .ctorInfo v => [v.induct]
  | _ => []

/-- The constants occurring in an expression. Lean's own `Expr.getUsedConstants` keeps only a
small direct-mapped cache of visited subterms, so on a term with heavy sharing it revisits
subterms without bound; on this archive it did not finish. This version keeps the full set of
visited nodes, by address, and is linear in the size of the term as a graph. -/
unsafe def usedConstsImpl (e : Expr) : Array Name := Id.run do
  let mut visited : Std.HashSet USize := {}
  let mut out : Std.HashSet Name := {}
  let mut stack : Array Expr := #[e]
  while !stack.isEmpty do
    let x := stack.back!
    stack := stack.pop
    match x with
    | .const n _ => out := out.insert n
    | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => pure ()
    | _ =>
      let addr := ptrAddrUnsafe x
      if visited.contains addr then continue
      visited := visited.insert addr
      match x with
      | .app f a => stack := (stack.push f).push a
      | .lam _ t b _ => stack := (stack.push t).push b
      | .forallE _ t b _ => stack := (stack.push t).push b
      | .letE _ t v b _ => stack := ((stack.push t).push v).push b
      | .mdata _ b => stack := stack.push b
      | .proj s _ b => out := out.insert s; stack := stack.push b
      | _ => pure ()
  return out.toArray

@[implemented_by usedConstsImpl]
opaque usedConsts (e : Expr) : Array Name

/-- Every constant reachable from the start names through types, values and
inductive/constructor links. -/
def cone (env : Environment) (starts : List Name) : IO (Std.HashSet Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := starts.toArray
  let mut steps : Nat := 0
  let t0 ← IO.monoMsNow
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    steps := steps + 1
    if steps % 200000 == 0 then
      IO.println s!"  cone: {steps} constants visited, stack {stack.size}, {((← IO.monoMsNow) - t0) / 1000} s"
      (← IO.getStdout).flush
    match env.find? n with
    | none => pure ()
    | some ci =>
      for c in usedConsts ci.type do
        if !seen.contains c then stack := stack.push c
      match valOf ci with
      | some v =>
        let t1 ← IO.monoMsNow
        for c in usedConsts v do
          if !seen.contains c then stack := stack.push c
        let dt := (← IO.monoMsNow) - t1
        if dt > 20000 then
          IO.println s!"  slow: {n} took {dt / 1000} s"
          (← IO.getStdout).flush
      | none => pure ()
      for c in extraOf ci do
        if !seen.contains c then stack := stack.push c
  return seen

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `_none

def projRoots : List Name := [`Formalism, `Development, `CompanionTheory, `PositivityTheory,
  `ReciprocityTheory, `GroundTheory, `Lemmata, `Supplements, `BuildAid, `Statements, `Main]

def shortProbes : List String := ["riemannHypothesis", "rhOfAll", "allChi",
  "every_character_of_green_v_win", "zero_free_all_of_green_v_win", "shape_closed_link_n_of_green",
  "shapeWin", "plugAll", "supplyChi", "zeroFreeAll_of_topG", "zeroFree_of_rpow_window",
  "each_unit_bound_statement", "key_identity5", "MeanBoundSecondForm", "theoremF", "theoremFSharp",
  "boundsMu", "gramWindow2_proved", "GramWindow2", "thmAGauss", "oneLetterGauss", "thmBGauss",
  "lemma_R_log_loss", "split_bound_eleven_one", "kernel_a_one_generic", "kernel_a_two_generic",
  "kernel_b_generic", "admissible_level_two", "admissible_tops_mertens", "cm3",
  "cmGoodModel_of_globalArtinReciprocity", "globalArtin", "chowla_selberg_eta",
  "tendsto_realEisenstein_sub_pole", "topCovolSlim2_use_alt_alt", "lcv_le", "resolutionCharZero",
  "principalisationCharZero_closed", "inEta_num", "divinN_of_hypV", "vvRecord", "zero_density_box",
  "meanSqK", "pair_share", "levelPrime_unconditional", "minkowski_bound_rat", "numberU3U_of_prints",
  "zetaUr", "galoisRepresentations_of_thetaLift", "tLiftK", "recTExists", "classSel",
  "linkG_fam_noKer", "link_of_local_closed", "theorem_A_closed_form_holds",
  "prvF_of_orbitLetterBounds", "orbitBound_standardSeries_inertPlaces", "comb_of_tied",
  "exists_beFam_evenConditionsInert_of_kerEnt", "scal_of_aForm_bForm", "lamLow_of_classicalTheorems",
  "congruenceLength_twistedPlaces_of_heckeIntegrality", "carU_of_star_alt", "cusp_of_pair_alt",
  "DetGain", "WeightedSieveImpliesRH", "WeightThm", "WeightCor", "RiemannHypothesisOfHalfLinks",
  "ZetaQuarterPowerCorollary", "BesselPeriodGGP", "DetChain", "DetBlocks", "hostThickExists",
  "of_four_alt", "lemmaK_litN_alt", "model_upper", "kato_eulerSystem_integrality", "uniqGap_holds",
  "standard_weyl_lattices_fock_dual", "Row0b", "AwayB", "LemmaM", "LevelPrime", "SizeData₂",
  "ChainTied", "InputSG", "LinkN", "DIVinN", "HypsAlt", "Hyps", "VWin", "Green", "frameB_share",
  "layer_cake_formula", "formB", "Fi", "cuspA", "adm2", "Iu", "NprimeDef", "LossBounds",
  "QuotientSlopeBoundsWith", "Count5", "AskMainBalance", "GrowthSizeBound", "CM2", "CM3", "ltLog",
  "LemmaRA", "UniqGap", "KExpansion", "CongruenceNumberRankThree", "TheoremF", "BoundsMu"]

def hubModule : Name :=
  `Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin

def tops : List Name := [`riemannHypothesis, `riemannZeta_eq_zero_re,
  `LFunction_ne_zero_of_half_lt_re, `LFunction_eq_zero_re, `LFunction_eq_zero_re_of_isPrimitive]

def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

def main (args : List String) : IO Unit := do
  let outDir := args.headD "."
  initSearchPath (← findSysroot)
  say "importing Main"
  let env ← importModules #[{ module := `Main }] {} (trustLevel := 1024)
  say s!"imported: {env.header.moduleNames.size} modules"
  let c ← cone env [`riemannHypothesis]
  say s!"CONE-SIZE {c.size}"
  -- the cone of all five theorems of Main, to see what the other four add
  let cAll ← cone env [`riemannHypothesis, `riemannZeta_eq_zero_re, `LFunction_ne_zero_of_half_lt_re,
    `LFunction_eq_zero_re, `LFunction_eq_zero_re_of_isPrimitive]
  say s!"CONE-SIZE-FIVE-THEOREMS {cAll.size}"
  IO.FS.writeFile (outDir ++ "/cut-five-extra.txt")
    (String.intercalate "\n" ((cAll.toList.filter fun n => !c.contains n).map toString))
  let probeSet : Std.HashSet String := Std.HashSet.ofList shortProbes
  let mut tot : Std.HashMap Name (Nat × Nat) := {}
  let mut modsIn : Std.HashSet Name := {}
  let mut modsAll : Std.HashSet Name := {}
  let mut thmAll := 0
  let mut thmIn := 0
  let mut defAll := 0
  let mut defIn := 0
  -- per probe: how many declarations end in that name, how many of those are in the cone, and
  -- the first few full names of each kind (counters, not arrays: some names are very common)
  let mut byShort : Std.HashMap String (Nat × Nat × Array Name × Array Name) := {}
  let mut hub : Array (Name × Bool) := #[]
  let mut seenConsts := 0
  -- every project declaration, one per line, with its kind: in the cone, and outside it
  let hIn ← IO.FS.Handle.mk (outDir ++ "/cut-in.txt") .write
  let hOut ← IO.FS.Handle.mk (outDir ++ "/cut-out.txt") .write
  let mods := env.header.moduleNames
  let data := env.header.moduleData
  for i in [0:mods.size] do
    let m := mods[i]!
    let root := m.getRoot
    let isProj := projRoots.contains root
    let isHub := m == hubModule
    let md := data[i]!
    if i % 20000 == 0 then say s!"  scan: module {i} of {mods.size}, {seenConsts} constants"
    let mut touched := false
    let mut a := 0
    let mut b := 0
    for j in [0:md.constNames.size] do
      let n := md.constNames[j]!
      let ci := md.constants[j]!
      seenConsts := seenConsts + 1
      let inC := c.contains n
      a := a + 1
      if inC then b := b + 1; touched := true
      if isProj then
        let kind := match ci with
          | .thmInfo _ => "T" | .defnInfo _ => "D" | .inductInfo _ => "I" | .ctorInfo _ => "C"
          | .recInfo _ => "R" | .opaqueInfo _ => "O" | .axiomInfo _ => "A" | .quotInfo _ => "Q"
        (if inC then hIn else hOut).putStrLn s!"{kind} {n}"
        match ci with
        | .thmInfo _ => thmAll := thmAll + 1; if inC then thmIn := thmIn + 1
        | .defnInfo _ => defAll := defAll + 1; if inC then defIn := defIn + 1
        | _ => pure ()
        if isHub then
          match ci with
          | .thmInfo _ => hub := hub.push (n, inC)
          | _ => pure ()
      match n with
      | .str _ s =>
        if probeSet.contains s then
          let (k, kin, ins, outs) := byShort.getD s (0, 0, #[], #[])
          byShort := byShort.erase s
          let ins := if inC && ins.size < 6 then ins.push n else ins
          let outs := if !inC && outs.size < 3 then outs.push n else outs
          byShort := byShort.insert s (k + 1, if inC then kin + 1 else kin, ins, outs)
      | _ => pure ()
    let (ta, tb) := tot.getD root (0, 0)
    tot := tot.insert root (ta + a, tb + b)
    if isProj && a > 0 then
      modsAll := modsAll.insert m
      if touched then modsIn := modsIn.insert m
  let mut out := s!"CONE-SIZE {c.size}\nCONE-SIZE-FIVE-THEOREMS {cAll.size}\nCONSTANTS-SCANNED {seenConsts}\n"
  out := out ++ "BY-ROOT root total-constants in-cone\n"
  for (r, (a, b)) in tot.toList do
    out := out ++ s!"  {r} {a} {b}\n"
  out := out ++ s!"PROJECT-THEOREMS total {thmAll} in-cone {thmIn}\n"
  out := out ++ s!"PROJECT-DEFINITIONS total {defAll} in-cone {defIn}\n"
  out := out ++ s!"PROJECT-MODULES with-constants {modsAll.size} touching-cone {modsIn.size}\n"
  out := out ++ "SHORT-NAME-PROBES name: declarations-with-that-last-component in-cone [up to 6 in cone] [up to 3 not in cone]\n"
  for s in shortProbes do
    let (k, kin, ins, outs) := byShort.getD s (0, 0, #[], #[])
    out := out ++ s!"  {s}: {k} {kin} {ins.toList.map toString} {outs.toList.map toString}\n"
  let hubOut := hub.filter (fun p => !p.2)
  out := out ++ s!"LITERATURE-HUB theorems {hub.size} not-in-cone {hubOut.size}\n"
  hIn.flush
  hOut.flush
  IO.FS.writeFile (outDir ++ "/cut-result.txt") out
  IO.FS.writeFile (outDir ++ "/cut-modules.txt")
    (String.intercalate "\n" (modsIn.toList.map toString))
  IO.FS.writeFile (outDir ++ "/cut-hub.txt")
    (String.intercalate "\n" (hub.toList.map (fun p => (if p.2 then "IN  " else "OUT ") ++ toString p.1)))
  say out
  say "CUT-DONE"
