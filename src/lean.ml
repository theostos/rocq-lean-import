(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Univ
open UVars
module RelDecl = Context.Rel.Declaration
open LeanExpr

let __ () = assert false
let invalid = Constr.(mkApp (mkSet, [| mkSet |]))

let add_universe l ~lbound g =
  let g = UGraph.add_universe l ~strict:false g in
  UGraph.enforce_constraint (lbound, Le, l) g

let quickdef ~name ~types ~univs body =
  let entry = Declare.definition_entry ?types ~univs body in
  let scope = Locality.(Global ImportDefaultBehavior) in
  let kind = Decls.(IsDefinition Definition) in
  let uctx =
    UState.empty
    (* used for ubinders and hook *)
  in
  Declare.declare_entry ~name ~scope ~kind ~impargs:[] ~uctx entry

type extended_level = Level of Level.t | LSProp

type scheme_family = SchemeSProp | SchemeType

(** produce [args, recargs] inside mixed context [args/recargs] [info] is in
    reverse order, ie the head is about the last arg in application order

    examples: [] -> [],[] [false] -> [1],[] [true] -> [2],[1] [true;false] ->
    [3;2],[1] [false;true] -> [3;1],[2] [false;false] -> [2;1],[] [true;true] ->
    [4;2],[3;1] *)
let reorder_inside_core info =
  let rec aux i args recargs = function
    | [] -> (args, recargs)
    | false :: info -> aux (i + 1) (i :: args) recargs info
    | true :: info -> aux (i + 2) ((i + 1) :: args) (i :: recargs) info
  in
  aux 1 [] [] info

let reorder_inside info =
  let args, recargs = reorder_inside_core info in
  CArray.map_of_list Constr.mkRel (List.append args recargs)

let rec insert_after k ((n, t) as v) c =
  if k = 0 then Constr.mkProd (n, t, Vars.lift 1 c)
  else
    match Constr.kind c with
    | Prod (na, a, b) -> Constr.mkProd (na, a, insert_after (k - 1) v b)
    | _ -> assert false

let insert_after k (n, t) c =
  insert_after k (n, Vars.lift k t) (Vars.subst1 invalid c)

let rec reorder_outside info hyps c =
  match (info, hyps) with
  | [], [] -> (c, 0)
  | false :: info, (n, t) :: hyps ->
    let c, k = reorder_outside info hyps c in
    (Constr.mkProd (n, t, c), k + 1)
  | true :: info, (n, t) :: rhyp :: hyps ->
    let c, k = reorder_outside info hyps c in
    let c = insert_after k rhyp c in
    (Constr.mkProd (n, t, c), k + 1)
  | _ -> assert false

(** produce [forall args recargs, P (C args)] from mixed
    [forall args/recargs, P (C args)] *)
let reorder_outside info ft =
  let hyps, out = Term.decompose_prod ft in
  fst (reorder_outside (List.rev info) (List.rev hyps) out)

(** Rocq normally generates a [match] for a record eliminator.  When the
    scrutinee is neutral, reducing projections of the result can then force the
    scrutinee merely to expose its constructor.  This is especially harmful
    when the neutral term contains a large closed computation.

    Primitive records have judgmental eta in Rocq.  Their one-branch
    eliminator can therefore apply the branch to the primitive projections of
    the scrutinee instead.  We check that the replacement has the original
    generated scheme's type, so this optimization relies only on Rocq's kernel
    eta rule and is independent of any particular Lean declaration. *)
let project_primitive_record_scheme env (mind, ind_index) body =
  let mib = Global.lookup_mind mind in
  let packet = mib.mind_packets.(ind_index) in
  match packet.mind_record with
  | Declarations.PrimRecord _ ->
    let nb_lambdas = mib.mind_nparams + 3 in
    let binders, inside = Term.decompose_lambda_n_assum nb_lambdas body in
    (match Constr.kind inside with
    | Constr.Case (_, _, _, _, _, scrutinee, branches)
      when Constr.equal scrutinee (Constr.mkRel 1)
           && Array.length branches = 1 ->
      let target = Constr.mkRel 1 in
      let fields =
        List.init packet.mind_consnrealargs.(0) (fun proj_arg ->
            let projection, relevance =
              Declareops.inductive_make_projection (mind, ind_index) mib
                ~proj_arg
            in
            Constr.mkProj
              (Projection.make projection false, relevance, target))
      in
      let projected =
        Term.it_mkLambda_or_LetIn
          (Constr.mkApp (Constr.mkRel 2, Array.of_list fields))
          binders
      in
      let evd = Evd.from_env env in
      let type_of term =
        Retyping.get_type_of env evd (EConstr.of_constr term)
      in
      if Reductionops.is_conv env evd (type_of body) (type_of projected) then
        projected
      else
        CErrors.user_err
          Pp.(str "Projection-based primitive-record scheme changed type")
    | _ -> body)
  | _ -> body

(** Whether Rocq's induction-scheme generator will add a recursive hypothesis
    for an argument of type [term]. A mere occurrence of [mind] is not enough:
    for a nested occurrence, Rocq only adds the hypothesis when the enclosing
    inductive has a suitable [AllForall] scheme registered. *)
let rec has_rec_hyp env mind term =
  let locals, head = Reduction.whd_decompose_prod_decls env term in
  let env = Environ.push_rel_context locals env in
  let head, args = Constr.decompose_app head in
  match Constr.kind head with
  | Constr.Ind (((nested_mind, _) as nested_ind), _) ->
    if MutInd.UserOrd.equal mind nested_mind then true
    else
      let nested_mib = Global.lookup_mind nested_mind in
      let positive =
        AllScheme.compute_params_rec_strpos env nested_mind nested_mib
      in
      let uniform = Array.sub args 0 nested_mib.mind_nparams_rec in
      let nested =
        Array.to_list
          (Array.mapi
             (fun i arg ->
               List.nth positive i && has_rec_hyp env mind arg)
             uniform)
      in
      List.exists (fun x -> x) nested
      && Result.is_ok
           (AllScheme.lookup_all_theorem (mind, 0)
              (GlobRef.IndRef nested_ind) nested)
  | Constr.Const (constant, _) when Environ.is_array_type env constant ->
    Array.length args = 1
    && has_rec_hyp env mind args.(0)
    && Result.is_ok
         (AllScheme.lookup_all_theorem (mind, 0)
            (GlobRef.ConstRef constant) [ true ])
  | _ -> false

(** Build the body of a Lean-style scheme. [u] instantiates the inductive, [s]
    is [None] for the SProp scheme and [Some l] for a scheme with motive [l].

    Lean schemes differ from Coq schemes:
    - the motive universe is the first bound universe for Lean but the last for
      Coq (handled by caller)
    - Lean puts induction hypotheses after all the constructor arguments, Coq
      puts them immediately after the corresponding recursive argument. *)
let lean_scheme env ~dep (mind, ind_index) u s =
  let mib = Global.lookup_mind mind in
  let nparams = mib.mind_nparams in
  (* if we start using non recursive params in the translation it will
     involve reordering arguments *)
  assert (nparams = mib.mind_nparams_rec);
  let body =
    let sigma = Evd.from_env env in
    let motive_level = ref None in
    let sigma, s' =
      match s with
      | LSProp -> sigma, EConstr.ESorts.sprop
      | Level _ ->
        let sigma, u = Evd.new_univ_level_variable UnivRigid sigma in
        motive_level := Some u;
        sigma, EConstr.ESorts.make @@ Sorts.sort_of_univ @@ Universe.make u
    in
    let sigma, body =
      if Array.length mib.mind_packets = 1 then
        Indrec.build_induction_scheme env sigma
          ((mind, ind_index), EConstr.EInstance.make u)
          dep s'
      else
        let specs =
          List.init (Array.length mib.mind_packets)
            (fun index -> ((mind, index), dep, s'))
        in
        let sigma, bodies =
          Indrec.build_mutual_induction_scheme env sigma ~force_mutual:true
            specs (EConstr.EInstance.make u)
        in
        sigma, List.nth bodies ind_index
    in
    let body = EConstr.Unsafe.to_constr body in
    let uctx = Evd.sort_context_set sigma in
    let subst_scheme_context quality default_level usubst =
      let (qvars, scheme_levels), csts = uctx in
      let body_qvars, _ = Vars.sort_and_universes_of_constr body in
      let qvars =
        Sorts.Quality.Set.fold
          (fun q qvars ->
            match q with
            | Sorts.Quality.QVar q -> Sorts.QVar.Set.add q qvars
            | Sorts.Quality.QConstant _ | Sorts.Quality.QGlobal _ -> qvars)
          body_qvars qvars
      in
      let qsubst =
        Sorts.QVar.Set.fold
          (fun q subst -> Sorts.QVar.Map.add q quality subst)
          qvars Sorts.QVar.Map.empty
      in
      let _, ind_levels = Instance.to_array u in
      let allowed_levels =
        Array.fold_left
          (fun levels level -> Level.Set.add level levels)
          (Level.Set.singleton Level.set) ind_levels
      in
      let add_scheme_level level graph =
        try UGraph.add_universe level ~strict:false graph
        with UGraph.AlreadyDeclared -> graph
      in
      let scheme_graph =
        UGraph.merge_constraints (PConstraints.univs csts)
          (Level.Set.fold add_scheme_level scheme_levels
             (Environ.universes env))
      in
      let equal_allowed_level level =
        let level_univ = Universe.make level in
        Level.Set.fold
          (fun allowed acc ->
            match acc with
            | Some _ -> acc
            | None ->
              let allowed_univ = Universe.make allowed in
              if UGraph.check_eq scheme_graph level_univ allowed_univ then
                Some allowed
              else None)
          allowed_levels None
      in
      let usubst =
        Level.Set.fold
          (fun level subst ->
            if
              Level.Map.mem level subst
              || Level.Set.mem level allowed_levels
            then subst
            else
              let target =
                match equal_allowed_level level with
                | Some allowed -> allowed
                | None -> default_level
              in
              Level.Map.add level target subst)
          scheme_levels usubst
      in
      Vars.subst_univs_level_constr (qsubst, usubst) body
    in
    match s with
    | LSProp ->
      subst_scheme_context Sorts.Quality.qsprop Level.set Level.Map.empty
    | Level s ->
      let v = match !motive_level with Some v -> v | None -> assert false in
      subst_scheme_context Sorts.Quality.qtype s (Level.Map.singleton v s)
  in
  let packet_recinfo (mip : Declarations.one_inductive_body) =
    assert (
      CArray.for_all2 Int.equal mip.mind_consnrealargs mip.mind_consnrealdecls);
    Array.mapi
      (fun i (args, _) ->
        let nargs = mip.mind_consnrealargs.(i) in
        (* skip params *)
        let args = CList.firstn nargs args in
        CList.map
          (fun arg ->
            let t = RelDecl.get_type arg in
            has_rec_hyp env mind t)
          args)
      mip.mind_nf_lc
  in
  let recinfo =
    Array.concat
      (Array.to_list (Array.map packet_recinfo mib.mind_packets))
  in
  let hasrec =
    (* NB: if the only recursive arg is the last arg, no need for reordering *)
    Array.exists
      (function [] -> false | _ :: info -> List.exists (fun x -> x) info)
      recinfo
  in

  let body =
    if not hasrec then body
    else begin
    (* body := fun params P (fc : forall args/recargs, P (C args)) => ...

       becomes

       fun params P (fc : forall args, forall recargs, P (C args)) =>
       body params P (fun args/recargs, fc args recargs)
    *)
    let open Constr in
    let nlc = Array.length recinfo in
    let nmotives = Array.length mib.mind_packets in
    let paramsP, inside =
      Term.decompose_lambda_n_assum (nparams + nmotives) body
    in
    let fcs, inside = Term.decompose_lambda_n nlc inside in
    let fcs = List.rev fcs in

    let body =
      mkApp
        ( body,
          Array.init (nparams + nmotives)
            (fun i -> mkRel (nlc + nparams + nmotives - i)) )
    in
    let body =
      mkApp
        ( body,
          Array.of_list
            (CList.map_i
               (fun i (_, ft) ->
                 let info = recinfo.(i) in
                 if not (List.exists (fun x -> x) info) then mkRel (nlc - i)
                 else
                   let hyps, _ = Term.decompose_prod ft in
                   let args = reorder_inside info in
                   Term.it_mkLambda_or_LetIn
                     (mkApp (mkRel (nlc - i + List.length hyps), args))
                     (List.map (fun (n, t) -> RelDecl.LocalAssum (n, t)) hyps))
               0 fcs) )
    in

    let fcs =
      CList.map_i
        (fun i (n, ft) ->
          let info = recinfo.(i) in
          let ft = reorder_outside info ft in
          RelDecl.LocalAssum (n, ft))
        0 fcs
    in
    let fcs = List.rev fcs in
    let body =
      let open CClosure in
      let open RedFlags in
      let env = Environ.push_rel_context paramsP env in
      let env = Environ.push_rel_context fcs env in
      norm_val (create_clos_infos betaiota env) (create_tab ()) (inject body)
    in
    Term.it_mkLambda_or_LetIn (Term.it_mkLambda_or_LetIn body fcs) paramsP
    end
  in
  project_primitive_record_scheme env (mind, ind_index) body

let with_unsafe_univs f () =
  let flags = Global.typing_flags () in
  Global.set_typing_flags { flags with check_eliminations = false };
  try
    let v = f () in
    Global.set_typing_flags flags;
    v
  with e ->
    let e = Exninfo.capture e in
    Global.set_typing_flags flags;
    Exninfo.iraise e

module N = LeanName

let sort_of_level = function
  | LSProp -> Sorts.sprop
  | Level u -> Sorts.sort_of_univ (Universe.make u)

let univ_of_sort = function
  | Sorts.SProp -> None
  | Prop -> assert false
  | Set -> Some Universe.type0
  | Type u | GSort (_, u) | VSort (_, u) -> Some u

let sort_max (s1 : Sorts.t) (s2 : Sorts.t) =
  match (s1, s2) with
  | SProp, SProp | Prop, Prop | Set, Set -> s1
  | SProp, ((Prop | Set | Type _) as s) | ((Prop | Set | Type _) as s), SProp ->
    s
  | Prop, ((Set | Type _) as s) | ((Set | Type _) as s), Prop -> s
  | Set, Type u | Type u, Set ->
    Sorts.sort_of_univ (Univ.Universe.sup Univ.Universe.type0 u)
  | Type u, Type v -> Sorts.sort_of_univ (Univ.Universe.sup u v)
  | GSort _, _ | _, GSort _ -> assert false
  | VSort _, _ | _, VSort _ -> assert false

(** [map] goes from lean names to universes (in practice either SProp or a named
    level) *)
let rec to_universe map = function
  | U.Prop -> Sorts.sprop
  | UNamed n -> sort_of_level (N.Map.get n map)
  | Succ u -> Sorts.super (to_universe map u)
  | Max (a, b) -> sort_max (to_universe map a) (to_universe map b)
  | IMax (a, b) ->
    let ub = to_universe map b in
    if Sorts.is_sprop ub then ub else sort_max (to_universe map a) ub

let rec do_n f x n = if n = 0 then x else do_n f (f x) (n - 1)

(** in lean, imax(Prop+1,l)+1 <= max(Prop+1,l+1) because:
    - either l=Prop, so Prop+1 <= Prop+1
    - or Prop+1 <= l so l+1 <= l+1

    to simulate this, each named level becomes > Set and we compute maxes
    accordingly *)

let simplify_universe u =
  match Universe.repr u with
  | (l, n) :: (l', n') :: rest when Level.is_set l ->
    if n <= n' + 1 || List.exists (fun (_, n') -> n <= n' + 1) rest then
      List.fold_left
        (fun u (l, n) ->
          Universe.sup u (do_n Universe.super (Universe.make l) n))
        (do_n Universe.super (Universe.make l') n')
        rest
    else u
  | _ -> u

let simplify_sort = function
  | Sorts.Type u -> Sorts.sort_of_univ (simplify_universe u)
  | s -> s

(* Return the biggest [n] such that [Set+n <= u]. Assumes a simplified
   [u] as above. *)
let max_increment u =
  match Universe.repr u with
  | (l, n) :: rest when Level.is_set l -> n
  | l -> List.fold_left (fun m (_, n) -> max m (n + 1)) 0 l

let to_universe map u =
  let u = to_universe map u in
  simplify_sort u

(** Map from [n] to the global level standing for [Set+n] (not including n=0).
*)
let sets : Level.t Int.Map.t ref =
  Summary.ref ~name:"lean-set-surrogates" Int.Map.empty

type uconv = {
  map : extended_level N.Map.t;  (** Map from lean names to Coq universes *)
  levels : Level.t Universe.Map.t;
      (** Map from algebraic universes to levels (only levels representing an
          algebraic) *)
  direct : Level.Set.t;
      (** Named Lean levels that occur directly in universe instances. Levels
          that only occur below an algebraic successor do not need to be exposed
          as parameters of the translated declaration. *)
  graph : UGraph.t;
}

let lean_id = Id.of_string "Lean"

let { Goptions.get = lean_fancy_univs } =
  Goptions.declare_bool_option_and_ref
    ~key:[ "Lean"; "Fancy"; "Universes" ]
    ~value:true ()

let level_of_universe_core u =
  let u =
    List.map
      (fun (l, n) ->
        let open Level in
        if is_set l then "Set+" ^ string_of_int n
        else
          match name l with
          | None -> assert false
          | Some name ->
            let d, s, i = UGlobal.repr name in
            let d = DirPath.repr d in
            (match (d, i) with
            | [ name; l ], 0 when Id.equal l lean_id ->
              Id.to_string name ^ if n = 0 then "" else "+" ^ string_of_int n
            | _ -> to_string l))
      u
  in
  let s = (match u with [ _ ] -> "" | _ -> "max__") ^ String.concat "_" u in
  Level.(
    make (UGlobal.make (DirPath.make [ Id.of_string_soft s; lean_id ]) "" 0))

let level_of_universe u =
  let u = Universe.repr u in
  level_of_universe_core u

let level_of_universe u =
  if lean_fancy_univs () then level_of_universe u else UnivGen.fresh_level ()

let update_graph (l, u) (l', u') graph =
  if UGraph.check_leq graph (Universe.super u) u' then
    UGraph.enforce_constraint (l, Lt, l') graph
  else if UGraph.check_leq graph (Universe.super u') u then
    UGraph.enforce_constraint (l', Lt, l) graph
  else if UGraph.check_leq graph u u' then
    UGraph.enforce_constraint (l, Le, l') graph
  else if UGraph.check_leq graph u' u then
    UGraph.enforce_constraint (l', Le, l) graph
  else graph

let is_sets u =
  match Universe.repr u with
  | [ (u, n) ] -> if Level.is_set u then Some n else None
  | _ -> None

(** Find or add a global level for Set+n *)
let rec level_of_sets uconv n =
  if n = 0 then (uconv, Level.set)
  else
    try (uconv, Int.Map.find n !sets)
    with Not_found ->
      let uconv, p = level_of_sets uconv (n - 1) in
      let l =
        if lean_fancy_univs () then level_of_universe_core [ (Level.set, n) ]
        else UnivGen.fresh_level ()
      in
      Global.push_context_set
        (Level.Set.singleton l, UnivConstraints.singleton (p, Lt, l));
      sets := Int.Map.add n l !sets;
      let graph = add_universe l ~lbound:p uconv.graph in
      ({ uconv with graph }, l)

let to_univ_level u uconv =
  match Universe.level u with
  | Some l -> ({ uconv with direct = Level.Set.add l uconv.direct }, l)
  | None ->
    (match is_sets u with
    | Some n -> level_of_sets uconv n
    | None ->
      (match Universe.Map.find_opt u uconv.levels with
      | Some l -> (uconv, l)
      | None ->
        let uconv, mset = level_of_sets uconv (max_increment u) in
        let l = level_of_universe u in
        let graph = add_universe l ~lbound:mset uconv.graph in
        let graph =
          Universe.Map.fold
            (fun u' l' graph -> update_graph (l, u) (l', u') graph)
            uconv.levels graph
        in
        let graph =
          N.Map.fold
            (fun _ l' graph ->
              match l' with
              | LSProp -> graph
              | Level l' -> update_graph (l, u) (l', Universe.make l') graph)
            uconv.map graph
        in
        let uconv =
          { uconv with levels = Universe.Map.add u l uconv.levels; graph }
        in
        (uconv, l)))

(** Definitional height, used for unfolding heuristics.

    The definitional height is the longest sequence of constant unfoldings until
    we get a term without definitions (recursors don't count). *)

let height_cache = Summary.ref ~name:"lean-heights" N.Map.empty

(** Lean names whose translated definitions are non-forcing structural
    eliminators.  Rocq's conversion oracle should expose these before it tries
    to reduce their neutral arguments. *)
let expand_head_cache = Summary.ref ~name:"lean-expand-heads" N.Set.empty

let rec expands_at_head = function
  | Const (constant, _) -> N.Set.mem constant !expand_head_cache
  | App (function_, _) -> expands_at_head function_
  | Lam (_, _, _, body) -> expands_at_head body
  | Let { rest; _ } -> expands_at_head rest
  | Bound _ | Sort _ | Pi _ | Proj _ | Nat _ | String _ -> false

let rec height = function
  | Const (c, _) ->
    (try N.Map.find c !height_cache + 1
     with Not_found ->
       (* non constant, recursor, or just skipped *)
       0)
  | Bound _ | Sort _ -> 0
  | Lam (_, _, a, b) | Pi (_, _, a, b) | App (a, b) -> max (height a) (height b)
  | Let { name = _; ty; v; rest } -> max (height ty) (max (height v) (height rest))
  | Proj (_, _, c) -> height c
  | Nat _ | String _ -> 0

let height n body =
  match N.Map.find_opt n !height_cache with
  | Some h -> h
  | None ->
    let h = height body in
    height_cache := N.Map.add n h !height_cache;
    h

type instantiation = {
  ref : GlobRef.t;
  algs : Universe.t list;
      (** Full Rocq universe instance as algebraic universes over the Lean
          universe parameters. *)
}

let universe_var i = Universe.make (Level.var i)
let identity_algs n = List.init n universe_var

let non_sprop_univ_count nunivs i =
  let rec loop j acc =
    if j = nunivs then acc
    else
      let acc = if i land (1 lsl j) = 0 then acc + 1 else acc in
      loop (j + 1) acc
  in
  loop 0 0

(*
Lean classifies inductives in the following way:
- inductive landing in always >Prop (even when instantiated to all Prop) -> never squashed
- inductive which has Prop instantiation:
  + no constructor -> never squashed
  + multi constructor -> always squashed
  + 1 constructor
    * no non param arguments
      -> not squashed, special reduction
      typically [eq]
    * all arguments appear in the output type
      -> not squashed, basic reduction
      no real world examples? eg [Inductive foo : nat -> Prop := bar : forall x, foo x.]
      2019 "type theory of lean" implies that there should be special reduction
      but testing says otherwise
    * some arguments don't appear in the output type, but are Prop or recursive
      -> not squashed, basic reduction
      typically [Acc], [and]
    * some non-Prop non-recursive arguments (for some instantiation) don't appear in the output type
      -> squashed
      typically [exists]

Additionally, the recursor is always dependent (since Lean 4)
(this implem detail isn't in the TTofLean paper)
Special reduction also seems restricted to always-Prop types.

NB: in practice (all stdlib and mathlib) the target universe is available without reduction
(ie syntactic arity) even though the system doesn't require it.
so we can just look at it directly (we don't want to implement a reduction system)
Update: now we have correct Coq envs so we could reduce the Coq term?

Difference with Coq:
- a non-Prop instantiation of possibly Prop types will never be squashed
- non squashed possibly-Prop types at a Prop instantiation are squashed
  (unless empty or uip branch)
- we need uip for the special reduction.
  TTofLean sounds like we need an encoding with primitive records
  but testing indicates otherwise (all args in output type case).
- we will always need unsafe flags for [Acc], and possibly for [and].

Instantiating the type with all-Prop may side-effect instantiate
some other globals with Prop that won't actually be used
(assuming the inductive is not used with all-Prop)
This probably doesn't matter much, also if we start using upfront
instantiations it won't matter at all.

Primitive records:
Lean autodetects all record-capable types as having primitive
projections, and also autogenerates the eliminators.
Squashed Props with 1 ctor have primitive projections up to the first non-Prop field.
*)

type squashy = {
  maybe_prop : bool;  (** used for optim, not fundamental *)
  always_prop : bool;
      (** controls special reduction, but we just let Coq do its thing for that
      *)
  lean_squashes : bool;
      (** Self descriptive. We handle necessity of unsafe flags
          per-instantiation. *)
}

let noprop = { maybe_prop = false; always_prop = false; lean_squashes = false }

let pp_squashy { maybe_prop; always_prop; lean_squashes } =
  let open Pp in
  (if maybe_prop then
     if always_prop then str "is always Prop" else str "may be Prop"
   else str "is never Prop")
  ++ spc ()
  ++
  if lean_squashes then str "and is squashed by Lean"
  else str "and is not squashed by Lean"

let coq_squashes graph (entry : Entries.mutual_inductive_entry) =
  let env = Global.env () in
  let env = Environ.set_universes graph env in
  let ind =
    match entry.mind_entry_inds with [ ind ] -> ind | _ -> assert false
  in
  let params = entry.mind_entry_params in
  let ty = ind.mind_entry_arity in
  let env_params = Environ.push_rel_context params env in
  let _, s = Reduction.dest_arity env_params ty in
  (* TODO merge with uip branch *)
  if not (Sorts.is_sprop s) then false
  else
    match ind.mind_entry_lc with
    | [] -> false
    | _ :: _ :: _ -> true
    | [ c ] -> (match Constr.kind c with Rel _ | App _ -> false | _ -> true)

let with_env_evm rels uconv f x =
  (* In non upfront mode,
     because we interleave defining new constants as we encounter them,
     pushing rels and handling local universes,
     we pass just the rel_context_val and merge it with the global env and the uconv here *)
  let env = Global.env () in
  let env = Environ.set_rel_context_val rels env in
  let env = Environ.set_universes uconv.graph env in
  let evd = Evd.from_env env in
  f env evd x

let to_annot rels n t uconv =
  let r =
    with_env_evm rels uconv
      (fun env evd r ->
        let r = Retyping.relevance_of_type env evd r in
        EConstr.Unsafe.to_relevance r)
      (EConstr.of_constr t)
  in
  Context.make_annot (N.to_name n) r

(* bit n of [int_of_univs univs] is 1 iff [List.nth univs n] is SProp *)
let int_of_univs =
  let rec aux i acc = function
    | [] -> (i, acc)
    | u :: rest ->
      (match univ_of_sort u with
      | None -> aux ((i * 2) + 1) acc rest
      | Some u -> aux (i * 2) (u :: acc) rest)
  in
  fun l -> aux 0 [] (List.rev l)

let univ_of_name u =
  if lean_fancy_univs () then
    let u = DirPath.make [ N.to_id u; lean_id ] in
    Level.(make (UGlobal.make u "" 0))
  else UnivGen.fresh_level ()

let start_uconv univs i =
  let uconv =
    {
      graph = Global.universes ();
      map = N.Map.empty;
      levels = Universe.Map.empty;
      direct = Level.Set.empty;
    }
  in
  let uconv, set1 = level_of_sets uconv 1 in
  let rec aux uconv i = function
    | [] ->
      assert (i = 0);
      uconv
    | u :: univs ->
      let map, graph =
        if i mod 2 = 0 then
          let v = univ_of_name u in
          ( N.Map.add u (Level v) uconv.map,
            add_universe v ~lbound:set1 uconv.graph )
        else (N.Map.add u LSProp uconv.map, uconv.graph)
      in
      aux { uconv with map; graph } (i / 2) univs
  in
  aux uconv i univs

let univ_entry_gen ?(drop_global_lower_bounds = false)
    { map; levels; direct; graph } ounivs =
  let original_pairs =
    CList.map_filter
      (fun u ->
        let v = N.Map.get u map in
        match v with LSProp -> None | Level v -> Some (u, v))
      ounivs
  in
  let original_levels = List.map snd original_pairs in
  let original_instance =
    Instance.of_array ([||], Array.of_list original_levels)
  in
  let original_subst = snd (make_instance_subst original_instance) in
  let direct_pairs =
    List.filter (fun (_, l) -> Level.Set.mem l direct) original_pairs
  in
  let direct_set =
    List.fold_left
      (fun kept (_, l) -> Level.Set.add l kept)
      Level.Set.empty direct_pairs
  in
  let extra_pairs =
    Universe.Map.fold (fun alg l acc -> (alg, l) :: acc) levels [] |> List.rev
  in
  let decl_pairs =
    List.map (fun (u, l) -> (Some u, Universe.make l, l)) direct_pairs
    @ List.map (fun (alg, l) -> (None, alg, l)) extra_pairs
  in
  let univs = List.map (fun (_, _, l) -> l) decl_pairs in
  let uset =
    List.fold_left (fun kept l -> Level.Set.add l kept) Level.Set.empty univs
  in
  let kept = Level.Set.add Level.set uset in
  let kept = Int.Map.fold (fun _ -> Level.Set.add) !sets kept in
  let csts = UGraph.constraints_for ~kept graph in
  let csts =
    UnivConstraints.filter
      (fun (a, _, b) ->
        if drop_global_lower_bounds then
          (Level.Set.mem a uset && Level.Set.mem b uset)
          || Level.Set.mem a direct_set || Level.Set.mem b direct_set
        else Level.Set.mem a uset || Level.Set.mem b uset)
      csts
  in
  let unames =
    {
      quals = [||];
      univs =
        Array.of_list
          (List.map
             (function
               | Some u, _, _ -> N.to_name u
               | None, _, l -> Name (Id.of_string_soft (Level.to_string l)))
             decl_pairs);
    }
  in
  let univs_inst = Instance.of_array ([||], Array.of_list univs) in
  let uctx = UContext.make unames (univs_inst, PConstraints.of_univs csts) in
  let algs =
    List.map
      (fun (_, alg, _) ->
        simplify_universe (subst_univs_level_universe original_subst alg))
      decl_pairs
  in
  (uctx, algs)

let univ_entry a b =
  let uctx, algs = univ_entry_gen a b in
  ((UState.Polymorphic_entry uctx, UnivNames.empty_binders), algs)

(* TODO restrict univs (eg [has_add : Sort (u+1) -> Sort(u+1)] can
   drop the [u] and keep only the replacement for [u+1]??

   Preserve algebraics in codomain position? *)

let name_for_core n i =
  if i = 0 then N.to_id n
  else Id.of_string (N.to_coq_string n ^ "_inst" ^ string_of_int i)

(* NB collisions for constructors/recursors are still possible but
   should be rare *)
let name_for n i =
  let base = name_for_core n i in
  if not (Global.exists_objlabel base) then base
  else
    (* prevent resetting the number *)
    let base = if i = 0 then base else Id.of_string (Id.to_string base ^ "_") in
    Namegen.next_global_ident_away (Global.safe_env ()) base Id.Set.empty

let get_predeclared_ind indn n i =
  if N.equal n (N.append_list N.anon indn) then
    let ind_name = name_for_core n i in
    let reg = "lean." ^ Id.to_string ind_name in
    match Rocqlib.lib_ref reg with
    | IndRef (ind, 0) -> Some (ind_name, ind)
    | _ ->
      CErrors.user_err
        Pp.(
          str "Bad registration for "
          ++ str reg
          ++ str " expected an inductive.")
    | exception _ -> None
  else None

(** Like [get_predeclared_ind] but looks for an inductive predeclared as a
    definition (using a ".cumul" suffix on the registration). Returns the
    ConstRef of the predeclared definition. *)
let get_predeclared_ind_as_def indn n i =
  if N.equal n (N.append_list N.anon indn) then
    let ind_name = name_for_core n i in
    let reg = "lean." ^ Id.to_string ind_name ^ ".cumul" in
    match Rocqlib.lib_ref reg with
    | ConstRef c -> Some (ind_name, c)
    | _ ->
      CErrors.user_err
        Pp.(
          str "Bad registration for "
          ++ str reg
          ++ str " expected a constant.")
    | exception _ -> None
  else None

let get_predeclared_def defn n i =
  if N.equal n (N.append_list N.anon defn) then
    let def_name = name_for_core n i in
    let reg = "lean." ^ Id.to_string def_name in
    match Rocqlib.lib_ref reg with
    | ConstRef c -> Some (def_name, c)
    | _ ->
      CErrors.user_err
        Pp.(
          str "Bad registration for " ++ str reg ++ str " expected a constant.")
    | exception _ -> None
  else None

type predeclared_ind_kind = Eq | Nat | Nat_le | Or | And | Fin | UInt32 | BitVec | Char
type predeclared_def_kind = UInt32_size | Add | Mult | Pow | Nat_isValidChar
type predeclared_ind_as_def_kind = ULift_cumul

let get_predeclared_cnames (k : predeclared_ind_kind) n =
  match k with
  | Eq -> [ N.append n "refl" ]
  | Nat -> [ N.append n "zero"; N.append n "succ" ]
  | Nat_le -> [ N.append n "refl"; N.append n "step" ]
  | Or -> [ N.append n "inl"; N.append n "inr" ]
  | And -> [ N.append n "intro" ]
  | Fin -> [ N.append n "mk" ]
  | UInt32 -> [ N.append n "ofBitVec" ]
  | BitVec -> [ N.append n "ofFin" ]
  | Char -> [ N.append n "mk" ]

let get_predeclared_ind_any n i =
  List.filter_map
    (fun (indk, indh) ->
      get_predeclared_ind indh n i |> Option.map (fun x -> (indk, indh, x)))
    [
      (Eq, [ "Eq" ]);
      (Nat, [ "Nat" ]);
      (Nat_le, [ "Nat"; "le" ]);
      (Or, [ "Or" ]);
      (And, [ "And" ]);
      (Fin, [ "Fin" ]);
      (UInt32, [ "UInt32" ]);
      (BitVec, [ "BitVec" ]);
      (Char, [ "Char" ]);
    ]

let get_predeclared_ind_some n i =
  match get_predeclared_ind_any n i with
  | [] -> None
  | [ x ] -> Some x
  | _ :: _ :: _ ->
    CErrors.user_err
      Pp.(str "Multiple predeclared inductive types for " ++ N.pp n)

let get_predeclared_ind_as_def_any n i =
  List.filter_map
    (fun (k, h) ->
      get_predeclared_ind_as_def h n i |> Option.map (fun x -> (k, h, x)))
    [
      (ULift_cumul, [ "ULift" ]);
    ]

let get_predeclared_ind_as_def_some n i =
  match get_predeclared_ind_as_def_any n i with
  | [] -> None
  | [ x ] -> Some x
  | _ :: _ :: _ ->
    CErrors.user_err
      Pp.(str "Multiple predeclared ind-as-def constants for " ++ N.pp n)

let get_predeclared_def_any n i =
  List.filter_map
    (fun (defk, defh) ->
      get_predeclared_def defh n i |> Option.map (fun x -> (defk, defh, x)))
    [
      (UInt32_size, [ "UInt32"; "size" ]);
      (Add, [ "Nat"; "add" ]);
      (Mult, [ "Nat"; "mul" ]);
      (Pow, [ "Nat" ; "pow" ]);
      (Nat_isValidChar, [ "Nat"; "isValidChar" ]);
    ]

let get_predeclared_def_some n i =
  match get_predeclared_def_any n i with
  | [] -> None
  | [ x ] -> Some x
  | _ :: _ :: _ ->
    CErrors.user_err Pp.(str "Multiple predeclared constants for " ++ N.pp n)

(* let get_predeclared_eq n i = get_predeclared_ind "eq" n i *)
let mk_char_prim = "Char.mk.reflective_prim"

(*
Register Nat_isValidChar as lean.Nat_isValidChar.
Register reflective_Char_mk_prim as lean.Char.mk.reflective_prim. *)
(** For each name, the instantiation with all non-sprop univs should always be
    declared, but the instantiations with SProp may be lazily declared. We
    expect small instance lengths (experimentally at most 4 in the stdlib) so we
    represent instantiations as bit fields, bit n is 1 iff universe n is
    instantiated by SProp. *)
let declared : instantiation Int.Map.t N.Map.t ref =
  Summary.ref ~name:"lean-declared-instances" N.Map.empty

let entries : entry N.Map.t ref = Summary.ref ~name:"lean-entries" N.Map.empty

(** Every member points to its complete mutual block.  Keeping this separately
    from [entries] is necessary when a later SProp universe instance is
    requested: such an instance must be declared as the same mutual block, not
    as an isolated inductive. *)
let mutual_entries : ind list N.Map.t ref =
  Summary.ref ~name:"lean-mutual-entries" N.Map.empty

let squash_info : squashy N.Map.t ref =
  Summary.ref ~name:"lean-squash-info" N.Map.empty

type translated_mutual_inductive = {
  source_inductive : ind;
  translated_arity : Constr.t;
  constructor_names : N.t list;
  constructor_types : Constr.t list;
}

let mutual_group_index names name =
  let rec find i = function
    | [] -> None
    | name' :: names ->
      if N.equal name name' then Some i else find (i + 1) names
  in
  find 0 names

let remap_mutual_constructor ~nparams ~ntypes ~group_names ~current =
  let rec remap depth = function
    | Bound k when k = nparams + depth ->
      Bound (nparams + (ntypes - current - 1) + depth)
    | Const (name, univs) ->
      (match mutual_group_index group_names name with
      | Some target -> Bound (nparams + (ntypes - target - 1) + depth)
      | None -> Const (name, univs))
    | (Bound _ | Sort _ | Nat _ | String _) as expr -> expr
    | App (f, x) -> App (remap depth f, remap depth x)
    | Let { name; ty; v; rest } ->
      Let
        {
          name;
          ty = remap depth ty;
          v = remap depth v;
          rest = remap (depth + 1) rest;
        }
    | Lam (bk, name, ty, body) ->
      Lam (bk, name, remap depth ty, remap (depth + 1) body)
    | Pi (bk, name, ty, body) ->
      Pi (bk, name, remap depth ty, remap (depth + 1) body)
    | Proj (name, field, c) -> Proj (name, field, remap depth c)
  in
  remap 0

type projection_alias = {
  projection_inst : instantiation;
  projection_record : N.t;
  projection_ind : Names.inductive;
  projection_field : int;
}

let projection_aliases : projection_alias Int.Map.t N.Map.t ref =
  Summary.ref ~name:"lean-projection-aliases" N.Map.empty

let add_projection_alias name instance alias =
  projection_aliases :=
    N.Map.update name
      (function
        | None -> Some (Int.Map.singleton instance alias)
        | Some aliases -> Some (Int.Map.add instance alias aliases))
      !projection_aliases

let find_projection_alias name instance =
  Option.bind (N.Map.find_opt name !projection_aliases) (fun aliases ->
      Int.Map.find_opt instance aliases)

let find_projection_alias_for_universes uconv name universes =
  let sorts = List.map (to_universe uconv.map) universes in
  let instance, _ = int_of_univs sorts in
  find_projection_alias name instance

let rec is_projection_wrapper record field = function
  | Lam (_, _, _, body) -> is_projection_wrapper record field body
  | Proj (projected_record, projected_field, Bound 0) ->
    N.equal record projected_record && Int.equal field projected_field
  | _ -> false

let add_declared n i inst =
  declared :=
    N.Map.update n
      (function
        | None -> Some (Int.Map.singleton i inst)
        | Some m -> Some (Int.Map.add i inst m))
      !declared

let to_univ_level' u uconv =
  match to_universe uconv.map u with
  | SProp -> (uconv, LSProp)
  | Type u | GSort (_, u) | VSort (_, u) ->
    let uconv, u = to_univ_level u uconv in
    (uconv, Level u)
  | Set -> (uconv, Level Level.set)
  | Prop -> assert false

let empty_env = Environ.empty_rel_context_val
let default_proj_id = Id.of_string "default_proj_id"

type error_mode = Skip | Stop | Fail

let { Goptions.get = error_mode } =
  let print = function Skip -> "Skip" | Stop -> "Stop" | Fail -> "Fail" in
  let interp = function
    | "Skip" -> Skip
    | "Stop" -> Stop
    | "Fail" -> Fail
    | s ->
      CErrors.user_err Pp.(str "Unknown error mode " ++ qstring s ++ str ".")
  in
  Goptions.declare_interpreted_string_option_and_ref ~stage:Interp
    ~key:[ "Lean"; "Error"; "Mode" ]
    ~value:Fail interp print ()

exception MissingQuot

let { Goptions.get = skip_missing_quot } =
  Goptions.declare_bool_option_and_ref ~stage:Interp
    ~key:[ "Lean"; "Skip"; "Missing"; "Quotient" ]
    ~value:true ()

let error_mode = function
  | MissingQuot when skip_missing_quot () -> Skip
  | _ -> error_mode ()

module ZMap = CMap.Make (Z)

let nat_ints = ref ZMap.empty
let max_known_int = ref (Z.pred Z.zero)

let one_more_int nat =
  let i = Z.succ !max_known_int in
  let c =
    if Z.equal i Z.zero then Constr.mkConstructU ((nat, 1), UVars.Instance.empty)
    else
      let cpred = ZMap.get !max_known_int !nat_ints in
      Constr.(
        mkApp (mkConstructU ((nat, 2), UVars.Instance.empty), [| cpred |]))
  in
  nat_ints := ZMap.add i c !nat_ints;
  max_known_int := i

let max_nat_int = Z.of_string "5000"

let registered_ref key =
  Constr.mkRef (Rocqlib.lib_ref key, UVars.Instance.empty)

let rec positive_int i =
  assert (Z.lt Z.zero i);
  if Z.equal i Z.one then registered_ref "num.pos.xH"
  else
    let constructor =
      if Z.equal (Z.rem i (Z.of_int 2)) Z.zero then "num.pos.xO"
      else "num.pos.xI"
    in
    Constr.mkApp
      (registered_ref constructor, [| positive_int (Z.div i (Z.of_int 2)) |])

let n_int i =
  assert (Z.leq Z.zero i);
  if Z.equal i Z.zero then registered_ref "num.N.N0"
  else
    Constr.mkApp (registered_ref "num.N.Npos", [| positive_int i |])

let nat_int nat nat_of_n i =
  assert (Z.leq Z.zero i);
  if Z.leq max_nat_int i then Constr.mkApp (nat_of_n, [| n_int i |])
  else begin
    while Z.lt !max_known_int i do
      one_more_int nat
    done;
    ZMap.get i !nat_ints
  end

(* Decode a UTF-8 string into a list of valid codepoints, with error reporting for bad characters *)
(* let string_to_codepoints s =
  (* Create a UTF-8 decoder for the input string *)
  let decoder = Uutf.decoder ~encoding:`UTF_8 (`String s) in

  (* Define the condition for filtering codepoints *)
  let is_valid_codepoint n = n < 0xd800 || (0xdfff < n && n < 0x110000) in

  (* Decode the string and collect valid codepoints *)
  let rec collect_codepoints acc =
    match Uutf.decode decoder with
    | `Uchar u when is_valid_codepoint (Uchar.to_int u) ->
      collect_codepoints (Uchar.to_int u :: acc)
    | `Uchar u when Uchar.to_int u >= 0x110000 ->
      (* Raise an exception with the problematic character *)
      let bad_char = Printf.sprintf "U+%04X" (Uchar.to_int u) in
      failwith (Printf.sprintf "Invalid codepoint (>= 0x110000): %s" bad_char)
    | `Uchar u when Uchar.to_int u >= 0xd800 && 0xdfff >= Uchar.to_int u ->
      (* Raise an exception with the problematic character *)
      let bad_char = Printf.sprintf "U+%04X" (Uchar.to_int u) in
      failwith
        (Printf.sprintf "Invalid codepoint (u >= 0xd800 && 0xdfff >= u): %s"
           bad_char)
    | `Uchar _ -> assert false
    | `End -> List.rev acc
    | `Malformed s ->
      (* Handle malformed UTF-8 sequences *)
      failwith (Printf.sprintf "Malformed UTF-8 sequence: %S" s)
    | `Await -> assert false (* This case should not occur for a string input *)
  in
  collect_codepoints [] *)

let string_to_codepoints str =
  let rec decode_utf8 s pos acc =
    if pos >= String.length s then List.rev acc
    else
      let c = Char.code (String.get s pos) in
      let n =
        if c < 0x80 then (1, c)
        else if c < 0xE0 then (2, c land 0x1F)
        else if c < 0xF0 then (3, c land 0x0F)
        else (4, c land 0x07)
      in
      let bytes, value = n in
      let code_point = ref value in
      for i = 1 to bytes - 1 do
        let next_byte = Char.code (String.get s (pos + i)) in
        code_point := (!code_point lsl 6) lor (next_byte land 0x3F)
      done;
      decode_utf8 s (pos + bytes) (!code_point :: acc)
  in
  decode_utf8 str 0 []

let check_valid_codepoints cs =
  List.map
    (fun c ->
      if c < 0xd800 || (0xdfff < c && c < 0x110000) then c
      else
        let bad_char = Printf.sprintf "U+%04X" c in
        CErrors.user_err
          Pp.(str (Printf.sprintf "Invalid codepoint: %s" bad_char)))
    cs

let mk_char mkChar (c : int) =
  Constr.(mkApp (mkChar, [| mkInt (Uint63.of_int c) |]))

let mk_list list uinst ty l =
  let cNil = Constr.(mkApp (mkConstructU ((list, 1), uinst), [| ty |])) in
  let cCons = Constr.mkConstructU ((list, 2), uinst) in
  let rec mk_list_rec l =
    match l with
    | [] -> cNil
    | hd :: tl -> Constr.mkApp (cCons, [| ty; hd; mk_list_rec tl |])
  in
  mk_list_rec l

let mk_string char list char_uinst mkChar string_of_chars s =
  let codepoints =
    try check_valid_codepoints (string_to_codepoints s)
    with Failure msg as exn ->
      let _, info = Exninfo.capture exn in
      CErrors.user_err ~info Pp.(str msg)
  in
  let chars = List.map (mk_char mkChar) codepoints in
  let ls = mk_list list char_uinst char chars in
  Constr.mkApp (string_of_chars, [| ls |])

(* [c] has type [indu] applied to [args] *)
let unfold_proj_case env evd ~field ~indu ~mib ~mip ~args c =
  let ind = fst indu in
  let npar = mib.Declarations.mind_nparams in
  let ntypes = Declareops.mind_ntypes mib in
  let u = snd indu in
  let ind_subst =
    List.init ntypes (fun i -> Constr.mkIndU ((fst ind, ntypes - i - 1), u))
  in
  let ctx, cty0 = mip.Declarations.mind_nf_lc.(0) in
  let cty_full = Term.it_mkProd_or_LetIn cty0 ctx in
  let rctx, _ = Term.decompose_prod_decls (Vars.substl ind_subst cty_full) in
  let ctor_ctx, _paramslet = CList.chop mip.mind_consnrealdecls.(0) rctx in
  let nargs = mip.mind_consnrealdecls.(0) in
  let ci =
    {
      Constr.ci_ind = ind;
      ci_npar = npar;
      ci_cstr_ndecls = mip.mind_consnrealdecls;
      ci_cstr_nargs = mip.mind_consnrealargs;
      ci_pp_info = { style = LetStyle };
    }
  in
  let params = Array.map EConstr.Unsafe.to_constr (Array.sub args 0 npar) in
  let self_annot = Context.make_annot Name.Anonymous mip.mind_relevance in
  let self_ty =
    Constr.mkApp
      (Constr.mkIndU indu, Array.map EConstr.Unsafe.to_constr args)
  in
  let env_self =
    Environ.push_rel
      (Context.Rel.Declaration.LocalAssum (self_annot, self_ty)) env
  in
  let make_case ~params ~field ~ret_ty c =
    let case_relev =
      EConstr.Unsafe.to_relevance
        (Retyping.relevance_of_type env_self evd (EConstr.of_constr ret_ty))
    in
    let p = ([| self_annot |], ret_ty) in
    let branch_nas =
      Array.of_list (List.rev_map Context.Rel.Declaration.get_annot ctor_ctx)
    in
    let branch = (branch_nas, Constr.mkRel (nargs - field)) in
    Constr.mkCase
      (ci, u, params, (p, case_relev), Constr.NoInvert, c, [| branch |])
  in
  let params_self = Array.map (Vars.lift 1) params in
  let ret_ty =
    let ctor = Constr.mkConstructU (((fst ind, 0), 1), u) in
    let ctor_applied = Constr.mkApp (ctor, params) in
    let rec get_field_type i ty =
      match Constr.kind ty with
      | Constr.Prod (_, t, rest) ->
        if i = field then t
        else
          let previous =
            make_case ~params:params_self ~field:i ~ret_ty:t (Constr.mkRel 1)
          in
          get_field_type (i + 1) (Vars.subst1 previous rest)
      | _ -> assert false
    in
    let ctor_ty =
      Retyping.get_type_of env evd (EConstr.of_constr ctor_applied)
    in
    let ctor_ty =
      EConstr.Unsafe.to_constr (Reductionops.whd_all env evd ctor_ty)
    in
    get_field_type 0 (Vars.lift 1 ctor_ty)
  in
  make_case ~params ~field ~ret_ty c

let lcnt = ref 0

let line_msg name =
  Feedback.msg_info Pp.(str "line " ++ int !lcnt ++ str ": " ++ N.pp name)

let list_name = N.append N.anon "List"
let option_name = N.append N.anon "Option"
let array_name = N.append N.anon "Array"
let prod_name = N.append N.anon "Prod"

let array_minds : MutInd.t list ref =
  Summary.ref ~name:"lean-array-minds" []

let prod_minds : MutInd.t list ref =
  Summary.ref ~name:"lean-prod-minds" []

let list_minds : MutInd.t list ref =
  Summary.ref ~name:"lean-list-minds" []

let option_minds : MutInd.t list ref =
  Summary.ref ~name:"lean-option-minds" []

type mutual_nested_focus = MutualMain of int | MutualAux of int

type mutual_nested_rec_info = {
  base_recs : N.t list;
  mind : MutInd.t;
  nparams : int;
  focus : mutual_nested_focus;
}

let mutual_nested_rec_info : mutual_nested_rec_info N.Map.t ref =
  Summary.ref ~name:"lean-mutual-nested-recursor-info" N.Map.empty

let register_mutual_nested_recursors ~mind ~nparams names =
  let base_recs = List.map (fun name -> N.append name "rec") names in
  List.iteri
    (fun index base_rec ->
      mutual_nested_rec_info :=
        N.Map.add base_rec
          { base_recs; mind; nparams; focus = MutualMain index }
          !mutual_nested_rec_info)
    base_recs

let find_mutual_nested_rec_info name =
  match N.Map.find_opt name !mutual_nested_rec_info with
  | Some _ as info -> info
  | None -> (
    match N.unappend name with
    | Some (parent, component)
      when String.starts_with ~prefix:"rec_" component ->
      let index_start = String.length "rec_" in
      let index_length = String.length component - index_start in
      let index =
        try
          let index =
            int_of_string
              (String.sub component index_start index_length)
          in
          if index > 0 then Some (index - 1) else None
        with Failure _ -> None
      in
      Option.bind index (fun index ->
          let base_rec = N.append parent "rec" in
          Option.map
            (fun info -> { info with focus = MutualAux index })
            (N.Map.find_opt base_rec !mutual_nested_rec_info))
    | None | Some _ -> None)

let append_array a b = Array.append a b

let extended_all_uctx source_uctx =
  let source_inst = UContext.instance source_uctx in
  let source_names = UContext.names source_uctx in
  let qinst, uinst = Instance.to_array source_inst in
  let q = Sorts.Quality.var (Array.length qinst) in
  let u = Level.var (Array.length uinst) in
  let names =
    {
      quals = append_array source_names.quals [| Name (Id.of_string "s") |];
      univs = append_array source_names.univs [| Name (Id.of_string "motive") |];
    }
  in
  let inst =
    Instance.of_array
      (append_array qinst [| q |], append_array uinst [| u |])
  in
  ( UContext.make names (inst, UContext.constraints source_uctx),
    source_inst,
    q,
    u )

let qsort q u = Constr.mkSort (Sorts.make q u)

let reln n = Constr.mkRel n

let app f args = Constr.mkApp (f, Array.of_list args)

let annot_for_type env name ty =
  let evd = Evd.from_env env in
  let relevance =
    Retyping.relevance_of_type env evd (EConstr.of_constr ty)
    |> EConstr.Unsafe.to_relevance
  in
  Context.make_annot name relevance

let push_typed_assum env name ty =
  Environ.push_rel
    (RelDecl.LocalAssum (annot_for_type env name ty, ty))
    env

let typed_prod env name ty body =
  Constr.mkProd (annot_for_type env name ty, ty, body)

let rec typed_lambdas env binders body =
  match binders with
  | [] -> body
  | (name, ty) :: rest ->
    let annot = annot_for_type env name ty in
    let env = Environ.push_rel (RelDecl.LocalAssum (annot, ty)) env in
    Constr.mkLambda (annot, ty, typed_lambdas env rest body)

let mk_global_ref ref inst = Constr.mkRef (ref, inst)

let all_name ind_name = Id.of_string (Id.to_string ind_name ^ "_all")
let all_forall_name ind_name =
  Id.of_string (Id.to_string ind_name ^ "_all_forall")

let dest_nested_ind_app c =
  let hd, args = Constr.decompose_app c in
  match Constr.kind hd with
  | Ind (ind, inst) -> Some (ind, inst, args)
  | _ -> None

let declare_array_all_scheme mind ind_name source_uctx fields projections =
  match (fields, projections) with
  | [ (_, field_ty) ], [ { Structures.Structure.proj_body = Some proj_c; _ } ] -> (
    match dest_nested_ind_app (EConstr.Unsafe.to_constr field_ty) with
    | Some (list_ind, list_inst, field_args) when Array.length field_args = 1 -> (
      match
        ( DeclareScheme.lookup_scheme_opt "All" (GlobRef.IndRef list_ind),
          DeclareScheme.lookup_scheme_opt "AllForall" (GlobRef.IndRef list_ind) )
      with
      | Some list_all_ref, Some list_all_forall_ref ->
        let all_uctx, source_inst, q, motive_level =
          extended_all_uctx source_uctx
        in
        let motive_univ = Universe.make motive_level in
        let a_ty =
          let params = (Global.lookup_mind mind).mind_params_ctxt in
          match params with
          | [ RelDecl.LocalAssum (_, ty) ] -> ty
          | _ -> Constr.mkSet
        in
        let motive_sort = qsort q motive_univ in
        let qinst, uinst = Instance.to_array list_inst in
        let list_all_inst =
          Instance.of_array
            ( append_array qinst [| q |],
              append_array uinst [| motive_level |] )
        in
        let list_all = mk_global_ref list_all_ref list_all_inst in
        let list_all_forall = mk_global_ref list_all_forall_ref list_all_inst in
        let array_ref = Constr.mkIndU ((mind, 0), source_inst) in
        let proj_ref = Constr.mkConstU (proj_c, source_inst) in
        let array_a rel_a = app array_ref [ reln rel_a ] in
        let proj_a rel_a rel_arr = app proj_ref [ reln rel_a; reln rel_arr ] in
        let scheme_env = Environ.push_context all_uctx (Global.env ()) in
        let a_name = Name (Id.of_string "A") in
        let p_name = Name (Id.of_string "P") in
        let x_name = Name (Id.of_string "x") in
        let value_name = Name (Id.of_string "a") in
        let env_a = push_typed_assum scheme_env a_name a_ty in
        let motive_ty = typed_prod env_a x_name (reln 1) motive_sort in
        let env_ap = push_typed_assum env_a p_name motive_ty in
        let forall_ty =
          typed_prod env_ap x_name (reln 2) (app (reln 2) [ reln 1 ])
        in
        let all_body =
          let body = app list_all [ reln 3; reln 2; proj_a 3 1 ] in
          typed_lambdas scheme_env
            [ (a_name, a_ty); (p_name, motive_ty); (value_name, array_a 2) ]
            body
        in
        let univs = (UState.Polymorphic_entry all_uctx, UnivNames.empty_binders) in
        let all_c =
          quickdef ~name:(all_name ind_name) ~types:None ~univs all_body
        in
        DeclareScheme.declare_scheme Libobject.SuperGlobal "All"
          (GlobRef.IndRef (mind, 0), all_c);
        let forall_body =
          let body =
            app list_all_forall [ reln 4; reln 3; reln 2; proj_a 4 1 ]
          in
          typed_lambdas scheme_env
            [
              (a_name, a_ty);
              (p_name, motive_ty);
              (Name (Id.of_string "h"), forall_ty);
              (value_name, array_a 3);
            ]
            body
        in
        let forall_c =
          quickdef ~name:(all_forall_name ind_name) ~types:None ~univs forall_body
        in
        DeclareScheme.declare_scheme Libobject.SuperGlobal "AllForall"
          (GlobRef.IndRef (mind, 0), forall_c)
      | _ -> ())
    | _ -> ())
  | _ -> ()

let declare_prod_second_all_scheme mind ind_name source_uctx projections =
  match projections with
  | [ _; { Structures.Structure.proj_body = Some snd_c; _ } ] ->
    let all_uctx, source_inst, q, motive_level =
      extended_all_uctx source_uctx
    in
    let motive_univ = Universe.make motive_level in
    let motive_sort = qsort q motive_univ in
    let params = (Global.lookup_mind mind).mind_params_ctxt in
    let a_ty, b_ty =
      match params with
      | [ RelDecl.LocalAssum (_, b_ty); RelDecl.LocalAssum (_, a_ty) ] ->
        (a_ty, b_ty)
      | _ -> (Constr.mkSet, Constr.mkSet)
    in
    let prod_ref = Constr.mkIndU ((mind, 0), source_inst) in
    let snd_ref = Constr.mkConstU (snd_c, source_inst) in
    let scheme_env = Environ.push_context all_uctx (Global.env ()) in
    let a_name = Name (Id.of_string "A") in
    let b_name = Name (Id.of_string "B") in
    let p_name = Name (Id.of_string "P") in
    let x_name = Name (Id.of_string "x") in
    let value_name = Name (Id.of_string "p") in
    let env_a = push_typed_assum scheme_env a_name a_ty in
    let env_ab = push_typed_assum env_a b_name b_ty in
    let motive_ty =
      typed_prod env_ab x_name (reln 1) motive_sort
    in
    let env_abp = push_typed_assum env_ab p_name motive_ty in
    let forall_ty =
      typed_prod env_abp x_name (reln 2) (app (reln 2) [ reln 1 ])
    in
    let prod_ab rel_a rel_b = app prod_ref [ reln rel_a; reln rel_b ] in
    let snd_abp rel_a rel_b rel_p =
      app snd_ref [ reln rel_a; reln rel_b; reln rel_p ]
    in
    let all_body =
      typed_lambdas scheme_env
        [
          (a_name, a_ty);
          (b_name, b_ty);
          (p_name, motive_ty);
          (value_name, prod_ab 3 2);
        ]
        (app (reln 2) [ snd_abp 4 3 1 ])
    in
    let univs =
      (UState.Polymorphic_entry all_uctx, UnivNames.empty_binders)
    in
    let all_c =
      quickdef ~name:(Id.of_string (Id.to_string ind_name ^ "_all_01"))
        ~types:None ~univs all_body
    in
    DeclareScheme.declare_scheme Libobject.SuperGlobal "All_01"
      (GlobRef.IndRef (mind, 0), all_c);
    let all_forall_body =
      typed_lambdas scheme_env
        [
          (a_name, a_ty);
          (b_name, b_ty);
          (p_name, motive_ty);
          (Name (Id.of_string "h"), forall_ty);
          (value_name, prod_ab 4 3);
        ]
        (app (reln 2) [ snd_abp 5 4 1 ])
    in
    let all_forall_c =
      quickdef
        ~name:
          (Id.of_string (Id.to_string ind_name ^ "_all_forall_01"))
        ~types:None ~univs all_forall_body
    in
    DeclareScheme.declare_scheme Libobject.SuperGlobal "AllForall_01"
      (GlobRef.IndRef (mind, 0), all_forall_c)
  | _ -> ()

let projection_parameter_usage source_uctx = function
  | { Structures.Structure.proj_body = Some field_c; _ } ->
    let env = Environ.push_context source_uctx (Global.env ()) in
    let evd = Evd.from_env env in
    let field_ref = Constr.mkConstU (field_c, UContext.instance source_uctx) in
    let field_ty =
      EConstr.Unsafe.to_constr
        (Retyping.get_type_of env evd (EConstr.of_constr field_ref))
    in
    let whd env term =
      EConstr.Unsafe.to_constr
        (Reductionops.whd_all env evd (EConstr.of_constr term))
    in
    (match Constr.kind (whd env field_ty) with
    | Constr.Prod (param_annot, param_ty, body) ->
      let env =
        Environ.push_rel (RelDecl.LocalAssum (param_annot, param_ty)) env
      in
      (match Constr.kind (whd env body) with
      | Constr.Prod (value_annot, value_ty, result_ty) ->
        let env =
          Environ.push_rel
            (RelDecl.LocalAssum (value_annot, value_ty))
            env
        in
        Some
          ( Reductionops.is_conv env evd
              (EConstr.of_constr result_ty)
              (EConstr.of_constr (Constr.mkRel 2)),
            not (Vars.noccurn 2 result_ty) )
      | _ -> None)
    | _ -> None)
  | _ -> None

let last_projection_is_only_parameter_use mind source_uctx projections =
  match
    ((Global.lookup_mind mind).mind_params_ctxt, List.rev projections)
  with
  | [ RelDecl.LocalAssum _ ], last :: previous -> (
    match projection_parameter_usage source_uctx last with
    | Some (true, _) ->
      List.for_all
        (fun projection ->
          match projection_parameter_usage source_uctx projection with
          | Some (_, false) -> true
          | Some (_, true) | None -> false)
        previous
    | Some (false, _) | None -> false)
  | _ -> false

let declare_last_field_all_scheme mind ind_name source_uctx projections =
  match List.rev projections with
  | { Structures.Structure.proj_body = Some field_c; _ } :: _ -> (
    match (Global.lookup_mind mind).mind_params_ctxt with
    | [ RelDecl.LocalAssum (a_na, a_ty) ] ->
      let all_uctx, source_inst, q, motive_level =
        extended_all_uctx source_uctx
      in
      let motive_univ = Universe.make motive_level in
      let motive_sort = qsort q motive_univ in
      let ind_ref = Constr.mkIndU ((mind, 0), source_inst) in
      let field_ref = Constr.mkConstU (field_c, source_inst) in
      let scheme_env = Environ.push_context all_uctx (Global.env ()) in
      let a_name = a_na.Context.binder_name in
      let p_name = Name (Id.of_string "P") in
      let x_name = Name (Id.of_string "x") in
      let value_name = Name (Id.of_string "value") in
      let env_a = push_typed_assum scheme_env a_name a_ty in
      let motive_ty =
        typed_prod env_a x_name (reln 1) motive_sort
      in
      let env_ap = push_typed_assum env_a p_name motive_ty in
      let forall_ty =
        typed_prod env_ap x_name (reln 2) (app (reln 2) [ reln 1 ])
      in
      let ind_a rel_a = app ind_ref [ reln rel_a ] in
      let field_ap rel_a rel_p = app field_ref [ reln rel_a; reln rel_p ] in
      let all_body =
        typed_lambdas scheme_env
          [ (a_name, a_ty); (p_name, motive_ty); (value_name, ind_a 2) ]
          (app (reln 2) [ field_ap 3 1 ])
      in
      let univs =
        (UState.Polymorphic_entry all_uctx, UnivNames.empty_binders)
      in
      let all_c =
        quickdef ~name:(all_name ind_name) ~types:None ~univs all_body
      in
      DeclareScheme.declare_scheme Libobject.SuperGlobal "All"
        (GlobRef.IndRef (mind, 0), all_c);
      let all_forall_body =
        typed_lambdas scheme_env
          [
            (a_name, a_ty);
            (p_name, motive_ty);
            (Name (Id.of_string "h"), forall_ty);
            (value_name, ind_a 3);
          ]
          (app (reln 2) [ field_ap 4 1 ])
      in
      let all_forall_c =
        quickdef ~name:(all_forall_name ind_name) ~types:None ~univs
          all_forall_body
      in
      DeclareScheme.declare_scheme Libobject.SuperGlobal "AllForall"
        (GlobRef.IndRef (mind, 0), all_forall_c)
    | _ -> ())
  | _ -> ()

let rec decompose_lean_app acc = function
  | App (f, x) -> decompose_lean_app (x :: acc) f
  | head -> (head, acc)

let constr_app f args =
  match args with [] -> f | _ -> Constr.mkApp (f, Array.of_list args)

let whd_constr env evd c =
  EConstr.Unsafe.to_constr
    (Reductionops.whd_all env evd (EConstr.of_constr c))

let type_of_constr env evd term =
  EConstr.Unsafe.to_constr
    (Retyping.get_type_of env evd (EConstr.of_constr term))

let whd_type_of_constr env evd term =
  whd_constr env evd (type_of_constr env evd term)

let anon_annot_for_type env evd ty =
  Context.make_annot Name.Anonymous
    (EConstr.Unsafe.to_relevance
       (Retyping.relevance_of_type env evd (EConstr.of_constr ty)))

let prod_domain env evd ty =
  match Constr.kind (whd_constr env evd ty) with
  | Prod (_, domain, _) -> domain
  | _ -> CErrors.user_err Pp.(str "Nested recursor is over-applied")

let prod_after_apply env evd ty arg =
  match Constr.kind (whd_constr env evd ty) with
  | Prod (_, _, body) -> Vars.subst1 arg body
  | _ -> CErrors.user_err Pp.(str "Nested recursor is over-applied")

let prod_parts env evd prod =
  let prod_ty = whd_type_of_constr env evd prod in
  let prod_head, _ = Constr.decompose_app prod_ty in
  let prod_ind =
    match Constr.kind prod_head with
    | Ind (ind, _) -> ind
    | _ -> CErrors.user_err Pp.(str "Nested recursor target is not a Prod")
  in
  let mib = Global.lookup_mind (fst prod_ind) in
  let fst_p, fst_r =
    Declareops.inductive_make_projection prod_ind mib ~proj_arg:0
  in
  let snd_p, snd_r =
    Declareops.inductive_make_projection prod_ind mib ~proj_arg:1
  in
  ( Constr.mkProj (Projection.make fst_p false, fst_r, prod),
    Constr.mkProj (Projection.make snd_p false, snd_r, prod) )

let require_recursive_prod_second env evd mind fst snd =
  let recursive term = has_rec_hyp env mind (type_of_constr env evd term) in
  match (recursive fst, recursive snd) with
  | false, true -> ()
  | true, false ->
    CErrors.user_err
      Pp.(str "Nested recursion through the first component of Prod is unsupported")
  | true, true ->
    CErrors.user_err
      Pp.(str "Nested recursion through both components of Prod is unsupported")
  | false, false ->
    CErrors.user_err Pp.(str "Nested Prod has no recursive component")

type mutual_aux_spec = {
  aux_domain : Constr.t;
  aux_motive : Constr.t;
  aux_cases : Constr.t list;
}

let mind_is_one_of mind minds =
  List.exists (MutInd.UserOrd.equal mind) minds

let is_unary_container_mind mind =
  mind_is_one_of mind !array_minds
  || mind_is_one_of mind !list_minds
  || mind_is_one_of mind !option_minds

let type_head_ind env evd ty =
  let ty = whd_constr env evd ty in
  let head, args = Constr.decompose_app ty in
  match Constr.kind head with
  | Constr.Ind (ind, inst) -> Some (ind, inst, args)
  | _ -> None

let motive_domain env evd motive =
  let ty = type_of_constr env evd motive in
  match Constr.kind (whd_constr env evd ty) with
  | Constr.Prod (_, domain, _) -> Some domain
  | _ -> None

let convertible env evd a b =
  Reductionops.is_conv env evd (EConstr.of_constr a) (EConstr.of_constr b)

let same_inductive_head env evd a b =
  match (type_head_ind env evd a, type_head_ind env evd b) with
  | Some ((a_mind, a_index), _, _), Some ((b_mind, b_index), _, _) ->
    a_index = b_index && MutInd.UserOrd.equal a_mind b_mind
  | _ -> false

let find_aux_spec env evd target_ty specs =
  match
    List.find_opt
      (fun spec -> convertible env evd target_ty spec.aux_domain)
      specs
  with
  | Some _ as spec -> spec
  | None -> (
    match
      List.filter
        (fun spec -> same_inductive_head env evd target_ty spec.aux_domain)
        specs
    with
    | [ spec ] -> Some spec
    | [] | _ :: _ :: _ -> None)

let aux_ctor_count env evd domain =
  match type_head_ind env evd domain with
  | Some ((mind, index), _, _) ->
    Some
      (Array.length
         (Global.lookup_mind mind).mind_packets.(index).mind_consnames)
  | None -> None

let all_rect env evd all_ind all_inst motive_at_target =
  let result_ty = type_of_constr env evd motive_at_target in
  let result_sort = whd_constr env evd result_ty in
  let result_sort =
    match Constr.kind result_sort with
    | Constr.Sort sort -> sort
    | _ -> CErrors.user_err Pp.(str "Nested motive does not return a sort")
  in
  let _, rect =
    Indrec.build_induction_scheme env evd
      (all_ind, EConstr.EInstance.make all_inst)
      true (EConstr.ESorts.make result_sort)
  in
  EConstr.Unsafe.to_constr rect

(** Convert the [All] evidence produced by Rocq's nested schemes into the
    corresponding Lean auxiliary motive. *)
type all_proof_view = {
  all_ind : Names.inductive;
  all_inst : Instance.t;
  all_element : Constr.t;
  all_predicate : Constr.t;
}

let view_all_proof env evd container proof =
  let proof_ty = whd_type_of_constr env evd proof in
  let head, args = Constr.decompose_app proof_ty in
  match Constr.kind head with
  | Ind (all_ind, all_inst) when Array.length args = 3 ->
    {
      all_ind;
      all_inst;
      all_element = args.(0);
      all_predicate = args.(1);
    }
  | _ ->
    CErrors.user_err
      Pp.(str "Nested " ++ str container ++ str " proof is not an All proof")

type unary_target_view = {
  unary_ind : Names.inductive;
  unary_inst : Instance.t;
  unary_element : Constr.t;
}

let view_unary_target env evd description target =
  let unary_type = whd_type_of_constr env evd target in
  match type_head_ind env evd unary_type with
  | Some (unary_ind, unary_inst, args) when Array.length args = 1 ->
    { unary_ind; unary_inst; unary_element = args.(0) }
  | _ ->
    CErrors.user_err
      Pp.(str "Malformed auxiliary " ++ str description ++ str " target")

type nested_leaf_state = RawLeaves | FoldedLeaves

let rec fold_mutual_nested env evd ~depth ~leaf_state mind specs target
    proof =
  let open Constr in
  let target_ty = whd_type_of_constr env evd target in
  match type_head_ind env evd target_ty with
  | Some ((target_mind, _), _, _)
    when MutInd.UserOrd.equal target_mind mind -> proof
  | Some (((target_mind, target_index) as target_ind), _, _) ->
    let spec =
      match find_aux_spec env evd target_ty specs with
      | Some spec -> spec
      | None ->
        CErrors.user_err
          Pp.(
            str "No nested motive matches recursive constructor argument "
            ++ Printer.pr_constr_env env evd target_ty
            ++ str "; candidates: "
            ++ prlist_with_sep (fun () -> str ", ")
                 (fun spec ->
                   Printer.pr_constr_env env evd spec.aux_domain)
                 specs)
    in
    let motive = Vars.lift depth spec.aux_motive in
    let cases = List.map (Vars.lift depth) spec.aux_cases in
    if mind_is_one_of target_mind !array_minds then
      let target_head, _ = Constr.decompose_app target_ty in
      let array_ind, _ = Constr.destInd target_head in
      let array_mib = Global.lookup_mind (fst array_ind) in
      let projection, relevance =
        Declareops.inductive_make_projection array_ind array_mib ~proj_arg:0
      in
      let list =
        mkProj (Projection.make projection false, relevance, target)
      in
      let folded =
        fold_mutual_nested env evd ~depth ~leaf_state mind specs list
          proof
      in
      (match cases with
      | [ array_case ] -> constr_app array_case [ list; folded ]
      | _ -> CErrors.user_err Pp.(str "Nested Array has unexpected cases"))
    else if mind_is_one_of target_mind !prod_minds then
      let fst, snd = prod_parts env evd target in
      require_recursive_prod_second env evd mind fst snd;
      let folded =
        fold_mutual_nested env evd ~depth ~leaf_state mind specs snd proof
      in
      (match cases with
      | [ prod_case ] -> constr_app prod_case [ fst; snd; folded ]
      | _ -> CErrors.user_err Pp.(str "Nested Prod has unexpected cases"))
    else if mind_is_one_of target_mind !list_minds then
      fold_mutual_list env evd ~depth ~leaf_state mind specs motive cases
        target proof
    else if mind_is_one_of target_mind !option_minds then
      fold_mutual_option env evd ~depth ~leaf_state mind specs motive cases
        target proof
    else
      let target_mib = Global.lookup_mind target_mind in
      let packet = target_mib.mind_packets.(target_index) in
      (match (packet.mind_record, cases) with
      | Declarations.PrimRecord _, [ _ ] when leaf_state = FoldedLeaves ->
        proof
      | Declarations.PrimRecord _, [ record_case ] ->
        let nfields = packet.mind_consnrealargs.(0) in
        let fields =
          List.init nfields (fun proj_arg ->
            let projection, relevance =
              Declareops.inductive_make_projection target_ind target_mib
                ~proj_arg
            in
            mkProj (Projection.make projection false, relevance, target))
        in
        constr_app record_case (fields @ [ proof ])
      | _ -> CErrors.user_err Pp.(str "Unsupported nested mutual container"))
  | None -> CErrors.user_err Pp.(str "Nested recursive argument is not inductive")

and fold_mutual_option env evd ~depth ~leaf_state mind specs motive cases
    target proof =
  let open Constr in
  let { all_ind; all_inst; all_element = a; all_predicate = p } =
    view_all_proof env evd "Option" proof
  in
  let target_ty = type_of_constr env evd target in
  let motive_at_target = constr_app motive [ target ] in
  let rect = all_rect env evd all_ind all_inst motive_at_target in
  let all_ind_head = mkIndU (all_ind, all_inst) in
  let all_motive =
    let target_annot = anon_annot_for_type env evd target_ty in
    let env_target =
      Environ.push_rel (RelDecl.LocalAssum (target_annot, target_ty)) env
    in
    let all_ty =
      constr_app (Vars.lift 1 all_ind_head)
        [ Vars.lift 1 a; Vars.lift 1 p; mkRel 1 ]
    in
    let all_annot = anon_annot_for_type env_target evd all_ty in
    mkLambda
      ( target_annot,
        target_ty,
        mkLambda
          (all_annot, all_ty, constr_app (Vars.lift 2 motive) [ mkRel 2 ]) )
  in
  match cases with
  | [ none_case; some_case ] ->
    let head_ty = a in
    let head_annot = anon_annot_for_type env evd head_ty in
    let env_head =
      Environ.push_rel (RelDecl.LocalAssum (head_annot, head_ty)) env
    in
    let p_head_ty = constr_app (Vars.lift 1 p) [ mkRel 1 ] in
    let p_head_annot = anon_annot_for_type env_head evd p_head_ty in
    let env_p_head =
      Environ.push_rel
        (RelDecl.LocalAssum (p_head_annot, p_head_ty))
        env_head
    in
    let head_ih =
      fold_mutual_nested env_p_head evd ~depth:(depth + 2) ~leaf_state
        mind specs (mkRel 2) (mkRel 1)
    in
    let some_branch =
      mkLambda
        ( head_annot,
          head_ty,
          mkLambda
            ( p_head_annot,
              p_head_ty,
              constr_app (Vars.lift 2 some_case) [ mkRel 2; head_ih ] ) )
    in
    constr_app rect
      [ a; p; all_motive; none_case; some_branch; target; proof ]
  | _ -> CErrors.user_err Pp.(str "Nested Option has unexpected cases")

and fold_mutual_list env evd ~depth ~leaf_state mind specs motive cases
    target proof =
  let open Constr in
  let { all_ind; all_inst; all_element = a; all_predicate = p } =
    view_all_proof env evd "List" proof
  in
  let target_ty = type_of_constr env evd target in
  let motive_at_target = constr_app motive [ target ] in
  let rect = all_rect env evd all_ind all_inst motive_at_target in
  let all_ind_head = mkIndU (all_ind, all_inst) in
  let all_motive =
    let target_annot = anon_annot_for_type env evd target_ty in
    let env_target =
      Environ.push_rel (RelDecl.LocalAssum (target_annot, target_ty)) env
    in
    let all_ty =
      constr_app (Vars.lift 1 all_ind_head)
        [ Vars.lift 1 a; Vars.lift 1 p; mkRel 1 ]
    in
    let all_annot = anon_annot_for_type env_target evd all_ty in
    mkLambda
      ( target_annot,
        target_ty,
        mkLambda
          (all_annot, all_ty, constr_app (Vars.lift 2 motive) [ mkRel 2 ]) )
  in
  match cases with
  | [ nil_case; cons_case ] ->
    let head_ty = a in
    let head_annot = anon_annot_for_type env evd head_ty in
    let env_head =
      Environ.push_rel (RelDecl.LocalAssum (head_annot, head_ty)) env
    in
    let p_head_ty = constr_app (Vars.lift 1 p) [ mkRel 1 ] in
    let p_head_annot = anon_annot_for_type env_head evd p_head_ty in
    let env_p_head =
      Environ.push_rel
        (RelDecl.LocalAssum (p_head_annot, p_head_ty))
        env_head
    in
    let tail_ty = Vars.lift 2 target_ty in
    let tail_annot = anon_annot_for_type env_p_head evd tail_ty in
    let env_tail =
      Environ.push_rel (RelDecl.LocalAssum (tail_annot, tail_ty)) env_p_head
    in
    let all_tail_ty =
      constr_app (Vars.lift 3 all_ind_head)
        [ Vars.lift 3 a; Vars.lift 3 p; mkRel 1 ]
    in
    let all_tail_annot = anon_annot_for_type env_tail evd all_tail_ty in
    let env_all_tail =
      Environ.push_rel
        (RelDecl.LocalAssum (all_tail_annot, all_tail_ty))
        env_tail
    in
    let ih_ty = constr_app (Vars.lift 4 motive) [ mkRel 2 ] in
    let ih_annot = anon_annot_for_type env_all_tail evd ih_ty in
    let head_ih =
      fold_mutual_nested env_all_tail evd ~depth:(depth + 4) ~leaf_state
        mind specs (mkRel 4) (mkRel 3)
    in
    let body =
      constr_app (Vars.lift 5 cons_case)
        [ mkRel 5; mkRel 3; Vars.lift 1 head_ih; mkRel 1 ]
    in
    let cons_branch =
      mkLambda
        ( head_annot,
          head_ty,
          mkLambda
            ( p_head_annot,
              p_head_ty,
              mkLambda
                ( tail_annot,
                  tail_ty,
                  mkLambda
                    ( all_tail_annot,
                      all_tail_ty,
                      mkLambda (ih_annot, ih_ty, body) ) ) ) )
    in
    constr_app rect
      [ a; p; all_motive; nil_case; cons_branch; target; proof ]
  | _ -> CErrors.user_err Pp.(str "Nested List has unexpected cases")

let container_all_forall env evd recursor predicate proof target =
  let {
    unary_ind = container_ind;
    unary_inst = container_inst;
    unary_element;
    _;
  } =
    view_unary_target env evd "container" target
  in
  let all_forall_ref =
    match
      DeclareScheme.lookup_scheme_opt "AllForall" (GlobRef.IndRef container_ind)
    with
    | Some all_forall_ref -> all_forall_ref
    | None -> CErrors.user_err Pp.(str "Nested AllForall is unavailable")
  in
  let _, rec_inst = Constr.destConst recursor in
  let _, rec_levels = Instance.to_array rec_inst in
  if Array.length rec_levels = 0 then
    CErrors.user_err Pp.(str "Nested recursor has no motive universe");
  let motive_level = rec_levels.(0) in
  let container_qs, container_levels = Instance.to_array container_inst in
  let all_inst =
    Instance.of_array
      ( append_array container_qs [| Sorts.Quality.qtype |],
        append_array container_levels [| motive_level |] )
  in
  let all_forall = Constr.mkRef (all_forall_ref, all_inst) in
  constr_app all_forall [ unary_element; predicate; proof; target ]

let rec mutual_nested_leaf env evd ~depth mind specs recursor main_motives
    main_recs target =
  let target_ty = whd_type_of_constr env evd target in
  match type_head_ind env evd target_ty with
  | Some ((target_mind, target_index), _, _)
    when MutInd.UserOrd.equal target_mind mind ->
    let predicate =
      constr_app (Vars.lift depth (List.nth main_motives target_index))
        [ target ]
    in
    let proof =
      constr_app (Vars.lift depth (List.nth main_recs target_index)) [ target ]
    in
    (predicate, proof)
  | Some ((target_mind, _), _, target_args)
    when is_unary_container_mind target_mind ->
    let spec =
      match find_aux_spec env evd target_ty specs with
      | Some spec -> spec
      | None ->
        CErrors.user_err Pp.(str "No motive for auxiliary recursive target")
    in
    let element_ty = target_args.(Array.length target_args - 1) in
    let predicate, proof =
      mutual_element_functions env evd ~depth mind specs recursor main_motives
        main_recs element_ty
    in
    let all_proof =
      container_all_forall env evd recursor predicate proof target
    in
    ( constr_app (Vars.lift depth spec.aux_motive) [ target ],
      fold_mutual_nested env evd ~depth ~leaf_state:FoldedLeaves mind specs
        target all_proof )
  | Some ((target_mind, _), _, _)
    when mind_is_one_of target_mind !prod_minds ->
    let fst, snd = prod_parts env evd target in
    require_recursive_prod_second env evd mind fst snd;
    mutual_nested_leaf env evd ~depth mind specs recursor main_motives
      main_recs snd
  | Some (((target_mind, target_index) as target_ind), _, _) ->
    let spec = find_aux_spec env evd target_ty specs in
    (match spec with
    | Some { aux_motive; aux_cases = [ record_case ]; _ } ->
      let target_mib = Global.lookup_mind target_mind in
      let packet = target_mib.mind_packets.(target_index) in
      (match packet.mind_record with
      | Declarations.PrimRecord _ ->
        let nfields = packet.mind_consnrealargs.(0) in
        let fields =
          List.init nfields (fun proj_arg ->
            let projection, relevance =
              Declareops.inductive_make_projection target_ind target_mib
                ~proj_arg
            in
            Constr.mkProj
              (Projection.make projection false, relevance, target))
        in
        let recursive_field =
          match List.rev fields with
          | recursive_field :: _ -> recursive_field
          | [] ->
            CErrors.user_err
              Pp.(str "Nested record has no recursive field")
        in
        let _, recursive_proof =
          mutual_nested_leaf env evd ~depth mind specs recursor main_motives
            main_recs recursive_field
        in
        ( constr_app (Vars.lift depth aux_motive) [ target ],
          constr_app (Vars.lift depth record_case)
            (fields @ [ recursive_proof ]) )
      | _ ->
        CErrors.user_err
          Pp.(str "Nested All predicate has an unsupported record type"))
    | _ ->
      CErrors.user_err
        Pp.(str "Nested All predicate has an unsupported element type"))
  | _ ->
    CErrors.user_err
      Pp.(str "Nested All predicate has an unsupported element type")

and mutual_element_functions env evd ~depth mind specs recursor main_motives
    main_recs element_ty =
  let open Constr in
  let annot = anon_annot_for_type env evd element_ty in
  let env_element =
    Environ.push_rel (RelDecl.LocalAssum (annot, element_ty)) env
  in
  let predicate_at, proof_at =
    mutual_nested_leaf env_element evd ~depth:(depth + 1) mind specs recursor
      main_motives main_recs (mkRel 1)
  in
  (mkLambda (annot, element_ty, predicate_at),
   mkLambda (annot, element_ty, proof_at))

let fold_mutual_auxiliary env evd info specs recursor main_motives main_recs
    target =
  snd
    (mutual_nested_leaf env evd ~depth:0 info.mind specs recursor
       main_motives main_recs target)

let adapt_mutual_branch env evd mind specs info branch_ty branch =
  let open Constr in
  let info = List.rev info in
  let nargs = List.length info in
  let rec_positions =
    List.filter_map
      (fun (i, recursive) -> if recursive then Some i else None)
      (CList.map_i (fun i recursive -> (i, recursive)) 0 info)
  in
  (* Products in the motive result are not recursor branch binders. *)
  let nbranch_binders = nargs + List.length rec_positions in
  let rec loop env depth ty original mapped binder_index =
    if binder_index = nbranch_binders then
      constr_app (Vars.lift depth branch) mapped
    else
      let ty = whd_constr env evd ty in
      match kind ty with
      | Prod (annot, binder_ty, body) ->
        let env' =
          Environ.push_rel (RelDecl.LocalAssum (annot, binder_ty)) env
        in
        let original = List.map (Vars.lift 1) original in
        let mapped = List.map (Vars.lift 1) mapped in
        if binder_index < nargs then
          let original = original @ [ mkRel 1 ] in
          let mapped = mapped @ [ mkRel 1 ] in
          mkLambda
            ( annot,
              binder_ty,
              loop env' (depth + 1) body original mapped (binder_index + 1) )
        else
          let rec_index = binder_index - nargs in
          let arg_index =
            match List.nth_opt rec_positions rec_index with
            | Some arg_index -> arg_index
            | None ->
              CErrors.user_err
                Pp.(
                  str "Unexpected mutual branch binder " ++ int binder_index
                  ++ str " after " ++ int nargs
                  ++ str " constructor arguments and "
                  ++ int (List.length rec_positions)
                  ++ str " recursive hypotheses")
          in
          let target = List.nth original arg_index in
          let target_ty = type_of_constr env' evd target in
          let mapped_hyp =
            match type_head_ind env' evd target_ty with
            | Some ((target_mind, _), _, _)
              when MutInd.UserOrd.equal target_mind mind -> mkRel 1
            | _ ->
              fold_mutual_nested env' evd ~depth:(depth + 1)
                ~leaf_state:RawLeaves mind specs target (mkRel 1)
          in
          let mapped = mapped @ [ mapped_hyp ] in
          mkLambda
            ( annot,
              binder_ty,
              loop env' (depth + 1) body original mapped (binder_index + 1) )
      | _ ->
        CErrors.user_err
          Pp.(
            str "Mutual branch ended after " ++ int binder_index
            ++ str " binders; expected " ++ int nbranch_binders)
  in
  loop env 0 branch_ty [] [] 0

let rec final_product_domain env evd ty =
  match Constr.kind (whd_constr env evd ty) with
  | Constr.Prod (annot, domain, body) ->
    let env =
      Environ.push_rel (RelDecl.LocalAssum (annot, domain)) env
    in
    (match Constr.kind (whd_constr env evd body) with
    | Constr.Prod _ -> final_product_domain env evd body
    | _ -> domain)
  | _ -> CErrors.user_err Pp.(str "Nested recursor has no target argument")

let recursor_mind env evd recursor =
  let ty = type_of_constr env evd recursor in
  match type_head_ind env evd (final_product_domain env evd ty) with
  | Some ((mind, _), _, _) -> mind
  | None -> CErrors.user_err Pp.(str "Nested recursor target is not inductive")

type mutual_recursor_layout = {
  layout_domains : Constr.t list;
  layout_case_counts : int list;
  layout_has_target : bool;
}

let adapt_mutual_nested_recursor env evd info recursors args =
  let recursor =
    match recursors with
    | recursor :: _ -> recursor
    | [] -> CErrors.user_err Pp.(str "Mutual recursor block is empty")
  in
  let info = { info with mind = recursor_mind env evd recursor } in
  let mib = Global.lookup_mind info.mind in
  let ntypes = Array.length mib.mind_packets in
  let nmain_cases =
    Array.fold_left
      (fun n (packet : Declarations.one_inductive_body) ->
        n + Array.length packet.mind_consnames)
      0 mib.mind_packets
  in
  if List.length args < info.nparams + ntypes + nmain_cases + 1 then None
  else
    let params, args = CList.chop info.nparams args in
    let main_motives, tail = CList.chop ntypes args in
    let focus_matches aux_domains target =
      let target_ty = type_of_constr env evd target in
      match info.focus with
      | MutualMain index -> (
        match type_head_ind env evd target_ty with
        | Some ((target_mind, target_index), _, _) ->
          MutInd.UserOrd.equal target_mind info.mind && target_index = index
        | None -> false)
      | MutualAux index ->
        index < List.length aux_domains
        &&
        let domain = List.nth aux_domains index in
        convertible env evd target_ty domain
        || same_inductive_head env evd target_ty domain
    in
    let partial_focus_matches aux_domains =
      match info.focus with
      | MutualMain index -> index < ntypes
      | MutualAux index -> index < List.length aux_domains
    in
    let rec find_layout k =
      if k > List.length tail then None
      else
        let aux_motives, _ = CList.chop k tail in
        let aux_domains = List.map (motive_domain env evd) aux_motives in
        if List.exists Option.is_empty aux_domains then find_layout (k + 1)
        else
          let aux_domains = List.map Option.get aux_domains in
          let counts = List.map (aux_ctor_count env evd) aux_domains in
          if List.exists Option.is_empty counts then find_layout (k + 1)
          else
            let naux_cases =
              List.fold_left ( + ) 0 (List.map Option.get counts)
            in
            let target_index = k + nmain_cases + naux_cases in
            if target_index > List.length tail then find_layout (k + 1)
            else if target_index = List.length tail then
              if partial_focus_matches aux_domains then
                Some
                  {
                    layout_domains = aux_domains;
                    layout_case_counts = List.map Option.get counts;
                    layout_has_target = false;
                  }
              else find_layout (k + 1)
            else
              let target = List.nth tail target_index in
              if focus_matches aux_domains target then
                Some
                  {
                    layout_domains = aux_domains;
                    layout_case_counts = List.map Option.get counts;
                    layout_has_target = true;
                  }
              else find_layout (k + 1)
    in
    match find_layout 0 with
    | None -> None
    | Some { layout_domains = []; layout_has_target = true; _ } -> (
      match info.focus with
      | MutualMain index ->
        Some (constr_app (List.nth recursors index) (params @ args))
      | MutualAux _ -> None)
    | Some
        {
          layout_domains = aux_domains;
          layout_case_counts = aux_counts;
          layout_has_target;
        } ->
      let naux = List.length aux_domains in
      let aux_motives, rest = CList.chop naux tail in
      let lean_main_cases, rest = CList.chop nmain_cases rest in
      let rest, specs_rev =
        CList.fold_left3
          (fun (rest, specs) domain motive count ->
            let cases, rest = CList.chop count rest in
            ( rest,
              { aux_domain = domain; aux_motive = motive; aux_cases = cases }
              :: specs ))
          (rest, []) aux_domains aux_motives aux_counts
      in
      let specs = List.rev specs_rev in
      let target_and_extra =
        match (layout_has_target, rest) with
        | true, target :: extra -> Some (target, extra)
        | false, [] -> None
        | _ -> CErrors.user_err Pp.(str "Malformed nested recursor application")
      in
      let rec_ty = type_of_constr env evd recursor in
      let rec_ty =
        List.fold_left (prod_after_apply env evd) rec_ty
          (params @ main_motives)
      in
      let ctor_infos =
        Array.to_list
          (Array.concat
             (Array.to_list
                (Array.map
                   (fun (packet : Declarations.one_inductive_body) ->
                     Array.mapi
                       (fun i (ctor_args, _) ->
                         let nargs = packet.mind_consnrealargs.(i) in
                         CList.map
                           (fun arg ->
                             has_rec_hyp env info.mind (RelDecl.get_type arg))
                           (CList.firstn nargs ctor_args))
                       packet.mind_nf_lc)
                   mib.mind_packets)))
      in
      let adapt_cases () =
        let _, cases_rev =
          (CList.fold_left2
             (fun (rec_ty, cases) branch ctor_info ->
               let branch_ty = prod_domain env evd rec_ty in
               let branch =
                 adapt_mutual_branch env evd info.mind specs ctor_info
                   branch_ty branch
               in
               (prod_after_apply env evd rec_ty branch, branch :: cases))
             (rec_ty, []) lean_main_cases ctor_infos)
        in
        List.rev cases_rev
      in
      let default_cases = adapt_cases () in
      let default_main_recs =
        List.map
          (fun recursor ->
            constr_app recursor (params @ main_motives @ default_cases))
          recursors
      in
      let result_at env specs recursor main_motives main_recs target =
        match info.focus with
        | MutualMain index -> constr_app (List.nth main_recs index) [ target ]
        | MutualAux _ ->
          fold_mutual_auxiliary env evd info specs recursor main_motives
            main_recs target
      in
      (match target_and_extra with
      | Some (target, extra) ->
        Some
          (constr_app
             (result_at env specs recursor main_motives default_main_recs target)
             extra)
      | None ->
        let target_ty =
          match info.focus with
          | MutualMain index ->
            prod_domain env evd
              (type_of_constr env evd (List.nth default_main_recs index))
          | MutualAux index -> List.nth aux_domains index
        in
        let annot = anon_annot_for_type env evd target_ty in
        let env_target =
          Environ.push_rel (RelDecl.LocalAssum (annot, target_ty)) env
        in
        let lift_spec spec =
          {
            aux_domain = Vars.lift 1 spec.aux_domain;
            aux_motive = Vars.lift 1 spec.aux_motive;
            aux_cases = List.map (Vars.lift 1) spec.aux_cases;
          }
        in
        let body =
          result_at env_target (List.map lift_spec specs)
            (Vars.lift 1 recursor)
            (List.map (Vars.lift 1) main_motives)
            (List.map (Vars.lift 1) default_main_recs)
            (Constr.mkRel 1)
        in
        Some (Constr.mkLambda (annot, target_ty, body)))

(** Proof-producing reflection for closed natural-number arithmetic.

    This deliberately does not add a reduction rule to Rocq.  [reify_nat]
    evaluates a small, generic arithmetic language with Zarith and constructs
    a proof of [NatCertificate] in parallel.  The proof is later consumed by
    [NatCertificate_equal] and [Nat_transport_sprop], so the value computed by
    OCaml is checked independently by the Rocq kernel. *)
type nat_certificate = {
  nat_term : Constr.t;
  nat_value : Z.t;
  nat_proof : Constr.t;
}

let ref_matches env term key =
  try
    let gr, _ = Constr.destRef term in
    Environ.QGlobRef.equal env gr (Rocqlib.lib_ref key)
  with Constr.DestKO -> false

let nat_constructor_matches env term index =
  match Rocqlib.lib_ref "lean.Nat", Constr.kind term with
  | GlobRef.IndRef ind, Construct ((constructor_ind, constructor_index), _) ->
    index = constructor_index && Environ.QInd.equal env ind constructor_ind
  | _ -> false

let cert_app key args = Constr.mkApp (registered_ref key, Array.of_list args)

let rec z_of_positive env evd term =
  let head, args = Constr.decompose_app term in
  if ref_matches env head "num.pos.xH" && Array.length args = 0 then Some Z.one
  else if ref_matches env head "num.pos.xO" && Array.length args = 1 then
    Option.map
      (fun n -> Z.mul (Z.of_int 2) n)
      (z_of_positive env evd args.(0))
  else if ref_matches env head "num.pos.xI" && Array.length args = 1 then
    Option.map
      (fun n -> Z.succ (Z.mul (Z.of_int 2) n))
      (z_of_positive env evd args.(0))
  else
    let reduced =
      Reductionops.whd_all env evd (EConstr.of_constr term)
      |> EConstr.Unsafe.to_constr
    in
    if Constr.equal reduced term then None
    else z_of_positive env evd reduced

let rec z_of_n env evd term =
  let head, args = Constr.decompose_app term in
  if ref_matches env head "num.N.N0" && Array.length args = 0 then Some Z.zero
  else if ref_matches env head "num.N.Npos" && Array.length args = 1 then
    z_of_positive env evd args.(0)
  else
    let reduced =
      Reductionops.whd_all env evd (EConstr.of_constr term)
      |> EConstr.Unsafe.to_constr
    in
    if Constr.equal reduced term then None else z_of_n env evd reduced

let beta_apply head args =
  let rec apply head index =
    if index = Array.length args then head
    else
      match Constr.kind head with
      | Lambda (_, _, body) -> apply (Vars.subst1 args.(index) body) (index + 1)
      | LetIn (_, value, _, body) -> apply (Vars.subst1 value body) index
      | _ ->
        Constr.mkApp
          (head, Array.sub args index (Array.length args - index))
  in
  apply head 0

let unfold_head_once env term =
  let head, args = Constr.decompose_app term in
  match Constr.kind head with
  | Const (constant, instance) -> (
    try beta_apply (Environ.constant_value_in env (constant, instance)) args
    with Environ.NotEvaluableConst _ -> term)
  | Lambda _ | LetIn _ -> beta_apply head args
  | _ -> term

let expose_iota_scrutinee env term =
  let head, args = Constr.decompose_app term in
  let expose head =
    match Constr.kind head with
    | Case (info, instance, params, return, invert, scrutinee, branches) ->
      let scrutinee = unfold_head_once env scrutinee in
      Constr.mkCase
        (info, instance, params, return, invert, scrutinee, branches)
    | Proj (projection, relevance, scrutinee) ->
      let scrutinee = unfold_head_once env scrutinee in
      let constructor, constructor_args = Constr.decompose_app scrutinee in
      (match Constr.kind constructor with
      | Construct _ ->
        constructor_args.(Projection.npars projection + Projection.arg projection)
      | _ -> Constr.mkProj (projection, relevance, scrutinee))
    | _ -> head
  in
  let exposed = expose head in
  if Array.length args = 0 then exposed else Constr.mkApp (exposed, args)

(** Take one transparent reduction step without invoking Rocq's conversion
    oracle on the whole closed computation. The returned constant list prevents
    cycles while following transparent wrappers. *)
let reduce_closed_term_once env evd unfolded term =
  let reduced =
    expose_iota_scrutinee env term |> EConstr.of_constr
    |> Reductionops.whd_betaiotazeta env evd
    |> EConstr.Unsafe.to_constr
  in
  if not (Constr.equal reduced term) then Some (unfolded, reduced)
  else
    let head, args = Constr.decompose_app term in
    let constant_unseen constant =
      not
        (List.exists
           (fun seen -> Environ.QConstant.equal env constant seen)
           unfolded)
    in
    match Constr.kind term, Constr.kind head with
    | LetIn (_, value, _, body), _ ->
      Some (unfolded, Vars.subst1 value body)
    | _, Const (constant, instance) when constant_unseen constant -> (
      try
        let body = Environ.constant_value_in env (constant, instance) in
        Some (constant :: unfolded, beta_apply body args)
      with Environ.NotEvaluableConst _ -> None)
    | App _, (Lambda _ | LetIn _) ->
      Some (unfolded, beta_apply head args)
    | _ -> None

let max_reflected_bits = Z.of_int 1_000_000

let reflected_size_ok value =
  Z.leq (Z.of_int (Z.numbits value)) max_reflected_bits

let reflected_pow base exponent =
  if Z.lt exponent Z.zero || not (Z.fits_int exponent) then None
  else
    let estimated_bits =
      if Z.leq base Z.one then Z.one
      else Z.mul (Z.of_int (Z.numbits base)) exponent
    in
    if Z.gt estimated_bits max_reflected_bits then None
    else
      let value = Z.pow base (Z.to_int exponent) in
      if reflected_size_ok value then Some value else None

let reify_nat env evd term =
  let rec reify fuel unfolded term =
    let preserve_original result =
      Option.map (fun certificate -> { certificate with nat_term = term }) result
    in
    if fuel = 0 || not (Vars.closed0 term) then None
    else
      let head, args = Constr.decompose_app term in
      if ref_matches env head "lean.Nat_of_N" && Array.length args = 1 then
        Option.map
          (fun value ->
            {
              nat_term = term;
              nat_value = value;
              nat_proof =
                cert_app "lean.NatCertificate_of_N" [ n_int value ];
            })
          (z_of_n env evd args.(0))
      else if nat_constructor_matches env head 1 && Array.length args = 0 then
        Some
          {
            nat_term = term;
            nat_value = Z.zero;
            nat_proof = registered_ref "lean.NatCertificate_zero";
          }
      else if nat_constructor_matches env head 2 && Array.length args = 1 then
        Option.bind (reify (fuel - 1) unfolded args.(0)) (fun arg ->
            let value = Z.succ arg.nat_value in
            if not (reflected_size_ok value) then None
            else
              Some
                {
                  nat_term = term;
                  nat_value = value;
                  nat_proof =
                    cert_app "lean.NatCertificate_succ"
                      [ arg.nat_term; n_int arg.nat_value; arg.nat_proof ];
                })
      else
        let binary key proof_key operation =
          if ref_matches env head key && Array.length args = 2 then
            Option.bind (reify (fuel - 1) unfolded args.(0)) (fun left ->
                Option.bind (reify (fuel - 1) unfolded args.(1)) (fun right ->
                    Option.bind (operation left.nat_value right.nat_value)
                      (fun value ->
                        if not (reflected_size_ok value) then None
                        else
                          Some
                            {
                              nat_term = term;
                              nat_value = value;
                              nat_proof =
                                cert_app proof_key
                                  [
                                    left.nat_term;
                                    right.nat_term;
                                    n_int left.nat_value;
                                    n_int right.nat_value;
                                    left.nat_proof;
                                    right.nat_proof;
                                  ];
                            })))
          else None
        in
        let reflected =
          List.find_map
            (fun (key, proof_key, operation) ->
              binary key proof_key operation)
            [
              ( "lean.Nat_add",
                "lean.NatCertificate_add",
                (fun a b -> Some (Z.add a b)) );
              ( "lean.Nat_mul",
                "lean.NatCertificate_mul",
                (fun a b -> Some (Z.mul a b)) );
              ("lean.Nat_pow", "lean.NatCertificate_pow", reflected_pow);
            ]
        in
        match reflected with
        | Some _ as result -> result
        | None ->
          Option.bind (reduce_closed_term_once env evd unfolded term)
            (fun (unfolded, reduced) ->
              preserve_original (reify (fuel - 1) unfolded reduced))
  in
  reify 128 [] term

type certificate_path_step =
  | AppArgument of int
  | ProdDomain
  | ProdCodomain
  | LambdaDomain
  | LambdaBody
  | LetValue
  | LetType
  | LetBody

let rec first_certified_nat_difference env evd path actual expected =
  if Constr.equal actual expected then None
  else
    match reify_nat env evd actual, reify_nat env evd expected with
    | Some left, Some right when Z.equal left.nat_value right.nat_value ->
      Some (List.rev path, left, right)
    | _ -> (
      match Constr.kind actual, Constr.kind expected with
      | Prod (_, actual_domain, actual_body),
        Prod (_, expected_domain, expected_body) -> (
        match
          first_certified_nat_difference env evd (ProdDomain :: path)
            actual_domain expected_domain
        with
        | Some _ as result -> result
        | None ->
          first_certified_nat_difference env evd (ProdCodomain :: path)
            actual_body expected_body)
      | Lambda (_, actual_domain, actual_body),
        Lambda (_, expected_domain, expected_body) -> (
        match
          first_certified_nat_difference env evd (LambdaDomain :: path)
            actual_domain expected_domain
        with
        | Some _ as result -> result
        | None ->
          first_certified_nat_difference env evd (LambdaBody :: path)
            actual_body expected_body)
      | LetIn (_, actual_value, actual_type, actual_body),
        LetIn (_, expected_value, expected_type, expected_body) -> (
        match
          first_certified_nat_difference env evd (LetValue :: path) actual_value
            expected_value
        with
        | Some _ as result -> result
        | None -> (
          match
            first_certified_nat_difference env evd (LetType :: path) actual_type
              expected_type
          with
          | Some _ as result -> result
          | None ->
            first_certified_nat_difference env evd (LetBody :: path) actual_body
              expected_body))
      | App _, App _ ->
        let actual_head, actual_args = Constr.decompose_app actual in
        let expected_head, expected_args = Constr.decompose_app expected in
        if
          not (Constr.equal actual_head expected_head)
          || Array.length actual_args <> Array.length expected_args
        then None
        else
          let rec scan index =
            if index = Array.length actual_args then None
            else
              match
                first_certified_nat_difference env evd
                  (AppArgument index :: path)
                  actual_args.(index) expected_args.(index)
              with
              | Some _ as result -> result
              | None -> scan (index + 1)
          in
          scan 0
      | _ -> None)

let replace_certificate_path term path replacement =
  let rec replace depth term = function
    | [] -> Vars.lift depth replacement
    | AppArgument index :: rest ->
      let head, args = Constr.decompose_app term in
      if index >= Array.length args then assert false;
      let args = Array.copy args in
      args.(index) <- replace depth args.(index) rest;
      Constr.mkApp (head, args)
    | ProdDomain :: rest ->
      let annot, domain, body = Constr.destProd term in
      Constr.mkProd (annot, replace depth domain rest, body)
    | ProdCodomain :: rest ->
      let annot, domain, body = Constr.destProd term in
      Constr.mkProd (annot, domain, replace (depth + 1) body rest)
    | LambdaDomain :: rest ->
      let annot, domain, body = Constr.destLambda term in
      Constr.mkLambda (annot, replace depth domain rest, body)
    | LambdaBody :: rest ->
      let annot, domain, body = Constr.destLambda term in
      Constr.mkLambda (annot, domain, replace (depth + 1) body rest)
    | LetValue :: rest ->
      let annot, value, ty, body = Constr.destLetIn term in
      Constr.mkLetIn (annot, replace depth value rest, ty, body)
    | LetType :: rest ->
      let annot, value, ty, body = Constr.destLetIn term in
      Constr.mkLetIn (annot, value, replace depth ty rest, body)
    | LetBody :: rest ->
      let annot, value, ty, body = Constr.destLetIn term in
      Constr.mkLetIn (annot, value, ty, replace (depth + 1) body rest)
  in
  replace 0 term path

let is_sprop_type env evd ty =
  let sort =
    Retyping.get_type_of env evd (EConstr.of_constr ty)
    |> Reductionops.whd_all env evd |> EConstr.Unsafe.to_constr
  in
  match Constr.kind sort with Sort sort -> Sorts.is_sprop sort | _ -> false

let transport_closed_nat env evd actual expected argument =
  if not (is_sprop_type env evd actual) then None
  else
    let rec transport fuel actual argument =
      if Constr.equal actual expected then Some argument
      else if fuel = 0 then None
      else
        match first_certified_nat_difference env evd [] actual expected with
        | None -> None
        | Some (path, left, right) ->
          let canonical = n_int left.nat_value in
          let equality =
            cert_app "lean.NatCertificate_equal"
              [
                left.nat_term;
                right.nat_term;
                canonical;
                left.nat_proof;
                right.nat_proof;
              ]
          in
          let motive_body =
            replace_certificate_path (Vars.lift 1 actual) path (Constr.mkRel 1)
          in
          let motive =
            Constr.mkLambda
              ( Context.make_annot Anonymous Sorts.Relevant,
                registered_ref "lean.Nat",
                motive_body )
          in
          let argument =
            cert_app "lean.Nat_transport_sprop"
              [ motive; left.nat_term; right.nat_term; equality; argument ]
          in
          let actual = replace_certificate_path actual path right.nat_term in
          transport (fuel - 1) actual argument
    in
    transport 16 actual argument

let maybe_transport_to_expected env evd expected argument =
  let actual =
    Retyping.get_type_of env evd (EConstr.of_constr argument)
    |> EConstr.Unsafe.to_constr
  in
  if Constr.equal actual expected then argument
  else
    match transport_closed_nat env evd actual expected argument with
    | Some argument -> argument
    | None -> argument

let maybe_transport_application env evd function_term argument =
  let function_type =
    Retyping.get_type_of env evd (EConstr.of_constr function_term)
    |> Reductionops.whd_all env evd |> EConstr.Unsafe.to_constr
  in
  match Constr.kind function_type with
  | Prod (_, expected, _) ->
    maybe_transport_to_expected env evd expected argument
  | _ -> argument

let rec to_constr =
  let open Constr in
  let ( >>= ) x f uconv =
    let uconv, x = x uconv in
    f x uconv
  in
  let get_uconv uconv = (uconv, uconv) in
  let ret x uconv = (uconv, x) in
  let to_annot env n t u = (u, to_annot env n t u) in
  let push_rel = Environ.push_rel_context_val in
  fun env -> function
    | Bound i -> ret (mkRel (i + 1))
    | Sort univ ->
      to_univ_level' univ >>= fun u -> ret (mkSort (sort_of_level u))
    | Const (n, univs) -> instantiate n univs
    | (App _ as app_expr) -> (
      let head, args = decompose_lean_app [] app_expr in
      let translate_plain () =
        let a, b_expr =
          match app_expr with App (a, b) -> a, b | _ -> assert false
        in
        to_constr env a >>= fun a ->
        to_constr env b_expr >>= fun b ->
        get_uconv >>= fun uconv ->
        let b =
          with_env_evm env uconv
            (fun env evd () -> maybe_transport_application env evd a b)
            ()
        in
        ret (mkApp (a, [| b |]))
      in
      match head with
      | Const (n, univs) when N.Map.mem n !projection_aliases ->
        fun uconv ->
          let alias = find_projection_alias_for_universes uconv n univs in
          let uconv, translated_args =
            CList.fold_left_map
              (fun uconv arg -> to_constr env arg uconv)
              uconv args
          in
          let apply_arguments function_ arguments =
            List.fold_left
              (fun function_ argument ->
                let argument =
                  with_env_evm env uconv
                    (fun env evd () ->
                      maybe_transport_application env evd function_ argument)
                    ()
                in
                Constr.mkApp (function_, [| argument |]))
              function_ arguments
          in
          (match alias with
          | Some alias ->
            let mib = Global.lookup_mind (fst alias.projection_ind) in
            let nparams = mib.mind_nparams in
            if List.length translated_args < nparams + 1 then
              let uconv, function_ = instantiate n univs uconv in
              uconv, apply_arguments function_ translated_args
            else
              let target = List.nth translated_args nparams in
              let projection, relevance =
                Declareops.inductive_make_projection alias.projection_ind mib
                  ~proj_arg:alias.projection_field
              in
              let projected =
                Constr.mkProj
                  (Projection.make projection false, relevance, target)
              in
              let extra =
                List.filteri
                  (fun index _ -> index > nparams)
                  translated_args
              in
              uconv, apply_arguments projected extra
          | None ->
            let uconv, function_ = instantiate n univs uconv in
            uconv, apply_arguments function_ translated_args)
      | Const (n, univs) -> (
        match find_mutual_nested_rec_info n with
        | None -> translate_plain ()
        | Some info ->
          fun uconv ->
            let uconv, recursors =
              CList.fold_left_map
                (fun uconv base_rec -> instantiate base_rec univs uconv)
                uconv info.base_recs
            in
            let uconv, args =
              CList.fold_left_map
                (fun uconv arg -> to_constr env arg uconv)
                uconv args
            in
            let adapted =
              with_env_evm env uconv
                (fun env evd () ->
                  adapt_mutual_nested_recursor env evd info recursors args)
                ()
            in
            match adapted with
            | Some term -> uconv, term
            | None ->
              let recursor_index =
                match info.focus with
                | MutualMain index -> index
                | MutualAux _ -> 0
              in
              let term =
                List.fold_left
                  (fun f x -> Constr.mkApp (f, [| x |]))
                  (List.nth recursors recursor_index) args
              in
              uconv, term)
      | _ -> translate_plain ())
    | Let { name; ty; v; rest } ->
      to_constr env ty >>= fun ty ->
      to_annot env name ty >>= fun name ->
      to_constr env v >>= fun v ->
      to_constr (push_rel (LocalDef (name, v, ty)) env) rest >>= fun rest ->
      ret (mkLetIn (name, v, ty, rest))
    | Lam (_bk, n, a, b) ->
      to_constr env a >>= fun a ->
      to_annot env n a >>= fun n ->
      to_constr (push_rel (LocalAssum (n, a)) env) b >>= fun b ->
      ret (mkLambda (n, a, b))
    | Pi (_bk, n, a, b) ->
      to_constr env a >>= fun a ->
      to_annot env n a >>= fun n ->
      to_constr (push_rel (LocalAssum (n, a)) env) b >>= fun b ->
      ret (mkProd (n, a, b))
    | Proj (lean_ind, field, c) ->
      to_constr env c >>= fun c ->
      get_uconv >>= fun uconv ->
      (* we retype to get the ind, because otherwise we need the lean
       univs for instantiation
       This means we ignore the lean_ind in the Proj data. *)
      let c =
        with_env_evm env uconv
          (fun env evd () ->
            let tc = Retyping.get_type_of env evd (EConstr.of_constr c) in
            let tc =
              Reductionops.whd_all env evd tc
            in
            let tc_head, args = EConstr.decompose_app evd tc in
            match EConstr.kind evd tc_head with
            | Constr.Ind _ ->
              (* Standard inductive: use normal projection *)
              let ((ind, _) as indu) =
                Constr.destInd (EConstr.Unsafe.to_constr tc_head)
              in
              let mib, mip = Inductive.lookup_mind_specif (Global.env()) ind in
              begin
                match mip.mind_record with
                | PrimRecord infos ->
                  let p, r =
                    Declareops.inductive_make_projection ind mib ~proj_arg:field
                  in
                  (* unfolded?? *)
                  mkProj (Projection.make p false, r, c)
                | NotRecord | FakeRecord ->
                  unfold_proj_case env evd ~field ~indu ~mib ~mip ~args c
              end
            | _ ->
              (* Type is not an inductive (e.g., transparent cumulative ULift).
                 Projection is the identity. *)
              c)
          ()
      in
      ret c
    | Nat i ->
      (* [nat_ints] is not synchronized so ensure Nat is instantiated *)
      instantiate (N.append N.anon "Nat") [] >>= fun nat ->
      let nat, _ = Constr.destInd nat in
      get_uconv >>= fun uconv ->
      let nat_of_n =
        with_env_evm env uconv
          (fun env evd () ->
            let _, p =
              Evd.fresh_global env evd (Rocqlib.lib_ref "lean.Nat_of_N")
            in
            EConstr.to_constr evd p)
          ()
      in
      ret (nat_int nat nat_of_n i)
    | String s ->
      (* instantiate (N.append N.anon "Char") [] >>= fun char -> *)
      (* let (_, charu) = Constr.destInd char in *)
      instantiate (N.append N.anon "String") [] >>= fun _string ->
      let string_mk = N.append (N.append N.anon "String") "mk" in
      let string_of_list = N.append (N.append N.anon "String") "ofList" in
      let string_of_chars =
        if N.Map.mem string_mk !entries || not (N.Map.mem string_of_list !entries)
        then string_mk
        else string_of_list
      in
      instantiate string_of_chars [] >>= fun string_of_chars ->
      get_uconv >>= fun uconv ->
      let list, char =
        with_env_evm env uconv
          (fun env evd () ->
            let ty =
              Retyping.get_type_of env evd (EConstr.of_constr string_of_chars)
            in
            let _, list_char, _ = EConstr.destProd evd ty in
            let list, char =
              match EConstr.destApp evd list_char with
              | list, [| char |] -> (list, char)
              | _ ->
                CErrors.user_err
                  Pp.(
                    str "Invalid type for string constructor: "
                    ++ Printer.pr_type_env env evd (EConstr.to_constr evd ty)
                    ++ str " ("
                    ++ Printer.pr_type_env env evd
                         (EConstr.to_constr evd list_char)
                    ++ str " should be an application of list to char)")
            in
            (EConstr.to_constr evd list, EConstr.to_constr evd char))
          ()
      in
      (* instantiate (N.append N.anon "List") [] >>= fun list -> *)
      let list, _ = Constr.destInd list in
      get_uconv >>= fun uconv ->
      let mkChar =
        with_env_evm env uconv
          (fun env evd () ->
            let _, mkChar =
              Evd.fresh_global env evd
                (Rocqlib.lib_ref ("lean." ^ mk_char_prim))
            in
            EConstr.to_constr evd mkChar)
          ()
      in
      ret (mk_string char list UVars.Instance.empty mkChar string_of_chars s)

and instantiate n univs uconv =
  assert (List.length univs < Sys.int_size);
  (* TODO what happens when is_large_elim and the motive is instantiated with Prop? *)
  let univs = List.map (to_universe uconv.map) univs in
  let i, univs = int_of_univs univs in
  let inst = ensure_exists n i in
  let subst l =
    let u =
      match Level.var_index l with
      | None -> Universe.make l
      | Some n -> List.nth univs n
    in
    Some u
  in
  let univs =
    List.map
      (fun alg -> simplify_universe (UnivSubst.subst_univs_universe subst alg))
      inst.algs
  in
  let uconv, univs =
    CList.fold_left_map (fun uconv u -> to_univ_level u uconv) uconv univs
  in
  let u = Instance.of_array ([||], Array.of_list univs) in
  (uconv, Constr.mkRef (inst.ref, u))

and ensure_exists n i =
  try !declared |> N.Map.find n |> Int.Map.find i
  with Not_found ->
    (* TODO can we end up asking for a ctor or eliminator before
       asking for the inductive type? *)
    (* if i = 0 then CErrors.user_err Pp.(N.pp n ++ str " was not instantiated!"); *)
    (* assert (not (upfront_instances ())); *)
    (match N.Map.find_opt n !mutual_entries with
    | Some inds ->
      declare_mutual_inductive_instance inds i;
      !declared |> N.Map.find n |> Int.Map.find i
    | None ->
      (match N.Map.find n !entries with
      | Def def -> declare_def def i
      | Ax ax -> declare_ax ax i
      | Ind ind -> declare_ind ind i
      | Quot _ -> CErrors.user_err Pp.(str "quot must be predeclared")
      | exception Not_found -> CErrors.user_err Pp.(str "missing " ++ N.pp n)))

and declare_def { name = n; ty; body; univs; } i =
  let ref, algs =
    match get_predeclared_def_some n i with
    | Some ((UInt32_size | Add | Mult | Pow | Nat_isValidChar), _, (def_name, c)) ->
      (* Hack to let the user predeclare some constants
         TODO make a more general Register-like API? *)
      Feedback.msg_info Pp.(Id.print def_name ++ str " is predeclared");
      (GlobRef.ConstRef c, [])
    | None ->
      let uconv = start_uconv univs i in
      let uconv, ty = to_constr empty_env ty uconv in
      let uconv, body = to_constr empty_env body uconv in
      let body =
        with_env_evm empty_env uconv
          (fun env evd () -> maybe_transport_to_expected env evd ty body)
          ()
      in
      let univs, algs = univ_entry uconv univs in
      let ref =
        try quickdef ~name:(name_for n i) ~types:(Some ty) ~univs body
        with e ->
          let e = Exninfo.capture e in
          Feedback.msg_info
            Pp.(
              str "Failed with" ++ fnl ()
              ++ Printer.pr_constr_env (Global.env ())
                   (Evd.from_env (Global.env ()))
                   body
              ++ fnl () ++ str ": "
              ++ Printer.pr_constr_env (Global.env ())
                   (Evd.from_env (Global.env ()))
                   ty);
          Exninfo.iraise e
      in
      (ref, algs)
  in
  let () =
    let c = match ref with ConstRef c -> c | _ -> assert false in
    if expands_at_head body then begin
      Global.set_strategy (Conv_oracle.EvalConstRef c) Conv_oracle.Expand;
      expand_head_cache := N.Set.add n !expand_head_cache
    end
    else
      let height = height n body in
      Global.set_strategy (Conv_oracle.EvalConstRef c) (Level (-height))
  in
  let inst =
    match find_projection_alias n i with
    | Some alias ->
      if is_projection_wrapper alias.projection_record alias.projection_field body
      then alias.projection_inst
      else
        CErrors.user_err
          Pp.(
            str "Generated field " ++ N.pp n
            ++ str " is not the expected primitive-record projection")
    | None -> { ref; algs }
  in
  let () = add_declared n i inst in
  inst

and declare_ax { name = n; ty; univs } i =
  let uconv = start_uconv univs i in
  let uconv, ty = to_constr empty_env ty uconv in
  let univs, algs = univ_entry uconv univs in
  let entry = Declare.(ParameterEntry (parameter_entry ~univs ty)) in
  let c =
    Declare.declare_constant ~name:(name_for n i)
      ~kind:Decls.(IsAssumption Definitional)
      entry
  in
  let inst = { ref = GlobRef.ConstRef c; algs } in
  let () = add_declared n i inst in
  inst

and to_params uconv params =
  let acc, params =
    CList.fold_left_map
      (fun (env, uconv) (_bk, p, ty) ->
        let uconv, ty = to_constr env ty uconv in
        let d = RelDecl.LocalAssum (to_annot env p ty uconv, ty) in
        let env = Environ.push_rel_context_val d env in
        ((env, uconv), d))
      (empty_env, uconv) params
  in
  (acc, List.rev params)

and declare_ind { name = n; params; ty; ctors; univs } i =
  (* Handle inductives predeclared as definitions (e.g., ULift with cumulativity).
     We check if there's a cumul registration for this specific instance. *)
  match get_predeclared_ind_as_def_some n i with
  | Some (ULift_cumul, _, _) ->
    let def_name = name_for_core n i in
    let cumul_reg nm = "lean." ^ Id.to_string (name_for_core nm i) ^ ".cumul" in
    Feedback.msg_info Pp.(Id.print def_name ++ str " is predeclared (cumulative)");
    (* The Rocq cumul definitions take four universes [r s s1 rs1] where
       [s1] stands for Lean's [s+1] and [rs1] for Lean's [max(r+1, s+1)].
       Lean provides two universes [r; s], so the Rocq instance is represented
       by four algebraic universes over the Lean instance.  For [ULift.rec] at
       scheme j = 2*i (motive non-SProp), Lean also provides [motive] as the
       first universe, shifting [r] and [s] to positions 1 and 2 in [Level.var].
       For [ULift.rec] at j = 2*i+1 (motive SProp), [motive] is filtered out by
       [int_of_univs] so the indices match the non-rec case. *)
    let algs_of r_idx s_idx =
      let r = Universe.make (Level.var r_idx) in
      let s = Universe.make (Level.var s_idx) in
      [
        r;
        s;
        Universe.super s;
        Universe.sup (Universe.super r) (Universe.super s);
      ]
    in
    let algs_2 = algs_of 0 1 in
    let algs_rec = universe_var 0 :: algs_of 1 2 in
    let ulift_ref = Rocqlib.lib_ref (cumul_reg n) in
    let inst = { ref = ulift_ref; algs = algs_2 } in
    add_declared n i inst;
    (* Register ULift.up constructor *)
    let cname = N.append n "up" in
    add_declared cname i { ref = Rocqlib.lib_ref (cumul_reg cname); algs = algs_2 };
    (* Register ULift.down *)
    let dname = N.append n "down" in
    add_declared dname i { ref = Rocqlib.lib_ref (cumul_reg dname); algs = algs_2 };
    (* Register eliminator (Type scheme at j=2*i, SProp scheme at j=2*i+1) *)
    let nrec = N.append n "rec" in
    let rec_base = cumul_reg nrec in
    add_declared nrec (2 * i) { ref = Rocqlib.lib_ref rec_base; algs = algs_rec };
    add_declared nrec ((2 * i) + 1) { ref = Rocqlib.lib_ref (rec_base ^ ".ind"); algs = algs_2 };
    inst
  | None ->
  let mind, algs, ind_name, cnames, univs, squashy, projection_aliases =
    match get_predeclared_ind_some n i with
    | Some (Eq, _, (ind_name, mind)) ->
      (* Hack to let the user predeclare eq and quot before running Lean Import
         TODO make a more general Register-like API? *)
      Feedback.msg_info Pp.(Id.print ind_name ++ str " is predeclared");
      let cname = N.append n "refl" in
      let squashy =
        { maybe_prop = true; always_prop = true; lean_squashes = false }
      in
      let univs =
        match i with
        | 0 ->
          UContext.make
            { quals = [||]; univs =  [| Name (Id.of_string "u") |]}
            ( Instance.of_array ([||], [| univ_of_name (N.append N.anon "u") |]),
              PConstraints.empty )
        | 1 -> UContext.empty
        | _ -> assert false
      in
      ( mind,
        identity_algs (non_sprop_univ_count 1 i),
        ind_name,
        [ cname ],
        univs,
        squashy,
        [] )
    | Some
        ( ((Nat | Nat_le | Or | And | Fin | UInt32 | BitVec | Char) as k),
          _,
          (ind_name, mind) ) ->
      (* Hack to let the user predeclare various types before running Lean Import
         TODO make a more general Register-like API? *)
      (* this case is for the ones without universes*)
      Feedback.msg_info Pp.(Id.print ind_name ++ str " is predeclared");
      let cnames = get_predeclared_cnames k n in
      let squashy = N.Map.get n !squash_info in
      (mind, [], ind_name, cnames, UContext.empty, squashy, [])
    | None ->
      let uconv = start_uconv univs i in
      let (env_params, uconv), params = to_params uconv params in
      let uconv, ty = to_constr env_params ty uconv in
      let indices, sort =
        let env_params =
          Environ.set_rel_context_val env_params
            (Environ.set_universes uconv.graph (Global.env ()))
        in
        Reduction.dest_arity env_params ty
      in
      let env_ind =
        Environ.push_rel_context_val
          (LocalAssum
             ( Context.make_annot (N.to_name n) (Sorts.relevance_of_sort sort),
               Term.it_mkProd_or_LetIn ty params ))
          empty_env
      in
      let env_ind_params =
        Context.Rel.fold_outside Environ.push_rel_context_val params
          ~init:env_ind
      in
      let uconv, ctors =
        CList.fold_left_map
          (fun uconv (n, ty) ->
            let uconv, ty = to_constr env_ind_params ty uconv in
            (uconv, (n, ty)))
          uconv ctors
      in
      let cnames, ctys = List.split ctors in
      let graph = uconv.graph in
      let drop_global_lower_bounds =
        N.equal n list_name || N.equal n array_name
      in
      let univs, algs =
        univ_entry_gen ~drop_global_lower_bounds uconv univs
      in
      let ind_name = name_for n i in
      let record, fields, ctys, field_names =
        match (indices, ctys) with
        | [], [ cty ] ->
          cty
          |> with_env_evm env_ind_params uconv (fun env evm cty ->
                 let fields, codom =
                   Reductionops.whd_decompose_prod env evm
                     (EConstr.of_constr cty)
                 in
                 let field_names =
                   List.rev_map
                     (fun (annot, _) ->
                       match annot.Context.binder_name with
                       | Names.Anonymous -> None
                       | Names.Name id ->
                         Some (N.append n (Names.Id.to_string id)))
                     fields
                 in
                 let _, fields =
                   CList.fold_left_map
                     (fun ids (na, t) ->
                       match na.Context.binder_name with
                       | Names.Anonymous -> (ids, (na, t))
                       | Names.Name id ->
                         let id = Namegen.next_global_ident_away (Global.safe_env ()) id ids in
                         let ids = Id.Set.add id ids in
                         line_msg
                           (N.of_list
                              [
                                Names.Id.to_string id;
                                "(field)";
                                Names.Id.to_string ind_name;
                              ]);
                         (ids, ({ na with binder_name = Names.Name id }, t)))
                     (Id.Set.add ind_name Id.Set.empty)
                     fields
                 in
                 let cty' = EConstr.it_mkProd codom fields in
                 let cty' = EConstr.Unsafe.to_constr cty' in
                 (* A recursive single-constructor inductive cannot admit
                    eta, so the kernel rejects the primitive-record
                    encoding. Fall through to plain Inductive in that case. *)
                 let npars = List.length params in
                 let is_recursive =
                   let rec walk k c =
                     match Constr.kind c with
                     | Constr.Prod (_, t, body) ->
                       (not (Vars.noccurn k t)) || walk (k + 1) body
                     | _ -> false
                   in
                   walk (npars + 1) cty'
                 in
                 match (fields, Sorts.is_sprop sort, is_recursive) with
                 | [], true, _ -> (None, [], ctys, [])
                 | _ :: _, false, false ->
                   if
                     List.exists
                       (fun (na, _) ->
                         na.Context.binder_relevance
                         == EConstr.ERelevance.relevant)
                       fields
                   then
                     ( Some (Some [| default_proj_id |]),
                       fields,
                       [ cty' ],
                       field_names )
                   else (None, [], ctys, [])
                 | [], false, _ -> (None, [], ctys, [])
                 | _ :: _, true, false ->
                   if
                     List.for_all
                       (fun (na, _) ->
                         na.Context.binder_relevance
                         == EConstr.ERelevance.irrelevant)
                       fields
                   then
                     ( Some (Some [| default_proj_id |]),
                       fields,
                       [ cty' ],
                       field_names )
                   else (None, [], ctys, [])
                 | _ :: _, _, true -> (None, [], ctys, []))
        | _ -> (None, [], ctys, [])
      in
      let entry finite =
        {
          Entries.mind_entry_params = params;
          mind_entry_record = record;
          mind_entry_finite = finite;
          mind_entry_inds =
            [
              {
                mind_entry_typename = ind_name;
                mind_entry_arity = ty;
                mind_entry_consnames = List.map (fun n -> name_for n i) cnames;
                mind_entry_lc = ctys;
              };
            ];
          mind_entry_private = None;
          mind_entry_universes = Polymorphic_ind_entry univs;
          mind_entry_variance = None;
        }
      in
      let squashy = N.Map.get n !squash_info in
      let coq_squashes =
        if squashy.maybe_prop then coq_squashes graph (entry Finite) else false
      in
      let mind =
        let act finite =
          let all_depth =
            if N.equal n list_name || N.equal n option_name then Some 1
            else None
          in
          let schemes =
            if N.equal n list_name || N.equal n option_name then
              DeclareInd.Default
            else DeclareInd.None
          in
          DeclareInd.declare_mutual_inductive_with_eliminations ?all_depth
            ~schemes (entry finite)
            (* the ubinders API is kind of shit here *)
            (UState.Polymorphic_entry UContext.empty, UnivNames.empty_binders)
            []
        in
        let act () = try act BiFinite with e -> act Finite in
        if squashy.lean_squashes || not coq_squashes then act ()
        else with_unsafe_univs act ()
      in
      assert (
        squashy.lean_squashes
        || (Global.lookup_mind mind).mind_packets.(0).mind_squashed == None);
      let () =
        if N.equal n array_name then array_minds := mind :: !array_minds
        else if N.equal n prod_name then prod_minds := mind :: !prod_minds
        else if N.equal n list_name then list_minds := mind :: !list_minds
        else if N.equal n option_name then option_minds := mind :: !option_minds
      in
      (* Declare projections if the inductive is a record *)
      let projections =
        match record with
        | Some (Some _) ->
          let inhabitant_id = ind_name in
          let kind = Decls.StructureComponent in
          let proj_flags =
            List.map
              (fun _ ->
                {
                  Record.Data.pf_coercion = None;
                  pf_instance = None;
                  pf_canonical = false;
                })
              fields
          in
          let implfs = List.map (fun _ -> []) fields in
          Record.Internal.declare_projections (mind, 0) ~kind ~inhabitant_id
            proj_flags implfs
        | _ -> []
      in
      let projection_aliases =
        let rec collect field projections names aliases =
          match projections, names with
          | [], [] -> List.rev aliases
          | projection :: projections, name :: names ->
            let aliases =
              match name, projection with
              | Some name,
                { Structures.Structure.proj_body = Some constant; _ } ->
                ( name,
                  {
                    projection_inst =
                      { ref = GlobRef.ConstRef constant; algs };
                    projection_record = n;
                    projection_ind = (mind, 0);
                    projection_field = field;
                  } )
                :: aliases
              | _ -> aliases
            in
            collect (field + 1) projections names aliases
          | _ ->
            CErrors.user_err
              Pp.(str "Primitive-record fields and projections differ")
        in
        collect 0 projections field_names []
      in
      let () =
        if N.equal n array_name then
          declare_array_all_scheme mind ind_name univs fields projections
        else if N.equal n prod_name then
          declare_prod_second_all_scheme mind ind_name univs projections
        else if
          last_projection_is_only_parameter_use mind univs projections
        then declare_last_field_all_scheme mind ind_name univs projections
      in
      (mind, algs, ind_name, cnames, univs, squashy, projection_aliases)
  in

  (* add ind and ctors to [declared] *)
  let inst = { ref = GlobRef.IndRef (mind, 0); algs } in
  let () = add_declared n i inst in
  let () =
    CList.iteri
      (fun cnum cname ->
        add_declared cname i
          { ref = GlobRef.ConstructRef ((mind, 0), cnum + 1); algs })
      cnames
  in
  let () =
    List.iter
      (fun (name, alias) ->
        add_declared name i alias.projection_inst;
        add_projection_alias name i alias)
      projection_aliases
  in

  declare_lean_schemes ~mind ~ind_index:0 ~n ~ind_name ~i ~univs ~algs
    ~squashy;
  let env = Environ.push_context ~strict:true univs (Global.env ()) in
  let packet = (Global.lookup_mind mind).mind_packets.(0) in
  let nested_recursive =
    Array.exists
      (fun (ctor_args, _) ->
        List.exists
          (fun arg ->
            let arg_ty = RelDecl.get_type arg in
            if not (has_rec_hyp env mind arg_ty) then false
            else
              let _, head = Reduction.whd_decompose_prod_decls env arg_ty in
              let head, _ = Constr.decompose_app head in
              match Constr.kind head with
              | Constr.Ind ((arg_mind, _), _) ->
                not (MutInd.UserOrd.equal mind arg_mind)
              | _ -> true)
          ctor_args)
      packet.mind_nf_lc
  in
  if nested_recursive then
    register_mutual_nested_recursors ~mind ~nparams:(List.length params) [ n ];
  inst

and declare_mutual_inductive_instance inds i =
  match inds with
  | [] | [ _ ] -> assert false
  | first :: _ ->
    let ntypes = List.length inds in
    let nparams = List.length first.params in
    if
      List.exists
        (fun ind -> ind.params <> first.params || ind.univs <> first.univs)
        inds
    then
      CErrors.user_err
        Pp.(str "Mutual inductives have different parameters or universes");
    let group_names = List.map (fun ind -> ind.name) inds in
    let uconv = start_uconv first.univs i in
    let (env_params, uconv), params = to_params uconv first.params in
    let uconv, arities =
      CList.fold_left_map
        (fun uconv ind ->
          let uconv, ty = to_constr env_params ind.ty uconv in
          let _indices, sort =
            let env =
              Environ.set_rel_context_val env_params
                (Environ.set_universes uconv.graph (Global.env ()))
            in
            Reduction.dest_arity env ty
          in
          uconv, (ind, ty, sort))
        uconv inds
    in
    let env_inds =
      List.fold_left
        (fun env (ind, ty, sort) ->
          Environ.push_rel_context_val
            (LocalAssum
               ( Context.make_annot
                   (N.to_name ind.name)
                   (Sorts.relevance_of_sort sort),
                 Term.it_mkProd_or_LetIn ty params ))
            env)
        empty_env arities
    in
    let env_ind_params =
      Context.Rel.fold_outside Environ.push_rel_context_val params
        ~init:env_inds
    in
    let (_current, uconv), packets =
      CList.fold_left_map
        (fun (current, uconv) (ind, ty, _sort) ->
          let uconv, ctors =
            CList.fold_left_map
              (fun uconv (ctor_name, ctor_ty) ->
                let ctor_ty =
                  remap_mutual_constructor ~nparams ~ntypes ~group_names
                    ~current ctor_ty
                in
                let uconv, ctor_ty = to_constr env_ind_params ctor_ty uconv in
                uconv, (ctor_name, ctor_ty))
              uconv ind.ctors
          in
          let ctor_names, ctor_types = List.split ctors in
          ( (current + 1, uconv),
            {
              source_inductive = ind;
              translated_arity = ty;
              constructor_names = ctor_names;
              constructor_types = ctor_types;
            } ))
        (0, uconv) arities
    in
    let univs, algs = univ_entry_gen uconv first.univs in
    let entry finite =
      {
        Entries.mind_entry_params = params;
        mind_entry_record = None;
        mind_entry_finite = finite;
        mind_entry_inds =
          List.map
            (fun packet ->
              {
                Entries.mind_entry_typename =
                  name_for packet.source_inductive.name i;
                mind_entry_arity = packet.translated_arity;
                mind_entry_consnames =
                  List.map
                    (fun name -> name_for name i)
                    packet.constructor_names;
                mind_entry_lc = packet.constructor_types;
              })
            packets;
        mind_entry_private = None;
        mind_entry_universes = Entries.Polymorphic_ind_entry univs;
        mind_entry_variance = None;
      }
    in
    let mind =
      let act finite =
        DeclareInd.declare_mutual_inductive_with_eliminations
          ~schemes:DeclareInd.None (entry finite)
          (UState.Polymorphic_entry UContext.empty, UnivNames.empty_binders)
          []
      in
      try act Declarations.BiFinite with _ -> act Declarations.Finite
    in
    List.iteri
      (fun ind_index packet ->
        add_declared packet.source_inductive.name i
          { ref = GlobRef.IndRef (mind, ind_index); algs };
        List.iteri
          (fun ctor_index ctor_name ->
            add_declared ctor_name i
              {
                ref =
                  GlobRef.ConstructRef
                    ((mind, ind_index), ctor_index + 1);
                algs;
              })
          packet.constructor_names)
      packets;
    List.iteri
      (fun ind_index packet ->
        let ind = packet.source_inductive in
        declare_lean_schemes ~mind ~ind_index ~n:ind.name
          ~ind_name:(name_for ind.name i) ~i ~univs ~algs
          ~squashy:(N.Map.get ind.name !squash_info))
      packets;
    register_mutual_nested_recursors ~mind ~nparams
      (List.map
         (fun packet -> packet.source_inductive.name)
         packets)

and declare_lean_schemes ~mind ~ind_index ~n ~ind_name ~i ~univs ~algs
    ~squashy =
  let make_scheme fam =
    let u =
      if fam = SchemeSProp then LSProp
      else
        let u =
          if lean_fancy_univs () then
            let u = DirPath.make [ Id.of_string "motive"; lean_id ] in
            Level.(make (UGlobal.make u "" 0))
          else UnivGen.fresh_level ()
        in
        Level u
    in
    let env = Environ.push_context ~strict:true univs (Global.env ()) in
    let env =
      match u with
      | LSProp -> env
      | Level u ->
        Environ.push_context_set ~strict:false
          (Univ.ContextSet.singleton u) env
    in
    let inst = UContext.instance univs in
    let csts = UContext.constraints univs in
    let { quals = qnames; univs = unames } = UContext.names univs in
    let uentry =
      match u with
      | LSProp -> UState.Polymorphic_entry univs
      | Level u ->
        UState.Polymorphic_entry
          (UContext.make
             {
               quals = qnames;
               univs =
                 Array.append [| Name (Id.of_string "motive") |] unames;
             }
             ( Instance.of_array
                 ([||], Array.append [| u |] (snd (Instance.to_array inst))),
               csts ))
    in
    lean_scheme env ~dep:true (mind, ind_index) inst u, uentry
  in
  let declare_one_scheme (suffix, sort) =
    let id = Id.of_string (Id.to_string ind_name ^ suffix) in
    let body, uentry = make_scheme sort in
    let elim =
      quickdef ~name:id ~types:None
        ~univs:(uentry, UnivNames.empty_binders) body
    in
    let liftu level =
      let u =
        match Level.var_index level with
        | None -> Universe.make level
        | Some index -> Universe.make (Level.var (index + 1))
      in
      Some u
    in
    let scheme_algs =
      if sort = SchemeSProp then algs
      else
        universe_var 0
        :: List.map (UnivSubst.subst_univs_universe liftu) algs
    in
    let scheme_index =
      if squashy.lean_squashes then i
      else if sort = SchemeType then 2 * i
      else (2 * i) + 1
    in
    let recursor = N.append n "rec" in
    (match (Global.lookup_mind mind).mind_packets.(ind_index).mind_record, elim
     with
    | Declarations.PrimRecord _, GlobRef.ConstRef constant ->
      Global.set_strategy (Conv_oracle.EvalConstRef constant)
        Conv_oracle.Expand;
      expand_head_cache := N.Set.add recursor !expand_head_cache
    | _ -> ());
    add_declared recursor scheme_index { ref = elim; algs = scheme_algs }
  in
  let elims =
    if squashy.lean_squashes then [ "_indl", SchemeSProp ]
    else [ "_recl", SchemeType; "_indl", SchemeSProp ]
  in
  List.iter
    (fun elim ->
      try declare_one_scheme elim
      with e when CErrors.noncritical e && error_mode e = Skip ->
        Feedback.msg_info Pp.(str "Skipping scheme"))
    elims

(** Generate and add the squashy info *)
let squashify { name = n; params; ty; ctors; univs } =
  let uconvP =
    (* NB: if univs = [] this is just instantiation 0 *)
    start_uconv univs ((1 lsl List.length univs) - 1)
  in
  let (env_paramsP, uconvP), paramsP = to_params uconvP params in
  let uconvP, tyP = to_constr env_paramsP ty uconvP in
  let envP =
    Environ.push_rel_context paramsP
      (Environ.set_universes uconvP.graph (Global.env ()))
  in
  let _, sortP = Reduction.dest_arity envP tyP in
  if not (Sorts.is_sprop sortP) then noprop
  else
    let uconvT = start_uconv univs 0 in
    let (env_paramsT, uconvT), paramsT = to_params uconvT params in
    let uconvT, tyT = to_constr env_paramsT ty uconvT in
    let envT =
      Environ.set_rel_context_val env_paramsT
        (Environ.set_universes uconvT.graph (Global.env ()))
    in
    let _, sortT = Reduction.dest_arity envT tyT in
    let always_prop = Sorts.is_sprop sortT in
    match ctors with
    | [] -> { maybe_prop = true; always_prop; lean_squashes = false }
    | _ :: _ :: _ -> { maybe_prop = true; always_prop; lean_squashes = true }
    | [ (_, ctor) ] ->
      let envT =
        Context.Rel.fold_outside Environ.push_rel_context_val paramsT
          ~init:
            (Environ.push_rel_context_val
               (LocalAssum
                  ( Context.make_annot (N.to_name n)
                      (Sorts.relevance_of_sort sortT),
                    Term.it_mkProd_or_LetIn tyT paramsT ))
               empty_env)
      in
      let uconvT, ctorT = to_constr envT ctor uconvT in
      let envT =
        Environ.set_rel_context_val envT
          (Environ.set_universes uconvT.graph (Global.env ()))
      in
      let args, out = Reduction.whd_decompose_prod envT ctorT in
      let forced =
        (* NB dest_prod returns [out] in whnf *)
        let _, outargs = Constr.decompose_app out in
        Array.fold_left
          (fun forced arg ->
            match Constr.kind arg with
            | Rel i -> Int.Set.add i forced
            | _ -> forced)
          Int.Set.empty outargs
      in
      let sigma = Evd.from_env envT in
      let npars = List.length params in
      let nargs = List.length args in
      let lean_squashes, _, _ =
        Context.Rel.fold_outside
          (fun d (squashed, i, envT) ->
            let squashed =
              if squashed then true
              else if Int.Set.mem (nargs - i) forced then false
              else
                let t = RelDecl.get_type d in
                if not (Vars.noccurn (npars + i + 1) t) then
                  (* recursive argument *)
                  false
                else
                  not
                    (EConstr.ESorts.is_sprop sigma
                       (Retyping.get_sort_of envT sigma (EConstr.of_constr t)))
            in

            (squashed, i + 1, Environ.push_rel d envT))
          args ~init:(false, 0, envT)
      in
      (* TODO translate to use non recursively uniform params (fix extraction)*)
      { maybe_prop = true; always_prop; lean_squashes }

let squashify ind =
  let s = squashify ind in
  squash_info := N.Map.add ind.name s !squash_info

let squashify_mutual inds =
  match inds with
  | [] | [ _ ] -> assert false
  | first :: _ ->
    let ntypes = List.length inds in
    let nparams = List.length first.params in
    let group_names = List.map (fun ind -> ind.name) inds in
    let context_for_instance i =
      let uconv = start_uconv first.univs i in
      let (env_params, uconv), params = to_params uconv first.params in
      let uconv, arities =
        CList.fold_left_map
          (fun uconv ind ->
            let uconv, ty = to_constr env_params ind.ty uconv in
            let env =
              Environ.set_rel_context_val env_params
                (Environ.set_universes uconv.graph (Global.env ()))
            in
            let _, sort = Reduction.dest_arity env ty in
            uconv, (ind, ty, sort))
          uconv inds
      in
      let env_inds =
        List.fold_left
          (fun env (ind, ty, sort) ->
            Environ.push_rel_context_val
              (LocalAssum
                 ( Context.make_annot (N.to_name ind.name)
                     (Sorts.relevance_of_sort sort),
                   Term.it_mkProd_or_LetIn ty params ))
              env)
          empty_env arities
      in
      let env_ind_params =
        Context.Rel.fold_outside Environ.push_rel_context_val params
          ~init:env_inds
      in
      (uconv, params, arities, env_ind_params)
    in
    let uconvP, _, aritiesP, _ =
      context_for_instance ((1 lsl List.length first.univs) - 1)
    in
    let uconvT, paramsT, aritiesT, envT = context_for_instance 0 in
    let _ = uconvP in
    CList.iteri
      (fun current ((ind, _, sortP), (_, _, sortT)) ->
        let info =
          if not (Sorts.is_sprop sortP) then noprop
          else
            let always_prop = Sorts.is_sprop sortT in
            if always_prop then
              { maybe_prop = true; always_prop; lean_squashes = true }
            else match ind.ctors with
            | [] -> { maybe_prop = true; always_prop; lean_squashes = false }
            | _ :: _ :: _ ->
              { maybe_prop = true; always_prop; lean_squashes = true }
            | [ (_, ctor) ] ->
              let ctor =
                remap_mutual_constructor ~nparams ~ntypes ~group_names
                  ~current ctor
              in
              let uconvT, ctorT = to_constr envT ctor uconvT in
              let envT =
                Environ.set_rel_context_val envT
                  (Environ.set_universes uconvT.graph (Global.env ()))
              in
              let args, out = Reduction.whd_decompose_prod envT ctorT in
              let _, outargs = Constr.decompose_app out in
              let forced =
                Array.fold_left
                  (fun forced arg ->
                    match Constr.kind arg with
                    | Rel i -> Int.Set.add i forced
                    | _ -> forced)
                  Int.Set.empty outargs
              in
              let sigma = Evd.from_env envT in
              let nargs = List.length args in
              let lean_squashes, _, _ =
                Context.Rel.fold_outside
                  (fun d (squashed, i, env) ->
                    let recursive =
                      let first_mutual = nparams + i + 1 in
                      let rec occurs offset =
                        offset < ntypes
                        &&
                        (not
                           (Vars.noccurn (first_mutual + offset)
                              (RelDecl.get_type d))
                        || occurs (offset + 1))
                      in
                      occurs 0
                    in
                    let squashed =
                      squashed
                      ||
                      (not (Int.Set.mem (nargs - i) forced)
                      && not recursive
                      && not
                           (EConstr.ESorts.is_sprop sigma
                              (Retyping.get_sort_of env sigma
                                 (EConstr.of_constr (RelDecl.get_type d)))))
                    in
                    (squashed, i + 1, Environ.push_rel d env))
                  args ~init:(false, 0, envT)
              in
              { maybe_prop = true; always_prop; lean_squashes }
        in
        squash_info := N.Map.add ind.name info !squash_info)
      (List.combine aritiesP aritiesT)

(* pairs of (name * number of univs) *)
let quots = [ ("", 1); ("mk", 1); ("lift", 2); ("ind", 1) ]

let declare_quot quot_name =
  let () =
    List.iter
      (fun (n, nunivs) ->
        let rec loop i =
          if i = 1 lsl nunivs then ()
          else
            let lean =
              if CString.is_empty n then quot_name else N.append quot_name n
            in
            let reg =
              "lean." ^ N.to_lean_string lean
              ^ if i = 0 then "" else "_inst" ^ string_of_int i
            in
            let ref = Rocqlib.lib_ref reg in
            let algs = identity_algs (non_sprop_univ_count nunivs i) in
            let () = add_declared lean i { ref; algs } in
            loop (i + 1)
        in
        loop 0)
      quots
  in
  Feedback.msg_info Pp.(str "quot registered")

let declare_quot quot_name =
  if Rocqlib.has_ref "lean.Quot" then declare_quot quot_name else raise MissingQuot

let { Goptions.get = just_parse } =
  Goptions.declare_bool_option_and_ref
    ~key:[ "Lean"; "Just"; "Parsing" ]
    ~value:false ()

(* with this off: best line 23000 in stdlib
   stack overflow

   update: got fixed by e9e637de26 (distinguish names foo.bar and foo_bar)
*)
let { Goptions.get = upfront_instances } =
  Goptions.declare_bool_option_and_ref
    ~key:[ "Lean"; "Upfront"; "Instantiation" ]
    ~value:false ()

let { Goptions.get = lazy_instances } =
  Goptions.declare_bool_option_and_ref
    ~key:[ "Lean"; "Lazy"; "Instantiation" ]
    ~value:false ()

let declare_instances act univs =
  let stop = if upfront_instances () then 1 lsl List.length univs else 1 in
  let rec loop i =
    if i = stop then ()
    else
      let () = act i in
      loop (i + 1)
  in
  if not (lazy_instances ()) then loop 0

let declare_def def =
  declare_instances (fun i -> ignore (declare_def def i)) def.univs

let declare_ax ax =
  declare_instances (fun i -> ignore (declare_ax ax i)) ax.univs

let declare_ind ind =
  let () = squashify ind in
  declare_instances (fun i -> ignore (declare_ind ind i)) ind.univs

let declare_mutual_inductive_group inds =
  squashify_mutual inds;
  match inds with
  | [] -> assert false
  | first :: _ ->
    declare_instances
      (fun i -> declare_mutual_inductive_instance inds i)
      first.univs

let entry_name = function
| Quot name | Def { name } | Ax { name } | Ind { name } -> name

let add_entry entry =
  let () =
    match entry with
    | Quot quot_name -> declare_quot quot_name
    | Def def -> declare_def def
    | Ax ax -> declare_ax ax
    | Ind ind -> declare_ind ind
  in
  entries := N.Map.add (entry_name entry) entry !entries

let add_mutual_entries inds =
  List.iter
    (fun ind ->
      entries := N.Map.add ind.name (Ind ind) !entries;
      mutual_entries := N.Map.add ind.name inds !mutual_entries)
    inds;
  declare_mutual_inductive_group inds

let rec is_arity = function
  | Sort _ -> true
  | Pi (_, _, _, b) -> is_arity b
  | _ -> false

let { Goptions.get = print_squashes } =
  Goptions.declare_bool_option_and_ref
    ~key:[ "Lean"; "Print"; "Squash"; "Info" ]
    ~value:false ()

type input_state = {
  pstate : LeanParse.parsing_state;
  skips : int;
}

type pending_inductive_group = {
  first_line : int;
  first_raw : string;
  members_rev : ind list;
}

let finish state =
  let max_univs, cnt =
    N.Map.fold
      (fun _ entry (m, cnt) ->
        match entry with
        | Ax { univs } | Def { univs } | Ind { univs } ->
          let l = List.length univs in
          (max m l, cnt + (1 lsl l))
        | Quot _ -> (max m 1, cnt + 2))
      !entries (0, 0)
  in
  let nonarities =
    N.Map.fold
      (fun _ entry cnt ->
        match entry with
        | Ax _ | Def _ | Quot _ -> cnt
        | Ind ind -> if is_arity ind.ty then cnt else cnt + 1)
      !entries 0
  in
  let squashes =
    if not (print_squashes ()) then Pp.mt ()
    else
      N.Map.fold
        (fun n s pp -> Pp.(pp ++ fnl () ++ N.pp n ++ spc () ++ pp_squashy s))
        !squash_info
        Pp.(mt ())
  in
  Feedback.msg_info
    Pp.(
      fnl () ++ fnl () ++ str "Done!" ++ fnl () ++ str "- "
      ++ int (N.Map.cardinal !entries)
      ++ str " entries (" ++ int cnt ++ str " possible instances)"
      ++ (if N.Map.exists (fun _ -> function Quot _ -> true | _ -> false) !entries then
            str " (including quot)."
          else str ".")
      ++ fnl () ++
      LeanParse.pp_state state.pstate ++
      (if state.skips > 0 then str "Skipped " ++ int state.skips ++ fnl ()
       else mt ())
      ++ str "Max universe instance length "
      ++ int max_univs ++ str "." ++ fnl () ++ int nonarities
      ++ str " inductives have non syntactically arity types."
      ++ squashes)

let prtime t0 t1 =
  let diff = System.time_difference t0 t1 in
  if diff > 1.0 then
    Feedback.msg_info
      Pp.(
        str "line " ++ int !lcnt ++ str " took "
        ++ System.fmt_time_difference t0 t1)

let timeout = ref None

let () =
  Goptions.declare_int_option
    {
      optdepr = None;
      optstage = Interp;
      optkey = [ "Lean"; "Line"; "Timeout" ];
      optread = (fun () -> !timeout);
      optwrite = (fun x -> timeout := x);
    }

exception TimedOut

let do_line state l =
  let do_line () = LeanParse.do_line state ~lcnt:!lcnt l in
  match !timeout with
  | None -> do_line ()
  | Some t ->
    (match Control.timeout (float_of_int t) do_line () with
    | Ok v -> v
    | Error info -> Exninfo.iraise (TimedOut, info))

let do_line state l =
  let t0 = System.get_time () in
  match do_line state l with
  | state ->
    let t1 = System.get_time () in
    prtime t0 t1;
    state
  | exception e ->
    let e = Exninfo.capture e in
    (if fst e <> TimedOut then
       let t1 = System.get_time () in
       prtime t0 t1);
    Exninfo.iraise e

let before_from = function None -> false | Some from -> !lcnt < from
let freeze () = (Lib.Interp.freeze (), Summary.Interp.freeze_summaries ())

let unfreeze (lib, sum) =
  Lib.Interp.unfreeze lib;
  Summary.Interp.unfreeze_summaries sum

let process_effect state ch ~line_no ~raw ~name act =
  let st = freeze () in
  match act () with
  | () -> Some state
  | exception e ->
    let e = Exninfo.capture e in
    let epp =
      Pp.(
        str "Error at line " ++ int line_no ++ str " (for " ++ N.pp name
        ++ str ")" ++ str (": " ^ raw) ++ fnl () ++ CErrors.iprint e)
    in
    unfreeze st;
    match error_mode (fst e) with
    | Skip ->
      Feedback.msg_info Pp.(str "Skipping: " ++ epp);
      Some { state with skips = state.skips + 1 }
    | Stop ->
      close_in ch;
      finish state;
      Feedback.msg_info epp;
      None
    | Fail ->
      close_in ch;
      finish state;
      CErrors.user_err epp

let process_pending state ch = function
  | None -> Some state
  | Some { first_line; first_raw; members_rev } ->
    let inds = List.rev members_rev in
    let first =
      match inds with first :: _ -> first | [] -> assert false
    in
    process_effect state ch ~line_no:first_line ~raw:first_raw
      ~name:first.name (fun () ->
        match inds with
        | [ ind ] -> add_entry (Ind ind)
        | _ -> add_mutual_entries inds)

let rec do_input_pending state ~from ~until ~pending ch =
  if until = Some !lcnt then begin
    match process_pending state ch pending with
    | None -> state
    | Some state ->
      close_in ch;
      finish state;
      state
  end
  else
    match input_line ch with
    | exception End_of_file ->
      (match process_pending state ch pending with
      | None -> state
      | Some state ->
        close_in ch;
        finish state;
        if not (until = None) then
          CErrors.user_err Pp.(str "unexpected EOF!");
        state)
    | _ when before_from from ->
      incr lcnt;
      do_input_pending state ~from ~until ~pending ch
    | line ->
      let pstate, oentry = do_line state.pstate line in
      let state = { state with pstate } in
      (match (just_parse (), oentry) with
      | false, Some (Entry (Ind ind)) ->
        let pending =
          match pending with
          | None ->
            Some
              {
                first_line = !lcnt;
                first_raw = line;
                members_rev = [ ind ];
              }
          | Some pending ->
            Some { pending with members_rev = ind :: pending.members_rev }
        in
        incr lcnt;
        do_input_pending state ~from ~until ~pending ch
      | _ ->
        match process_pending state ch pending with
        | None -> state
        | Some state ->
          let state_opt =
            match (just_parse (), oentry) with
            | true, _ | false, None | false, Some (Nota _) -> Some state
            | false, Some (Entry entry) ->
              process_effect state ch ~line_no:!lcnt ~raw:line
                ~name:(entry_name entry) (fun () -> add_entry entry)
          in
          match state_opt with
          | None -> state
          | Some state ->
            incr lcnt;
            do_input_pending state ~from ~until ~pending:None ch)

let do_input state ~from ~until ch =
  do_input_pending state ~from ~until ~pending:None ch

let pstate = Summary.ref ~name:"lean-parse-state" LeanParse.empty_state

let lean_obj =
  let cache
      ( pstatev,
        setsv,
        declaredv,
        entriesv,
        mutual_entriesv,
        squash_infov,
        heightv ) =
    pstate := pstatev;
    sets := setsv;
    declared := declaredv;
    entries := entriesv;
    mutual_entries := mutual_entriesv;
    squash_info := squash_infov;
    height_cache := heightv;
    ()
  in
  let open Libobject in
  declare_object
    {
      (default_object "LEAN-IMPORT-STATE") with
      cache_function = cache;
      load_function = (fun _ v -> cache v);
      classify_function = (fun _ -> Keep);
    }

let import ~from ~until f =
  lcnt := 1;
  (* silence the definition messages from Coq *)
  let { pstate = pstatev } =
    Flags.silently (fun () ->
        do_input { pstate = !pstate; skips = 0 } ~from ~until (open_in f)) ()
  in
  Lib.add_leaf
    (lean_obj
       ( pstatev,
         !sets,
         !declared,
         !entries,
         !mutual_entries,
         !squash_info,
         !height_cache ))
