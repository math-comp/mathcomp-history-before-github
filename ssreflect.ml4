(* (c) Copyright Microsoft Corporation. All rights reserved. *)
(*i camlp4deps: "parsing/grammar.cma" i*)

open Names
open Pp
open Pcoq
open Genarg
open Term
open Topconstr
open Libnames
open Tactics
open Tacticals
open Termops
open Tacmach
open Coqlib
open Rawterm
open Util
open Evd
open Extend
open Goptions
open Tacexpr
open Tacinterp
open Constr
open Tactic
open Extraargs
open Ppconstr
open Printer

let tactic_expr = Tactic.tactic_expr
let sprintf = Printf.sprintf

(** 1. Utilities *)

(** Primitive parsing to avoid syntax conflicts with basic tactics. *)

let accept_before_syms syms strm =
  match Stream.npeek 2 strm with
  | [_; "", sym] when List.mem sym syms -> Stream.junk strm
  | _ -> raise Stream.Failure

let accept_before_syms_or_id syms strm =
  match Stream.npeek 2 strm with
  | [_; "", sym] when List.mem sym syms -> Stream.junk strm
  | [_; "IDENT", _] -> Stream.junk strm
  | _ -> raise Stream.Failure

(** Pretty-printing utilities *)

let pr_id = Ppconstr.pr_id
let pr_name = function Name id -> pr_id id | Anonymous -> str "_"
let pr_spc () = str " "
let pr_bar () = Pp.cut() ++ str "|"
let pr_list = prlist_with_sep

let tacltop = (5,Ppextend.E)

(* More sensible names for constr printers *)

let prl_constr = pr_lconstr
let pr_constr = pr_constr

let prl_rawconstr c = pr_lrawconstr_env (Global.env ()) c
let pr_rawconstr c = pr_rawconstr_env (Global.env ()) c

let prl_constr_expr = pr_lconstr_expr
let pr_constr_expr = pr_constr_expr

let prl_rawconstr_and_expr = function
  | _, Some c -> prl_constr_expr c
  | c, None -> prl_rawconstr c

let pr_rawconstr_and_expr = function
  | _, Some c -> pr_constr_expr c
  | c, None -> pr_rawconstr c

(* primitive intropatterns (for ltac argument substitution) *)

let rec pr_intropattern = function
  | IntroIdentifier id -> pr_id id
  | IntroAnonymous -> str "?"
  | IntroWildcard -> str "_"
  | IntroOrAndPattern iorpat ->
    let pr_iorpat = pr_list pr_bar (pr_list pr_spc pr_intropattern) in
    hov 1 (str "[" ++ pr_iorpat iorpat ++ str "]")

(* Term printing utilities functions for deciding bracketing.  *)

let pr_paren prx x = hov 1 (str "(" ++ prx x ++ str ")")

(* String lexing utilities *)
let skip_wschars s =
  let rec loop i = match s.[i] with '\n'..' ' -> loop (i + 1) | _ -> i in loop

let skip_numchars s =
  let rec loop i = match s.[i] with '0'..'9' -> loop (i + 1) | _ -> i in loop

(* The call 'guard s i' should return true if the contents of s *)
(* starting at i need bracketing to avoid ambiguities.          *)

let pr_guarded guard prc c =
  msg_with Format.str_formatter (prc c);
  let s = Format.flush_str_formatter () ^ "$" in
  if guard s (skip_wschars s 0) then pr_paren prc c else prc c

(** Tactic-level diagnosis *)

let loc_error loc msg = user_err_loc (loc, msg, str msg)

let errorstrm = errorlabstrm "ssreflect"

let pf_pr_constr gl = pr_constr_env (pf_env gl)

let pf_pr_rawconstr gl = pr_rawconstr_env (pf_env gl)

(* debug *)

let pf_msg gl =
   let ppgl = pr_lconstr_env (pf_env gl) (pf_concl gl) in
   msgnl (str "goal is " ++ ppgl)

let msgtac gl = pf_msg gl; tclIDTAC gl

(** Tactic utilities *)

let pf_image gl tac = let gls, _ = tac gl in first_goal gls

let last_goal gls = let sigma, gll = Refiner.unpackage gls in
   Refiner.repackage sigma (List.nth gll (List.length gll - 1))

let pf_image_last gl tac = let gls, _ = tac gl in last_goal gls

let pf_type_id gl t = id_of_string (hdchar (pf_env gl) t)

let in_context id = List.exists (fun (id', _, _) -> id' = id)

let proof_local () =
  let section_context = Environ.named_context (Global.env ()) in
  fun id -> not (in_context id section_context)

let pf_filter_hyps gl select =
  let add_hyp (id, _, _) ids = if select id then id :: ids else ids in
  List.fold_right add_hyp (pf_hyps gl) []
  
let pf_is_hyp gl id = in_context id (pf_hyps gl) && proof_local () id

let pf_ids_of_proof_hyps gl = pf_filter_hyps gl (proof_local ())

let pf_check_hyps gl hyps =
  let count_match id n = if List.mem id hyps then n + 1 else n in
  let n = List.fold_right count_match (pf_ids_of_proof_hyps gl) 0 in
  if n = List.length hyps then hyps else
  Util.error "Incorrect or duplicate assumption name for \"in\" tactical"

(* Private version of some tactics *)

let convert_concl_no_check t = convert_concl_no_check t DEFAULTcast
let convert_concl t = convert_concl t DEFAULTcast
let reduct_in_concl t = reduct_in_concl (t, DEFAULTcast)
let assert_tac = function
  | Anonymous -> forward None IntroAnonymous
  | Name id -> forward None (IntroIdentifier id)

(** Name generation *)

(* Separator for composite ids; should be '_' or ' '. The latter avoids *)
(* clashes with user names and gives prettier error, but may give       *)
(* incorrect printouts of proofs.                                       *)

let tag_sep = ' '

let id_of_tag s =
  if tag_sep = ' ' then id_of_string s else begin
    let s' = String.copy s in
    for i = 0 to String.length s - 1 do
      if s.[i] = ' ' then s'.[i] <- tag_sep
    done;
    id_of_string s'
  end

let tag_id tag id = id_of_tag (sprintf "%s %s" tag (string_of_id id))

let is_tag_id tag id =
  let n = String.length tag in let s = string_of_id id in
  String.length s > n && s.[n] = tag_sep && String.sub s 0 n = tag

(** Constructors for constr_expr *)

let mkCProp loc = CSort (loc, RProp Null)

let mkCType loc = CSort (loc, RType None)

let mkCVar loc id = CRef (Ident (loc, id))

let exactCVarId loc = function
  | CRef (Ident(loc', id)) when loc' = loc -> Some id
  | _ -> None

(** Constructors for rawconstr *)

let dC = CastConv DEFAULTcast

let mkRHole = RHole (dummy_loc, InternalHole)

let rec mkRHoles n = if n > 0 then mkRHole :: mkRHoles (n - 1) else []

let mkRApp f args = if args = [] then f else RApp(dummy_loc, f, args)

let mkRVar id = RVar (dummy_loc, id)

let mkRCast rc rt =  RCast (dummy_loc, rc, dC, rt)

let mkRType =  RSort (dummy_loc, RType None)

let mkRArrow rt1 rt2 = RProd (dummy_loc, Anonymous, rt1, rt2)

let mkRConstruct c = RRef (dummy_loc, ConstructRef c)

(* look up a name in the ssreflect internals module *)

let ssrdirpath = make_dirpath [id_of_string "ssreflect"]

let ssrqid name = make_qualid ssrdirpath (id_of_string name) 

let mkSsrRef name =
  try Constrintern.locate_reference (ssrqid name)
  with Not_found -> Util.error "Small scale reflection library not loaded"

let mkSsrRRef name = RRef (dummy_loc, mkSsrRef name)

let mkSsrConst name = constr_of_reference (mkSsrRef name)

(** Constructors for constr *)

let mkAppRed f c = match kind_of_term f with
| Lambda (_, _, b) -> subst1 c b
| _ -> mkApp (f, [|c|])

let pf_mkProd gl oid t c = match oid with
  | Some id -> mkProd (Name id, t, c)
  | None when noccurn 1 c -> mkArrow t c
  | None ->  mkProd (Name (pf_type_id gl t), t, c)

let mkProt t c = mkApp (mkSsrConst "protect_term", [|t; c|])

(** Open term to lambda-term coercion *)

(* This operation takes a goal gl and an open term (sigma, t), and   *)
(* returns a term t' where all the new evars in sigma are abstracted *)
(* with the mkAbs argument, i.e., for mkAbs = mkLambda then there is *)
(* some duplicate-free array args of evars of sigma such that the    *)
(* term mkApp (t', args) is convertible to t.                        *)
(* This makes a useful shorthand for local definitions in proofs,    *)
(* i.e., pose succ = _ + 1 means pose succ := fun n : nat => n + 1,  *)
(* and, in context of the the 4CT library, pose mid := maps id means *)
(*    pose mid := fun d : dataSet => @maps d d (@id (datum d))       *)
(* Note that this facility does not extend to set and def, which try *)
(* instead to fill holes by matching a goal subterm.                 *)
(* The argument to step uses product abstraction, e.g.               *)
(*    step Hmid: forall s, (maps id s) = s.                          *)
(* stands for                                                        *)
(*    step Hmid: forall (d : dataSet) (s : seq d), (maps id s) = s.  *)
(* We also use this feature for rewrite rules, so that, e.g.,        *)
(*   rewrite: (plus_assoc _ 3).                                      *)
(* will execute as                                                   *)
(*   rewrite (fun n => plus_assoc n 3)                               *)
(* i.e., it will rewrite some subterm .. + (3 + ..) to .. + 3 + ...  *)
(* The convention is also used for the argument of the congr tactic, *)
(* e.g., congr (x + _ * 1).                                          *)

let nf_etype sigma ev =
  Evarutil.nf_evar sigma (Evd.existential_type sigma ev)

let pf_abs_evars_with mkAbs gl sigma c0 =
  let sigma0 = project gl in
  let rec put evlist c = match kind_of_term c with
  | Evar (k, _ as ev) ->  
    if List.mem ev evlist || Evd.mem sigma0 k then evlist else
    if List.mem_assoc k evlist then
      Util.error "Can't generalize dependent evar" else
    ev :: put evlist (nf_etype sigma ev)
  | _ -> fold_constr put evlist c in
  let evlist = put [] c0 in
  if evlist = [] then c0 else
  let rec lookup ev k = function
    | [] -> mkEvar ev
    | ev' :: evl -> if ev = ev' then mkRel k else lookup ev (k + 1) evl in
  let rec get k c = match kind_of_term c with
  | Evar ev -> lookup ev k evlist
  | _ -> map_constr_with_binders ((+) 1) get k c in
  let rec loop c k = function
  | [] -> c
  | ev :: evl ->
    let t = get (k - 1) (nf_etype sigma ev) in
    loop (mkAbs (Name (pf_type_id gl t), t, c)) (k - 1) evl in
  loop (get 1 c0) 1 evlist

let pf_abs_evars = pf_abs_evars_with mkLambda

let pf_prod_evars = pf_abs_evars_with mkProd

(** Patches for the term-matching utilities in term and termops. *)

let rec strip_term c0 = match kind_of_term c0 with
| Cast (c, _, _) -> strip_term c
| App (f, args) ->
  let f' = strip_term f in let args' = Array.map strip_term args in
  begin match kind_of_term f' with
  | App (f1, args1) -> mkApp (f1, Array.append args1 args')
  | _ ->  mkApp (f', args')
  end
| _ -> map_constr strip_term c0

let rec eq_strip v0 c0 = match kind_of_term c0, kind_of_term v0 with
| Cast (c, _, _), _ -> eq_strip v0 c
| App _, App (vf, va) ->
  let rec eqva i c1 = match kind_of_term c1 with
  | Cast (c, _, _) -> eqva i c
  | App (f, a) when i > 0 ->
    let n = Array.length va in
    n <= i && eqva (i - n) f && eq_strip_array_at va a (i - n) n
  | _ -> i = 0 && eq_strip vf c1 in
  eqva (Array.length va) c0
| Prod (_, t, c), Prod (_, vt, v) -> eq_strip vt t && eq_strip v c
| Lambda (_, t, c), Lambda (_, vt, v) -> eq_strip vt t && eq_strip v c
| LetIn (_, b, t, c), LetIn (_, vb, vt, v) ->
  eq_strip vb b && eq_strip vt t && eq_strip v c
| Evar (e, a), Evar (ve, va) -> e = ve && eq_strip_array va a
| Case (_, rt, c, ba), Case (_, vrt, v, vba) ->
  eq_strip vrt rt && eq_strip v c && eq_strip_array vba ba
| Fix (i, (_, ta, ba)), Fix (vi, (_, vta, vba)) ->
  vi = i  && eq_strip_array vta ta && eq_strip_array vba ba
| CoFix (i, (_, ta, ba)), CoFix (vi, (_, vta, vba)) ->
  vi = i  && eq_strip_array vta ta && eq_strip_array vba ba
| c, v -> v = c
and eq_strip_array_at va a i n =
  let rec loop j = j = n || eq_strip va.(i + j) a.(j) && loop (j + 1) in loop 0
and eq_strip_array va a =
  let n = Array.length a in n = Array.length va && eq_strip_array_at va a 0 n

type subst_result = SubstTerm of constr | SubstMatch of int

let subst_strip v =
  let vf, va = match kind_of_term v with
  | App (vf, va) -> vf, va
  | _ -> v, [||] in
  let nv = Array.length va in
  let rec subst k c =
    match substa k c 0 with SubstMatch _ -> c | SubstTerm c' -> c'
  and substa k c m = match kind_of_term c with
  | Cast (c', kind, t) ->
    begin match substa k c' m with
    | SubstTerm c'' -> SubstTerm (mkCast (c'', kind, subst k t))
    | SubstMatch _ as r -> r
    end
  | App (f, a) ->
    let n = Array.length a in let nv' = nv - n in
    begin match substa k f (m + n) with
    | SubstTerm f' -> SubstTerm (mkApp (f', Array.map (subst k) a))
    | SubstMatch i when i <= nv' && eq_strip_array_at va a i n ->
      if i = nv' then SubstTerm (mkRel k) else SubstMatch (i + n)
    | SubstMatch i when i > nv' && eq_strip_array_at va a i (nv - i) ->
      let substa_at j = subst k a.(nv - i + j) in
      SubstTerm (mkApp (mkRel k, Array.init (i - nv') substa_at))
    | _ -> SubstTerm (mkApp (f, Array.map (subst k) a))
    end
  | _ when m >= nv && eq_strip vf c ->
    if nv = 0 then SubstTerm (mkRel k) else SubstMatch 0
  | _ -> SubstTerm (map_constr_with_binders ((+) 1) subst k c) in
  subst 1

let patched_subst_term v = subst_strip (strip_term v)

let patched_subst_term_occ occ =
  if occ = [] then patched_subst_term else Termops.subst_term_occ occ

(** Adding a new uninterpreted generic argument type *)

let add_genarg tag pr =
  let wit, globwit, rawwit as wits = create_arg tag in
  let glob _ rarg = in_gen globwit (out_gen rawwit rarg) in
  let interp _ _ garg = in_gen wit (out_gen globwit garg) in
  let subst _ garg = garg in
  add_interp_genarg tag (glob, interp, subst);
  let gen_pr _ _ _ = pr in
  Pptactic.declare_extra_genarg_pprule
    (rawwit, gen_pr) (globwit, gen_pr) (wit, gen_pr);
  wits

(** Tactical extensions. *)

(* The TACTIC EXTEND facility can't be used for defining new user   *)
(* tacticals, because:                                              *)
(*  - the concrete syntaxt must start with a fixed string           *)
(*  - the lexical Ltac environment is NOT used to interpret tactic  *)
(*    arguments                                                     *)
(* The second limitation means that the extended tacticals will     *)
(* exhibit run-time scope errors if used inside Ltac functions or   *)
(* pattern-matching constructs.                                     *)
(*   We use the following workaround:                               *)
(*  - We use the (unparsable) "(**)"  token for tacticals that      *)
(*    don't start with a token, then redefine the grammar and       *)
(*    printer using GEXTEND and set_pr_ssrtac, respectively.        *)
(*  - We use a global stack and side effects to pass the lexical    *)
(*    Ltac evaluation context to the extended tactical. The context *)
(*    is grabbed by interpreting an (empty) ssrltacctx argument,    *)
(*    which should appear last in the grammar rules; the            *)
(*    get_ssrevaltac function pops the stack and returns a tactic   *)
(*    interpreter that uses the context. For additional safety,     *)
(*    the push returns an integer key that is checked by the pop.   *)
(* - To avoid a spurrious option type, we don't push the context    *)
(*    for a null tag.                                               *)

type ssrargfmt = ArgSsr of string | ArgCoq of argument_type | ArgSep of string

let set_pr_ssrtac name prec afmt =
  let fmt = List.map (function ArgSep s -> Some s | _ -> None) afmt in
  let rec mk_akey = function
  | ArgSsr s :: afmt' -> ExtraArgType ("ssr" ^ s) :: mk_akey afmt'
  | ArgCoq a :: afmt' -> a :: mk_akey afmt'
  | ArgSep _ :: afmt' -> mk_akey afmt'
  | [] -> [] in
  let tacname = "ssr" ^ name in
  Pptactic.declare_extra_tactic_pprule (tacname, mk_akey afmt, (prec, fmt))

let ssrtac_atom loc name args = TacExtend (loc, "ssr" ^ name, args)
let ssrtac_expr loc name args = TacAtom (loc, ssrtac_atom loc name args)

type ssrltacctx = int

let pr_ssrltacctx _ _ _ i = str (sprintf "<Ltac context #%d>" i)

let ssrltacctxs = ref (1, [])

let interp_ltacctx ist _ n0 =
  if n0 = 0 then 0 else
  let n, s = !ssrltacctxs in
  let n' = if n >= max_int then 1 else n + 1 in
  ssrltacctxs := (n', (n, ist) :: s); n

let noltacctx = 0
let rawltacctx = 1

ARGUMENT EXTEND ssrltacctx TYPED AS int PRINTED BY pr_ssrltacctx
  INTERPRETED BY interp_ltacctx
| [ ] -> [ rawltacctx ]
END

let tacarg_id = id_of_tag "tactical argument"
let tacarg_expr = TacArg (Reference (Ident (dummy_loc, tacarg_id)))

let get_ssrevaltac i = match !ssrltacctxs with
| _ when i = noltacctx -> fun _ -> Util.anomaly "Missing Ltac context"
| n, (i', ist) :: s when i' = i ->
  let evtac tacexp gl =
    let lfun = [tacarg_id, val_interp ist gl tacexp] in
    interp_tac_gen lfun ist.debug tacarg_expr gl in
  ssrltacctxs := (n, s); evtac
| _ -> Util.anomaly "Bad scope in SSR tactical"

(** Generic argument-based globbing/typing utilities *)

(* Toplevel constr must be globalized twice ! *)
let glob_constr ist gl = function
  | _, Some ce ->
    let ltacvars = List.map fst ist.lfun, [] in
    let gsigma = project gl in
    let genv = pf_env gl in
    Constrintern.intern_gen false ~ltacvars:ltacvars gsigma genv ce
  | rc, None -> rc

let interp_wit globwit wit ist gl x = 
  let globarg = in_gen globwit x in
  let arg = interp_genarg ist gl globarg in
  out_gen wit arg

let interp_constr = interp_wit globwit_constr wit_constr

let interp_open_constr ist gl gc =
  interp_wit globwit_open_constr wit_open_constr ist gl ((), gc)

let interp_refine ist gl rc =
   let roc = (), (rc, None) in
   interp_wit globwit_casted_open_constr wit_casted_open_constr ist gl roc

let pf_match gl c =
  let typ = Pretyping.OfType (Some (pf_concl gl)) in
  let understand = Pretyping.Default.understand_ltac in
  let (evars, c') = understand (project gl) (pf_env gl) ([],[]) typ c in
  (evars_of evars, c')

(* Estimate a bound on the number of arguments of a raw constr. *)
(* This is not perfect, because the unifier may fail to         *)
(* typecheck the partial application, so we use a minimum of 5. *)
(* Also, we don't handle delayed or iterated coercions to       *)
(* FUNCLASS, which is probably just as well since these can     *)
(* lead to infinite arities.                                    *)

let splay_open_constr gl (sigma, c) =
  let env = pf_env gl in let t = Retyping.get_type_of env sigma c in
  Reductionops.splay_prod env sigma t

let nbargs_open_constr gl oc =
  let pl, _ = splay_open_constr gl oc in List.length pl

let interp_nbargs ist gl rc =
  try
    let rc6 = mkRApp rc (mkRHoles 6) in
    6 + nbargs_open_constr gl (interp_open_constr ist gl (rc6, None))
  with _ -> 5

let pf_nbargs gl c = nbargs_open_constr gl (project gl, c)

let isAppInd gl c =
  try ignore (pf_reduce_to_atomic_ind gl c); true with _ -> false

let interp_view_nbimps ist gl rc =
  try
    let pl, c = splay_open_constr gl (interp_open_constr ist gl (rc, None)) in
    if isAppInd gl c then List.length pl else -1
  with _ -> 0

(** 2. Vernacular command Prenex Implicits *)

(* This should really be implemented as an extension to the implicit   *)
(* arguments feature, but unfortuately that API is sealed. The current *)
(* workaround uses a combination of notations that works reasonably,   *)
(* with the following caveats:                                         *)
(*  - The pretty-printing always elides prenex implicits, even when    *)
(*    they are obviously needed.                                       *)
(*  - Prenex Implicits are NEVER exported from a module, because this  *)
(*    would lead to faulty pretty-printing and scoping errors.         *)
(*  - The command "Import Prenex Implicits" can be used to reassert    *)
(*    Prenex Implicits for all the visible constants that had been     *)
(*    declared as Prenex Implicits.                                    *)

let prenex_implicits f =
  let args =
    try Impargs.implicits_of_global (Nametab.locate (make_short_qualid f))
    with _ -> errorstrm (pr_id f ++ str " is not declared") in
  let rec loop i = function
  | a :: args' when Impargs.is_status_implicit a -> loop (i + 1) args'
  | args' when List.exists Impargs.is_status_implicit args' ->
      errorstrm (str "Expected prenex implicits for " ++ pr_id f)
  | _ when i = 0 ->
      errorstrm (str "Expected some implicits for " ++ pr_id f)
  | _ -> i, List.length args in
  loop 0 args

let prenex_implicit_id = id_of_string "prenex_implicit_constant"
let prenex_implicit_submod_id = id_of_string "Prenex_Implicit_Notation"

(* Fixup to get the right priorities amongst pretty-printing rules.   *)
(* The dummy meta avoids a quirk in Notation.declare_uninterpretation. *)
let redeclare_prenex_pp other_pp =
  let dummy_meta = id_of_string "prenex pp override", (None, []) in
  let redeclare_pp (rule, (metas, pat), _) () =
    Notation.declare_uninterpretation rule (metas @ [dummy_meta], pat) in
  List.fold_right redeclare_pp other_pp ()

let declare_prenex_uninterpretation loc f =
  let fkn = Nametab.locate_syntactic_definition (make_short_qualid f) in
  let rawf = Syntax_def.search_syntactic_definition loc fkn in
  let fpat = aconstr_of_rawconstr [] rawf in
  Notation.declare_uninterpretation (Notation.SynDefRule fkn) ([], fpat)
    
let declare_one_prenex_implicit loc f =
  let n, m = prenex_implicits f in
  let fref = Ident (loc, f) in
  let f_term args = CAppExpl (loc, (None, fref), args) in
  let f_string = string_of_id f in
  let f_tok = "'" ^ f_string ^ "'" in
  let add_implicit_notation () =
    let atf = "@ " ^ f_tok, [SetLevel 10] in
    Metasyntax.add_notation false (f_term []) atf None in
  let rec holes i = if i = 0 then [] else CHole(loc) :: holes (i - 1) in
  let mod_id = id_of_string ("Prenex_" ^ f_string) in
  let start_module = Declaremods.start_module Modintern.interp_modtype None in
  let submod_id = prenex_implicit_submod_id in
  let make_loc_qid id = loc, make_short_qualid id in
  start_module mod_id [] None;
    Command.syntax_definition prenex_implicit_id (CRef fref) false true;
    start_module submod_id [] None;
      add_implicit_notation ();
      Command.syntax_definition f (f_term (holes n)) false true;
    Declaremods.end_module submod_id;
  Declaremods.end_module mod_id;
  let rref = RRef (loc, Nametab.locate (make_short_qualid f)) in
  let other_pp = Notation.uninterp_notations rref in
  Library.import_module true (make_loc_qid mod_id);
  Library.import_module false (make_loc_qid submod_id);
  declare_prenex_uninterpretation loc f;
  redeclare_prenex_pp other_pp

let declare_prenex_implicits loc fl =
  List.iter (declare_one_prenex_implicit loc) fl;
  Lib.add_frozen_state ()
  
let import_one_prenex_implicit loc = function
  | TrueGlobal _ -> ()
  | SyntacticDef kn ->
    try match Syntax_def.search_syntactic_definition loc kn with
    | RRef (_, (ConstRef knf as fref)) as rref ->
      let f = id_of_label (con_label knf) in
      if fref = Nametab.locate (make_short_qualid f) then
      let submod_label = label_of_id prenex_implicit_submod_id in
      let other_pp = Notation.uninterp_notations rref in
      Declaremods.import_module false (MPdot (modpath kn, submod_label));
      declare_prenex_uninterpretation loc f;
      redeclare_prenex_pp other_pp
    | _ -> ()
    with _ -> ()

let import_prenex_implicits loc =
  let prenex_qid = make_short_qualid prenex_implicit_id in
  let import_list = Nametab.extended_locate_all prenex_qid in
  List.iter (import_one_prenex_implicit loc) import_list;
  Lib.add_frozen_state ()

VERNAC COMMAND EXTEND Ssrpreneximplicits
  | [ "Import" "Prenex" "Implicits" ]
  -> [ import_prenex_implicits dummy_loc ]
  | [ "Prenex" "Implicits" ne_ident_list(fl) ]
  -> [ declare_prenex_implicits dummy_loc fl ]
END

(* Vernac grammar visibility patch *)

let gallina_ext = Vernac_.gallina_ext in
GEXTEND Gram
  GLOBAL: gallina_ext;
  gallina_ext: [
    [ IDENT "Import"; IDENT "Prenex"; IDENT "Implicits" ->
      Vernacexpr.VernacExtend ("Ssrpreneximplicits", []) ]
    ];
END

(* Fixup to allow predicates with prenex implicits to be used *)
(* as coercion classes (also allows syntactic notations for   *)
(* long constants).                                           *)

let qualify_class_ref clref =
  let loc, qid = qualid_of_reference clref in
  try match Nametab.extended_locate qid with
  | TrueGlobal _ -> clref
  | SyntacticDef kn ->
    try match Syntax_def.search_syntactic_definition dummy_loc kn with
    | RApp (_, RRef (_, gref), _) ->
      let qid' = Nametab.shortest_qualid_of_global Idset.empty gref in
      let (_, id), (_, id') = repr_qualid qid, repr_qualid qid' in
      if id = id' then Qualid (loc, qid') else clref
    | RRef (_, gref) -> Qualid (loc, qualid_of_sp (Nametab.sp_of_global gref))
    | _ -> clref
    with _ -> clref
  with _ -> clref

let class_rawexpr = G_vernac.class_rawexpr in
let global = Constr.global in
GEXTEND Gram
  GLOBAL: class_rawexpr global;
  ssr_class_rawexpr: [
     [ IDENT "Funclass" -> Vernacexpr.FunClass
     | IDENT "Sortclass" -> Vernacexpr.SortClass
     | clref = global -> Vernacexpr.RefClass (qualify_class_ref clref) ]
  ];
  class_rawexpr: [[ class_expr = ssr_class_rawexpr -> class_expr ]];
END

(** 3. Alternative notations for "match" (let or if with pattern). *)

(* Syntax:                                                        *)
(*  if <term> is <pattern> then ... else ...                      *)
(*  if <term> is <pattern> [in ..] return ... then ... else ...   *)
(*  let: <pattern> := <term> in ...                               *)
(*  let: <pattern> [in ...] := <term> return ... in ...           *)
(* The scope of a top-level 'as' in the pattern extends over the  *)
(* 'return' type (dependent if/let).                              *)
(* Note that the optional "in ..." appears next to the <pattern>  *)
(* rather than the <term> in then "let:" syntax. The alternative  *)
(* would lead to ambiguities in, e.g.,                            *)
(* let: p1 := (*v---INNER LET:---v *)                             *)
(*   let: p2 := let: p3 := e3 in k return t in k2 in k1 return t' *)
(* in b       (*^--ALTERNATIVE INNER LET--------^ *)              *)

(* Caveat : There is no pretty-printing support, since this would *)
(* require a modification to the Coq kernel (adding a new match   *)
(* display style -- why aren't these strings?); also, the v8.0    *)
(* pretty-printer only allows extension hooks for printing        *)
(* integers constants.                                            *)
(*   Also note that in the v8 grammar "is" needs to be a keyword; *)
(* as this can't be done from an ML extension file, the new       *)
(* syntax will only work when ssreflect.v is imported.            *)

let no_ct = None, None and no_rt = None in 
let aliasvar = function CPatAlias (_, _, id) -> Some (Name id) | _ -> None in
let mk_cnotype p = aliasvar p, None in
let mk_ctype p t = aliasvar p, Some t in
let mk_rtype t = Some t in
let cook_let_rtype p rt = rt in
let mk_dthen loc (p, ct, rt) c = (loc, [[p]], c), ct, rt in
GEXTEND Gram
  GLOBAL: binder_constr operconstr pattern lconstr;
  ssr_rtype: [[ "return"; t = operconstr LEVEL "100" -> mk_rtype t ]];
  ssr_dpat: [
    [ p = pattern; "in"; t = lconstr; rt = ssr_rtype -> p, mk_ctype p t, rt
    | p = pattern; rt = ssr_rtype -> p, mk_cnotype p, rt
    | p = pattern -> p, no_ct, no_rt ]
  ];
  ssr_dthen: [[ dp = ssr_dpat; "then"; c = lconstr -> mk_dthen loc dp c ]];
  ssr_elsepat: [[ "else" -> CPatAtom (loc, None) ]];
  ssr_else: [[ p = ssr_elsepat; c = lconstr -> loc, [[p]], c ]];
  binder_constr: [
    [ "if"; c = operconstr LEVEL "200"; "is"; db1 = ssr_dthen; b2 = ssr_else ->
      let b1, ct, rt = db1 in CCases (loc, rt, [c, ct], [b1; b2])
    | "let"; ":"; p = pattern; ":="; c = lconstr; "in"; c1 = lconstr ->
      CCases (loc, no_rt, [c, no_ct], [loc, [[p]], c1])
    | "let"; ":"; p = pattern; ":="; c = lconstr; rt = ssr_rtype;
       "in"; c1 = lconstr ->
      CCases (loc, cook_let_rtype p rt, [c, mk_cnotype p], [loc, [[p]], c1])
    | "let"; ":"; p = pattern; "in"; t = lconstr; ":="; c = lconstr;
       rt = ssr_rtype; "in"; c1 = lconstr ->
      CCases (loc, cook_let_rtype p rt, [c, mk_ctype p t], [loc, [[p]], c1]) ]
  ];
END

(** 4. Tacticals (+, -, *, done, by, do+in, =>, first, and last). *)

(** Bracketing tactical *)

(* The tactic pretty-printer doesn't know that some extended tactics *)
(* are actually tacticals. To prevent it from improperly removing    *)
(* parentheses we override the parsing rule for bracketed tactic     *)
(* expressions so that the pretty-print always reflects the input.   *)
(* (Removing user-specified parentheses is dubious anyway).          *)

GEXTEND Gram
  GLOBAL: tactic_expr;
  ssrparentacarg: [[ "("; tac = tactic_expr; ")" -> Tacexp tac ]];
  tactic_expr: LEVEL "0" [[ arg = ssrparentacarg -> TacArg arg ]];
END

(** The internal "done" tactic. *)

(* For additional flexibility, "done" is defined in Ltac.    *)
(* Although we provide a default definition in ssreflect,    *)
(* we look up the definition dynamically at each call point, *)
(* to allow for user extensions.                             *)

let donetac gl =
  let tacname = 
    try Nametab.locate_tactic (make_short_qualid (id_of_string "done"))
    with Not_found -> try Nametab.locate_tactic (ssrqid "done")
    with Not_found -> Util.error "The ssreflect library was not loaded" in
  let tacexpr = Tacexpr.Reference (ArgArg (dummy_loc, tacname)) in
  eval_tactic (Tacexpr.TacArg tacexpr) gl

let tclBY tac = tclTHEN tac donetac

(** Tactical arguments. *)

(* We have three kinds: simple tactics, [|]-bracketed lists, and hints *)

let pr_ssrtacexp _ _ prt = prt tacltop

ARGUMENT EXTEND ssrtacexp TYPED AS tactic PRINTED BY pr_ssrtacexp
| [ "(**)" ] -> [ Util.anomaly "Grammar placeholder match" ]
END

ARGUMENT EXTEND ssrtacexp1 TYPED AS tactic PRINTED BY pr_ssrtacexp
| [ "(**)" ] -> [ Util.anomaly "Grammar placeholder match" ]
END

ARGUMENT EXTEND ssrtacexp3 TYPED AS tactic PRINTED BY pr_ssrtacexp
| [ "(**)" ] -> [ Util.anomaly "Grammar placeholder match" ]
END

GEXTEND Gram
  GLOBAL: ssrtacexp ssrtacexp1 ssrtacexp3 tactic_expr;
  ssrtacexp: [[ tac = tactic_expr LEVEL "5" -> tac ]];
  ssrtacexp1: [[ tac = tactic_expr LEVEL "1" -> tac ]];
  ssrtacexp3: [[ tac = tactic_expr LEVEL "3" -> tac ]];
END

type ssrtac = glob_tactic_expr
type ssrortacs = ssrtac list

let pr_orbar () = spc () ++ str "| "
let pr_ortacs prt = pr_list pr_orbar (prt tacltop)
let pr_ssrortacs _ _ = pr_ortacs

ARGUMENT EXTEND ssrortacs TYPED AS tactic list PRINTED BY pr_ssrortacs
| [ ssrtacexp(tac) "|" ssrortacs(tacs) ] -> [ tac :: tacs ]
| [ ssrtacexp(tac) ] -> [ [tac] ]
END

type ssrtacarg = bool * (ssrortacs * ssrltacctx)

let pr_tacarg prt = function
  | true, (tacs, _) -> hv 0 (str "[ " ++ pr_ortacs prt tacs ++ str " ]")
  | false, ([tac], _) -> prt tacltop tac
  | _ -> mt ()

let pr_ssrtacarg _ _ = pr_tacarg

let mk_tacarg tac = false, ([tac], rawltacctx)
let mk_ortacarg tacs = true, (tacs, rawltacctx)
let nulltacarg = true, ([], noltacctx)
let notacarg = false, ([], noltacctx)

ARGUMENT EXTEND ssrtacarg TYPED AS bool * (ssrortacs * ssrltacctx)
                          PRINTED BY pr_ssrtacarg
| [ ssrtacexp(tac) ] ->  [ mk_tacarg tac ]
END

ARGUMENT EXTEND ssrtacarg3 TYPED AS ssrtacarg PRINTED BY pr_ssrtacarg
| [ ssrtacexp3(tac) ] ->  [ mk_tacarg tac ]
END

ARGUMENT EXTEND ssrortacarg TYPED AS ssrtacarg PRINTED BY pr_ssrtacarg
| [ "[" ssrortacs(tacs) "]" ] -> [ mk_ortacarg tacs ]
END

ARGUMENT EXTEND ssrhintarg TYPED AS ssrtacarg PRINTED BY pr_ssrtacarg
| [ "[" ssrortacs(tacs) "]" ] -> [ mk_ortacarg tacs ]
| [ "[" "]" ] -> [ nulltacarg ]
| [ ssrtacarg(arg) ] -> [ arg ]
END

let argtac (_, (atacs, ctx)) =
  let gettac = get_ssrevaltac ctx in
  match atacs with
  | [atac] -> gettac atac
  | _ -> tclFIRST (List.map gettac atacs)

let hinttac (is_or, (atacs, ctx)) =
  if atacs = [] then if is_or then donetac else tclIDTAC else
  let gettac = get_ssrevaltac ctx in
  let mktac atac = tclBY (gettac atac) in
  match List.map mktac atacs with [tac] -> tac | tacs -> tclFIRST tacs

(** The "-"/"+"/"*" tacticals. *)

(* These are just visual cues to flag the beginning of the script for *)
(* new subgoals, when indentation is not appropriate (typically after *)
(* tactics that generate more than two subgoals).                     *)

TACTIC EXTEND ssrtclplus
| [ "(**)" "+" ssrtacarg(arg) ] -> [ argtac arg ]
END
set_pr_ssrtac "tclplus" 5 [ArgSep "+ "; ArgSsr "tacarg"]

TACTIC EXTEND ssrtclminus
| [ "(**)" "-" ssrtacarg(arg) ] -> [ argtac arg ]
END
set_pr_ssrtac "tclminus" 5 [ArgSep "- "; ArgSsr "tacarg"]

TACTIC EXTEND ssrtclstar
| [ "(**)" "*" ssrtacarg(arg) ] -> [ argtac arg ]
END
set_pr_ssrtac "tclstar" 5 [ArgSep "- "; ArgSsr "tacarg"]

let gen_tacarg = in_gen rawwit_ssrtacarg

GEXTEND Gram
  GLOBAL: ssrtacarg tactic;
  tactic: [
    [ "+"; tac = ssrtacarg -> ssrtac_expr loc "tclplus" [gen_tacarg tac]
    | "-"; tac = ssrtacarg -> ssrtac_expr loc "tclminus" [gen_tacarg tac]
    | "*"; tac = ssrtacarg -> ssrtac_expr loc "tclstar" [gen_tacarg tac]
    ] ];
END

(** The "by" tactical. *)

type ssrhint = ssrtacarg

let pr_hint prt arg =
  if arg = notacarg then mt() else str "by " ++ pr_tacarg prt arg
let pr_ssrhint _ _ = pr_hint
let nohint = notacarg

ARGUMENT EXTEND ssrhint TYPED AS ssrtacarg PRINTED BY pr_ssrhint
| [ ]                       -> [ nohint ]
END

TACTIC EXTEND ssrtclby
| [ "(**)" ssrtacarg(arg) ] -> [ hinttac arg ]
END
set_pr_ssrtac "tclby" 0 [ArgSep "by "; ArgSsr "tacarg"]

(* We can't parse "by" in ARGUMENT EXTEND because it will only be made *)
(* into a keyword in ssreflect.v; so we anticipate this in GEXTEND.    *)

GEXTEND Gram
  GLOBAL: ssrhint ssrtacarg ssrortacs simple_tactic;
  ssrhint: [[ "by"; arg = ssrhintarg -> arg ]];
  simple_tactic: [
  [ "by"; arg = ssrhintarg -> ssrtac_atom loc "tclby" [gen_tacarg arg]
  ] ];
END

(** The "in" pseudo-tactical *)

(* We can't make "in" into a general tactical because this would create a  *)
(* crippling conflict with the ltac let .. in construct. Hence, we add     *)
(* explicitly an "in" siffix to all the extended tactics for which it is   *)
(* relevant (including move, case, elim) and to the extended do tactical   *)
(* below, which yields a general-purpose "in" of the form do [...] in ...  *)

(* This tactical needs to come before the intro tactics because the latter *)
(* must take precautions in order not to interfere with the discharged     *)
(* assumptions. This is especially difficult for discharged "let"s, which  *)
(* the default simpl and unfold tactics would erase blindly.               *)

type ssrcls = identifier list * int

let pr_clshyps = pr_list spc pr_id
let pr_ssrclshyps _ _ _ = pr_clshyps

ARGUMENT EXTEND ssrclshyps TYPED AS ident list PRINTED BY pr_ssrclshyps
  | [ ident(hyp) "," ssrclshyps(hyps) ] -> [ hyp :: hyps ]
  | [ ident(hyp) ssrclshyps(hyps) ] -> [ hyp :: hyps ]
  | [ ident(hyp) ] -> [ [hyp] ]
END

let pr_cls = function
  | [], 0 -> spc () ++ str "in |- *"
  | [], 1 -> spc () ++ str "in * |-"
  | [], 2 -> spc () ++ str "in *"
  | hyps, 1 -> spc () ++ str "in " ++ pr_clshyps hyps
  | hyps, 2 -> spc () ++ str "in " ++ pr_clshyps hyps ++ str " *"
  | hyps, 3 -> spc () ++ str "in " ++ pr_clshyps hyps ++ str " |- *"
  | _ -> mt ()

let pr_ssrcls _ _ _ = pr_cls

ARGUMENT EXTEND ssrclsarg TYPED AS ident list * int
  PRINTED BY pr_ssrcls
  | [ "in" ssrclshyps(hyps) "|-" "*" ] -> [ hyps, 3 ]
  | [ "in" ssrclshyps(hyps) "*" ] -> [ hyps, 2 ]
  | [ "in" ssrclshyps(hyps) "|-" ] -> [ hyps, 1 ]
  | [ "in" ssrclshyps(hyps) ] -> [ hyps, 1 ]
  | [ "in" "*" ] -> [ [], 2 ]
  | [ "in" "*" "|-" ] -> [ [], 1 ]
  | [ "in" "|-" "*" ] -> [ [], 0 ]
END

ARGUMENT EXTEND ssrcls TYPED AS ssrclsarg PRINTED BY pr_ssrcls
  | [ ssrclsarg(arg) ] -> [ arg ]
  | [ ] -> [ [], -1 ]
END

let ctx_tag = "discharged"
let ctx_id = tag_id ctx_tag
let is_ctx_id = is_tag_id ctx_tag

let nohide = mkRel 0
let hidden_id = id_of_tag "the hidden goal"

let pf_ctx_let_depth gl =
  let rec depth c = match kind_of_term c with
  | LetIn (Name id, _, _, c') when is_ctx_id id -> 1 + depth c'
  | LetIn (_, _, _, c') -> lifted_depth c'
  | Prod (_, _, c') -> lifted_depth c'
  | _ -> 0
  and lifted_depth c = match depth c with 0 -> 0 | n -> n + 1 in
  depth (pf_concl gl)

let pf_clshyps gl clhyps n =
  if clhyps <> [] then pf_check_hyps gl clhyps else
  let dep_term var = mkNamedProd_or_LetIn (pf_get_hyp gl var) mkProp in
  let rec rem_var var =  function
  | [] -> raise Not_found
  | hyp :: hyps when hyp <> var -> hyp :: rem_var var hyps
  | _ :: hyps -> rem_deps hyps (dep_term var)
  and rem_deps hyps c =
    try match kind_of_term c with
    | Var id -> rem_var id hyps
    | _ -> fold_constr rem_deps hyps c
    with Not_found -> hyps in
  let hyps = pf_ids_of_proof_hyps gl in
  List.rev (if n >= 2 then hyps else rem_deps hyps (pf_concl gl))

let hidetacs n idhide cl0 =
  if n >= 2 then [] else
  [letin_tac true (Name idhide) cl0 nowhere;
   convert_concl_no_check (mkVar idhide)]

let discharge_hyp (idhyp, hyp) gl =
  let cl' = subst_var hyp (pf_concl gl) in
  match pf_get_hyp gl hyp with
  | _, None, t -> apply_type (mkProd (Name idhyp, t, cl')) [mkVar hyp] gl
  | _, Some v, t -> convert_concl (mkLetIn (Name idhyp, v, t, cl')) gl

let endclstac idhyps n idhide cl0 gl =
  let not_idhyp id = not (List.mem_assoc id idhyps) in
  let idhyp_id id = try List.assoc id idhyps with _ -> id in
  let dc, c = Sign.decompose_prod_assum (pf_concl gl) in
  let c_hidden = (n = 1 && c = mkVar idhide) in
  let rec fits forced = function
  | (id, _) :: ids, (Name id', _, _) :: dc' when id' = id ->
    fits true (ids, dc')
  | ids, dc' ->
    forced && ids = [] && (n >= 2 || dc' = [] && c_hidden) in
  let rec unmark c = match kind_of_term c with
  | Var id when n = 1 && id = idhide -> cl0
  | Prod (Name id, t, c') when List.mem_assoc id idhyps ->
    mkProd (Name (idhyp_id id), unmark t, unmark c')
  | LetIn (Name id, v, t, c') when List.mem_assoc id idhyps ->
    mkLetIn (Name (idhyp_id id), unmark v, unmark t, unmark c')
  | _ -> map_constr unmark c in
  let utac hyp = convert_hyp_no_check (map_named_declaration unmark hyp) in
  let utacs = List.map utac (pf_hyps gl) in
  let ugtac gl' = convert_concl_no_check (unmark (pf_concl gl')) gl' in
  let ctacs = if n = 1 then [clear [idhide]] else [] in
  let mktac itacs = tclTHENLIST (itacs @ utacs @ ugtac :: ctacs) in
  let itac (_, id) = introduction id in
  if fits false (idhyps, List.rev dc) then mktac (List.map itac idhyps) gl else
  let all_ids = ids_of_rel_context dc @ pf_ids_of_hyps gl in
  if List.for_all not_idhyp all_ids && not c_hidden then mktac [] gl else
  Util.error "tampering with discharged assumptions of \"in\" tactical"
    
let tclCLS tac (clhyps, n) gl =
  if n <= 0 then tac gl else
  let hyps = pf_clshyps gl clhyps n in
  let idhyps = List.map (fun id -> ctx_id id, id) hyps in
  let idhide = fresh_id [] hidden_id gl in
  let cl0 = pf_concl gl in
  let dtacs = List.map discharge_hyp (List.rev idhyps) in
  let endtac = endclstac idhyps n idhide cl0 in
  tclTHENLIST (hidetacs n idhide cl0 @ dtacs @ [clear hyps; tac; endtac]) gl

(** Clear switch *)

type ssrclear = identifier list

let pr_clear_ne clr = str "{" ++ pr_list pr_spc pr_id clr ++ str "}"
let pr_clear sep = function [] -> mt () | clr -> sep () ++ pr_clear_ne clr

let pr_ssrclear _ _ _ = pr_clear mt

ARGUMENT EXTEND ssrclear_ne TYPED AS ident list PRINTED BY pr_ssrclear
| [ "{" ne_ident_list(clr) "}" ] -> [ clr ]
END

ARGUMENT EXTEND ssrclear TYPED AS ssrclear_ne PRINTED BY pr_ssrclear
| [ ssrclear_ne(clr) ] -> [ clr ]
| [ ] -> [ [] ]
END

(** Simpl switch *)

type ssrsimpl = Simpl | Cut | SimplCut | Nop

let pr_simpl = function
  | Simpl -> str "/="
  | Cut -> str "//"
  | SimplCut -> str "//="
  | Nop -> mt ()

let pr_ssrsimpl _ _ _ = pr_simpl

let wit_ssrsimplrep, globwit_ssrsimplrep, rawwit_ssrsimplrep =
  add_genarg "ssrsimplrep" pr_simpl

ARGUMENT EXTEND ssrsimpl_ne TYPED AS ssrsimplrep PRINTED BY pr_ssrsimpl
| [ "/=" ] -> [ Simpl ]
| [ "//" ] -> [ Cut ]
| [ "//=" ] -> [ SimplCut ]
END

ARGUMENT EXTEND ssrsimpl TYPED AS ssrsimplrep PRINTED BY pr_ssrsimpl
| [ ssrsimpl_ne(sim) ] -> [ sim ]
| [ ] -> [ Nop ]
END

let simpl_with_ctx gl =
  let n = pf_ctx_let_depth gl in
  if n = 0 then simpl_in_concl gl else
  let rec itacs i = if i = 1 then intro else tclTHEN intro (itacs (i - 1)) in
  let gl' = pf_image gl (itacs n) in
  let rec mkcl n cl = function
    | hyp :: hyps when n > 0 ->
      let hyp' = map_named_declaration (pf_nf gl) hyp in
      mkcl (n - 1) (mkNamedProd_or_LetIn hyp' cl) hyps
    | _ -> cl in
  convert_concl_no_check (mkcl n (pf_nf gl' (pf_concl gl')) (pf_hyps gl')) gl

let simpltac = function
  | Simpl -> simpl_with_ctx
  | Cut -> tclTRY donetac
  | SimplCut -> tclTHEN simpl_with_ctx (tclTRY donetac)
  | Nop -> tclIDTAC

(** Rewriting direction *)

type ssrdir = L2R | R2L

let pr_dir = function L2R -> str "->" | R2L -> str "<-"

let pr_rwdir = function L2R -> mt() | R2L -> str "-"

let rewritetac dir = Equality.general_rewrite (dir = L2R)

let wit_ssrdir, globwit_ssrdir, rawwit_ssrdir =
  add_genarg "ssrdir" pr_dir

(** Extended intro patterns *)

type ssripat =
  | IpatSimpl of ssrclear * ssrsimpl
  | IpatId of identifier
  | IpatWild
  | IpatCase of ssripats list
  | IpatRw of ssrdir
  | IpatAll
and ssripats = ssripat list

let rec ipat_of_intro_pattern = function
  | IntroIdentifier id -> IpatId id
  | IntroWildcard -> IpatWild
  | IntroOrAndPattern iorpat ->
    IpatCase (List.map (List.map ipat_of_intro_pattern) iorpat)
  | IntroAnonymous -> failwith "TODO"

let rec pr_ipat = function
  | IpatId id -> pr_id id
  | IpatSimpl (clr, sim) -> pr_clear mt clr ++ pr_simpl sim
  | IpatCase iorpat -> hov 1 (str "[" ++ pr_iorpat iorpat ++ str "]")
  | IpatRw dir -> pr_dir dir
  | IpatAll -> str "*"
  | IpatWild -> str "_"
and pr_ipats ipats = pr_list spc pr_ipat ipats
and pr_iorpat iorpat = pr_list pr_bar pr_ipats iorpat

let pr_ssripat _ _ _ = pr_ipat
let pr_ssripats _ _ _ = pr_ipats
let pr_ssriorpat _ _ _ = pr_iorpat

let interp_introid interp ist gl id =
  let ipat = IntroIdentifier id in
  interp (interp_wit globwit_intro_pattern wit_intro_pattern ist gl ipat)

let rec add_ids_of_intro_pattern ipat ids = match ipat with
  | IntroIdentifier id -> id :: ids
  | IntroWildcard -> ids
  | IntroOrAndPattern iorpat ->
    List.fold_right (List.fold_right add_ids_of_intro_pattern) iorpat ids
  | IntroAnonymous -> failwith "TODO"

let wit_ipatrep, globwit_ipatrep, rawwit_ipatrep = add_genarg "ipatrep" pr_ipat

let rec interp_ipat ist gl garg =
  let ltacvar id = List.mem_assoc id ist.lfun in
  let rec iipat = function
  | IpatId id when ltacvar id -> interp_introid ipat_of_intro_pattern ist gl id
  | IpatSimpl (clr, sim) ->
    let add_ids id ids =
      if not (ltacvar id) then id :: ids else
      interp_introid add_ids_of_intro_pattern ist gl id ids in
    IpatSimpl (List.fold_right add_ids clr [], sim)
  | IpatCase iorpat -> IpatCase (List.map (List.map iipat) iorpat)
  | ipat -> ipat in
  iipat garg

ARGUMENT EXTEND ssripat TYPED AS ipatrep PRINTED BY pr_ssripat
  INTERPRETED BY interp_ipat
  | [ "_" ] -> [ IpatWild ]
END

ARGUMENT EXTEND ssrspat TYPED AS ssripat PRINTED BY pr_ssripat
| [ ssrclear_ne(clr) ssrsimpl(sim) ] -> [ IpatSimpl (clr, sim) ]
| [ ssrsimpl_ne(sim) ] -> [ IpatSimpl ([], sim) ]
END

ARGUMENT EXTEND ssrrpat TYPED AS ssripat PRINTED BY pr_ssripat
  | [ "->" ] -> [ IpatRw L2R ]
  | [ "<-" ] -> [ IpatRw R2L ]
END

ARGUMENT EXTEND ssripats TYPED AS ssripat list PRINTED BY pr_ssripats
  | [ ] -> [ [] ]
END

ARGUMENT EXTEND ssripats_ne TYPED AS ssripats PRINTED BY pr_ssripats
  | [ ssripat(pat) ssripats(pats) ] -> [ pat :: pats ]
  | [ "*" ] -> [ [IpatAll] ]
  | [ ssrspat(spat) ssripat(pat) ssripats(pats) ] -> [ spat :: pat :: pats ]
  | [ ssrspat(spat) "*" ] -> [ [spat; IpatAll] ]
  | [ ssrspat(spat) ] -> [ [spat] ]
END

let pushIpatRw = function
  | pats :: orpat -> (IpatRw L2R :: pats) :: orpat
  | [] -> []

ARGUMENT EXTEND ssriorpat TYPED AS ssripat list list PRINTED BY pr_ssriorpat
| [ ssripats(pats) "|" ssriorpat(orpat) ] -> [ pats :: orpat ]
| [ ssripats(pats) "|-" ">" ssriorpat(orpat) ] -> [ pats :: pushIpatRw orpat ]
| [ ssripats(pats) "|->" ssriorpat(orpat) ] -> [ pats :: pushIpatRw orpat ]
| [ ssripats(pats) "||" ssriorpat(orpat) ] -> [ pats :: [] :: orpat ]
| [ ssripats(pats) "|||" ssriorpat(orpat) ] -> [ pats :: [] :: [] :: orpat ]
| [ ssripats(pats) "||||" ssriorpat(orpat) ] -> [ [pats; []; []; []] @ orpat ]
| [ ssripats(pats) ] -> [ [pats] ]
END

ARGUMENT EXTEND ssrcpat TYPED AS ssripat PRINTED BY pr_ssripat
  | [ "[" ssriorpat(iorpat) "]" ] -> [ IpatCase iorpat ]
END

ARGUMENT EXTEND ssrvpat TYPED AS ssripat PRINTED BY pr_ssripat
  | [ ident(id) ] -> [ IpatId id ]
  | [ ssrcpat(pat) ] -> [ pat ]
  | [ ssrrpat(pat) ] -> [ pat ]
END

GEXTEND Gram
  GLOBAL: ssripat ssrvpat ssrrpat ssripats ssripats_ne;
  ssripat: [[ pat = ssrvpat -> pat ]];
  ssripats: [[ pat = ssripats_ne -> pat ]];
END

let pr_intros sep intrs =
  if intrs = [] then mt() else sep () ++ str "=> " ++ pr_ipats intrs
let pr_ssrintros _ _ _ = pr_intros mt

ARGUMENT EXTEND ssrintros_ne TYPED AS ssripats PRINTED BY pr_ssrintros
  | [ "=>" ssripats_ne(pats) ] -> [ pats ]
END

ARGUMENT EXTEND ssrintros TYPED AS ssripats PRINTED BY pr_ssrintros
  | [ ssrintros_ne(intrs) ] -> [ intrs ]
  | [ ] -> [ [] ]
END

let introid = intro_mustbe_force

let injecteq_id = id_of_tag "injection equation"

let pf_nb_prod gl = nb_prod (pf_concl gl)

let rev_id = id_of_tag "rev concl"

let revtoptac n0 gl =
  let n = pf_nb_prod gl - n0 in
  let dc, cl = decompose_prod_n n (pf_concl gl) in
  let dc' = dc @ [Name rev_id, compose_prod (List.rev dc) cl] in
  let f = mkApp (mkRel (n + 1), Array.init n (fun i -> mkRel (i + 1))) in
  refine (mkApp (compose_lam dc' f, [|mkMeta (Evarutil.new_meta())|])) gl

let injectidl2rtac id gl =
  let injarg = Some (NamedHyp id) in
  tclTHEN (Equality.injClause injarg) (revtoptac (pf_nb_prod gl)) gl

let injectl2rtac c = match kind_of_term c with
| Var id -> injectidl2rtac id
| _ ->
  let posetac = assert_tac (Name injecteq_id) c in
  tclTHENLIST [posetac; injectidl2rtac injecteq_id; clear [injecteq_id]]

let ssrscasetac c gl =
  let mind, t = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
  if mkInd mind <> build_coq_eq () then simplest_case c gl else
  injectl2rtac c gl

(* We must not anonymize context names discharged by the "in" tactical. *)

let anon_id = function
  | Name id -> if is_ctx_id id then id else tag_id "anon" id
  | _ -> id_of_tag "anon hyp "

let intro_all gl =
  let dc, _ = Sign.decompose_prod_assum (pf_concl gl) in
  let anontac (x, _, _) = intro_using (anon_id x) in
  tclTHENLIST (List.map anontac (List.rev dc)) gl

let top_id = id_of_tag "top assumption"

let with_top tac =
  tclTHENLIST [introid top_id; tac (mkVar top_id); clear [top_id]]

let rec mapLR f = function [] -> [] | x :: s -> let y = f x in y :: mapLR f s

let wild_ids = ref []

let new_wild_id () =
  let i = 1 + List.length !wild_ids in
  let sufx = match i with 1 -> "st" | 2 -> "nd" | 3 -> "rd" | _ -> "th" in
  let id = id_of_tag (sprintf "the %d%s wildcard" i sufx) in
  wild_ids := id :: !wild_ids;
  id

let clear_wilds wids gl =
  clear (List.filter (fun id -> List.mem id wids) (pf_ids_of_hyps gl)) gl

let clear_with_wilds wids clr0 gl =
  let extend_clr clr (id, _, _ as nd) =
    if List.mem id clr || not (List.mem id wids) then clr else
    let vars = global_vars_set_of_decl (pf_env gl) nd in
    let occurs id = Idset.mem id vars in
    if List.exists occurs clr then id :: clr else clr in
  clear (Sign.fold_named_context_reverse extend_clr ~init:clr0 (pf_hyps gl)) gl

let rec ipattac = function
  | IpatWild -> introid (new_wild_id ())
  | IpatCase iorpat -> tclIORPAT (with_top ssrscasetac) iorpat
  | IpatRw dir -> with_top (rewritetac dir)
  | IpatId id -> introid id
  | IpatSimpl (clr, sim) ->
    tclTHEN (simpltac sim) (clear_with_wilds !wild_ids clr)
  | IpatAll -> intro_all
and tclIORPAT tac = function
  | [[]] -> tac
  | iorpat -> tclTHENS tac (mapLR ipatstac iorpat)
and ipatstac ipats = tclTHENLIST (mapLR ipattac ipats)

(* For "move" *)
let introstac ipats =
  wild_ids := [];
  let tac = ipatstac ipats in
  tclTHEN tac (clear_wilds !wild_ids)

let rec eqintrostac id = function
  | IpatSimpl (clr, sim) :: ipats ->
    tclTHENLIST [simpltac sim; clear clr; eqintrostac id ipats]
  | [IpatAll] -> tclTHENLIST [intro; introid id; intro_all]
  | ipat :: ipats -> introstac (ipat :: IpatId id :: ipats)
  | [] -> tclTHEN intro (introid id)

(* For "case" and "elim" *)
let tclEQINTROS tac eqtac ipats =
  let rec split_itacs tac' = function
  | (IpatSimpl _ as spat) :: ipats' -> 
    split_itacs (tclTHEN tac' (ipattac spat)) ipats'
  | IpatCase iorpat :: ipats' -> tclIORPAT tac' iorpat, ipats'
  | ipats' -> tac', ipats' in
  wild_ids := [];
  let tac1, ipats' = split_itacs tac ipats in
  let tac2 = ipatstac ipats' in
  tclTHENLIST [tac1; eqtac; tac2; clear_wilds !wild_ids]

(* General case *)
let tclINTROS tac = tclEQINTROS tac tclIDTAC

(** The "=>" tactical *)

let ssrintros_sep =
  let atom_sep = function
    | TacSplit (_, NoBindings) -> mt
    | TacLeft NoBindings -> mt
    | TacRight NoBindings -> mt
    | TacExtend (_, "ssrapply", []) -> mt
    | _ -> spc in
  let tac_sep = function
    | TacId [] -> mt
    | TacArg (Reference _) -> mt
    | TacAtom (_, atom) -> atom_sep atom
    | _ -> spc in
  function _, ([tac], _) -> tac_sep tac | _ -> spc

let pr_ssrintrosarg _ _ prt (tac, ipats) =
  pr_tacarg prt tac ++ pr_intros (ssrintros_sep tac) ipats

ARGUMENT EXTEND ssrintrosarg TYPED AS ssrtacarg * ssripats
   PRINTED BY pr_ssrintrosarg
| [ "(**)" ssrtacarg(arg) ssrintros_ne(ipats) ] -> [ arg, ipats ]
END

TACTIC EXTEND ssrtclintros
| [ "(**)" ssrintrosarg(arg) ] ->
  [ let tacarg, ipats = arg in tclINTROS (argtac tacarg) ipats ]
END
set_pr_ssrtac "tclintros" 0 [ArgSsr "introsarg"]

let tclintros_expr loc tac ipats =
  let args = [in_gen rawwit_ssrintrosarg (mk_tacarg tac, ipats)] in
  ssrtac_expr loc "tclintros" args

GEXTEND Gram
  GLOBAL: tactic_expr ssrintros_ne;
  tactic_expr: LEVEL "1" [ RIGHTA
    [ tac = tactic_expr; ipats = ssrintros_ne -> tclintros_expr loc tac ipats
    ] ];
END

(** Indexes *)

(* Since SSR indexes are always positive numbers, we use the 0 value *)
(* to encode an omitted index. We reuse the in or_var type, but we   *)
(* supply our own interpretation function, which checks for non      *)
(* positive values, and allows the use of constr numerals, so that   *)
(* e.g., "let n := eval compute in (1 + 3) in (do n!clear)" works.   *)

type ssrindex = int or_var

let pr_index = function
  | ArgVar (_, id) -> pr_id id
  | ArgArg n when n > 0 -> pr_int n
  | _ -> mt ()
let pr_ssrindex _ _ _ = pr_index

let noindex = ArgArg 0
let check_index loc i =
  if i > 0 then i else loc_error loc "Index not positive"
let mk_index loc = function ArgArg i -> ArgArg (check_index loc i) | iv -> iv
let get_index = function ArgArg i -> i | _ -> anomaly "Uninterpreted index"

let interp_index ist gl idx =
  match idx with
  | ArgArg _ -> idx
  | ArgVar (loc, id) ->
    let i = try match List.assoc id ist.lfun with
    | VInteger i -> i
    | VConstr c ->
      let rc = Detyping.detype false [] [] c in
      begin match Notation.uninterp_prim_token rc with
      | _, Numeral bigi -> int_of_string (Bigint.to_string bigi)
      | _ -> raise Not_found
      end
    | _ -> raise Not_found
    with _ -> loc_error loc "Index not a number" in
    ArgArg (check_index loc i)

(* We don't actually use the ssrindex parser below because we need  *)
(* to resolve conflicts.                                            *)

ARGUMENT EXTEND ssrindex TYPED AS int_or_var PRINTED BY pr_ssrindex
  INTERPRETED BY interp_index
| [ int_or_var(i) ] -> [ mk_index loc i ]
| [ ] -> [ noindex ]
END

(** Multipliers *)

(* modality *)

type ssrmmod = May | Must | Once

let pr_mmod = function May -> str "?" | Must -> str "!" | Once -> mt ()

let wit_ssrmmod, globwit_ssrmmod, rawwit_ssrmmod = add_genarg "ssrmmod" pr_mmod
let ssrmmod = Gram.Entry.create "ssrmmod"
GEXTEND Gram
  GLOBAL: ssrmmod;
  ssrmmod: [[ "!" -> Must | "?" -> May ]];
END

(* tactical *)

let tclID tac = tac

let rec tclDOTRY n tac gl =
  if n <= 0 then tclIDTAC gl else
  tclTRY (tclTHEN tac (tclDOTRY (n - 1) tac)) gl

let tclMULT = function
  | 0, May  -> tclREPEAT
  | 1, May  -> tclTRY
  | n, May  -> tclDOTRY n
  | 0, Must -> tclAT_LEAST_ONCE
  | n, Must when n > 1 -> tclDO n
  | _       -> tclID

(** The "do" tactical. *)

type ssrdoarg = (ssrindex * ssrmmod) * (ssrtacarg * ssrcls)

let pr_ssrdoarg _ _ prt ((n, m), (tac, cls)) =
  pr_index n ++ pr_mmod m ++ pr_tacarg prt tac ++ pr_cls cls

ARGUMENT EXTEND ssrdoarg TYPED AS (ssrindex * ssrmmod) * (ssrtacarg * ssrcls)
                         PRINTED BY pr_ssrdoarg
| [ ssrindex(n) ssrmmod(m) ssrtacarg(t) ssrcls(cls) ] -> [ (n, m), (t, cls) ]
END

let ssrdotac ((n, m), (tac, cls)) =
  tclCLS (tclMULT (get_index n, m) (argtac tac)) cls

TACTIC EXTEND ssrtcldo
| [ "(**)" "do" ssrdoarg(arg) ] -> [ ssrdotac arg ]
END
set_pr_ssrtac "tcldo" 3 [ArgSep "do "; ArgSsr "doarg"]

let ssrdotac_expr loc n m tac cls =
  ssrtac_expr loc "tcldo" [in_gen rawwit_ssrdoarg ((n, m), (tac, cls))]

GEXTEND Gram
  GLOBAL: tactic_expr int_or_var ssrmmod ssrtacarg3 ssrortacarg ssrcls;
  ssr_dotacarg: [[ tac = ssrtacarg3 -> tac | tac = ssrortacarg -> tac ]];
  tactic_expr: LEVEL "3" [ RIGHTA
    [ IDENT "do"; m = ssrmmod; tac = ssr_dotacarg; cls = ssrcls ->
      ssrdotac_expr loc noindex m tac cls
    | IDENT "do"; tac = ssrortacarg; cls = ssrcls ->
      ssrdotac_expr loc noindex Once tac cls
    | IDENT "do"; n = int_or_var; m = ssrmmod;
                    tac = ssr_dotacarg; cls = ssrcls ->
      ssrdotac_expr loc (mk_index loc n) m tac cls
    ] ];
END

(** The "first" and "last" tacticals. *)

type ssrseqdir = ssrdir

let pr_seqdir = function
  | L2R -> str ";" ++ spc () ++ str "first "
  | R2L -> str ";" ++ spc () ++ str "last "

(* We can't actually parse the direction separately because this   *)
(* would introduce conflicts with the basic ltac syntax.           *)
let wit_ssrseqdir, globwit_ssrseqdir, rawwit_ssrseqdir =
   add_genarg "ssrseqdir" pr_seqdir
let ssrseqdir : ssrdir Gram.Entry.e = Gram.Entry.create "ssrseqdir"

type ssrseqarg = ssrindex * (ssrtacarg * ssrtac option)

let pr_ssrseqarg _ _ prt = function
  | ArgArg 0, (tac, _) -> pr_tacarg prt tac
  | i, (tac, None) -> pr_index i ++ str " " ++ pr_tacarg prt tac
  | i, (tac1, Some tac2) ->
    pr_index i ++ str " " ++
    hv 0 (pr_tacarg prt tac1 ++ spc() ++ str "|| " ++ prt tacltop tac2)

(* We must parse the index separately to resolve the conflict with *)
(* an unindexed tactic.                                            *)
ARGUMENT EXTEND ssrseqarg TYPED AS ssrindex * (ssrtacarg * tactic option)
                          PRINTED BY pr_ssrseqarg
| [ ssrtacarg3(i_tac) ] -> [ noindex, (i_tac, None) ]
END

let sq_brace_tacnames = ["first"; "solve"; "do"; "rewrite"; "have"; "suffice"]
let input_ssrseqvar strm =
  match Stream.npeek 1 strm with
  | ["IDENT", id] when not (List.mem id sq_brace_tacnames) ->
     accept_before_syms ["["] strm; id_of_string id
  | _ -> raise Stream.Failure

let ssrseqvar = Gram.Entry.of_parser "ssrseqvar" input_ssrseqvar

let ssrorelse = Gram.Entry.create "ssrorelse"
GEXTEND Gram
  GLOBAL: ssrseqvar Prim.natural tactic_expr ssrseqarg ssrorelse;
  ssr_seqindex: [
    [ id = ssrseqvar -> ArgVar (loc, id)
    | n = Prim.natural -> ArgArg (check_index loc n)
    ] ];
  ssrorelse: [[ "||"; tac = tactic_expr LEVEL "2" -> tac ]];
  ssrseqarg: [
    [ i = ssr_seqindex; tac1 = ssrortacarg; tac2 = OPT ssrorelse ->
      i, (tac1, tac2)
    ] ];
END

let tclSEQAT atac1 dir (i, ((_, (atacs2, ctx)), atac3)) =
  let evtac = get_ssrevaltac ctx in
  let tac1 = evtac atac1 in
  let tac3 = match atac3 with Some atac -> evtac atac | _ -> tclIDTAC in
  let rec mk_pad n = if n > 0 then tac3 :: mk_pad (n - 1) else [] in
  match dir, mk_pad (get_index i - 1), List.map evtac atacs2 with
  | L2R, [], [tac2] when atac3 = None -> tclTHENFIRST tac1 tac2
  | L2R, [], [tac2] when atac3 = None -> tclTHENLAST tac1 tac2
  | L2R, pad, tacs2 -> tclTHENSFIRSTn tac1 (Array.of_list (pad @ tacs2)) tac3
  | R2L, pad, tacs2 -> tclTHENSLASTn tac1 tac3 (Array.of_list (tacs2 @ pad))

TACTIC EXTEND ssrtclseq
| [ "(**)" ssrtacexp(tac) ssrseqdir(dir) ssrseqarg(arg) ] ->
  [ tclSEQAT tac dir arg ]
END
set_pr_ssrtac "tclseq" 5 [ArgSsr "tacexp"; ArgSsr "seqdir"; ArgSsr "seqarg"]

let tclseq_expr loc tac dir arg =
  let arg1 = in_gen rawwit_ssrtacexp tac in
  let arg2 = in_gen rawwit_ssrseqdir dir in
  let arg3 = in_gen rawwit_ssrseqarg arg in
  ssrtac_expr loc "tclseq" [arg1; arg2; arg3]

let input_ssrseqvar strm =
  match Stream.npeek 1 strm with
  | ["IDENT", id] when id <> "rewrite" ->
     accept_before_syms ["["] strm; id_of_string id
  | _ -> raise Stream.Failure

let ssrseqvar = Gram.Entry.of_parser "ssrseqvar" input_ssrseqvar

GEXTEND Gram
  GLOBAL: ssrintros_ne tactic_expr ssrorelse ssrseqarg ssrortacarg;
  ssr_first: [
    [ tac = ssr_first; ipats = ssrintros_ne -> tclintros_expr loc tac ipats
    | "["; tacl = LIST0 tactic_expr SEP "|"; "]" -> TacFirst tacl
    ] ];
  ssr_first_else: [
    [ tac1 = ssr_first; tac2 = ssrorelse -> TacOrelse (tac1, tac2)
    | tac = ssr_first -> tac ]];
  tactic_expr: LEVEL "5" [ LEFTA
    [ tac1 = tactic_expr; ";"; IDENT "first"; tac2 = ssr_first_else ->
      TacThen (tac1, tac2)
    | tac = tactic_expr; ";"; IDENT "first"; arg = ssrseqarg ->
      tclseq_expr loc tac L2R arg
    | tac = tactic_expr; ";"; IDENT "last"; arg = ssrseqarg ->
      tclseq_expr loc tac R2L arg
    ] ];
END

(** 5. Bookkeeping tactics (clear, move, case, elim) *)

(** Term references *)

(* Because we allow wildcards in term references, we need to stage the *)
(* interpretation of terms so that it occurs at the right time during  *)
(* the execution of the tactic (e.g., so that we don't report an error *)
(* for a term that isn't actually used in the execution).              *)

(* kinds of terms *)

type ssrtermkind =
  | ClosedTerm                  (* type-checking succeeded *)
  | OpenTerm of evar_map * exn  (* nedd to fill or abstract wildcards *)
  | ErrorTerm of exn            (* type or scope error; should not be used *)

let pr_termkind = function
  | ErrorTerm _ -> str "<<type error>>"
  | OpenTerm _ -> str "<<pattern>>"
  | ClosedTerm -> mt ()

let wit_ssrtermkind, globwit_ssrtermkind, rawwit_ssrtermkind =
  add_genarg "ssrtermkind" pr_termkind

(* terms *)

type ssrterm = ssrtermkind * constr

let pr_term prc = function
  | ErrorTerm _, _ -> str "<<type error>>"
  | _, c -> prc c

let pr_ssrterm prc _ _ = pr_term prc

let in_ssrterm = out_gen (wit_pair wit_ssrtermkind wit_constr)
let out_glob_ssrterm = in_gen (wit_pair globwit_ssrtermkind globwit_constr)

let interp_term_pattern ist gl gterm error =
  let _, gc = gterm in
  let sigma, c = interp_open_constr ist gl gc in
  (OpenTerm (sigma, error), c)

let interp_term ist gl gterm =
  try in_ssrterm (interp_genarg ist gl (out_glob_ssrterm gterm)) with error ->
  try interp_term_pattern ist gl gterm error with _ ->
  (ErrorTerm error, mkProp)

let force_term = function
  | ClosedTerm, c -> c
  | ErrorTerm e, _ -> raise e
  | OpenTerm (_, e), _ -> raise e

ARGUMENT EXTEND ssrterm TYPED AS ssrtermkind * constr PRINTED BY pr_ssrterm
                        INTERPRETED BY interp_term
  | [ constr(c) ] -> [ ClosedTerm, c ]
END

(* post-interpretation of terms *)

let pf_abs_term gl = function
  | ErrorTerm e, _ -> raise e
  | ClosedTerm, c -> c
  | OpenTerm (sigma, _), c -> pf_abs_evars gl sigma c

let pf_prod_term gl = function
  | ErrorTerm e, _ -> raise e
  | ClosedTerm, c -> c
  | OpenTerm (sigma, _), c -> pf_prod_evars gl sigma c

(* The function that fills an OpenTerm by matching the conclusion also  *)
(* returns a term convertible with the conclusion, but where the filled *)
(* term appears exactly (as higher-order matching is up to conversion). *)

let pf_fill_term gl = function
  | ErrorTerm e, _ -> raise e
  | ClosedTerm, c -> pf_concl gl, c
  | OpenTerm (sigma, e), c ->
    try
      let t0 = Retyping.get_type_of (pf_env gl) sigma c in
      let t = Evarutil.nf_evar sigma t0 in
      let eqcc = mkApp ( (build_coq_eq_data()).refl, [|t; c|]) in
      let abs_eqcc = pf_abs_evars gl sigma eqcc, NoBindings in
      let elim_eq = mkSsrConst "eq_protect_rect", NoBindings in
      let gl' = pf_image gl (general_elim abs_eqcc elim_eq) in
      let _, args = destApplication (pf_concl gl') in
      let c' = args.(2) in mkAppRed args.(1) c', c'
    with _ -> raise e

(** Discharged terms *)

(* A discharged term specification tracks whether the initial term *)
(* specification was an explicit identifier, as this might mean a  *)
(* deleted assumption. The pretty-printer maintains consistency.   *)

type ssrdterm = identifier option * ssrterm

let guard_dterm s i = match s.[i] with
| '(' | '?' | '0'..'9' -> false
| '_' -> skip_wschars s (i + 1) < String.length s - 1
| _ -> true

let pr_dterm prc = function
  | Some id, ((ClosedTerm | OpenTerm _), _) -> pr_id id
  | _, kc -> pr_term (pr_guarded guard_dterm prc) kc

let pr_ssrdterm prc _ _ = pr_dterm prc

ARGUMENT EXTEND ssrdterm TYPED AS ident option * ssrterm PRINTED BY pr_ssrdterm
| [ constr(c) ] -> [ exactCVarId loc c, (ClosedTerm, c) ]
END

(** Occurrence switch *)

(* The standard syntax of complemented occurrence lists involves a single *)
(* initial "-", e.g., {-1 3 5}. This is later converted the "all negated" *)
(* internal representation (e.g., {-1 -3 -5}). Also, we allow a single 0  *)
(* to indicate "no occurrences".                                          *)

type ssrocc = int list

let pr_occ = function
  | -1 :: occ -> str "{-" ++ pr_list pr_spc int occ ++ str "}"
  | occ -> str "{" ++ pr_list pr_spc int occ ++ str "}"

let pr_ssrocc _ _ _ = pr_occ

let check_occ occ =
  if occ = [0] || List.for_all (fun n -> n > 0) occ then occ else
  errorstrm (str "Inconsistent occurence list: " ++ pr_occ occ)

let cook_occ = function
  | [-1; 0] -> []
  | -1 :: occ -> List.map (fun n -> -n) occ
  | occ -> occ

ARGUMENT EXTEND ssrocc TYPED AS int list PRINTED BY pr_ssrocc
| [ ne_natural_list(occ) ] -> [ check_occ occ ]
| [ "-" ne_natural_list(occ) ] -> [ -1 :: check_occ occ ]
END

(** Discharge occ switch (combined occurrence / clear switch *)

type ssrdocc = ssrclear option * ssrocc

let mkocc occ = None, occ
let noclr = mkocc []
let mkclr clr = Some clr, []
let nodocc = mkclr []

let pr_docc = function
  | None, occ -> pr_occ occ
  | Some clr, _ -> pr_clear mt clr

let pr_ssrdocc _ _ _ = pr_docc

ARGUMENT EXTEND ssrdocc TYPED AS ssrclear option * ssrocc PRINTED BY pr_ssrdocc
| [ "{" ne_ident_list(clr) "}" ] -> [ mkclr clr ]
| [ "{" ssrocc(occ) "}" ] -> [ mkocc occ ]
END

(** Generalization (discharge) item *)

(* An item is a switch + term pair.                                     *)

type ssrgen = ssrdocc * ssrdterm

let pr_gen prc (docc, dt) = pr_docc docc ++ pr_dterm prc dt

let pr_ssrgen prc _ _ = pr_gen prc

ARGUMENT EXTEND ssrgen TYPED AS ssrdocc * ssrdterm PRINTED BY pr_ssrgen
| [ ssrdocc(docc) ssrdterm(dt) ] -> [ docc, dt ]
| [ ssrdterm(dt) ] -> [ nodocc, dt ]
END

let has_occ ((_, occ), _) = occ <> []

let pf_interp_clr gl = function
| None, _ -> []
| Some clr, Some id when pf_is_hyp gl id -> id :: clr
| Some clr, _ -> clr

let pf_interp_gen gl abswild ((oclr, occ), (oid, t)) =
  let clr' = pf_interp_clr gl (oclr, oid) in
  try
    let cl, c = pf_fill_term gl t in
    let cl' = patched_subst_term_occ (cook_occ occ) c cl in
    pf_mkProd gl oid (pf_type_of gl c) cl', c, clr'
  with _ when abswild && occ = [] ->
    let c = pf_abs_term gl t in
    mkArrow (pf_type_of gl c) (pf_concl gl), c, clr'

let genclrtac cl cs clr = tclTHEN (apply_type cl cs) (clear clr)
let exactgentac cl cs = tclTHEN (apply_type cl cs) (convert_concl cl)

let gentac gen gl =
  let cl, c, clr = pf_interp_gen gl true gen in genclrtac cl [c] clr gl

(** Generalization (discharge) sequence *)

(* A discharge sequence is represented as a list of up to two   *)
(* lists of d-items, plus an ident list set (the possibly empty *)
(* final clear switch). The main list is empty iff the command  *)
(* is defective, and has length two if there is a sequence of   *)
(* dependent terms (and in that case it is the first of the two *)
(* lists). Thus, the first of the two lists is never empty.     *)

type ssrgens = ssrgen list
type ssrdgens = ssrgens list * ssrclear

let gens_sep = function [], [] -> mt | _ -> spc

let rec pr_dgens prc (gensl, clr) =
  let prgens s gens = str s ++ pr_list spc (pr_gen prc) gens in
  let prdeps deps = prgens ": " deps ++ spc () ++ str "/" in
  match gensl with
  | [deps; []] -> prdeps deps ++ pr_clear pr_spc clr
  | [deps; gens] -> prdeps deps ++ prgens " " gens ++ pr_clear spc clr
  | [gens] -> prgens ": " gens ++ pr_clear spc clr
  | _ -> pr_clear pr_spc clr

let pr_ssrdgens prc _ _ = pr_dgens prc

let cons_gen gen = function
  | gens :: gensl, clr -> (gen :: gens) :: gensl, clr
  | _ -> Util.anomaly "missing gen list"

let cons_dep (gensl, clr) =
  if List.length gensl = 1 then ([] :: gensl, clr) else
  Util.error "multiple dependents switches '/'"

ARGUMENT EXTEND ssrdgens_tl TYPED AS ssrgen list list * ssrclear
                            PRINTED BY pr_ssrdgens
| [ "{" ne_ident_list(clr) "}" ssrdterm(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (mkclr clr, dt) dgens ]
| [ "{" ne_ident_list(clr) "}" ] ->
  [ [[]], clr ]
| [ "{" ssrocc(occ) "}" ssrdterm(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (mkocc occ, dt) dgens ]
| [ "/" ssrdgens_tl(dgens) ] ->
  [ cons_dep dgens ]
| [ ssrdterm(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (nodocc, dt) dgens ]
| [ ] ->
  [ [[]], [] ]
END

ARGUMENT EXTEND ssrdgens TYPED AS ssrdgens_tl PRINTED BY pr_ssrdgens
| [ ":" ssrgen(gen) ssrdgens_tl(dgens) ] -> [ cons_gen gen dgens ]
END

let genstac (gens, clr) = tclTHENLIST (clear clr :: List.rev_map gentac gens)

(* Common code to handle generalization lists along with the defective case *)

let with_defective maintac deps clr =
  let top_gen = mkclr clr, (Some top_id, (ClosedTerm, mkVar top_id)) in
  tclTHEN (introid top_id) (maintac deps top_gen)

let with_dgens (gensl, clr) maintac = match gensl with
  | [deps; []] -> with_defective maintac deps clr
  | [deps; gen :: gens] -> tclTHEN (genstac (gens, clr)) (maintac deps gen)
  | [gen :: gens] -> tclTHEN (genstac (gens, clr)) (maintac [] gen)
  | _ -> with_defective maintac [] clr

let with_deps deps0 maintac cl0 cs0 clr0 gl0 =
  let rec loop gl cl cs clr args clrs = function
  | [] ->
    let n = List.length args in
    maintac (if n > 0 then applist (to_lambda n cl, args) else cl) clrs gl0
  | dep :: deps ->
    let gl' = pf_image gl (genclrtac cl cs clr) in
    let cl', c', clr' = pf_interp_gen gl' false dep in
    loop gl' cl' [c'] clr' (c' :: args) (clr' :: clrs) deps in
  loop gl0 cl0 cs0 clr0 cs0 [clr0] (List.rev deps0)

(** Views *)

(* Views for the "move" and "case" commands are actually open *)
(* terms, but this is handled by interp_view, which is called *)
(* by interp_casearg. We use lists, to support the            *)
(* "double-view" feature of the apply command.                *)

type ssrview = ssrterm list

let pr_view prc = pr_list mt (fun c -> str "/" ++ prc c)

let pr_ssrview prc _ _ = pr_view prc

ARGUMENT EXTEND ssrview TYPED AS constr list PRINTED BY pr_ssrview
| [ "/" constr(c) ] -> [ [c] ]
END

(* There are two ways of "applying" a view to term:            *)
(*  1- using a reflection lemma if the view is an instance of  *)
(*     the reflect inductive predicate.                        *)
(*  2- applying the view if it coerces to a function, adding   *)
(*     implicit arguments.                                     *)
(* They require guessing the reflection lemma and the number   *)
(* of implicits, respectively, which we do by brute force.     *)

let move_view_lemmas =
  ["elimNTF", 3; "elimTF", 3; "elimTFn", 3;
   "introT", 2; "introTn", 2; "introN", 2;
   "iff_l2r", 2;  "iff_r2l", 2]

let view_error s gl rv =
  errorstrm (str ("Cannot " ^ s ^ " view ") ++ pf_pr_rawconstr gl rv)

let interp_view ist gl gv id =
  let rv = glob_constr ist gl gv in
  let interp rc rargs =
    let (sigma, c) = interp_open_constr ist gl (mkRApp rc rargs, None) in
    let c' = pf_abs_evars gl sigma c in
    match kind_of_term c' with
    | App (f, args) -> mkApp (f, Array.sub args 0 (Array.length args - 1))
    | _ -> mkNamedLambda id (pf_get_hyp_typ gl id) c' in
  let rec simple_view rargs n =
    if n < 0 then view_error "use" gl rv else
    try interp rv rargs with _ -> simple_view (mkRHole :: rargs) (n - 1) in
  let view_nbimps = interp_view_nbimps ist gl rv in
  let view_args = [mkRApp rv (mkRHoles view_nbimps); mkRVar id] in
  let mkView (name, nb_lemma_imps) =
    interp (mkSsrRRef name) (mkRHoles nb_lemma_imps @ view_args) in
  let rec view_with = function
  | [] -> simple_view [mkRVar id] (interp_nbargs ist gl rv)
  | lemma :: lemmas -> try mkView lemma with _ -> view_with lemmas in
  view_with (if view_nbimps < 0 then [] else move_view_lemmas)

let pf_with_view gl view cl c = match view with
| [f] ->
   let c' = mkApp (f, [|c|]) in
   let cl' = prod_applist cl [c] in
   pf_mkProd gl None (pf_type_of gl c') (patched_subst_term c' cl'), c'
| _ -> cl, c

(** Equations *)

(* argument *)

type ssreqid = identifier option

let pr_eqid = function Some id -> str " " ++ pr_id id | None -> mt ()
let pr_ssreqid _ _ _ = pr_eqid

(* We must use primitive parsing here to avoid conflicts with the  *)
(* basic move, case, and elim tactics.                             *)
ARGUMENT EXTEND ssreqid TYPED AS ident option PRINTED BY pr_ssreqid
| [ "(**)" ] -> [ Util.anomaly "Grammar placeholder match" ]
END

let input_ssreqid strm =
  match Stream.npeek 1 strm with
  | ["IDENT", id] -> accept_before_syms [":"] strm; Some (id_of_string id)
  | ["", ":"] -> None
  | _ -> raise Stream.Failure

let ssreqid_p4 = Gram.Entry.of_parser "ssreqid" input_ssreqid

GEXTEND Gram
  GLOBAL: ssreqid ssreqid_p4;
  ssreqid: [[ eqid = ssreqid_p4 -> eqid ]];
END

(* creation *)

let mkEq dir cl c t n =
  let {refl = refl; eq = eq} = build_coq_eq_data () in
  let v = mkRel n in
  let eqargs = match dir with L2R -> [|t; v; c|] | R2L -> [|t; c; v|] in
  mkArrow (mkApp (eq, eqargs)) (lift 1 cl), mkApp (refl, [|t; c|])

let pushmoveeqtac cl c =
  let x, t, cl1 = destProd cl in
  let cl2, eqc = mkEq R2L cl1 c t 1 in
  apply_type (mkProd (x, t, cl2)) [c; eqc]

let pushcaseeqtac cl gl =
  let cl1, args = destApplication cl in
  let n = Array.length args in
  let dc, cl2 = decompose_lam_n n cl1 in
  let _, t = List.nth dc (n - 1) in
  let cl3, eqc = mkEq R2L cl2 args.(0) t n in
  let cl4 = mkApp (compose_lam dc (mkProt (pf_type_of gl cl) cl3), args) in
  tclTHEN (apply_type cl4 [eqc]) (convert_concl cl4) gl

let pushelimeqtac gl =
  let _, args = destApplication (pf_concl gl) in
  let x, t, _ = destLambda args.(1) in
  let cl1 = mkApp (args.(1), Array.sub args 2 (Array.length args - 2)) in
  let cl2, eqc = mkEq L2R cl1 args.(2) t 1 in
  tclTHEN (apply_type (mkProd (x, t, cl2)) [args.(2); eqc]) intro gl

(** Bookkeeping (discharge-intro) argument *)

(* Since all bookkeeping ssr commands have the same discharge-intro    *)
(* argument format we use a single grammar entry point to parse them.  *)
(* the entry point parses only non-empty arguments to avoid conflicts  *)
(* with the basic Coq tactics.                                         *)

type ssrarg = ssrview * (ssreqid * (ssrdgens * ssripats))

let pr_ssrarg prc _ _ (view, (eqid, (dgens, ipats))) =
  let pri = pr_intros (gens_sep dgens) in
  pr_view prc view ++ pr_eqid eqid ++ pr_dgens prc dgens ++ pri ipats

ARGUMENT EXTEND ssrarg TYPED AS ssrview * (ssreqid * (ssrdgens * ssripats))
   PRINTED BY pr_ssrarg
| [ ssrview(view) ssreqid(eqid) ssrdgens(dgens) ssrintros(ipats) ] ->
  [ view, (eqid, (dgens, ipats)) ]
| [ ssrview(view) ssrclear(clr) ssrintros(ipats) ] ->
  [ view, (None, (([], clr), ipats)) ]
| [ ssreqid(eqid) ssrdgens(dgens) ssrintros(ipats) ] ->
  [ [], (eqid, (dgens, ipats)) ]
| [ ssrclear_ne(clr) ssrintros(ipats) ] ->
  [ [], (None, (([], clr), ipats)) ]
| [ ssrintros_ne(ipats) ] ->
  [ [], (None, (([], []), ipats)) ]
END

(* This constant is used for the fully defective case.   *)

let no_ssrarg = [], (None, (([], []), []))

(* Interpreting move/case views *)

let defdgenstac (gensl, clr) gl =
  match (match gensl with [gens] -> gens | [_; gens] -> gens | _ -> []) with
  | [] -> introid top_id gl
  | (_, (_, (ClosedTerm, c))) :: _ -> assert_tac (Name top_id) c gl
  | (_, (_, t)) :: gens' ->
    let ttac gl' = assert_tac (Name top_id) (snd (pf_fill_term gl' t)) gl in
    tclTHEN (genstac (gens', clr)) ttac gl

let interp_ssrarg ist gl (gvs, garg) =
  let _, arg = interp_wit globwit_ssrarg wit_ssrarg ist gl ([], garg) in
  let _, (dgens, _) = arg in
  let interp_view_with_arg gv =
    interp_view ist (pf_image gl (defdgenstac dgens)) gv top_id in
  (List.map interp_view_with_arg gvs, arg)


(** The "clear" tactic *)

(* We just add a defective version that clears the top assumption. *)

let poptac = tclTHEN (introid top_id) (clear [top_id])
TACTIC EXTEND ssrclear
  | [ "clear" natural(n)] -> [ tclDO n poptac ]
END

(** The "move" tactic *)

let rec improper_intros = function
  | IpatSimpl _ :: ipats -> improper_intros ipats
  | IpatId _ :: _ | IpatCase _ :: _ | IpatAll :: _ -> false
  | _ -> true

let check_movearg = function
  | view, (eqid, _) when view <> [] && eqid <> None ->
    Util.error "incompatible view and equation in move tactic"
  | view, (_, (([gen :: _], _), _)) when view <> [] && has_occ gen ->
    Util.error "incompatible view and occurrence switch in move tactic"
  | _, (_, ((dgens, _), _)) when List.length dgens > 1 ->
    Util.error "dependents switch `/' in move tactic"
  | _, (eqid, (_, ipats)) when eqid <> None && improper_intros ipats ->
    Util.error "no proper intro pattern for equation in move tactic"
  | arg -> arg

ARGUMENT EXTEND ssrmovearg TYPED AS ssrarg PRINTED BY pr_ssrarg
  INTERPRETED BY interp_ssrarg
| [ ssrarg(arg) ] -> [ check_movearg arg ]
END

let viewmovetac view _ gen gl =
  let cl, c, clr = pf_interp_gen gl false gen in
  let cl', c' = pf_with_view gl view cl c in genclrtac cl' [c'] clr gl

let eqmovetac _ gen gl =
  let cl, c, _ = pf_interp_gen gl false gen in pushmoveeqtac cl c gl

let movehnftac gl = match kind_of_term (pf_concl gl) with
  | Prod _ | LetIn _ -> tclIDTAC gl
  | _ -> hnf_in_concl gl

let ssrmovetac = function
  | ([_] as view), (_, (dgens, ipats)) ->
    tclTHEN (with_dgens dgens (viewmovetac view)) (introstac ipats)
  | _, (Some id, (dgens, ipats)) ->
    tclTHEN (with_dgens dgens eqmovetac) (eqintrostac id ipats)
  | _, (_, (([gens], clr), ipats)) ->
    tclTHEN (genstac (gens, clr)) (introstac ipats)
  | _, (_, ((_, clr), ipats)) ->
    tclTHENLIST [movehnftac; clear clr; introstac ipats]

TACTIC EXTEND ssrmove
| [ "move" ssrmovearg(arg) ssrrpat(pat) ] ->
  [ tclTHEN (ssrmovetac arg) (ipattac pat) ]
| [ "move" ssrmovearg(arg) ssrcls(cls) ] ->
  [ tclCLS (ssrmovetac arg) cls ]
| [ "move" ssrrpat(pat) ] -> [ ipattac pat ]
| [ "move" ] -> [ movehnftac ]
END

(** The "case" tactic *)

(* A case without explicit dependent terms but with both a view and an    *)
(* occurrence switch and/or an equation is treated as dependent, with the *)
(* viewed term as the dependent term (the occurrence switch would be      *)
(* meaningless otherwise). When both a view and explicit dependents are   *)
(* present, it is forbidden to put a (meaningless) occurrence switch on   *)
(* the viewed term.                                                       *)

let check_casearg = function
| view, (_, (([_; gen :: _], _), _)) when view <> [] && has_occ gen ->
  Util.error "incompatible view and occurrence switch in dependent case tactic"
| arg -> arg

ARGUMENT EXTEND ssrcasearg TYPED AS ssrarg PRINTED BY pr_ssrarg
   INTERPRETED BY interp_ssrarg
| [ ssrarg(arg) ] -> [ check_casearg arg ]
END

let depcasetac ctac eqid c cl clrs =
  let pattac, clrs' =
    if eqid = None then convert_concl cl, clrs else
    pushcaseeqtac cl, List.tl clrs in
  tclTHENLIST [pattac; ctac c; clear (List.flatten clrs')]

let ndefectcasetac view eqid deps ((_, occ), _ as gen) gl =
  let simple = (eqid = None && deps = [] && occ = []) in
  let cl, c, clr = pf_interp_gen gl (simple && eqid = None) gen in
  let cl', c' = pf_with_view gl view cl c in
  if simple then
     depcasetac ssrscasetac eqid c' (prod_applist cl' [c']) [clr] gl
  else
    let deps', clr' =
      if deps <> [] || view = [] then deps, clr else
      [gen], (if simple then clr else []) in
    with_deps deps' (depcasetac simplest_case eqid c') cl' [c'] clr' gl

let popcaseeqtac = function
  | None -> tclIDTAC
  | Some id -> tclTHEN intro_all (introid id)

let ssrcasetac (view, (eqid, (dgens, ipats))) =
  let casetac = with_dgens dgens (ndefectcasetac view eqid) in
  tclEQINTROS casetac (popcaseeqtac eqid) ipats

TACTIC EXTEND ssrcase
| [ "case" ssrcasearg(arg) ssrcls(cls) ] ->
  [ tclCLS (ssrcasetac arg) cls ]
| [ "case" ] -> [ ssrcasetac no_ssrarg ]
END

(** The "elim" tactic *)

(* Elim views are elimination lemmas, so the eliminated term is not addded *)
(* to the dependent terms as for "case", unless it actually occurs in the  *)
(* goal, the "all occurrences" {-0} switch is used, or the equation switch *)
(* is used and there are no dependents.                                    *)

let elimtac view c gl = match view with
  | [v] -> general_elim (c, NoBindings) (v, NoBindings) gl
  | _ -> simplest_elim c gl

let protectreceqtac cl gl =
  let cl1, args1 = destApplication cl in
  let n = Array.length args1 in
  let dc, _ = decompose_lam_n n cl1 in
  let cl2 = mkProt (pf_type_of gl cl1) cl1 in
  let args2 = Array.init n (fun i -> mkRel (n - i)) in
  convert_concl (mkApp (compose_lam dc (mkApp (cl2, args2)), args1)) gl

let depelimtac view eqid c cl clrs =
  let pattac = if eqid = None then convert_concl else protectreceqtac in
  tclTHENLIST [pattac cl; elimtac view c; clear (List.flatten clrs)]

let ndefectelimtac view eqid deps ((_, occ), _ as gen) gl =
  let cl, c, clr = pf_interp_gen gl true gen in
  if deps = [] && eqid = None && occ = [] then
    depelimtac view eqid c (prod_applist cl [c]) [clr] gl else
  let cl', args =
    let _, _, cl' = destProd cl in
    let force_dep = (occ = [-1; 0]) || (eqid <> None && deps = []) in
    if not force_dep && noccurn 1 cl' then cl', [] else cl, [c] in
  with_deps deps (depelimtac view eqid c) cl' args clr gl

let unprotecttac gl =
  let prot = destConst (mkSsrConst "protect_term") in
  onClauses (unfold_option [[], EvalConstRef prot]) allClauses gl

let popelimeqtac = function
| None -> tclIDTAC
| Some id -> tclTHENLIST [intro_all; pushelimeqtac; introid id; unprotecttac]

let ssrelimtac (view, (eqid, (dgens, ipats))) =
  let elimtac = with_dgens dgens (ndefectelimtac view eqid) in
  tclEQINTROS elimtac (popelimeqtac eqid) ipats

TACTIC EXTEND ssrelim
| [ "elim" ssrarg(arg) ssrcls(cls) ] ->
  [ tclCLS (ssrelimtac arg) cls ]
| [ "elim" ] -> [ ssrelimtac no_ssrarg ]
END

(** 6. Backward chaining tactics: apply, exact, congr. *)

(** The "apply" tactic *)

ARGUMENT EXTEND ssragen TYPED AS ssrgen PRINTED BY pr_ssrgen
| [ "{" ne_ident_list(clr) "}" ssrdterm(dt) ] -> [ mkclr clr, dt ]
(* | [ "{" "}" ssrdterm(dt) ] -> [ noclr, dt ] *)
| [ ssrdterm(dt) ] -> [ nodocc, dt ]
END

ARGUMENT EXTEND ssragens TYPED AS ssrdgens PRINTED BY pr_ssrdgens
| [ "{" ne_ident_list(clr) "}" ssrdterm(dt) ssragens(agens) ] ->
  [ cons_gen (mkclr clr, dt) agens ]
(* | [ "{" "}" ssrdterm(dt) ssragens(agens) ] ->
  [ cons_gen (noclr, dt) agens ] *)
| [ "{" ne_ident_list(clr) "}" ] -> [ [[]], clr]
| [ ssrdterm(dt) ssragens(agens) ] ->
  [ cons_gen (nodocc, dt) agens ]
| [ ] -> [ [[]], [] ]
END

type ssrapplyarg = open_constr list * ssrarg

let mk_applyarg views agens ipats = [], (views, (None, (agens, ipats)))

let pr_ssrapplyarg prc prlc prt (_, arg) = pr_ssrarg prc prlc prt arg

ARGUMENT EXTEND ssrapplyargrep TYPED AS open_constr list * ssrarg
  PRINTED BY pr_ssrapplyarg
| [ ":" ssragen(gen) ssragens(dgens) ssrintros(ipats) ] ->
  [ mk_applyarg [] (cons_gen gen dgens) ipats ]
| [ ssrclear_ne(clr) ssrintros(ipats) ] ->
  [ mk_applyarg [] ([], clr) ipats ]
| [ ssrintros_ne(ipats) ] ->
  [ mk_applyarg [] ([], []) ipats ]
| [ ssrview(view1) ssrview(view2) ssrclear(clr) ssrintros(ipats) ] ->
  [ mk_applyarg (view1 @ view2) ([], clr) ipats ]
| [ ssrview(view) ssrclear(clr) ssrintros(ipats) ] ->
  [ mk_applyarg view ([], clr) ipats ]
END

let interp_agen ist gl ((goclr, _), (goid, (_, gc))) (clr, rcs) =
  let interp_opt gwit wit = interp_wit (wit_opt gwit) (wit_opt wit) ist gl in
  let oclr = interp_opt globwit_ssrclear wit_ssrclear goclr in
  let oid =  interp_opt globwit_ident wit_ident goid in
  pf_interp_clr gl (oclr, oid) @ clr, glob_constr ist gl gc :: rcs 

let rm_genid (docc, (_, t)) = docc, (None, t)

let interp_agens ist gl gagens =
  match List.fold_right (interp_agen ist gl) gagens ([], []) with
  | clr, rlemma :: args ->
    let n = interp_nbargs ist gl rlemma - List.length args in
    let rec loop i =
      if i > n then
         errorstrm (str "Cannot apply lemma " ++ pf_pr_rawconstr gl rlemma)
      else
        try interp_refine ist gl (mkRApp rlemma (mkRHoles i @ args))
        with _ -> loop (i + 1) in
    clr, loop 0
  | _ -> assert false

let rec interp_refine_args ist gl args = function
  | [] -> None
  | (name, nb_imps) :: lemmas ->
    let lemma = mkRApp (mkSsrRRef name) (mkRHoles nb_imps @ args) in
    try Some (interp_refine ist gl lemma)
    with _ -> interp_refine_args ist gl args lemmas

let apply_reflect_lemmas =
  ["introNTF", 3; "introTF", 3; "introTFn", 3]

let apply_view_lemmas =
  apply_reflect_lemmas @
  [ "elimT", 2; "elimTn", 2; "elimN", 2;
    "iff_l2r", 2;  "iff_r2l", 2]

let open_arg (_, c) i = let _, a = destApplication c in a.(i)

let mkRAppViewArgs ist gl rv nb_goals =
  let nb_view_imps = interp_view_nbimps ist gl rv in
  if nb_view_imps < 0 then view_error "apply" gl rv else
  mkRApp rv (mkRHoles nb_view_imps) :: mkRHoles nb_goals

let interp_apply_view1 ist gl gv lemmas =
  let rv = glob_constr ist gl gv in
  let args = mkRAppViewArgs ist gl rv 1 in
  match interp_refine_args ist gl args lemmas with
  | Some vl -> open_arg vl 2, vl
  | None -> view_error "apply" gl rv

let equiv_reflect_lemmas = ["equivPif", 3; "equivPifn", 3]

let negate_reflect_lemmas = ["if_negE_Prop", 4; "if_negI_Prop", 4]

let interp_apply_view2 ist gl gv =
  let rv = glob_constr ist gl gv in
  let args = mkRAppViewArgs ist gl rv 2 in
  let view_at gl' p =
    match interp_refine_args ist gl' args equiv_reflect_lemmas with
    | Some vl -> Some (open_arg vl 2, p @ [vl])
    | None -> None in
  let rec view_after lemma =
   match interp_refine_args ist gl [] [lemma] with
    | Some p -> view_at (pf_image gl (Refine.refine p)) [p]
    | None -> None in
  let rec loop = function
    | [] -> view_error "apply" gl rv
    | lemma :: lemmas ->
      match view_after lemma with Some vl -> vl | None -> loop lemmas in
  match view_at gl [] with Some vl -> vl | None -> loop negate_reflect_lemmas

let dependent_apply_error =
  try Util.error "Could not fill dependent hole in \"apply\"" with err -> err

let rec refine_with oc gl =
  try Refine.refine oc gl with _ -> raise dependent_apply_error

let rec refine_with_list = function
  | lemma :: lemmas ->
    tclTHENLAST (refine_with lemma) (refine_with_list lemmas)
  | [] ->
    tclIDTAC

let interp_ssrapplyarg ist gl gen_arg =
  let _, (gviews, (_, ((ggenl, gclr), gipats))) = gen_arg in
  let clr = interp_wit globwit_ssrclear wit_ssrclear ist gl gclr in
  let ipats = interp_wit globwit_ssrintros wit_ssrintros ist gl gipats in
  let arg = match gviews, ggenl with
  | [], [agens] ->
    let clr', (sigma, c as lemma) = interp_agens ist gl agens in
    let dt = None, (OpenTerm (sigma, dependent_apply_error), c) in
    [lemma], ([], (None, (([[(Some clr', []), dt]], clr), ipats)))
  | [gv1], [] ->
    let v1, lv1 = interp_apply_view1 ist gl gv1 apply_view_lemmas in
    [lv1], ([v1], (None, (([], clr), ipats)))
  | [gv1; gv2], [] -> 
    let v1, lv1 = interp_apply_view1 ist gl gv1 apply_reflect_lemmas in
    let gl1 = pf_image_last gl (refine_with lv1) in
    let v2, lv2 = interp_apply_view2 ist gl1 gv2 in
    lv1 :: lv2, ([v1; v2], (None, (([], clr), ipats)))
  | _ ->
    [], ([], (None, (([], clr), ipats))) in
  arg

ARGUMENT EXTEND ssrapplyarg TYPED AS ssrapplyargrep PRINTED BY pr_ssrapplyarg
  INTERPRETED BY interp_ssrapplyarg
  | [ ssrapplyargrep(arg) ] -> [ arg ]
END

let apply_id id gl =
  let lemma = mkVar id in
  let n = pf_nbargs gl lemma in
  let rec loop i =
    if i > n then errorstrm (str "Could not apply " ++ pr_id id) else
    try pf_match gl (mkRApp (mkRVar id) (mkRHoles i)) with _ -> loop (i + 1) in
  refine_with (loop 0) gl

let apply_top_tac =
  tclTHENLIST [introid top_id; apply_id top_id; clear [top_id]]

let ssrapplytac (lemmas, (_, (_, ((gens, clr), ipats)))) =
  let apptac = match lemmas, gens with
  | [], _ ->
    tclTHEN apply_top_tac (clear clr)
  | [lemma], [[(Some clr', _), _]] ->
    tclTHENLIST [clear clr; refine_with lemma; clear clr']
  | _ ->
    tclTHEN (refine_with_list lemmas) (clear clr) in
  tclINTROS apptac ipats

TACTIC EXTEND ssrapply
| [ "apply" ssrapplyarg(arg) ] -> [ ssrapplytac arg ]
| [ "apply" ] -> [ apply_top_tac ]
END

(** The "exact" tactic *)

ARGUMENT EXTEND ssrexactarg TYPED AS ssrapplyargrep PRINTED BY pr_ssrapplyarg
  INTERPRETED BY interp_ssrapplyarg
| [ ":" ssragen(gen) ssragens(dgens) ] ->
  [ mk_applyarg [] (cons_gen gen dgens) [] ]
| [ ssrview(view1) ssrview(view2) ssrclear(clr) ] ->
  [ mk_applyarg (view1 @ view2) ([], clr) [] ]
| [ ssrview(view) ssrclear(clr) ] ->
  [ mk_applyarg view ([], clr) [] ]
| [ ssrclear_ne(clr) ] ->
  [ mk_applyarg [] ([], clr) [] ]
END

TACTIC EXTEND ssrexact
| [ "exact" ssrexactarg(arg) ] -> [ tclBY (ssrapplytac arg) ]
| [ "exact" ] -> [ tclORELSE donetac (tclBY apply_top_tac) ]
END

(** The "congr" tactic *)

type ssrcongrarg = open_constr * (int * constr)

let pr_ssrcongrarg prc _ _ (_, (n, f)) =
  (if n <= 0 then mt () else str " " ++ pr_int n) ++  str " " ++ prc f

ARGUMENT EXTEND ssrcongrargrep TYPED AS open_constr * (int * constr)
  PRINTED BY pr_ssrcongrarg
| [ natural(n) constr(c) ] -> [ ((), c), (n, c) ]
| [ constr(c) ] -> [ ((), c), (0, c)  ]
END

let rec mkRnat n =
  if n <= 0 then RRef (dummy_loc, glob_O) else
  mkRApp (RRef (dummy_loc, glob_S)) [mkRnat (n - 1)]

let interp_congrarg_at ist gl n rf m =
  let congrn = mkSsrRRef "nary_congruence" in
  let args1 = mkRnat n :: mkRHoles (n + 1) in
  let args2 = mkRHoles (3 * n) in
  let rec loop i =
    if i + n > m then None else
    try
      let rt = mkRApp congrn (args1 @  mkRApp rf (mkRHoles i) :: args2) in
      let _, t as ot = interp_refine ist gl rt in
      let _, ta = destApplication t in Some (ot, (n, ta.(n + 2)))
    with _ -> loop (i + 1) in
  loop 0

let interp_congrarg ist gl garg =
  let _, (n, gf) = garg in
  let sigma, f' = interp_open_constr ist gl gf in
  let f = pf_abs_evars gl sigma f' in
  let rf = Detyping.detype false [] [] f in
  let m = pf_nbargs gl f in
  if n > 0 then
    match interp_congrarg_at ist gl n rf m with
    | Some f' -> f'
    | None ->  errorstrm (str "No " ++ pr_int n ++ str "-congruence with "
                        ++ pf_pr_constr gl f)
  else let rec loop i =
    if i > m then errorstrm (str "No congruence with " ++ pf_pr_constr gl f)
    else match interp_congrarg_at ist gl i rf m with
    | Some f' -> f'
    | None -> loop (i + 1) in
  loop 1

ARGUMENT EXTEND ssrcongrarg TYPED AS ssrcongrargrep PRINTED BY pr_ssrcongrarg
  INTERPRETED BY interp_congrarg
| [ ssrcongrargrep(arg) ] -> [ arg ]
END

let congrtac (congr, _) = tclTHEN (refine_with congr) (tclTRY reflexivity)

TACTIC EXTEND ssrcongr
| [ "congr" ssrcongrarg(arg) ] -> [ congrtac arg ]
END

(** 7. Rewriting tactics (rewrite, unlock) *)

(** Direction *)

let pr_rwdir = function L2R -> mt () | R2L -> str "-"

(** Rewrite multiplier *)

type ssrmult = int * ssrmmod

let notimes = 0
let nomult = 1, Once

let pr_mult (n, m) =
  if n > 0 && m <> Once then pr_int n ++ pr_mmod m else pr_mmod m

let pr_ssrmult _ _ _ = pr_mult

ARGUMENT EXTEND ssrmult_ne TYPED AS int * ssrmmod PRINTED BY pr_ssrmult
  | [ natural(n) ssrmmod(m) ] -> [ check_index loc n, m ]
  | [ ssrmmod(m) ]            -> [ notimes, m ]
END

ARGUMENT EXTEND ssrmult TYPED AS ssrmult_ne PRINTED BY pr_ssrmult
  | [ ssrmult_ne(m) ] -> [ m ]
  | [ ] -> [ nomult ]
END

(** Rewrite redex switch *)

type ssrredex = ssrterm option

let pr_redex prlc = function
  | None -> mt ()
  | Some t -> str "[" ++ pr_term prlc t ++ str "]"

let pr_ssrredex prc _ _ = pr_redex prc

ARGUMENT EXTEND ssrredex_ne TYPED AS ssrterm option PRINTED BY pr_ssrredex
  | [ "[" lconstr(c) "]" ] -> [ Some (ClosedTerm, c) ]
END

ARGUMENT EXTEND ssrredex TYPED AS ssrredex_ne PRINTED BY pr_ssrredex
  | [ ssrredex_ne(rdx) ] -> [ rdx ]
  | [ ] -> [ None ]
END

let redexpattac occ t gl =
  let cl, c, _ = pf_interp_gen gl false (mkocc occ, (None, t)) in
  convert_concl (mkApp (to_lambda 1 cl, [|c|])) gl

let with_redexocc occ redex rwtac = match redex with
  | None -> rwtac
  | Some t -> tclTHEN (redexpattac occ t) rwtac

(** Rewrite clear/occ switches *)

let pr_rwocc = function
  | None, [] -> mt ()
  | None, occ -> pr_occ occ
  | Some clr,  _ ->  pr_clear_ne clr

let pr_ssrrwocc _ _ _ = pr_rwocc

ARGUMENT EXTEND ssrrwocc TYPED AS ssrdocc PRINTED BY pr_ssrrwocc
| [ "{" ident_list(clr) "}" ] -> [ mkclr clr ]
| [ "{" ssrocc(occ) "}" ] -> [ mkocc occ ]
| [ ] -> [ noclr ]
END

(** Rewrite rules *)

type ssrwkind = RWred of ssrsimpl | RWdef | RWeq
type ssrrule = ssrwkind * ssrdterm

let pr_rwkind = function
  | RWred s -> pr_simpl s
  | RWdef -> str "/"
  | RWeq -> mt ()

let wit_ssrrwkind, globwit_ssrrwkind, rawwit_ssrrwkind =
  add_genarg "ssrrwkind" pr_rwkind

let pr_rule prc = function
  | RWred s, _ -> pr_simpl s
  | RWdef, r-> str "/" ++ pr_dterm prc r
  | RWeq, r -> pr_dterm prc r

let pr_ssrrule prc _ _ = pr_rule prc

ARGUMENT EXTEND ssrrule_nt TYPED AS ssrrwkind * ssrdterm PRINTED BY pr_ssrrule
  | [ ssrsimpl_ne(s) ] -> [ RWred s, (None, (ClosedTerm, mkCProp loc)) ]
  | [ "/" ssrdterm(t) ] -> [ RWdef, t ] 
END

ARGUMENT EXTEND ssrrule_ne TYPED AS ssrrule_nt PRINTED BY pr_ssrrule
  | [ ssrrule_nt(r) ] -> [ r ]
  | [ ssrdterm(t) ] -> [ RWeq, t ] 
END

ARGUMENT EXTEND ssrrule TYPED AS ssrrule_nt PRINTED BY pr_ssrrule
  | [ ssrrule_ne(r) ] -> [ r ]
  | [ ] -> [ RWred Nop, (None, (ClosedTerm, mkCProp loc)) ]
END

(** Rewrite arguments *)

type ssrrwarg = (ssrdir * ssrmult) * ((ssrdocc * ssrredex) * ssrrule)

let pr_rwarg prc prlc ((d, m), ((docc, rx), r)) =
  pr_rwdir d ++ pr_mult m ++ pr_rwocc docc ++ pr_redex prlc rx ++ pr_rule prc r

let pr_ssrrwarg prc _ _ = pr_rwarg prc prc

let mk_rwarg (d, (n, _ as m)) ((clr, occ as docc), rx) (rt, _ as r) =   
 if rt <> RWeq then begin
   if rt = RWred Nop && not (m = nomult && occ = [] && rx = None)
                     && (clr = None || clr = Some []) then
     Util.anomaly "Improper rewrite clear switch";
   if d = R2L && rt <> RWdef then
     Util.error "Right-to-left switch on simplification";
   if n <> 1 && (rt = RWred Cut || rx = None) then
     Util.error "Bad or useless multiplier";
   if d = R2L && occ <> [] && rx = None && rt = RWdef then
     Util.error "Missing redex for occurrence fold"
 end; (d, m), ((docc, rx), r)

let norwmult = L2R, nomult
let norwocc = noclr, None

ARGUMENT EXTEND ssrrwarg_nt
  TYPED AS (ssrdir * ssrmult) * ((ssrdocc * ssrredex) * ssrrule)
  PRINTED BY pr_ssrrwarg
  | [ "-" ssrmult(m) ssrrwocc(docc) ssrredex(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg (R2L, m) (docc, rx) r ]
  | [ "-/" ssrdterm(t) ] ->     (* just in case '-/' should become a token *)
    [ mk_rwarg (R2L, nomult) norwocc (RWdef, t) ]
  | [ ssrmult_ne(m) ssrrwocc(docc) ssrredex(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg (L2R, m) (docc, rx) r ]
  | [ "{" ne_ident_list(clr) "}" ssrredex_ne(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (mkclr clr, rx) r ]
  | [ "{" ne_ident_list(clr) "}" ssrrule(r) ] ->
    [ mk_rwarg norwmult (mkclr clr, None) r ]
  | [ "{" ssrocc(occ) "}" ssrredex(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (mkocc occ, rx) r ]
  | [ "{" "}" ssrredex(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (nodocc, rx) r ]
  | [ ssrredex_ne(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (noclr, rx) r ]
  | [ ssrrule_nt(r) ] ->
    [ mk_rwarg norwmult norwocc r ]
END

ARGUMENT EXTEND ssrrwarg TYPED AS ssrrwarg_nt PRINTED BY pr_ssrrwarg
  | [ ssrrwarg_nt(arg) ] -> [ arg ]
  | [ ssrdterm(t) ] -> [ mk_rwarg norwmult norwocc (RWeq, t) ]
END

let simplintac occ rdx sim gl = match rdx with
  | None when occ <> [] ->
    Util.error "no explicit redex to interpret occurrence switch"
  | None -> simpltac sim gl
  | Some t ->
    let cl, c, _ = pf_interp_gen gl false (mkocc occ, (None, t)) in
    let simptac = convert_concl (prod_applist cl [pf_nf gl c]) in
    match sim with
    | Simpl -> simptac gl
    | SimplCut -> tclTHEN simptac (tclTRY donetac) gl
    | _ -> Util.error "useless redex switch"

let rwtermtac dir t gl = rewritetac dir (pf_abs_term gl t) gl

let rec get_evalref c =  match kind_of_term c with
  | Var id -> EvalVarRef id, c
  | Const k -> EvalConstRef k, c
  | App (c', _) -> get_evalref c'
  | Cast (c', _, _) -> get_evalref c'
  | _ -> Util.error "Bad unfold head term"

let nb_occ v =
  let rec add_occs n c = if c = v then n + 1 else fold_constr add_occs n c in
  add_occs 0

let unfold_val = mkVar (id_of_tag "unfold occurrence")

(* Strip a pattern generated by a prenex implicit to its constant. *)
let strip_unfold_term oid t = match oid, t with
  | Some id, (OpenTerm _, c) ->
    let f, args = decompose_app c in
    if args <> [] && List.for_all isEvar args then begin
      match kind_of_term f with
      | Const kn when con_label kn = label_of_id id -> ClosedTerm, f
      | _ -> t
      end
    else t
  | _ -> t

(* We disable the zeta-reductions of the simple unfold when they would *)
(* interfere with the "in" tactical.                                   *)

let unfoldtac occ oid t gl =
  let t' = strip_unfold_term oid t in
  let cl, c, _ = pf_interp_gen gl false (mkocc occ, (None, t')) in
  let r, v = get_evalref c in
  if c = v && List.for_all ((<) 0) occ && pf_ctx_let_depth gl = 0
    then unfold_in_concl [occ, r] gl else
  let m = nb_occ v c in
  let rec mk_occ (i, occ') c' =
    if c' = v then (i + 1, occ') else
    if c' = unfold_val then (i + m, i :: occ') else
    fold_constr mk_occ (i, occ') c' in
  let _, occ' = mk_occ (1, []) (prod_applist cl [unfold_val]) in
  tclTHEN (convert_concl (prod_applist cl [c])) (unfold_in_concl [occ', r]) gl

let unfoldintac occ rdx oid t gl = match rdx with
| None ->
  unfoldtac occ oid t gl
| Some r ->
  let cl, c, _ = pf_interp_gen gl false (mkocc occ, (None, r)) in
  let tcl = pf_type_of gl cl in
  let cl' = mkLambda (Anonymous, tcl, mkApp (mkRel 1, [|c|])) in
  let gl' = pf_image gl (tclTHEN (apply_type cl' [cl]) (unfoldtac [] oid t)) in
  let _, args = destApplication (pf_concl gl') in
  convert_concl (prod_applist cl [args.(0)]) gl

let foldtac occ rdx t gl = match rdx with
  | None when occ <> [] ->
    Util.error "no explicit redex to interpret occurrence switch"
  | None ->
    let cl, c = pf_fill_term gl t in
    tclTHEN (convert_concl cl) (reduct_in_concl (Tacred.fold_commands [c])) gl
  | Some _ ->
    let ftac gl' =
      let _, c = pf_fill_term gl' t in
      let cl, _ = destApplication (pf_concl gl') in
      convert_concl (mkAppRed cl c) gl' in
    with_redexocc occ rdx ftac gl

let rwrxtac occ rx dir t gl =
  if rx <> None then with_redexocc occ rx (rwtermtac dir t) gl else
  if occ = [] then rwtermtac dir t gl else
  let {eq = eq; refl = refl} = build_coq_eq_data () in
  let eqc = pf_abs_term gl t in
  let _, t' = pf_reduce_to_quantified_ind gl (pf_type_of gl eqc) in
  let dc, eqt = decompose_prod t' in
  match kind_of_term eqt with
  | App (eq', eqa) when eq' = eq ->
    let c0 = eqa.(if dir = L2R then 1 else 2) in
    let rec zip_abs cl = function
      | [] -> cl
      | _ :: dc' when noccurn 1 cl -> zip_abs (liftn (-1) 1 cl) dc' 
      | (x, tx) :: dc' -> zip_abs (mkLambda(x, tx, cl)) dc' in
    let eqc' = zip_abs (mkApp (refl, [|eqa.(0); c0|])) dc in
    let c', with_c' =
      if nb_lam eqc' = 0 then c0, fun tac -> tac else
      let elim_eq = mkSsrConst "eq_protect_rect", NoBindings in
      let gl' = pf_image gl (general_elim (eqc', NoBindings) elim_eq) in
      let _, args = destApplication (pf_concl gl') in
      args.(2), tclTHEN (convert_concl (mkAppRed args.(1) args.(2))) in
    with_c' (with_redexocc occ (Some (ClosedTerm, c')) (rwtermtac dir t)) gl
  | _ -> Util.error "can't infer redex for nonstandard equality"

let rwargtac ((dir, mult), (((oclr, occ), rx), (kind, (oid, t)))) gl =
  let rwtac = match kind with
  | RWred sim -> simplintac occ rx sim
  | RWdef -> if dir = R2L then foldtac occ rx t else unfoldintac occ rx oid t
  | RWeq -> rwrxtac occ rx dir t in
  tclTHEN (tclMULT mult rwtac) (clear (pf_interp_clr gl (oclr, oid))) gl

(** Rewrite argument sequence *)

type ssrrwargs = ssrrwarg list

let pr_ssrrwargs prc prlc _ = function
  | [] -> mt ()
  | rwargs -> spc() ++ pr_list spc (pr_rwarg prc prlc) rwargs

ARGUMENT EXTEND ssrrwargs
       TYPED AS ssrrwarg list      PRINTED BY pr_ssrrwargs
  | [ ssrrwarg_list(args) ] -> [ args ]
END

ARGUMENT EXTEND ssrrwargs_nt
       TYPED AS ssrrwarg list      PRINTED BY pr_ssrrwargs
  | [ ssrrwarg_nt(arg) ssrrwargs(args) ] -> [ arg :: args ]
END

(** The "rewrite" tactic *)

let pr_ssrdtermspc prc _ _ dt = spc () ++ pr_dterm prc dt

ARGUMENT EXTEND ssrdtermspc TYPED AS ssrdterm PRINTED BY pr_ssrdtermspc
  | [ ssrdterm(dt) ] -> [ dt ]
END

let ssrrewritetac rwargs = tclTHENLIST (List.map rwargtac rwargs)

let ssrrewritebindtac (_, t) bl =
  Equality.general_rewrite_bindings true (force_term t, bl)

let ssrrewrite1tac (_, t) = rwtermtac L2R t

TACTIC EXTEND ssrrewrite
  | [ "rewrite" ssrrwargs_nt(args) ssrcls(cls) ] ->
    [ tclCLS (ssrrewritetac args) cls ]
  | [ "rewrite" ssrdtermspc(r) "with" bindings(bl) ssrcls(cls) ] ->
    [ tclCLS (ssrrewritebindtac r bl) cls ]
  | [ "rewrite" ssrdtermspc(r) ssrrwargs(args) ssrcls(cls) ] ->
    [ tclCLS (tclTHEN (ssrrewrite1tac r) (ssrrewritetac args)) cls ]
END

(** The "unlock" tactic *)

let pr_ssrunlockarg prc _ _ (occ, t) = pr_occ occ ++ pr_dterm prc t

ARGUMENT EXTEND ssrunlockarg TYPED AS ssrocc * ssrdterm
  PRINTED BY pr_ssrunlockarg
  | [  "{" ssrocc(occ) "}" ssrdterm(t) ] -> [ occ, t ]
  | [  ssrdterm(t) ] -> [ [], t ]
END

let rec unlocktac = function
  | (occ, (oid, t)) :: args ->
   tclTHEN (unfoldtac occ oid t) (unlocktac args)
  | [] ->
    let locked = mkSsrConst "locked" in
    let key = mkSsrConst "master_key" in
    tclTHEN (unfoldtac [] None (ClosedTerm, locked)) (simplest_case key)

TACTIC EXTEND ssrunlock
  | [ "unlock" ssrunlockarg_list(args) ssrcls(cls) ] ->
    [  tclCLS (unlocktac args) cls ]
END

(** 8. Forward chaining tactics (pose, set, have, suffice) *)

(** Defined identifier *)

type ssrfwdid = identifier

let pr_ssrfwdid _ _ _ = pr_id

(* We use a primitive parser for the head identifier of forward *)
(* tactis to avoid syntactic conflicts with basic Coq tactics. *)
ARGUMENT EXTEND ssrfwdid TYPED AS ident PRINTED BY pr_ssrfwdid
  | [ "(**)" ] -> [ Util.anomaly "Grammar placeholder match" ]
END

let input_ssrfwdid strm =
  match Stream.npeek 1 strm with
  | ["IDENT", id] ->
    accept_before_syms_or_id [":"; ":="; "("] strm; id_of_string id
  | _ -> raise Stream.Failure

let ssrfwdid_p4 = Gram.Entry.of_parser "ssrfwdid" input_ssrfwdid

GEXTEND Gram
  GLOBAL: ssrfwdid_p4 ssrfwdid;
  ssrfwdid: [[ id = ssrfwdid_p4 -> id ]];
END

(** Definition value formatting *)

(* We use an intermediate structure to correctly render the binder list  *)
(* abbreviations. We use a list of hints to extract the binders and      *)
(* base term from a term, for each of the three levels of representation *)
(* of constr terms.                                                      *)

type 'term ssrbind =
  | Bvar of name
  | Bdecl of name list * 'term
  | Bdef of name * 'term option * 'term
  | Bstruct of name
  | Bcast of 'term

let pr_binder prlc = function
  | Bvar x ->
    pr_name x
  | Bdecl (xs, t) ->
    str "(" ++ pr_list pr_spc pr_name xs ++ str " : " ++ prlc t ++ str ")"
  | Bdef (x, None, v) ->
    str "(" ++ pr_name x ++ str " := " ++ prlc v ++ str ")"
  | Bdef (x, Some t, v) ->
    str "(" ++ pr_name x ++ str " : " ++ prlc t ++
                            str " := " ++ prlc v ++ str ")"
  | Bstruct x ->
    str "{struct " ++ pr_name x ++ str "}"
  | Bcast t ->
    str ": " ++ prlc t

type 'term ssrbindval = 'term ssrbind list * 'term

type ssrbindfmt =
  | BFvar
  | BFdecl of int        (* #xs *)
  | BFcast               (* final cast *)
  | BFdef of bool        (* has cast? *)
  | BFrec of bool * bool (* has struct? * has cast? *)

let rec mkBstruct i = function
  | Bvar x :: b ->
    if i = 0 then [Bstruct x] else mkBstruct (i - 1) b
  | Bdecl (xs, _) :: b ->
    let i' = i - List.length xs in
    if i' < 0 then [Bstruct (List.nth xs i)] else mkBstruct i' b
  | _ :: b -> mkBstruct i b
  | [] -> []

let rec format_local_binders h0 bl0 = match h0, bl0 with
  | BFvar :: h, LocalRawAssum ([_, x], _) :: bl ->
    Bvar x :: format_local_binders h bl
  | BFdecl _ :: h, LocalRawAssum (lxs, t) :: bl ->
    Bdecl (List.map snd lxs, t) :: format_local_binders h bl
  | BFdef false :: h, LocalRawDef ((_, x), v) :: bl ->
    Bdef (x, None, v) :: format_local_binders h bl
  | BFdef true :: h, LocalRawDef ((_, x), CCast (_, v, _, t)) :: bl ->
    Bdef (x, Some t, v) :: format_local_binders h bl
  | _ -> []
  
let rec format_constr_expr h0 c0 = match h0, c0 with
  | BFvar :: h, CLambdaN (_, [[_, x], _], c) ->
    let bs, c' = format_constr_expr h c in
    Bvar x :: bs, c'
  | BFdecl _:: h, CLambdaN (_, [lxs, t], c) ->
    let bs, c' = format_constr_expr h c in
    Bdecl (List.map snd lxs, t) :: bs, c'
  | BFdef false :: h, CLetIn(_, (_, x), v, c) ->
    let bs, c' = format_constr_expr h c in
    Bdef (x, None, v) :: bs, c'
  | BFdef true :: h, CLetIn(_, (_, x), CCast (_, v, _, t), c) ->
    let bs, c' = format_constr_expr h c in
    Bdef (x, Some t, v) :: bs, c'
  | [BFcast], CCast (_, c, _, t) ->
    [Bcast t], c
  | BFrec (has_str, has_cast) :: h, 
    CFix (_, _, [_, (Some i, CStructRec), bl, t, c]) ->
    let bs = format_local_binders h bl in
    let bstr = if has_str then mkBstruct i bs else [] in
    bs @ bstr @ (if has_cast then [Bcast t] else []), c
  | BFrec (_, has_cast) :: h, CCoFix (_, _, [_, bl, t, c]) ->
    format_local_binders h bl @ (if has_cast then [Bcast t] else []), c
  | _, c ->
    [], c

let rec format_rawdecl h0 d0 = match h0, d0 with
  | BFvar :: h, (x, None, _) :: d ->
    Bvar x :: format_rawdecl h d
  | BFdecl 1 :: h,  (x, None, t) :: d ->
    Bdecl ([x], t) :: format_rawdecl h d
  | BFdecl n :: h, (x, None, t) :: d when n > 1 ->
    begin match format_rawdecl (BFdecl (n - 1) :: h) d with
    | Bdecl (xs, _) :: bs -> Bdecl (x :: xs, t) :: bs
    | bs -> Bdecl ([x], t) :: bs
    end
  | BFdef false :: h, (x, Some v, _)  :: d ->
    Bdef (x, None, v) :: format_rawdecl h d
  | BFdef true:: h, (x, Some (RCast (_, v, _, t)), _) :: d ->
    Bdef (x, Some t, v) :: format_rawdecl h d
  | _, (x, None, t) :: d ->
    Bdecl ([x], t) :: format_rawdecl [] d
  | _, (x, Some v, _) :: d ->
     Bdef (x, None, v) :: format_rawdecl [] d
  | _, [] -> []

let rec format_rawconstr h0 c0 = match h0, c0 with
  | BFvar :: h, RLambda (_, x, _, c) ->
    let bs, c' = format_rawconstr h c in
    Bvar x :: bs, c'
  | BFdecl 1 :: h,  RLambda (_, x, t, c) ->
    let bs, c' = format_rawconstr h c in
    Bdecl ([x], t) :: bs, c'
  | BFdecl n :: h,  RLambda (_, x, t, c) when n > 1 ->
    begin match format_rawconstr (BFdecl (n - 1) :: h) c with
    | Bdecl (xs, _) :: bs, c' -> Bdecl (x :: xs, t) :: bs, c'
    | _ -> [Bdecl ([x], t)], c
    end
  | BFdef false :: h, RLetIn(_, x, v, c) ->
    let bs, c' = format_rawconstr h c in
    Bdef (x, None, v) :: bs, c'
  | BFdef true :: h, RLetIn(_, x, RCast (_, v, _, t), c) ->
    let bs, c' = format_rawconstr h c in
    Bdef (x, Some t, v) :: bs, c'
  | [BFcast], RCast (_, c, _, t) ->
    [Bcast t], c
  | BFrec (has_str, has_cast) :: h, RRec (_, f, _, bl, t, c)
      when Array.length c = 1 ->
    let bs = format_rawdecl h bl.(0) in
    let bstr = match has_str, f with
    | true, RFix ([|Some i, RStructRec|], _) -> mkBstruct i bs
    | _ -> [] in
    bs @ bstr @ (if has_cast then [Bcast t.(0)] else []), c.(0)
  | _, c ->
    [], c

let bname_id = function Name id -> id | _ -> id_of_tag "argument wildcard"
let substBvar x c = subst1 (mkVar (bname_id x)) c

let rec strip_fix_type h0 c0 = match h0, kind_of_term c0 with
  | (BFvar | BFdecl 1) :: h, Prod (x, _, c) ->
    strip_fix_type h (substBvar x c)
  | BFdecl n :: h, Prod (x, _, c) when n > 1 ->
    strip_fix_type (BFdecl (n - 1) :: h) (substBvar x c)
  | BFdef _ :: h, LetIn(x, _, _, c) ->
    strip_fix_type h (substBvar x c)
  | _ ->
    c0

let rec format_constr h0 c0 = match h0, kind_of_term c0 with
  | BFvar :: h, Lambda (x, _, c) ->
    let bs, c' = format_constr h (substBvar x c) in
    Bvar x :: bs, c'
  | BFdecl 1 :: h, Lambda (x, t, c) ->
    let bs, c' = format_constr h (substBvar x c) in
    Bdecl ([x], t) :: bs, c'
  | BFdecl n :: h, Lambda (x, t, c) when n > 1 ->
    begin match format_constr (BFdecl (n - 1) :: h) (substBvar x c) with
    | Bdecl (xs, _) :: bs, c' -> Bdecl (x :: xs, t) :: bs, c'
    | _ -> [Bdecl ([x], t)], c
    end
  | BFdef has_cast :: h, LetIn(x, v, _, c) ->
    let bs, c' = format_constr h (substBvar x c) in
    begin match kind_of_term v with
    | Cast (v', _, t') when has_cast -> Bdef (x, Some t', v') :: bs, c'
    | _ -> Bdef (x, None, v) :: bs, c'
    end
  | [BFcast], Cast (c, _, t) ->
    [Bcast t], c
  | BFrec (has_str, has_cast) :: h, Fix ((i, _), (x, t0, c))
      when Array.length c = 1 ->
    let t = strip_fix_type h t0.(0) in
    let bs, c' = format_constr h (substBvar x.(0) c.(0)) in
    let bstr = if has_str then mkBstruct i.(0) bs else [] in
    bs @ bstr @ (if has_cast then [Bcast t] else []), c'
  | BFrec (has_str, has_cast) :: h, CoFix (_, (x, t0, c))
      when Array.length c = 1 ->
    let t = strip_fix_type h t0.(0) in
    let bs, c' = format_constr h (substBvar x.(0) c.(0)) in
    bs @ (if has_cast then [Bcast t] else []), c'
  | _ ->
    [], c0

(** Forward chaining argument *)

(* There are three kinds of forward definitions:           *)
(*   - Hint: type only, cast to Type, may have proof hint. *)
(*   - Have: type option + value, no space before type     *)
(*   - Pose: binders + value, space before binders.        *)

type ssrfwdkind = FwdHint | FwdHave | FwdPose

type ssrfwdfmt = ssrfwdkind * ssrbindfmt list

let pr_fwdkind = function FwdHint -> str ": " | _ -> str " :=" ++ spc ()
let pr_fwdfmt (fk, _ : ssrfwdfmt) = pr_fwdkind fk

let wit_ssrfwdfmt, globwit_ssrfwdfmt, rawwit_ssrfwdfmt =
  add_genarg "ssrfwdfmt" pr_fwdfmt

type ssrfwd = ssrfwdfmt * ssrterm

let pr_ssrfwd prc _ _ (k, c) = pr_fwdfmt k ++ pr_term prc c

let mkFwdVal fk c = (fk, []), (ClosedTerm, c)

let mkFwdCast fk loc t c = (fk, [BFcast]), (ClosedTerm, CCast (loc, c, dC, t))

let mkFwdHint loc t = mkFwdCast FwdHint loc (mkCType loc) t

ARGUMENT EXTEND ssrfwd TYPED AS ssrfwdfmt * ssrterm PRINTED BY pr_ssrfwd
  | [ ":=" lconstr(c) ] -> [ mkFwdVal FwdPose c ]
  | [ ":" lconstr (t) ":=" lconstr(c) ] -> [ mkFwdCast FwdPose loc t c ]
END

(* Representation level-specific printers. *)

let pr_gen_fwd prval prc prlc fk (bs, c) =
  let prc s = str s ++ spc () ++ prval prc prlc c in
  match fk, bs with
  | FwdHint, _ -> prc ":"
  | FwdHave, [Bcast t] -> str ":" ++ spc () ++ prlc t ++ prc " :="
  | _, [] -> prc " :="
  | _ -> spc () ++ pr_list spc (pr_binder prlc) bs ++ prc " :="

let pr_raw_fwd prval = function
| (fk, _), ((ErrorTerm _ as ck), _) -> pr_fwdkind fk ++ pr_termkind ck
| (fk, h), (_, c) ->
  pr_gen_fwd prval pr_constr_expr prl_constr_expr fk (format_constr_expr h c)

let pr_glob_fwd prval prval' = function
| (fk, _), ((ErrorTerm _ as ck), _) -> pr_fwdkind fk ++ pr_termkind ck
| fh, (ck, (_, Some c)) -> pr_raw_fwd prval (fh, (ck, c))
| (fk, h), (_, (c, None)) ->
  pr_gen_fwd prval' pr_rawconstr prl_rawconstr fk (format_rawconstr h c)

let pr_closed_fwd prval = function
| (fk, _), ((ErrorTerm _ as ck), _) -> pr_fwdkind fk ++ pr_termkind ck
| (fk, h), (_, c) ->
  pr_gen_fwd prval pr_constr prl_constr fk (format_constr h c)

let pr_unguarded prc prlc = prlc

let pr_closed_ssrfwd _ _ _ = pr_closed_fwd pr_unguarded
let pr_glob_ssrfwd   _ _ _ = pr_glob_fwd pr_unguarded pr_unguarded
let pr_raw_ssrfwd    _ _ _ = pr_raw_fwd pr_unguarded
 
(** Independent parsing for binders *)

(* The pose, pose fix, and pose cofix tactics use these internally to  *)
(* parse argument fragments.                                           *)

let pr_ssrbvar prc _ _ v = prc v

ARGUMENT EXTEND ssrbvar TYPED AS constr PRINTED BY pr_ssrbvar
| [ ident(id) ] -> [ mkCVar loc id ]
| [ "_" ] -> [ CHole loc ]
END

let bvar_lname = function
  | CRef (Ident (loc, id)) -> loc, Name id
  | c -> constr_loc c, Anonymous

let pr_ssrbinder prc _ _ (_, c) = prc c

ARGUMENT EXTEND ssrbinder TYPED AS ssrfwdfmt * constr PRINTED BY pr_ssrbinder
  | [ ssrbvar(bv) ] ->
    [ let xloc, _ as x = bvar_lname bv in
      (FwdPose, [BFvar]), CLambdaN (loc, [[x], CHole xloc], CHole loc) ]
  | [ "(" ssrbvar(bv) ":" lconstr(t) ")" ] ->
    [ let x = bvar_lname bv in
      (FwdPose, [BFdecl 1]), CLambdaN (loc, [[x], t], CHole loc) ]
  | [ "(" ssrbvar(bv) ne_ssrbvar_list(bvs) ":" lconstr(t) ")" ] ->
    [ let xs = List.map bvar_lname (bv :: bvs) in
      let n = List.length xs in
      (FwdPose, [BFdecl n]), CLambdaN (loc, [xs, t], CHole loc) ]
  | [ "(" ssrbvar(id) ":" lconstr(t) ":=" lconstr(v) ")" ] ->
    [ let loc' = Util.join_loc (constr_loc t) (constr_loc v) in
      let v' = CCast (loc', v, dC, t) in
      (FwdPose, [BFdef true]), CLetIn (loc, bvar_lname id, v', CHole loc) ]
  | [ "(" ssrbvar(id) ":=" lconstr(v) ")" ] ->
    [ (FwdPose, [BFdef false]), CLetIn (loc, bvar_lname id, v, CHole loc) ]
END

let rec binders_fmts = function
  | ((_, h), _) :: bs -> h @ binders_fmts bs
  | _ -> []

let push_binders c2 =
  let loc2 = constr_loc c2 in let mkloc loc1 = Util.join_loc loc1 loc2 in
  let rec loop = function
  | (_, CLambdaN (loc1, b, _)) :: bs -> CLambdaN (mkloc loc1, b, loop bs)
  | (_, CLetIn (loc1, x, v, _)) :: bs -> CLetIn (mkloc loc1, x, v, loop bs)
  | _ -> c2 in
  loop

let rec fix_binders = function
  | (_, CLambdaN (_, [xs, t], _)) :: bs ->
    LocalRawAssum (xs, t) :: fix_binders bs
  | (_, CLetIn (_, x, v, _)) :: bs ->
    LocalRawDef (x, v) :: fix_binders bs
  | _ -> []

let pr_ssrstruct _ _ _ = function
  | Some id -> str "{struct " ++ pr_id id ++ str "}"
  | None -> mt ()

ARGUMENT EXTEND ssrstruct TYPED AS ident option PRINTED BY pr_ssrstruct
| [ "{" "struct" ident(id) "}" ] -> [ Some id ]
| [ ] -> [ None ]
END

(** The "pose" tactic *)

(* The plain pose form. *)

ARGUMENT EXTEND ssrposefwd TYPED AS ssrfwd      PRINTED BY pr_closed_ssrfwd
                       RAW_TYPED AS ssrfwd  RAW_PRINTED BY pr_raw_ssrfwd
                      GLOB_TYPED AS ssrfwd GLOB_PRINTED BY pr_glob_ssrfwd
  | [ ssrbinder_list(bs) ssrfwd(fwd) ] ->
    [ let (fk, h), (ck, c) = fwd in
      (fk, binders_fmts bs @ h), (ck, push_binders c bs) ]
END

(* The pose fix form. *)

let pr_ssrfixfwd prfwd prc prlc prt (id, fwd) =
  str " fix " ++ pr_id id ++ prfwd prc prlc prt fwd

let pr_closed_ssrfixfwd = pr_ssrfixfwd pr_closed_ssrfwd
let pr_raw_ssrfixfwd = pr_ssrfixfwd pr_raw_ssrfwd
let pr_glob_ssrfixfwd = pr_ssrfixfwd pr_glob_ssrfwd

let bvar_locid = function
  | CRef (Ident (loc, id)) -> loc, id
  | _ -> Util.error "Missing identifier after \"(co)fix\""

ARGUMENT EXTEND ssrfixfwd
      TYPED AS ident * ssrfwd      PRINTED BY pr_closed_ssrfixfwd
  RAW_TYPED AS ident * ssrfwd  RAW_PRINTED BY pr_raw_ssrfixfwd
 GLOB_TYPED AS ident * ssrfwd GLOB_PRINTED BY pr_glob_ssrfixfwd
  | [ "fix" ssrbvar(bv) ssrbinder_list(bs) ssrstruct(sid) ssrfwd(fwd) ] ->
    [ let (_, id) as lid = bvar_locid bv in
      let (fk, h), (ck, c) = fwd in
      let has_cast, t', c' = match format_constr_expr h c with
      | [Bcast t'], c' -> true, t', c'
      | _ -> false, CHole (constr_loc c), c in
      let lb = fix_binders bs in
      let has_struct, i =
        let rec loop i = function
          (_, Name id') :: _ when sid = Some id' -> true, i
          | _ :: bn -> loop (i + 1 ) bn
          | [] when sid <> None -> Util.error "Bad structural argument"
	  | [] -> false, i - 1 in
        loop 0 (names_of_local_assums lb) in
      let h' = BFrec (has_struct, has_cast) :: binders_fmts bs in
      let fix = CFix (loc, lid, [id, (Some i, CStructRec), lb, t', c']) in
      id, ((fk, h'), (ck, fix)) ]
END

(* The pose cofix form. *)

let pr_ssrcofixfwd prfwd prc prlc prt (id, fwd) =
  str " cofix " ++ pr_id id ++ prfwd prc prlc prt fwd

let pr_closed_ssrcofixfwd = pr_ssrcofixfwd pr_closed_ssrfwd
let pr_raw_ssrcofixfwd = pr_ssrcofixfwd pr_raw_ssrfwd
let pr_glob_ssrcofixfwd = pr_ssrcofixfwd pr_glob_ssrfwd

ARGUMENT EXTEND ssrcofixfwd
      TYPED AS ssrfixfwd      PRINTED BY pr_closed_ssrcofixfwd
  RAW_TYPED AS ssrfixfwd  RAW_PRINTED BY pr_raw_ssrcofixfwd
 GLOB_TYPED AS ssrfixfwd GLOB_PRINTED BY pr_glob_ssrcofixfwd
  | [ "cofix" ssrbvar(bv) ssrbinder_list(bs) ssrfwd(fwd) ] ->
    [ let _, id as lid = bvar_locid bv in
      let (fk, h), (ck, c) = fwd in
      let has_cast, t', c' = match format_constr_expr h c with
      | [Bcast t'], c' -> true, t', c'
      | _ -> false, CHole (constr_loc c), c in
      let h' = BFrec (false, has_cast) :: binders_fmts bs in
      id, ((fk, h'), (ck, CCoFix (loc, lid, [id, fix_binders bs, t', c']))) ]
END

let ssrposetac (id, (_, t)) gl =
  letin_tac true (Name id) (pf_abs_term gl t) nowhere gl
  
TACTIC EXTEND ssrpose
| [ "pose" ssrfixfwd(ffwd) ] -> [ ssrposetac ffwd ]
| [ "pose" ssrcofixfwd(ffwd) ] -> [ ssrposetac ffwd ]
| [ "pose" ssrfwdid(id) ssrposefwd(fwd) ] -> [ ssrposetac (id, fwd) ]
END

(** The "set" tactic *)

type ssrsetfwd = ssrfwd * ssrdocc

let guard_setrhs s i = s.[i] = '{'

let pr_setrhs occ prc prlc c =
  if occ = nodocc then pr_guarded guard_setrhs prlc c else
  pr_docc occ ++ prc c

let pr_closed_ssrsetfwd _ _ _ (fwd, docc) = pr_closed_fwd (pr_setrhs docc) fwd
let pr_raw_ssrsetfwd _ _ _ (fwd, docc) = pr_raw_fwd (pr_setrhs docc) fwd
let pr_glob_ssrsetfwd _ _ _ (fwd, docc) =
  pr_glob_fwd (pr_setrhs docc) (pr_setrhs docc) fwd

ARGUMENT EXTEND ssrsetfwd
       TYPED AS ssrfwd * ssrdocc      PRINTED BY pr_closed_ssrsetfwd
   RAW_TYPED AS ssrfwd * ssrdocc  RAW_PRINTED BY pr_raw_ssrsetfwd
  GLOB_TYPED AS ssrfwd * ssrdocc GLOB_PRINTED BY pr_glob_ssrsetfwd
| [ ":" lconstr(t) ":=" "{" ssrocc(occ) "}" constr(c) ] ->
  [ mkFwdCast FwdPose loc t c, mkocc occ ]
| [ ":" lconstr(t) ":=" lconstr(c) ] -> [ mkFwdCast FwdPose loc t c, nodocc ]
| [ ":=" "{" ssrocc(occ) "}" constr(c) ] -> [ mkFwdVal FwdPose c, mkocc occ ]
| [ ":=" lconstr(c) ] -> [ mkFwdVal FwdPose c, nodocc ]
END

let settac id ((_, c0), (_, occ)) gl =
  let cl, c = pf_fill_term gl c0 in
  let occ' = List.map (fun n -> ArgArg n) occ in
  let coq_cls = {onhyps = Some []; onconcl = true; concl_occs = occ'} in
  tclTHEN (convert_concl cl) (letin_tac true (Name id) c coq_cls) gl

TACTIC EXTEND Ssrset
| [ "set" ssrfwdid(id) ssrsetfwd(fwd) ssrcls(cls) ] ->
  [ tclCLS (settac id fwd) cls ]    
END

(** The "have" tactic *)

(* Intro pattern. *)

let pr_ssrhpats _ _ _ = function [pat] -> str " " ++ pr_ipat pat | _ -> mt ()

ARGUMENT EXTEND ssrhpats TYPED AS ssripats PRINTED BY pr_ssrhpats
| [ ssrvpat(pat) ] -> [ [pat] ]
| [ ] -> [ [] ]
END

(* Argument. *)

type ssrhavefwd = ssrfwd * ssrhint

let pr_ssrhavefwd prfwd prc prlc prt (fwd, hint) =
  prfwd prc prlc prt fwd ++ pr_hint prt hint
let pr_closed_ssrhavefwd = pr_ssrhavefwd pr_closed_ssrfwd
let pr_glob_ssrhavefwd = pr_ssrhavefwd pr_glob_ssrfwd
let pr_raw_ssrhavefwd = pr_ssrhavefwd pr_raw_ssrfwd

ARGUMENT EXTEND ssrhavefwd
       TYPED AS ssrfwd * ssrhint      PRINTED BY pr_closed_ssrhavefwd
   RAW_TYPED AS ssrfwd * ssrhint  RAW_PRINTED BY pr_raw_ssrhavefwd
  GLOB_TYPED AS ssrfwd * ssrhint GLOB_PRINTED BY pr_glob_ssrhavefwd
| [ ":" lconstr(t) ssrhint(hint) ] -> [ mkFwdHint (constr_loc t) t, hint ]
| [ ":" lconstr(t) ":=" lconstr(c) ] -> [ mkFwdCast FwdHave loc t c, nohint ]
| [ ":=" lconstr(c) ] -> [ mkFwdVal FwdHave c, nohint ]
END

(* Tactic. *)

let basecuttac name c gl =
  apply (mkApp (mkSsrConst name, [|pf_prod_term gl c|])) gl

let havegentac c gl =
  let c' = pf_abs_term gl c in
  apply_type (mkArrow (pf_type_of gl c') (pf_concl gl)) [c'] gl

let havetac clr pats (((fk, _), c), hint) =
 let itac = tclTHEN (introstac pats) (clear clr) in
 if fk = FwdHave then tclTHEN (havegentac c) itac else
 tclTHENS (basecuttac "ssr_have" c) [hinttac hint; itac]

TACTIC EXTEND ssrhave
| [ "have" ssrclear(clr) ssrhpats(pats) ssrhavefwd(fwd) ] ->
  [ havetac clr pats fwd ]
END

(** The "suffice" tactic *)

ARGUMENT EXTEND ssrsufficefwd
       TYPED AS ssrhavefwd      PRINTED BY pr_closed_ssrhavefwd
   RAW_TYPED AS ssrhavefwd  RAW_PRINTED BY pr_raw_ssrhavefwd
  GLOB_TYPED AS ssrhavefwd GLOB_PRINTED BY pr_glob_ssrhavefwd
| [ ":" lconstr(t) ssrhint(hint) ] ->[ mkFwdHint (constr_loc t) t, hint ]
END

let sufficetac clr pats ((_, c), hint) =
  let htac = tclTHEN (introstac pats) (hinttac hint) in
  tclTHENS (basecuttac "ssr_suffice" c) [htac; clear clr]

TACTIC EXTEND Ssrsuffice
| [ "suffice" ssrclear(clr) ssrhpats(pats) ssrsufficefwd(fwd) ] ->
  [ sufficetac clr pats fwd ]
END

(** 9. Coq v8.1 compatibility fixes. *)

(* New Coq v8.1 notation uses a "by" quasi-keyword, i.e., a reserved   *)
(* identifier used as a keyword. This is incompatible with ssreflect.v *)
(* which makes "by" a true keyword, because of technicalities in the   *)
(* internal lexer-parser API of Coq. We patch this here by adding      *)
(* new parsing rules that recognize the new keyword.                   *)

let lpar_id_colon = G_tactic.lpar_id_colon in
GEXTEND Gram
  GLOBAL: tactic_expr simple_tactic lpar_id_colon simple_intropattern
          lconstr constr;
  simple_tactic: [
  [ IDENT "assert"; id = lpar_id_colon; c = lconstr; ")";
         "by"; tac = tactic_expr LEVEL "3" -> 
       TacAssert (Some (TacComplete tac), IntroIdentifier id, c)
  | IDENT "assert"; c = constr; "as"; ipat = simple_intropattern;
         "by"; tac = tactic_expr LEVEL "3" -> 
       TacAssert (Some (TacComplete tac), ipat, c)
  | IDENT "assert"; c = constr; "as"; ipat = simple_intropattern -> 
       TacAssert (Some (TacId []), ipat, c)
  | IDENT "assert"; c = constr; "by"; tac = tactic_expr LEVEL "3" -> 
       TacAssert (Some (TacComplete tac), IntroAnonymous, c)
  ] ];
END

let pr_ssrrelattr prc _ _ (a, c) = pr_id a ++ str " proved by " ++ prc c

ARGUMENT EXTEND ssrrelattr TYPED AS ident * constr PRINTED BY pr_ssrrelattr
  [ ident(a) "proved" "by" constr(c) ] -> [ a, c ]
END

GEXTEND Gram
  GLOBAL: ident constr ssrrelattr;
  ssrrelattr: [[ a = ident; IDENT "proved"; "by"; c = constr -> a, c ]];
END

let rec ssr_add_relation n d deq pf_refl pf_sym pf_trans = function
  | [] ->
    Setoid_replace.add_relation n d deq pf_refl pf_sym pf_trans
  | (aid, c) :: al -> match string_of_id aid with
  | "reflexivity" when pf_refl = None ->
    ssr_add_relation n d deq (Some c) pf_sym pf_trans al
  | "symmetry" when pf_sym = None ->
    ssr_add_relation n d deq pf_refl (Some c) pf_trans al
  | "transitivity" when pf_trans = None ->
    ssr_add_relation n d deq pf_refl pf_sym (Some c) al
  | a -> Util.error ("bad attribute \"" ^ a ^ "\" in Add Relation")

VERNAC COMMAND EXTEND SsrAddRelation
 [ "Add" "Relation" constr(d) constr(deq) ssrrelattr_list(al) "as" ident(n) ]
 -> [ ssr_add_relation n d deq None None None al ]
END
