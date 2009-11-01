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
open Pretyping.Default
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

let not_section_id id = not (is_section_variable id)

let is_pf_var c = isVar c && not_section_id (destVar c)

let pf_ids_of_proof_hyps gl =
  let add_hyp (id, _, _) ids = if not_section_id id then id :: ids else ids in
  Sign.fold_named_context add_hyp (pf_hyps gl) ~init:[]

(* Basic tactics *)

let convert_concl_no_check t = convert_concl_no_check t DEFAULTcast
let convert_concl t = convert_concl t DEFAULTcast
let reduct_in_concl t = reduct_in_concl (t, DEFAULTcast)
let havetac id = forward None (IntroIdentifier id)
let settac id = letin_tac true (Name id)
let posetac id cl = settac id cl nowhere

(** Name generation *)

(* Separator for composite ids; should be '_' or ' '. The latter avoids *)
(* clashes with user names and gives prettier error, but may give       *)
(* incorrect printouts of proofs, and cause extraction errors.          *)

let tag_sep = ref ' '

let id_of_tag s =
  if !tag_sep = ' ' then id_of_string s else begin
    let s' = String.copy s in
    for i = 0 to String.length s - 1 do
      if s.[i] = ' ' then s'.[i] <- !tag_sep
    done;
    id_of_string s'
  end

let tag_id tag id = id_of_tag (sprintf "%s %s" tag (string_of_id id))

let is_tag_id tag id =
  let n = String.length tag in let s = string_of_id id in
  String.length s > n && s.[n] = !tag_sep && String.sub s 0 n = tag

let sync_ids = ref []

let mk_sync_id s =
  let idref = ref (id_of_tag s) in sync_ids := (s, idref) :: !sync_ids; idref

let set_tag_sep s =
  if String.length s = 1 then begin
    tag_sep := s.[0];
    List.iter (fun (s, r) -> r := id_of_tag s) !sync_ids
  end else
  error "ssr internal ident separator must be a single character"

let get_tag_sep () = String.make 1 !tag_sep

let _ =
  Goptions.declare_string_option 
    { Goptions.optsync  = true;
      Goptions.optname  = "internal ident separator";
      Goptions.optkey   = (PrimaryTable "SsrIdSeparator");
      Goptions.optread  = get_tag_sep;
      Goptions.optwrite = set_tag_sep }

let rec constr_name c = match kind_of_term c with
  | Var id -> Name id
  | Cast (c', _, _) -> constr_name c'
  | Const cn -> Name (id_of_label (con_label cn))
  | App (c', _) -> constr_name c'
  | _ -> Anonymous

(** Constructors for constr_expr *)

let mkCProp loc = CSort (loc, RProp Null)

let mkCType loc = CSort (loc, RType None)

let mkCVar loc id = CRef (Ident (loc, id))

let rec mkCHoles loc n =
  if n <= 0 then [] else CHole loc :: mkCHoles loc (n - 1)

let rec isCHoles = function CHole _ :: cl -> isCHoles cl | cl -> cl = []

let mkCExplVar loc id n =
   CAppExpl (loc, (None, Ident (loc, id)), mkCHoles loc n)

(** Constructors for rawconstr *)

let dC = CastConv DEFAULTcast

let mkRHole = RHole (dummy_loc, InternalHole)

let rec mkRHoles n = if n > 0 then mkRHole :: mkRHoles (n - 1) else []

let rec isRHoles = function RHole _ :: cl -> isRHoles cl | cl -> cl = []

let mkRApp f args = if args = [] then f else RApp (dummy_loc, f, args)

let mkRVar id = RRef (dummy_loc, VarRef id)

(* let mkRVar id = RVar (dummy_loc, id) *)

let mkRCast rc rt =  RCast (dummy_loc, rc, dC, rt)

let mkRType =  RSort (dummy_loc, RType None)

let mkRArrow rt1 rt2 = RProd (dummy_loc, Anonymous, rt1, rt2)

let mkRConstruct c = RRef (dummy_loc, ConstructRef c)

let mkRInd mind = RRef (dummy_loc, IndRef mind)

(* look up a name in the ssreflect internals module *)

let ssrdirpath = make_dirpath [id_of_string "ssreflect"]

let ssrqid name = make_qualid ssrdirpath (id_of_string name) 
let ssrtopqid name = make_short_qualid (id_of_string name) 

let mkSsrRef name =
  try Constrintern.locate_reference (ssrqid name) with Not_found ->
  try Constrintern.locate_reference (ssrtopqid name) with Not_found ->
  error "Small scale reflection library not loaded"

let mkSsrRRef name = RRef (dummy_loc, mkSsrRef name)

let mkSsrConst name = constr_of_reference (mkSsrRef name)

(** Constructors for constr *)

let mkAppRed f c = match kind_of_term f with
| Lambda (_, _, b) -> subst1 c b
| _ -> mkApp (f, [|c|])

let mkProt t c = mkApp (mkSsrConst "protect_term", [|t; c|])

let mkRefl t c = mkApp ((build_coq_eq_data()).refl, [|t; c|])

(* Application to a sequence of n rels (for building eta-expansions). *)
(* The rel indices decrease down to imin (inclusive), unless n < 0,   *)
(* in which case they're incresing (from imin).                       *)
let mkEtaApp c n imin =
  if n = 0 then c else
  let nargs, mkarg =
    if n < 0 then -n, (fun i -> mkRel (imin + i)) else
    let imax = imin + n - 1 in n, (fun i -> mkRel (imax - i)) in
  mkApp (c, Array.init nargs mkarg)

(* Same, but optimizing head beta redexes *)
let rec whdEtaApp c n =
  if n = 0 then c else match kind_of_term c with
  | Lambda (_, _, c') -> whdEtaApp c' (n - 1)
  | _ -> mkEtaApp (lift n c) n 1

(** Open term to lambda-term coercion *)

(* This operation takes a goal gl and an open term (sigma, t), and   *)
(* returns a term t' where all the new evars in sigma are abstracted *)
(* with the mkAbs argument, i.e., for mkAbs = mkLambda then there is *)
(* some duplicate-free array args of evars of sigma such that the    *)
(* term mkApp (t', args) is convertible to t.                        *)
(* This makes a useful shorthand for local definitions in proofs,    *)
(* i.e., pose succ := _ + 1 means pose succ := fun n : nat => n + 1, *)
(* and, in context of the the 4CT library, pose mid := maps id means *)
(*    pose mid := fun d : detaSet => @maps d d (@id (datum d))       *)
(* Note that this facility does not extend to set, which tries       *)
(* instead to fill holes by matching a goal subterm.                 *)
(* The argument to "have" et al. uses product abstraction, e.g.      *)
(*    have Hmid: forall s, (maps id s) = s.                          *)
(* stands for                                                        *)
(*    have Hmid: forall (d : dataSet) (s : seq d), (maps id s) = s.  *)
(* We also use this feature for rewrite rules, so that, e.g.,        *)
(*   rewrite: (plus_assoc _ 3).                                      *)
(* will execute as                                                   *)
(*   rewrite (fun n => plus_assoc n 3)                               *)
(* i.e., it will rewrite some subterm .. + (3 + ..) to .. + 3 + ...  *)
(* The convention is also used for the argument of the congr tactic, *)
(* e.g., congr (x + _ * 1).                                          *)

(*
let nf_etype sigma ev =
  Evarutil.nf_evar sigma (Evd.existential_type sigma ev)

let pf_abs_evars gl (sigma, c0) =
  let sigma0 = project gl in
  let rec put evlist c = match kind_of_term c with
  | Evar (k, _ as ev) ->  
    if List.mem ev evlist || Evd.mem sigma0 k then evlist else
    if List.mem_assoc k evlist then error "Incompatible evar dependencies" else
    ev :: put evlist (nf_etype sigma ev)
  | _ -> fold_constr put evlist c in
  let evlist = put [] c0 in
  if evlist = [] then 0, c0 else
  let rec lookup ev i = function
    | [] -> mkEvar ev
    | ev' :: evl -> if ev = ev' then mkRel i else lookup ev (i + 1) evl in
  let rec get i c = match kind_of_term c with
  | Evar ev -> lookup ev i evlist
  | _ -> map_constr_with_binders ((+) 1) get i c in
  let rec loop c i = function
  | [] -> c
  | ev :: evl ->
    let t = get (i - 1) (nf_etype sigma ev) in
    loop (mkLambda (Name (pf_type_id gl t), t, c)) (i - 1) evl in
  List.length evlist, loop (get 1 c0) 1 evlist
*)

let mk_evar_name n = Name (id_of_string (sprintf "(*SSR*)evar_%d_" n))

let nb_evar_deps x =
  try
    let s = match x with Name id -> string_of_id id | _ -> "" in
    if String.sub s 0 12 <> "(*SSR*)evar_" then raise Exit;
    int_of_string (String.sub s 12 (String.rindex s '_' - 12))
  with _ -> 0

let env_size env = List.length (Environ.named_context env)

(* Replace new evars with lambda variables, retaining local dependencies *)
(* but stripping global ones. We use the variable names to encode the    *)
(* the number of dependencies, so that the transformation is reversible. *)

let pf_abs_evars gl (sigma, c0) =
  let sigma0 = project gl in
  let nenv = env_size (pf_env gl) in
  let abs_evar n k =
    let evi = Evd.find sigma k in
    let dc = list_firstn n (evar_context evi) in
    let abs_dc c = function
    | x, Some b, t -> mkNamedLetIn x b t (mkArrow t c)
    | x, None, t -> mkNamedProd x t c in
    let t = Sign.fold_named_context_reverse abs_dc ~init:evi.evar_concl dc in
    Evarutil.nf_evar sigma t in
  let rec put evlist c = match kind_of_term c with
  | Evar (k, a) ->  
    if List.mem_assoc k evlist || Evd.mem sigma0 k then evlist else
    let n = Array.length a - nenv in
    let t = abs_evar n k in (k, (n, t)) :: put evlist t
  | _ -> fold_constr put evlist c in
  let evlist = put [] c0 in
  if evlist = [] then 0, c0 else
  let rec lookup k i = function
    | [] -> 0, 0
    | (k', (n, _)) :: evl -> if k = k' then i, n else lookup k (i + 1) evl in
  let rec get i c = match kind_of_term c with
  | Evar (ev, a) ->
    let j, n = lookup ev i evlist in
    if j = 0 then map_constr (get i) c else if n = 0 then mkRel j else
    mkApp (mkRel j, Array.init n (fun k -> get i a.(n - 1 - k)))
  | _ -> map_constr_with_binders ((+) 1) get i c in
  let rec loop c i = function
  | (_, (n, t)) :: evl ->
    loop (mkLambda (mk_evar_name n, get (i - 1) t, c)) (i - 1) evl
  | [] -> c in
  List.length evlist, loop (get 1 c0) 1 evlist

(* Strip all non-essential dependencies from an abstracted term, generating *)
(* standard names for the abstracted holes.                                 *)

let pf_abs_cterm gl n c0 =
  if n <= 0 then c0 else
  let noargs = [|0|] in
  let eva = Array.make n noargs in
  let rec strip i c = match kind_of_term c with
  | App (f, a) when isRel f ->
    let j = i - destRel f in
    if j >= n || eva.(j) = noargs then mkApp (f, Array.map (strip i) a) else
    let dp = eva.(j) in
    let nd = Array.length dp - 1 in
    let mkarg k = strip i a.(if k < nd then dp.(k + 1) - j else k + dp.(0)) in
    mkApp (f, Array.init (Array.length a - dp.(0)) mkarg)
  | _ -> map_constr_with_binders ((+) 1) strip i c in
  let rec strip_ndeps j i c = match kind_of_term c with
  | Prod (x, t, c1) when i < j ->
    let dl, c2 = strip_ndeps j (i + 1) c1 in
    if noccurn 1 c2 then dl, lift (-1) c2 else
    i :: dl, mkProd (x, strip i t, c2)
  | LetIn (x, b, t, c1) when i < j ->
    let _, _, c1' = destProd c1 in
    let dl, c2 = strip_ndeps j (i + 1) c1' in
    if noccurn 1 c2 then dl, lift (-1) c2 else
    i :: dl, mkLetIn (x, strip i b, strip i t, c2)
  | _ -> [], strip i c in
  let rec strip_evars i c = match kind_of_term c with
    | Lambda (x, t1, c1) when i < n ->
      let na = nb_evar_deps x in
      let dl, t2 = strip_ndeps (i + na) i t1 in
      let na' = List.length dl in
      eva.(i) <- Array.of_list (na - na' :: dl);
      let x' =
        if na' = 0 then Name (pf_type_id gl t2) else mk_evar_name na' in
      mkLambda (x', t2, strip_evars (i + 1) c1)
(*      if noccurn 1 c2 then lift (-1) c2 else
      mkLambda (Name (pf_type_id gl t2), t2, c2) *)
    | _ -> strip i c in
  strip_evars 0 c0

(* Undo the evar abstractions. Also works for non-evar variables. *)

let pf_unabs_evars gl ise n c0 =
  if n = 0 then c0 else
  let evv = Array.make n mkProp in
  let nev = ref 0 in
  let env0 = pf_env gl in
  let nenv0 = env_size env0 in
  let rec unabs i c = match kind_of_term c with
  | Rel j when i - j < !nev -> evv.(i - j)
  | App (f, a0) when isRel f ->
    let a = Array.map (unabs i) a0 in
    let j = i - destRel f in
    if j >= !nev then mkApp (f, a) else
    let ev, eva = destEvar evv.(j) in
    let nd = Array.length eva - nenv0 in
    if nd = 0 then mkApp (evv.(j), a) else
    let evarg k = if k < nd then a.(nd - 1 - k) else eva.(k) in
    let c' = mkEvar (ev, Array.init (nd + nenv0) evarg) in
    let na = Array.length a - nd in
    if na = 0 then c' else mkApp (c', Array.sub a nd na)
  | _ -> map_constr_with_binders ((+) 1) unabs i c in
  let push_rel = Environ.push_rel in
  let rec mk_evar j env i c = match kind_of_term c with
  | Prod (x, t, c1) when i < j ->
    mk_evar j (push_rel (x, None, unabs i t) env) (i + 1) c1
  | LetIn (x, b, t, c1) when i < j ->
    let _, _, c2 = destProd c1 in
    mk_evar j (push_rel (x, Some (unabs i b), unabs i t) env) (i + 1) c2
  | _ -> Evarutil.e_new_evar ise env (unabs i c) in
  let rec unabs_evars c =
    if !nev = n then unabs n c else match kind_of_term c with
  | Lambda (x, t, c1) when !nev < n ->
    let i = !nev in
    evv.(i) <- mk_evar (i + nb_evar_deps x) env0 i t;
    incr nev; unabs_evars c1
  | _ -> unabs !nev c in
  unabs_evars c0

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
(*  - the concrete syntax must start with a fixed string            *)
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

let interp_intro_pattern = interp_wit globwit_intro_pattern wit_intro_pattern

let interp_constr = interp_wit globwit_constr wit_constr

let interp_open_constr ist gl gc =
  interp_wit globwit_open_constr wit_open_constr ist gl ((), gc)

let interp_refine ist gl rc =
   let roc = (), (rc, None) in
   interp_wit globwit_casted_open_constr wit_casted_open_constr ist gl roc

let pf_match = pf_apply (fun e s c t -> understand_tcc s e ~expected_type:t c)

(*
let pf_match gl rc t =
  let tspec = Pretyping.OfType (Some t) in
  let understand = Pretyping.Default.understand_ltac in
  let (sigma, c) = understand (project gl) (pf_env gl) ([],[]) tspec rc in
  (evars_of sigma, c)
*)

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

(** 2. Vernacular commands: Prenex Implicits and Search *)

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
  let add_implicit_notation () =
    let atf = "@ '" ^ string_of_id f ^ "'", [SetLevel 10] in
    Metasyntax.add_notation false (mkCExplVar loc f 0) atf None in
  let mod_id = id_of_string ("Prenex_" ^ string_of_id f) in
  let start_module = Declaremods.start_module Modintern.interp_modtype None in
  let submod_id = prenex_implicit_submod_id in
  let make_loc_qid id = loc, make_short_qualid id in
  start_module mod_id [] None;
    Command.syntax_definition prenex_implicit_id (mkCVar loc f) false true;
    start_module submod_id [] None;
      add_implicit_notation ();
      Command.syntax_definition f (mkCExplVar loc f n) false true;
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

let qualify_ref clref =
  let loc, qid = qualid_of_reference clref in
  try match Nametab.extended_locate qid with
  | TrueGlobal _ -> clref
  | SyntacticDef kn ->
    let rec head_of = function
    | RRef (_, gref) ->
      Qualid (loc, Nametab.shortest_qualid_of_global Idset.empty gref)
    | RApp (_, rc, _) -> head_of rc
    | RCast (_, rc, _, _) -> head_of rc
    | RLetIn (_, _, _, rc) -> head_of rc
    | rc -> clref in
    head_of (Syntax_def.search_syntactic_definition loc kn)
  with _ -> clref

let ssrqref = Gram.Entry.create "ssrqref"

let class_rawexpr = G_vernac.class_rawexpr in
let global = Constr.global in
GEXTEND Gram
  GLOBAL: class_rawexpr global ssrqref;
  ssrqref: [[ gref = global -> qualify_ref gref ]];
  class_rawexpr: [[ class_ref = ssrqref -> Vernacexpr.RefClass class_ref ]];
END

(* Unfortunately, the Vernac grammar does not define and/or export  *)
(* entry points for the Search auxiliary non-termainals, so we have *)
(* to paraphrase part of the Vernac grammar here.                   *)
let command = Vernac_.command in
let ne_string = Prim.ne_string in
let global = Constr.global in
GEXTEND Gram
  GLOBAL: global ssrqref ne_string command;
  ssr_modloc: [
    [ IDENT "inside"; mods = LIST1 global -> Vernacexpr.SearchInside mods
    | IDENT "outside"; mods = LIST1 global -> Vernacexpr.SearchOutside mods
    | -> Vernacexpr.SearchOutside []
    ] ];
  ssr_search_item: [
    [ qref = ssrqref -> Vernacexpr.SearchRef qref
    | string = ne_string -> Vernacexpr.SearchString string
    ] ];
  ssr_search_list: [
    [ "["; list = LIST1 ssr_search_item; "]" -> list
    | item = ssr_search_item -> [item]
    ] ];
  command: [
    [ IDENT "Search"; head = ssrqref; modloc = ssr_modloc -> 
      Vernacexpr.VernacSearch (Vernacexpr.SearchHead head, modloc)
    | IDENT "SearchAbout"; list = ssr_search_list; modloc = ssr_modloc -> 
      Vernacexpr.VernacSearch (Vernacexpr.SearchAbout list, modloc)
    ] ];
END

(** Extend Search/SearchPattern to add hidden coercions to Sortclass *)

(* Name string prefilter *)

let pr_ssrlabs _ _ _ =
  pr_list spc (fun (b, s) ->  str (if b then "~" else "") ++ qs s)

ARGUMENT EXTEND ssrlabs TYPED AS (bool * string) list PRINTED BY pr_ssrlabs
  | [ "~" string(s) ssrlabs(labs) ] -> [ (true, s) :: labs ]
  | [ string(s) ssrlabs(labs) ] -> [ (false, s) :: labs ]
  | [ ] -> [ [] ]
END

let interp_labels labs =
  if labs = [] then fun _ -> true else fun gr ->
  let name = string_of_id (Nametab.id_of_global gr) in
  let filter_by (b, s) = b != string_string_contains ~where:name ~what:s in
  List.for_all filter_by labs

(* Main type conclusion pattern filter *)

let rec splay_search_pattern na = function 
  | Pattern.PApp (fp, args) -> splay_search_pattern (na + Array.length args) fp
 (* | Pattern.PLetIn (_, _, _, bp) -> splay_search_pattern na bp *)
    (* would need support in raw_pattern_search *)
  | Pattern.PRef hr -> hr, na
  | _ -> error "no head constant in head search pattern"

let coerce_search_pattern_to_sort env sigma hpat =
  let mkPApp fp n_imps args =
    let args' = Array.append (Array.make n_imps (Pattern.PMeta None)) args in
    Pattern.PApp (fp, args') in
  let hr, na = splay_search_pattern 0 hpat in
  let dc, ht = Reductionops.splay_prod env sigma (Global.type_of_global hr) in
  let np = List.length dc in
  if np < na then error "too many arguments in head search pattern" else
  let hpat' = if np = na then hpat else mkPApp hpat (np - na) [||] in
  if isSort ht then hpat' else
  let coe_path =
    try 
      let _, hcl = Classops.class_of (push_rels_assum dc env) sigma ht in
      Classops.lookup_path_to_sort_from hcl
    with _ -> error "head search pattern is not a type, even up to coercion" in
  let coerce hp coe_index =
    let coe = Classops.get_coercion_value coe_index in
    try
      let coe_ref = reference_of_constr coe in
      let n_imps = out_some (Classops.hide_coercion coe_ref) in
      mkPApp (Pattern.PRef coe_ref) n_imps [|hp|]
    with _ ->
    errorstrm (str "need explicit coercion " ++ pr_constr coe ++ spc ()
            ++ str "to interpret head search pattern as type") in
  List.fold_left coerce hpat' coe_path

let rec strip_null_app = function
  | RApp (_, c, []) -> strip_null_app c
  | c -> map_rawconstr strip_null_app c

let interp_searchpat isarity env sigma pat =
  let c = Constrintern.intern_gen isarity sigma env ~allow_soapp: true pat in
  snd (Pattern.pattern_of_rawconstr (strip_null_app c))

let interp_headpat env sigma = function
  | None ->
    Search.gen_filtered_search
  | Some rhpat ->
    let hpat = interp_searchpat true env sigma rhpat in
    let hpat' = coerce_search_pattern_to_sort env sigma hpat in
    fun accept display -> Search.raw_pattern_search accept display hpat'

(* Type subpattern postfilter *)

let pr_ssrspats prc _ _ spats = str "[" ++  pr_list spc prc spats ++ str "]"

ARGUMENT EXTEND ssrspats TYPED AS constr list PRINTED BY pr_ssrspats
  | [ "[" ne_constr_list(spats) "]" ] -> [ spats ]
END

let interp_searchsubpats env sigma rpats =
  let rec pwid = function
    | Pattern.PApp(p, a) -> Array.length a + pwid p
    | _ -> 0 in
  let match_sub rp = match interp_searchpat false env sigma rp with
  | Pattern.PRef gr -> Termops.occur_term (constr_of_reference gr)
  | p ->
    let na = pwid p in
    let rec check c =
      let c' =  match kind_of_term c with
      | App(f, a) when na > 0 && Array.length a > na ->
        mkApp (f, Array.sub a 0 na)
      | _ -> c in
      if Matching.is_matching p c' then raise Exit else iter_constr check c in
      fun typ -> try check typ; false with Exit -> true in
  let pats = List.map match_sub rpats in
  fun typ -> List.for_all (fun p -> p typ) pats

(* Module path postfilter *)

let pr_modloc (inmod, mods) =
  let keyword = if inmod then "inside " else "outside " in
  str keyword ++ pr_list pr_spc pr_reference mods

let pr_ssrmodloc _ _ _ = pr_modloc

let wit_ssrmodloc, globwit_ssrmodloc, rawwit_ssrmodloc =
  add_genarg "ssrmodloc" pr_modloc

let ssrmodloc = Gram.Entry.create "ssrmodloc"

ARGUMENT EXTEND ssrmodloc_ne TYPED AS ssrmodloc PRINTED BY pr_ssrmodloc
  | [ "inside" ne_global_list(mods) ] -> [ true, mods ]
  | [ "outside" ne_global_list(mods) ] -> [ false, mods ]
END

GEXTEND Gram
  GLOBAL: ssrmodloc ssrmodloc_ne;
  ssrmodloc: [[ -> false, [] | modloc = ssrmodloc_ne -> modloc ]];
END

let interp_modloc env sigma (inmod, rmods) =
  if rmods = [] then fun _ -> true else
  let interp_mod mr =
    let (loc,qid) = qualid_of_reference mr in
    try Nametab.full_name_module qid with Not_found ->
    user_err_loc (loc, "interp_modloc", str "Mo Module " ++ pr_qualid qid) in
  let mods = List.map interp_mod rmods in
  fun gr -> Search.filter_by_module_from_list (mods, not inmod) gr env sigma

(* The unified, extended vernacular "Search" command *)

let ssrdisplaysearch gr env t =
  let pr_res = pr_global gr ++ spc () ++ str " " ++ pr_lconstr_env env t in
  msg (hov 2 pr_res ++ fnl ())

let ssrsearch rlabs rhpat rspats rmodloc =
  let env = Global.env() and sigma = Evd.empty in
  let labs = interp_labels rlabs in
  let hpat = interp_headpat env sigma rhpat in
  let spats = interp_searchsubpats env sigma rspats in
  let modloc = interp_modloc env sigma rmodloc in
  hpat (fun gr _ typ -> labs gr && modloc gr && spats typ) ssrdisplaysearch

VERNAC COMMAND EXTEND SsrSearchPattern
| [ "Search" ssrlabs(labs) ssrmodloc_ne(modloc) ] ->
  [ ssrsearch labs None [] modloc ]
| [ "Search" ssrlabs(labs) ssrspats(spats) ssrmodloc(modloc) ] ->
  [ ssrsearch labs None spats modloc ]
| [ "Search" ssrlabs(labs) constr(hpat) ssrspats(spats) ssrmodloc(modloc) ] ->
  [ ssrsearch labs (Some hpat) spats modloc ]
| [ "Search" ssrlabs(labs) constr(hpat) ssrmodloc(modloc) ] ->
  [ ssrsearch labs (Some hpat) [] modloc ]
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
(* display style -- why aren't these strings?); also, the v8.1    *)
(* pretty-printer only allows extension hooks for printing        *)
(* integer or string literals.                                    *)
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

(** Alternative syntax for anonymous arguments (for ML-style constructors) *)

GEXTEND Gram
  GLOBAL: binder_let operconstr;
  binder_let: [
    [ ["of" | "&"]; c = operconstr LEVEL "99" ->
       LocalRawAssum ([loc, Anonymous], c)
    ]];
END

(** 4. Tacticals (+, -, *, done, by, do, =>, first, and last). *)

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

(* We have four kinds: simple tactics, [|]-bracketed lists, hints, and swaps *)
(* The latter two are used in forward-chaining tactics (have, suffice, wlog) *)
(* and subgoal reordering tacticals (; first & ; last), respectively.        *)

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
type ssrortacs = ssrtac option list

let pr_ortacs prt = 
  let rec pr_rec = function
  | [None]           -> spc() ++ str "|" ++ spc()
  | None :: tacs     -> spc() ++ str "|" ++ pr_rec tacs
  | Some tac :: tacs -> spc() ++ str "| " ++ prt tacltop tac ++  pr_rec tacs
  | []                -> mt() in
  function
  | [None]           -> spc()
  | None :: tacs     -> pr_rec tacs
  | Some tac :: tacs -> prt tacltop tac ++ pr_rec tacs
  | []                -> mt()
let pr_ssrortacs _ _ = pr_ortacs

ARGUMENT EXTEND ssrortacs TYPED AS tactic option list PRINTED BY pr_ssrortacs
| [ ssrtacexp(tac) "|" ssrortacs(tacs) ] -> [ Some tac :: tacs ]
| [ ssrtacexp(tac) "|" ] -> [ [Some tac; None] ]
| [ ssrtacexp(tac) ] -> [ [Some tac] ]
| [ "|" ssrortacs(tacs) ] -> [ None :: tacs ]
| [ "|" ] -> [ [None; None] ]
END

type ssrtacarg = bool * (ssrortacs * ssrltacctx)

let pr_tacarg prt = function
  | true, (tacs, _) -> hv 0 (str "[ " ++ pr_ortacs prt tacs ++ str " ]")
  | false, ([Some tac], _) -> prt tacltop tac
  | _, _ -> mt()

let pr_ssrtacarg _ _ = pr_tacarg

let mk_tacarg tac = false, ([Some tac], rawltacctx)
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
| [ "[" "]" ] -> [ nulltacarg ]
| [ "[" ssrortacs(tacs) "]" ] -> [ mk_ortacarg tacs ]
| [ ssrtacarg(arg) ] -> [ arg ]
END

let argtac (_, (atacs, ctx)) =
  let gettac = get_ssrevaltac ctx in
  let mktac = function Some atac -> gettac atac | _ -> tclIDTAC in
  match atacs with
  | [atac] -> mktac atac
  | _ -> tclFIRST (List.map mktac atacs)

let hinttac (is_or, (atacs, ctx)) =
  if atacs = [] then if is_or then donetac else tclIDTAC else
  let gettac = get_ssrevaltac ctx in
  let mktac = function Some atac -> tclBY (gettac atac) | _ -> donetac in
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

(** Bound assumption argument *)

(* The Ltac API does have a type for assumptions but it is level-dependent *)
(* and therefore impratical to use for complex arguments, so we substitute *)
(* our own to have a uniform representation. Also, we refuse to intern     *)
(* idents that match global/section constants, since this would lead to    *)
(* fragile Ltac scripts.                                                   *)

type ssrhyp = SsrHyp of loc * identifier

let hyp_id (SsrHyp (_, id)) = id
let pr_hyp (SsrHyp (_, id)) = pr_id id
let pr_ssrhyp _ _ _ = pr_hyp

let wit_ssrhyprep, globwit_ssrhyprep, rawwit_ssrhyprep =
  add_genarg "ssrhyprep" pr_hyp

let hyp_err loc msg id =
  user_err_loc (loc, "ssrhyp", str msg ++ pr_id id)

let intern_hyp ist (SsrHyp (loc, id) as hyp) =
  let _ = intern_genarg ist (in_gen rawwit_var (loc, id)) in
  if not_section_id id then hyp else
  hyp_err loc "Can't clear section hypothesis " id

let interp_hyp ist gl (SsrHyp (loc, id)) =
  let id' = interp_wit globwit_var wit_var ist gl (loc, id) in
  if not_section_id id' then SsrHyp (loc, id') else
  hyp_err loc "Can't clear section hypothesis " id'

ARGUMENT EXTEND ssrhyp TYPED AS ssrhyprep PRINTED BY pr_ssrhyp
                       INTERPRETED BY interp_hyp
                       GLOBALIZED BY intern_hyp
  | [ ident(id) ] -> [ SsrHyp (loc, id) ]
END

type ssrhyps = ssrhyp list

let pr_hyps = pr_list pr_spc pr_hyp
let pr_ssrhyps _ _ _ = pr_hyps
let hyps_ids = List.map hyp_id

let rec check_hyps_uniq ids = function
  | SsrHyp (loc, id) :: _ when List.mem id ids ->
    hyp_err loc "Duplicate assumption " id
  | SsrHyp (_, id) :: hyps -> check_hyps_uniq (id :: ids) hyps
  | [] -> ()

let interp_hyps ist gl ghyps =
  let hyps = List.map (interp_hyp ist gl) ghyps in
  check_hyps_uniq [] hyps; hyps

ARGUMENT EXTEND ssrhyps TYPED AS ssrhyp list PRINTED BY pr_ssrhyps
                        INTERPRETED BY interp_hyps
  | [ ssrhyp_list(hyps) ] -> [ check_hyps_uniq [] hyps; hyps ]
END

(** The "in" pseudo-tactical *)

(* We can't make "in" into a general tactical because this would create a  *)
(* crippling conflict with the ltac let .. in construct. Hence, we add     *)
(* explicitly an "in" suffix to all the extended tactics for which it is   *)
(* relevant (including move, case, elim) and to the extended do tactical   *)
(* below, which yields a general-purpose "in" of the form do [...] in ...  *)

(* This tactical needs to come before the intro tactics because the latter *)
(* must take precautions in order not to interfere with the discharged     *)
(* assumptions. This is especially difficult for discharged "let"s, which  *)
(* the default simpl and unfold tactics would erase blindly.               *)

type ssrclseq = InGoal | InHyps
 | InHypsGoal | InHypsSeqGoal | InSeqGoal | InHypsSeq | InAll | InAllHyps

let pr_clseq = function
  | InGoal | InHyps -> mt ()
  | InSeqGoal       -> str "|- *"
  | InHypsSeqGoal   -> str " |- *"
  | InHypsGoal      -> str " *"
  | InAll           -> str "*"
  | InHypsSeq       -> str " |-"
  | InAllHyps       -> str "* |-"

let wit_ssrclseq, globwit_ssrclseq, rawwit_ssrclseq =
  add_genarg "ssrclseq" pr_clseq

ARGUMENT EXTEND ssrclausehyps TYPED AS ssrhyps PRINTED BY pr_ssrhyps
  | [ ssrhyp(hyp) "," ssrclausehyps(hyps) ] -> [ hyp :: hyps ]
  | [ ssrhyp(hyp) ssrclausehyps(hyps) ] -> [ hyp :: hyps ]
  | [ ssrhyp(hyp) ] -> [ [hyp] ]
END

type ssrclauses = ssrhyps * ssrclseq

let pr_clauses (hyps, clseq) = 
  if clseq = InGoal then mt () else str "in " ++ pr_hyps hyps ++ pr_clseq clseq

let pr_ssrclauses _ _ _ = pr_clauses

let mkclause hyps clseq = check_hyps_uniq [] hyps; (hyps, clseq)

ARGUMENT EXTEND ssrclauses TYPED AS ssrclausehyps * ssrclseq
    PRINTED BY pr_ssrclauses
  | [ "in" ssrclausehyps(hyps) "|-" "*" ] -> [ mkclause hyps InHypsSeqGoal ]
  | [ "in" ssrclausehyps(hyps) "|-" ]     -> [ mkclause hyps InHypsSeq ]
  | [ "in" ssrclausehyps(hyps) "*" ]      -> [ mkclause hyps InHypsGoal ]
  | [ "in" ssrclausehyps(hyps) ]          -> [ mkclause hyps InHyps ]
  | [ "in" "|-" "*" ]                     -> [ mkclause []   InSeqGoal ]
  | [ "in" "*" ]                          -> [ mkclause []   InAll ]
  | [ "in" "*" "|-" ]                     -> [ mkclause []   InAllHyps ]
  | [ ]                                   -> [ mkclause []   InGoal ]
END

let ctx_tag = "discharged"
let ctx_id = tag_id ctx_tag
let is_ctx_id = is_tag_id ctx_tag

let nohide = mkRel 0
let hidden_goal_id = mk_sync_id "the hidden goal"

let pf_ctx_let_depth gl =
  let rec depth c = match kind_of_term c with
  | LetIn (Name id, _, _, c') when is_ctx_id id -> 1 + depth c'
  | LetIn (_, _, _, c') -> lifted_depth c'
  | Prod (_, _, c') -> lifted_depth c'
  | _ -> 0
  and lifted_depth c = match depth c with 0 -> 0 | n -> n + 1 in
  depth (pf_concl gl)

let pf_clauseids gl clhyps clseq =
  if clhyps <> [] then (check_hyps_uniq [] clhyps; hyps_ids clhyps) else
  if clseq <> InAll && clseq <> InAllHyps then [] else
  let dep_term var = mkNamedProd_or_LetIn (pf_get_hyp gl var) mkProp in
  let rec rem_var var =  function
  | [] -> raise Not_found
  | id :: ids when id <> var -> id :: rem_var var ids
  | _ :: ids -> rem_deps ids (dep_term var)
  and rem_deps ids c =
    try match kind_of_term c with
    | Var id -> rem_var id ids
    | _ -> fold_constr rem_deps ids c
    with Not_found -> ids in
  let ids = pf_ids_of_proof_hyps gl in
  List.rev (if clseq = InAll then ids else rem_deps ids (pf_concl gl))

let hidden_clseq = function InHyps | InHypsSeq | InAllHyps -> true | _ -> false

let hidetacs clseq idhide cl0 =
  if not (hidden_clseq clseq) then  [] else
  [posetac idhide cl0; convert_concl_no_check (mkVar idhide)]

let discharge_hyp (id', id) gl =
  let cl' = subst_var id (pf_concl gl) in
  match pf_get_hyp gl id with
  | _, None, t -> apply_type (mkProd (Name id', t, cl')) [mkVar id] gl
  | _, Some v, t -> convert_concl (mkLetIn (Name id', v, t, cl')) gl

let endclausestac id_map clseq gl_id cl0 gl =
  let not_hyp' id = not (List.mem_assoc id id_map) in
  let orig_id id = try List.assoc id id_map with _ -> id in
  let dc, c = Sign.decompose_prod_assum (pf_concl gl) in
  let hide_goal = hidden_clseq clseq in
  let c_hidden = hide_goal && c = mkVar gl_id in
  let rec fits forced = function
  | (id, _) :: ids, (Name id', _, _) :: dc' when id' = id ->
    fits true (ids, dc')
  | ids, dc' ->
    forced && ids = [] && (not hide_goal || dc' = [] && c_hidden) in
  let rec unmark c = match kind_of_term c with
  | Var id when hidden_clseq clseq && id = gl_id -> cl0
  | Prod (Name id, t, c') when List.mem_assoc id id_map ->
    mkProd (Name (orig_id id), unmark t, unmark c')
  | LetIn (Name id, v, t, c') when List.mem_assoc id id_map ->
    mkLetIn (Name (orig_id id), unmark v, unmark t, unmark c')
  | _ -> map_constr unmark c in
  let utac hyp = convert_hyp_no_check (map_named_declaration unmark hyp) in
  let utacs = List.map utac (pf_hyps gl) in
  let ugtac gl' = convert_concl_no_check (unmark (pf_concl gl')) gl' in
  let ctacs = if hide_goal then [clear [gl_id]] else [] in
  let mktac itacs = tclTHENLIST (itacs @ utacs @ ugtac :: ctacs) in
  let itac (_, id) = introduction id in
  if fits false (id_map, List.rev dc) then mktac (List.map itac id_map) gl else
  let all_ids = ids_of_rel_context dc @ pf_ids_of_hyps gl in
  if List.for_all not_hyp' all_ids && not c_hidden then mktac [] gl else
  Util.error "tampering with discharged assumptions of \"in\" tactical"
    
let tclCLAUSES tac (clhyps, clseq) gl =
  if clseq = InGoal || clseq = InSeqGoal then tac gl else
  let cl_ids = pf_clauseids gl clhyps clseq in
  let id_map = List.map (fun id -> ctx_id id, id) cl_ids in
  let gl_id = fresh_id [] !hidden_goal_id gl in
  let cl0 = pf_concl gl in
  let dtacs = List.map discharge_hyp (List.rev id_map) @ [clear cl_ids] in
  let endtac = endclausestac id_map clseq gl_id cl0 in
  tclTHENLIST (hidetacs clseq gl_id cl0 @ dtacs @ [tac; endtac]) gl

(** Clear switch *)

(* This code isn't actually used by the intro patterns below, because the *)
(* Ltac interpretation of the clear switch in an intro pattern is         *)
(* different than in terms: the hyps aren't necessarily in the context at *)
(* the time the argument is interpreted, i.e., they could be introduced   *)
(* earlier in the pattern.                                                *)

type ssrclear = ssrhyps

let pr_clear_ne clr = str "{" ++ pr_hyps clr ++ str "}"
let pr_clear sep clr = if clr = [] then mt () else sep () ++ pr_clear_ne clr

let pr_ssrclear _ _ _ = pr_clear mt

ARGUMENT EXTEND ssrclear_ne TYPED AS ssrhyps PRINTED BY pr_ssrclear
| [ "{" ne_ssrhyp_list(clr) "}" ] -> [ check_hyps_uniq [] clr; clr ]
END

ARGUMENT EXTEND ssrclear TYPED AS ssrclear_ne PRINTED BY pr_ssrclear
| [ ssrclear_ne(clr) ] -> [ clr ]
| [ ] -> [ [] ]
END

let cleartac clr = check_hyps_uniq [] clr; clear (hyps_ids clr)

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

(* We must avoid zeta-converting any "let"s created by the "in" tactical. *)

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

let dir_org = function L2R -> 1 | R2L -> 2

(** Extended intro patterns *)

type ssripat =
  | IpatSimpl of ssrclear * ssrsimpl
  | IpatId of identifier
  | IpatWild
  | IpatCase of ssripats list
  | IpatRw of ssrdir
  | IpatAll
  | IpatAnon
and ssripats = ssripat list

let rec ipat_of_intro_pattern = function
  | IntroIdentifier id -> IpatId id
  | IntroWildcard -> IpatWild
  | IntroOrAndPattern iorpat ->
    IpatCase (List.map (List.map ipat_of_intro_pattern) iorpat)
  | IntroAnonymous -> IpatAnon

let rec pr_ipat = function
  | IpatId id -> pr_id id
  | IpatSimpl (clr, sim) -> pr_clear mt clr ++ pr_simpl sim
  | IpatCase iorpat -> hov 1 (str "[" ++ pr_iorpat iorpat ++ str "]")
  | IpatRw dir -> pr_dir dir
  | IpatAll -> str "*"
  | IpatWild -> str "_"
  | IpatAnon -> str "?"
and pr_ipats ipats = pr_list spc pr_ipat ipats
and pr_iorpat iorpat = pr_list pr_bar pr_ipats iorpat

let wit_ssripatrep, globwit_ssripatrep, rawwit_ssripatrep =
  add_genarg "ssripatrep" pr_ipat

let pr_ssripat _ _ _ = pr_ipat
let pr_ssripats _ _ _ = pr_ipats
let pr_ssriorpat _ _ _ = pr_iorpat

let intern_ipat ist ipat =
  let rec check_pat = function
  | IpatSimpl (clr, _) -> ignore (List.map (intern_hyp ist) clr)
  | IpatCase iorpat -> List.iter (List.iter check_pat) iorpat
  | _ -> () in
  check_pat ipat; ipat

let interp_introid ist gl id =
  try IntroIdentifier (hyp_id (interp_hyp ist gl (SsrHyp (dummy_loc, id))))
  with _ -> interp_intro_pattern ist gl (IntroIdentifier id)

let rec add_intro_pattern_hyps loc ipat hyps = match ipat with
  | IntroIdentifier id ->
    if not_section_id id then SsrHyp (loc, id) :: hyps else
    hyp_err loc "Can't delete section hypothesis " id
  | IntroWildcard -> hyps
  | IntroOrAndPattern iorpat ->
    List.fold_right (List.fold_right (add_intro_pattern_hyps loc)) iorpat hyps
  | IntroAnonymous -> []

let rec interp_ipat ist gl =
  let ltacvar id = List.mem_assoc id ist.lfun in
  let rec interp = function
  | IpatId id when ltacvar id ->
    ipat_of_intro_pattern (interp_introid ist gl id)
  | IpatSimpl (clr, sim) ->
    let add_hyps (SsrHyp (loc, id) as hyp) hyps =
      if not (ltacvar id) then hyp :: hyps else
      add_intro_pattern_hyps loc (interp_introid ist gl id) hyps in
    let clr' = List.fold_right add_hyps clr [] in
    check_hyps_uniq [] clr'; IpatSimpl (clr', sim)
  | IpatCase iorpat -> IpatCase (List.map (List.map interp) iorpat)
  | ipat -> ipat in
  interp

ARGUMENT EXTEND ssripat TYPED AS ssripatrep PRINTED BY pr_ssripat
  INTERPRETED BY interp_ipat
  GLOBALIZED BY intern_ipat
  | [ "_" ] -> [ IpatWild ]
  | [ "*" ] -> [ IpatAll ]
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
  | [ ssrspat(spat) ssripat(pat) ssripats(pats) ] -> [ spat :: pat :: pats ]
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
  | [ "?" ] -> [ IpatAnon ]
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

let injecteq_id = mk_sync_id "injection equation"

let pf_nb_prod gl = nb_prod (pf_concl gl)

let rev_id = mk_sync_id "rev concl"

let revtoptac n0 gl =
  let n = pf_nb_prod gl - n0 in
  let dc, cl = decompose_prod_n n (pf_concl gl) in
  let dc' = dc @ [Name !rev_id, compose_prod (List.rev dc) cl] in
  let f = compose_lam dc' (mkEtaApp (mkRel (n + 1)) (-n) 1) in
  refine (mkApp (f, [|Evarutil.mk_new_meta ()|])) gl

let injectidl2rtac id gl =
  tclTHEN (Equality.inj [] id) (revtoptac (pf_nb_prod gl)) gl

let injectl2rtac c = match kind_of_term c with
| Var id -> injectidl2rtac id
| _ ->
  let id = !injecteq_id in
  tclTHENLIST [havetac id c; injectidl2rtac id; clear [id]]

let ssrscasetac c gl =
  let mind, t = pf_reduce_to_quantified_ind gl (pf_type_of gl c) in
  if mkInd mind <> build_coq_eq () then simplest_case c gl else
  let dc, eqt = decompose_prod t in
  if dc = [] then injectl2rtac c gl else
  if not (closed0 eqt) then error "can't decompose a quantified equality" else
  let cl = pf_concl gl in let n = List.length dc in
  let c_eq = mkEtaApp c n 2 in
  let cl1 = mkLambda (Anonymous, mkArrow eqt cl, mkApp (mkRel 1, [|c_eq|])) in
  let injtac =tclTHEN (introid !injecteq_id) (injectidl2rtac !injecteq_id) in 
  tclTHENLAST (apply (compose_lam dc cl1)) injtac gl  

(* We must not anonymize context names discharged by the "in" tactical. *)

let anon_id = function
  | Name id -> if is_ctx_id id then id else tag_id "anon" id
  | _ -> id_of_tag "anon hyp"

let anontac (x, _, _) = intro_using (anon_id x)

let intro_all gl =
  let dc, _ = Sign.decompose_prod_assum (pf_concl gl) in
  tclTHENLIST (List.map anontac (List.rev dc)) gl

let rec intro_anon gl =
  try anontac (List.hd (fst (Sign.decompose_prod_n_assum 1 (pf_concl gl)))) gl
  with _ -> try tclTHEN red_in_concl intro_anon gl
  with _ -> error "No product even after reduction"

let top_id = mk_sync_id "top assumption"

let with_top tac =
  tclTHENLIST [introid !top_id; tac (mkVar !top_id); clear [!top_id]]

let rec mapLR f = function [] -> [] | x :: s -> let y = f x in y :: mapLR f s

let wild_ids = ref []

let new_wild_id () =
  let i = 1 + List.length !wild_ids in
  let sufx = match i with 1 -> "st" | 2 -> "nd" | 3 -> "rd" | _ -> "th" in
  let id = id_of_tag (sprintf "the %d%s wildcard" i sufx) in
  wild_ids := id :: !wild_ids;
  id

let clear_wilds wilds gl =
  clear (List.filter (fun id -> List.mem id wilds) (pf_ids_of_hyps gl)) gl

let clear_with_wilds wilds clr0 gl =
  let extend_clr clr (id, _, _ as nd) =
    if List.mem id clr || not (List.mem id wilds) then clr else
    let vars = global_vars_set_of_decl (pf_env gl) nd in
    let occurs id' = Idset.mem id' vars in
    if List.exists occurs clr then id :: clr else clr in
  clear (Sign.fold_named_context_reverse extend_clr ~init:clr0 (pf_hyps gl)) gl

let tclTHENS_nonstrict tac tacl taclname gl =
  let tacres = tac gl in
  let n_gls = List.length (sig_it (fst tacres)) in
  let n_tac = List.length tacl in
  if n_gls = n_tac then tclTHENS (fun _ -> tacres) tacl gl else
  if n_gls = 0 then tacres else
  let pr_only n1 n2 = if n1 < n2 then str "only " else mt () in
  let pr_nb n1 n2 name =
    pr_only n1 n2 ++ int n1 ++ str (" " ^ plural n1 name) in
  errorstrm (pr_nb n_tac n_gls taclname ++ spc ()
             ++ str "for " ++ pr_nb n_gls n_tac "subgoal")


(* Forward reference to extended rewrite *)
let ipat_rewritetac = ref rewritetac

let rec ipattac = function
  | IpatWild -> introid (new_wild_id ())
  | IpatCase iorpat -> tclIORPAT (with_top ssrscasetac) iorpat
  | IpatRw dir -> with_top (!ipat_rewritetac dir)
  | IpatId id -> introid id
  | IpatSimpl (clr, sim) ->
    tclTHEN (simpltac sim) (clear_with_wilds !wild_ids (hyps_ids clr))
  | IpatAll -> intro_all
  | IpatAnon -> intro_anon
and tclIORPAT tac = function
  | [[]] -> tac
  | iorpat -> tclTHENS_nonstrict tac (mapLR ipatstac iorpat) "intro pattern"
and ipatstac ipats = tclTHENLIST (mapLR ipattac ipats)

(* For "move" *)
let introstac ipats =
  wild_ids := [];
  let tac = ipatstac ipats in
  tclTHEN tac (clear_wilds !wild_ids)

let rec eqmoveitac eqpat = function
  | IpatSimpl (clr, sim) :: ipats ->
    tclTHENLIST [simpltac sim; cleartac clr; eqmoveitac eqpat ipats]
  | (IpatAll :: _ | []) as ipats -> introstac (IpatAnon :: eqpat :: ipats)
  | ipat :: ipats -> introstac (ipat :: eqpat :: ipats)

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
  function _, ([Some tac], _) -> tac_sep tac | _ -> spc

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

ARGUMENT EXTEND ssrindex TYPED AS int_or_var PRINTED BY pr_ssrindex
  INTERPRETED BY interp_index
| [ int_or_var(i) ] -> [ mk_index loc i ]
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

type ssrdoarg = (ssrindex * ssrmmod) * (ssrtacarg * ssrclauses)

let pr_ssrdoarg prc _ prt ((n, m), (tac, clauses)) =
  pr_index n ++ pr_mmod m ++ pr_tacarg prt tac ++ pr_clauses clauses

ARGUMENT EXTEND ssrdoarg
  TYPED AS (ssrindex * ssrmmod) * (ssrtacarg * ssrclauses)
  PRINTED BY pr_ssrdoarg
| [ ssrindex(n) ssrmmod(m) ssrtacarg(t) ssrclauses(clauses) ] ->
  [ (n, m), (t, clauses) ]
| [ ssrmmod(m) ssrtacarg(t) ssrclauses(clauses) ] ->
  [ (noindex, m), (t, clauses) ]
END

let ssrdotac ((n, m), (tac, clauses)) =
  tclCLAUSES (tclMULT (get_index n, m) (argtac tac)) clauses

TACTIC EXTEND ssrtcldo
| [ "(**)" "do" ssrdoarg(arg) ] -> [ ssrdotac arg ]
END
set_pr_ssrtac "tcldo" 3 [ArgSep "do "; ArgSsr "doarg"]

let ssrdotac_expr loc n m tac clauses =
  ssrtac_expr loc "tcldo" [in_gen rawwit_ssrdoarg ((n, m), (tac, clauses))]

GEXTEND Gram
  GLOBAL: tactic_expr int_or_var ssrmmod ssrtacarg3 ssrortacarg ssrclauses;
  ssr_dotacarg: [[ tac = ssrtacarg3 -> tac | tac = ssrortacarg -> tac ]];
  tactic_expr: LEVEL "3" [ RIGHTA
    [ IDENT "do"; m = ssrmmod; tac = ssr_dotacarg; clauses = ssrclauses ->
      ssrdotac_expr loc noindex m tac clauses
    | IDENT "do"; tac = ssrortacarg; clauses = ssrclauses ->
      ssrdotac_expr loc noindex Once tac clauses
    | IDENT "do"; n = int_or_var; m = ssrmmod;
                    tac = ssr_dotacarg; clauses = ssrclauses ->
      ssrdotac_expr loc (mk_index loc n) m tac clauses
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

let pr_seqtacarg prt = function
  | (true, _), Some (TacAtom (_, TacLeft _)) -> str "first"
  | (true, _), Some (TacAtom (_, TacRight _)) -> str "last"
  | tac, Some dtac ->
    hv 0 (pr_tacarg prt tac ++ spc() ++ str "|| " ++ prt tacltop dtac)
  | tac, _ -> pr_tacarg prt tac

let pr_ssrseqarg _ _ prt = function
  | ArgArg 0, tac -> pr_seqtacarg prt tac
  | i, tac -> pr_index i ++ str " " ++ pr_seqtacarg prt tac

(* We must parse the index separately to resolve the conflict with *)
(* an unindexed tactic.                                            *)
ARGUMENT EXTEND ssrseqarg TYPED AS ssrindex * (ssrtacarg * tactic option)
                          PRINTED BY pr_ssrseqarg
| [ ssrtacarg3(i_tac) ] -> [ noindex, (i_tac, None) ]
END

let sq_brace_tacnames =
   ["first"; "solve"; "do"; "rewrite"; "have"; "suffices"; "wlog"]
   (* "by" is a keyword *)
let input_ssrseqvar strm =
  match Stream.npeek 1 strm with
  | ["IDENT", id] when not (List.mem id sq_brace_tacnames) ->
     accept_before_syms ["["] strm; id_of_string id
  | _ -> raise Stream.Failure

let ssrseqvar = Gram.Entry.of_parser "ssrseqvar" input_ssrseqvar

let swaptacarg dtac = mk_tacarg dtac, Some dtac

let check_seqtacarg dir (_, ((is_or, _), atac3) as arg) = match atac3 with
  | Some (TacAtom (loc, TacLeft _)) when dir = L2R && not is_or ->
    loc_error loc "expected \"last\""
  | Some (TacAtom (loc, TacRight _)) when dir = R2L && not is_or ->
    loc_error loc "expected \"first\""
  | _ -> arg

let ssrorelse = Gram.Entry.create "ssrorelse"
GEXTEND Gram
  GLOBAL: ssrseqvar Prim.natural tactic_expr ssrorelse ssrseqarg;
  ssrseqidx: [
    [ id = ssrseqvar -> ArgVar (loc, id)
    | n = Prim.natural -> ArgArg (check_index loc n)
    ] ];
  ssrswaparg: [
    [ IDENT "first" -> swaptacarg (TacAtom (loc, TacLeft NoBindings))
    | IDENT "last" -> swaptacarg (TacAtom (loc, TacRight NoBindings))
    ] ];
  ssrorelse: [[ "||"; tac = tactic_expr LEVEL "2" -> tac ]];
  ssrseqarg: [
    [ arg = ssrswaparg -> noindex, arg
    | i = ssrseqidx; tac = ssrortacarg; def = OPT ssrorelse -> i, (tac, def)
    | i = ssrseqidx; arg = ssrswaparg -> i, arg
    ] ];
END

let tclPERMsalt = ref 1

let tclPERM perm tac gls =
  let mkpft n g r =
    {Proof_type.open_subgoals = n; Proof_type.goal = g; Proof_type.ref = r} in
  let mkleaf g = mkpft 0 g None in
  let mkprpft n g pr a = mkpft n g (Some (Proof_type.Prim pr, a)) in
  let mkrpft n g c = mkprpft n g (Proof_type.Refine c) in
  let mkipft n g =
    let mki pft (id, _, _ as d) =
      let g' = {g with evar_concl = mkNamedProd_or_LetIn d g.evar_concl} in
      mkprpft n g' (Proof_type.Intro id) [pft] in
    List.fold_left mki in
  let gl = Refiner.sig_it gls in
  let mklhyps =
    let rhyps = List.rev (pf_hyps gls) in
    let rec chop = function
      | d1 :: h1, d2 :: h2 when d1 = d2 -> chop (h1, h2)
      | _, h2 -> h2 in
    fun subgl ->
    let full_lhyps = Environ.named_context_of_val subgl.evar_hyps in
    List.rev (chop (rhyps, List.rev full_lhyps)) in
  let mkhyp subgl =
    let salt = !tclPERMsalt in tclPERMsalt := salt mod 1000000000 + 1;
    id_of_tag ("perm hyp" ^ string_of_int salt), subgl, mklhyps subgl in
  let mkpfvar (hyp, subgl, lhyps) =
    let mkarg args (lhyp, body, _) =
      if body = None then mkVar lhyp :: args else args in
    mkrpft 0 subgl (applist (mkVar hyp, List.fold_left mkarg [] lhyps)) [] in
  let mkpfleaf (_, subgl, lhyps) = mkipft 1 gl (mkleaf subgl) lhyps in
  let mkmeta _ = Evarutil.mk_new_meta () in
  let mkhypdecl (hyp, subgl, lhyps) =
    hyp, None, it_mkNamedProd_or_LetIn subgl.evar_concl lhyps in
  let subgls, v as res0 = tac gls in
  let sigma, subgll = Refiner.unpackage subgls in
  let n = List.length subgll in if n = 0 then res0 else
  let hyps = List.map mkhyp subgll in
  let hyp_decls = List.map mkhypdecl (List.rev (perm hyps)) in
  let c = applist (mkmeta (), List.map mkmeta subgll) in
  let pft0 = mkipft 0 gl (v (List.map mkpfvar hyps)) hyp_decls in
  let pft1 = mkrpft n gl c (pft0 :: List.map mkpfleaf (perm hyps)) in
  let subgll', v' = Refiner.frontier pft1 in
  Refiner.repackage sigma subgll', v'

let tclREV = tclPERM List.rev

let rot_hyps dir i hyps =
  let n = List.length hyps in
  if i = 0 then List.rev hyps else
  if i > n then error "Not enough subgoals" else
  let rec rot i l_hyps = function
    | hyp :: hyps' when i > 0 -> rot (i - 1) (hyp :: l_hyps) hyps'
    | hyps' -> hyps' @ (List.rev l_hyps) in
  rot (match dir with L2R -> i | R2L -> n - i) [] hyps

let tclSEQAT atac1 dir (ivar, ((is_or, (atacs2, ctx)), atac3)) =
  let i = get_index ivar in
  let evtac = get_ssrevaltac ctx in
  let tac1 = evtac atac1 in
  if not is_or && atac3 <> None then tclPERM (rot_hyps dir i) tac1  else
  let evotac = function Some atac -> evtac atac | _ -> tclIDTAC in
  let tac3 = evotac atac3 in
  let rec mk_pad n = if n > 0 then tac3 :: mk_pad (n - 1) else [] in
  match dir, mk_pad (i - 1), List.map evotac atacs2 with
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
  let arg3 = in_gen rawwit_ssrseqarg (check_seqtacarg dir arg) in
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
  tactic_expr: LEVEL "4" [ LEFTA
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
(*   The term representation tracks whether the concrete initial term  *)
(* started with an opening paren, which might avoid a conflict between *)
(* the ssrreflect term syntax and Gallina notation.                    *)

(* kinds of terms *)

type ssrtermkind =
  | SsrTerm of char * int (* print flag * number of type-checking holes *)
  | ErrorTerm of exn      (* delayed globalizing or type-checking error *)

let pr_termkind = function
  | SsrTerm (_, 0) -> mt ()
  | SsrTerm _      -> str "<<pattern>>"
  | ErrorTerm _    -> str "<<type error>>"

let wit_ssrtermkind, globwit_ssrtermkind, rawwit_ssrtermkind =
  add_genarg "ssrtermkind" pr_termkind

let input_ssrtermkind strm = match Stream.npeek 1 strm with
  | ["", "("] -> SsrTerm ('(', 0)
  | _ -> raise Stream.Failure

let ssrtermkind = Gram.Entry.of_parser "ssrtermkind" input_ssrtermkind

let notermkind = SsrTerm (' ', 0)

(* terms *)

type ssrterm = ssrtermkind * constr

(* We also guard characters that might interfere with the ssreflect   *)
(* tactic syntax.                                                     *)
let guard_term ch1 s i = match s.[i] with
  | '(' -> false
  | '{' | '/' | '=' -> true
  | _ -> ch1 <> ' '

let pat_of_ssrterm n c =
  let rec mkvars i =
    let v = mkVar (id_of_string (sprintf "_(*%d*)" i)) in
    if i = 0 then [v] else v :: mkvars (i - 1) in
  if n <= 0 then c else substl (mkvars n) (snd (decompose_lam_n n c))

let pr_pattern n c = pr_constr (pat_of_ssrterm n c)

let rec pr_holes n = if n <= 0 then mt () else str " _" ++ pr_holes (n - 1)

let pr_term prc = function
  | SsrTerm (ch1, 0), c -> pr_guarded (guard_term ch1) prc c
  | SsrTerm (ch1, n), c -> str "(" ++ prc c ++ pr_holes n ++ str ")"
  | ErrorTerm _, _      -> str "<<type error>>"

let pr_ssrterm prc _ _ = pr_term prc

let interp_term ist gl = function
  | ErrorTerm err, _  -> ErrorTerm err, mkProp
  | SsrTerm (ch1, _), gt ->
    try
      let n, c = pf_abs_evars gl (interp_open_constr ist gl gt) in
      SsrTerm (ch1, n), c
    with err -> ErrorTerm err, mkProp

let force_term = function
  | SsrTerm (_, 0), c         -> c
  | SsrTerm _, _         -> error "unresolved holes"
  | ErrorTerm err, _        -> raise err

ARGUMENT EXTEND ssrterm TYPED AS ssrtermkind * constr PRINTED BY pr_ssrterm
                        INTERPRETED BY interp_term
| [ ssrtermkind(k) constr(c) ] -> [ k, c ]
| [ constr(c) ] -> [ notermkind, c ]
END

(* post-interpretation of terms *)

(*
let abs_ssrterm = function ErrorTerm e, _ -> raise e | _, c -> c

let prod_ssrterm = function
  | ErrorTerm e, _ -> raise e
  | SsrTerm (_, n), c ->
    match decompose_lam_n n c with
    | (_, t) :: dc, cc when isCast cc -> compose_prod dc t
    | _ -> anomaly "ssr cast hole deleted by typecheck"
*)

let pf_abs_ssrterm gl = function
  | ErrorTerm e, _ -> raise e
  | SsrTerm (_, n), c -> pf_abs_cterm gl n c

let pf_prod_ssrterm gl = function
  | ErrorTerm e, _ -> raise e
  | SsrTerm (_, n), c ->
    match decompose_lam_n n (pf_abs_cterm gl n c) with
    | (_, t) :: dc, cc when isCast cc -> compose_prod dc t
    | _ -> anomaly "ssr cast hole deleted by typecheck"

(*
let pf_understand_new_holes gl ise na pat =
  let env = pf_env gl in
  if na = 0 then begin
    let tpat = Retyping.get_type env (evars_of ise) pat in
    if pf_no_evars gl tpat then
      begin fun c -> e_conv env ise pat c && closed0 c end
    else
      begin fun c ->
        e_conv env ise tpat (pf_type_of gl c)
      && e_conv env ise pat c
      end
  end else begin
    let f, a =
      let f, a = destApp pat in
      if fixed f then
        fun a' ->
          for i = 0 to n - 1 do
            if not (e_conv env ise a.(i) a'.(i)) then
              error "unification mismatch"
          done
      else
        let t = Retyping.get_type env (evars_of ise) f in
        if pf_no_evars gl tpat then
      begin fun f' a' ->
          e_conv env ise f f' &&
          (for i = 0 to n - 1 do
            if not (e_conv env ise a.(i) a'.(i)) then
              error "unification mismatch"
          done; true) end
    else
      begin fun f' a' ->
          e_conv env ise t (try pf_type_of gl f' with _ -> t) &&
          e_conv env ise f f' &&
          (for i = 0 to n - 1 do
            if not (e_conv env ise a.(i) a'.(i)) then
              error "unification mismatch"
          done; true) end
fun c ->
        e_conv env ise tpat (pf_type_of gl c)
      && e_conv env ise pat c
      end   
  let cp = pf_unabs_evars gl ise n pat in
  let cp' = if na = 0 then cp else Reductionops.whd_betaiota cp in
  let cvx c1 c2 = ise := Evarconv.the_conv_x env c1 c2 !ise in
  let cvc = if na = 0 then cvx cp else
    fun c -> let f1, a1 = destApp cp' and f2, a2 = destApp c in
    let k = Array.length a2 - Array.length a1 in
    let f2' = if k = 0 then f2 else mkApp(f2, Array.sub a2 0 k) in
    cvx f1 f2'; for i = 0 to na - 1 do cvx a1.(i) a2.(i + k) done in
  let check_var ev evi () =
    let evb = evar_body evi in
    if try evar_body (Evd.find sigma ev) != evb with _ -> evb = Evar_empty
       then error "matching changed evar" in
  fun c ->
    let sigma' = cvc c; evars_of !ise in
    Evd.fold check_var sigma' ();
    Array.of_list (List.rev_map (Evarutil.nf_evar sigma') vars)
*)

(* pf_understand_holes gl n na pat c returns an array of n values such   *)
(* that pat v1 .. vn is convertible to c; if na > 0, pat should be beta- *)
(* iota convertible to fun x1 .. xn => a0 a1 .. a_na, c should be of the *)
(* form b0 ... b_na and aj{vi/xi} and bj should be convertible. The      *)
(* procedure encodes the matching problem as a typechecking problem for  *)
(* Coq's type inference engine. The problem setup is staged so that most *)
(* of it is only done once during repeated matching in pf_fill_occ_pat.  *)

let pattern_id = mk_sync_id "pattern value"
let phantom_id = mk_sync_id "pattern phantom"

let pf_understand_holes gl n na pat =
  let env = pf_env gl and sigma = project gl in
  let dc, tp = decompose_prod_n n (Retyping.get_type_of env sigma pat) in
  let cp = whdEtaApp pat n in
  let locked = mkSsrConst "locked" in
  let cp' = if na = 0 then cp else
    let f, args = Reductionops.whd_betaiota_stack cp in
    if List.length args <> na then anomaly "inconsistent pattern args" else
    let tf = Retyping.get_type_of (push_rels_assum dc env) sigma f in
    applist (locked, tf :: f :: args) in
  let coq_eq = build_coq_eq () in
  let mkeq args = mkApp (coq_eq, args) in
  let phdc = (Name !pattern_id, tp) :: dc in
  let pht = compose_prod phdc (mkeq [|lift 1 tp; lift 1 cp'; mkRel 1|]) in
  let phenv = Environ.push_named (!phantom_id, None, pht) env in
  let phrc = mkRApp (mkRVar !phantom_id) (mkRHoles (n + 1)) in
  fun c ->
    let c' = if na = 0 then c else
      let f, args = destApp c in
      let i = Array.length args - na in
      let f', args' = if i <= 0 then f, args else
        mkApp (f, Array.sub args 0 i), Array.sub args i na in
      let tf' = Retyping.get_type_of env sigma f' in
      mkApp (locked, Array.append [|tf'; f'|] args') in
    let expected_type = mkeq [|Retyping.get_type_of env sigma c'; c'; c'|] in
    Array.sub (snd (destApp (understand sigma phenv ~expected_type phrc))) 0 n

let whd_app f args = Reductionops.whd_betaiota (mkApp (f, args))

let pf_match_pattern gl n pat c0 =
  if n = 0 then pat else
  let pat = pf_abs_cterm gl n pat in
  whd_app pat (pf_understand_holes gl n 0 pat c0)
  
(* pf_fill_pat gl occ n pat, with pat of the form fun x1 .. xn => e,       *)
(* matches pat _ ... _ (n wildcards) with a subterm of cl = pf_concl gl,   *)
(* and returns the pair cl where the matched term is replaced with Rel 1   *)
(* (suitably lifted) at the occurrences specified by occ, together with an *)
(* array [|a1;...;an|] of terms such that the matched term is convertible  *)
(*   pat a1 ... an == e[a1/x1;...;an/xn].                                  *)
(* If n = 0 the comparison used to determine subterms match pat is         *)
(* KEYED CONVERSION. This looks for convertible terms that either have the *)
(* same head constant as pat if pat is an application (after beta-iota),   *)
(* or start with the same constr constructor (esp. for LetIn). An          *)
(* application whose head is a LetIn is compared with any application with *)
(* the same number of arguments (casts are ignored, but not removed).      *)
(* If n > 0, the matching uses the type inference engine (as per refine)   *)
(* to fill in the wildcards, but otherwise behaves as in the n = 0 case    *)
(* (a head wildcard is treated as a LetIn, but an error is reported if it  *)
(* has no arguments). The matched term must not have any bound variables,  *)
(* including let-bound, and the function reports whether the only matches  *)
(* were ruled out by the free-variable check.                              *)

type pat_key =
  | KpatFixed
  | KpatRigid
  | KpatFlex   (* must be letin if #args = 0 *)

let pat_key c =  match kind_of_term c with
  | Rel _ | LetIn _ | App _ -> KpatFlex
  | Var _ | Const _ | Ind _ | Construct _ -> KpatFixed
  | Meta _ -> anomaly "meta in ssreflect pattern"
  | Cast _  -> KpatFlex (* does not happen in splay_pat *)
  | Evar _ | Prod _ | Sort _ | Lambda _ | Case _ | Fix _ | CoFix _ -> KpatRigid

let splay_pat n c0 =
  let dc, c = decompose_lam_n n c0 in
  let f, argl = Reductionops.whd_betaiota_stack c in
  let args = Array.of_list argl in
  match kind_of_term f with
  | Rel i ->
    let x, _ = List.nth dc (i - 1) in
    let dep_args, args' = array_chop (nb_evar_deps x) args in
    if args' = [||] then 
      errorstrm (str "need " ++ int (nb_evar_deps x) ++ str " args in " ++
      pr_constr c0) (* error "need more context to fill wildcard" *) else
    mkApp(f, dep_args), args'
  | _ -> f, args

let destApp_n na c =
  let f, args = destApp c in
  let i = Array.length args - na in
  if i = 0 then f, args else
  mkApp(f, Array.sub args 0 i), Array.sub args i na

let pf_eq_pat gl k na c =
  let eqx = pf_conv_x gl in
  if na = 0 then eqx c else
  let f, args = destApp_n na c in
  match k with
  | KpatFixed ->
    fun c' -> array_for_all2 eqx args (snd (destApp c'))
  | KpatRigid ->
    fun c' -> eqx c c'
  | KpatFlex ->
    fun c' ->
    let f', args' = destApp_n na c' in
    eqx f f' && array_for_all2 eqx args args'
  
let pop_match_args n = function
| a :: _ when Array.length a = n -> a
| st ->
  let args = Array.make n mkProp in
  let rec loop i = function
  | a :: st' ->
    let m = Array.length a in
    if m >= n - i then Array.blit a 0 args i (n - i) else
    begin Array.blit a 0 args i m; loop (i + m) st' end
  | _ -> () in
  loop 0 st; args

let pf_fill_occ_pat gl occ n pat =
  let pat_f, pat_args = splay_pat n pat in
  let k = pat_key pat_f and nak = Array.length pat_args in
  let unify = ref (fun _ -> false) in
  let match_args = ref [||] in
  let _ =
    if n = 0 then unify := pf_eq_pat gl k nak (mkApp (pat_f, pat_args)) else
    let unif_args = pf_understand_holes gl n nak pat in
    let unify_holes c =
      match_args := unif_args c;
      closed0 c && (unify := pf_eq_pat gl k nak c; true) in
    unify := (fun c -> try unify_holes c with _ -> false);      
    try (* WARNING: w_unify_to_subterm does NOT assign metas that occur only *)
        (* in the types of those metas which actually occur in the pattern,  *)
        (* so we CANNOT compute match_args by mapping nf_metas on uargs.     *)
      let evd = create_evar_defs (project gl) in
      let tpat = pf_type_of gl pat in
      let env = pf_env gl in
      let uenv, uargs, _ = Clenv.clenv_environments evd (Some n) tpat in
      let upat = whd_app pat (Array.of_list uargs) in
      let w_unif2sub = Unification.w_unify_to_subterm env ~mod_delta:false in
      ignore (!unify (snd (w_unif2sub (upat, pf_concl gl) uenv)))
    with  _ -> () in
  let unify_app f n st = !unify (mkApp (f, pop_match_args n st)) in
  let nocc = ref 0 and nsubst = ref 0 in
  let occ_default, occ_list = match List.map get_index occ with
  | -1 :: ol -> ol <> [], ol
  | 0 :: ol | ol -> ol = [], ol in
  let max_occ = List.fold_right max occ_list 0 in
  let occ_set = Array.make max_occ occ_default in
  let _ = List.iter (fun i -> occ_set.(i - 1) <- not occ_default) occ_list in  
  let subst_occ h c =
    let i = !nocc in nocc := i + 1;
    let occ_ok = if i < max_occ then occ_set.(i) else occ_default in
    if i >= max_occ - 1 && not occ_default then unify := (fun _ -> false);
    if occ_ok then (incr nsubst; mkRel h) else c in
  let rec subst h c = match kind_of_term c with
  | Rel _ -> c
  | LetIn _ when k = KpatFlex && nak = 0 && !unify c -> subst_occ h c
  | Var _ | Evar _ | Const _ | Ind _ | Construct _ ->
    if nak = 0 && c = pat_f then subst_occ h c else c
  | Prod _ | Sort _ | Lambda _ | Case _ | Fix _ | CoFix _
      when nak = 0 && k = KpatRigid & !unify c -> subst_occ h c
  | App _ when nak > 0 ->
    let ns = !nsubst in
    let rec subst_app na st c' = match kind_of_term c' with
    | _ when nak <= na && k = KpatFlex ->
      let st' = [pop_match_args na st] in
      if unify_app c' na st' then na, c' else subst_app (na - 1) st' c'
    | Cast (f, ck, t) ->
      let ma, f' = subst_app na st f in
      if ma > 0 then ma, c' else
      let t' = subst h t in
      if !nsubst > ns then 0, mkCast (f', ck, t') else 0, c'
    | App (f, args) ->
      let n = Array.length args in
      let ma, f' = subst_app (na + n) (args :: st) f in
      if ma >= n then ma - n, (if ma = n then subst_occ h c' else c') else
      let f'' = if ma = 0 then f' else subst_occ h f in
      let ns' = !nsubst in
      let ma' = if ns < ns' then ma else 0 in
      let args' = Array.sub args ma' (n - ma') in
      for i = ma to n - 1 do args'.(i - ma') <- subst h args.(i) done;
      if ma' > 0 || ns' < !nsubst then 0, mkApp (f'', args') else
      if ns < ns' then 0, mkApp (f'', args) else 0, c'
    | Var _ | Evar _ | Const _ | Ind _ | Construct _ ->
      let match_key = nak <= na && c' = pat_f in
      if match_key && unify_app c' nak st then nak, c' else 0, c'
    | Prod _ | Sort _ | Lambda _ | Case _ | Fix _ | CoFix _
      when nak <= na && k = KpatRigid && unify_app c' nak st -> nak, c'
    | _ -> 0, subst h c' in
    snd (subst_app 0 [] c)
  | _ ->
    let ns = !nsubst in
    let inch _ h' = h' + 1 in
    let c' = map_constr_with_binders_left_to_right inch subst h c in
    if !nsubst > ns then c' else c in
  let cl = subst 1 (pf_concl gl) in
  if n > 0 && !nocc = 0 then
    let m1 = "does not match any subterm" in
    let m2 = "only matches term with bound variables" in
    let m = if !match_args = [||] then m1 else m2 in
    errorstrm (str "pattern " ++ pr_pattern n pat ++ spc() ++ 
                                 pr_constr pat ++ spc() ++ str m)
  else if !nocc >= max_occ then cl, !match_args else
  errorstrm (str "only " ++ int !nocc ++ str " < " ++ int max_occ
            ++ str (plural !nocc " occurence")
            ++ str " of pattern" ++ spc () ++ pr_pattern n pat)

let pf_fill_occ_term gl occ = function
  | ErrorTerm e, _ ->
    raise e
  | SsrTerm (_, n), c ->
    if n = 0 && occ = [] && pat_key c = KpatFixed then
      subst_term c (pf_concl gl), c
    else
     let cl, args = pf_fill_occ_pat gl occ n (pf_abs_cterm gl n c) in
     cl, if n = 0 then c else whd_app c args

let pf_fill_term gl t = let cl, c = pf_fill_occ_term gl [] t in subst1 c cl, c

let pf_ind_type_of gl c =
  snd (pf_reduce_to_quantified_ind gl (pf_type_of gl c))

(** Occurrence switch *)

(* The standard syntax of complemented occurrence lists involves a single *)
(* initial "-", e.g., {-1 3 5} (the get_occ_indices function handles the  *)
(* conversion to the "all negated" form used by the Coq API). An initial  *)
(* "+" may be used to indicate positive occurrences (the default). The    *)
(* "+" is optional, except if the list of occurrences starts with a       *)
(* variable or is empty (to avoid confusion with a clear switch). The     *)
(* empty positive switch "{+}" selects no occurrences, while the empty    *)
(* negative switch "{-}" selects all occurrences explicitly; this is the  *)
(* default, but "{-}" prevents the implicit clear, and can be used to     *)
(* force dependent elimination -- see ndefectelimtac below.               *)

type ssrocc = ssrindex list

let pr_occ = function
  | ArgArg -1 :: occ -> str "{-" ++ pr_list pr_spc pr_index occ ++ str "}"
  | ArgArg 0 :: occ -> str "{+" ++ pr_list pr_spc pr_index occ ++ str "}"
  | occ -> str "{" ++ pr_list pr_spc pr_index occ ++ str "}"

let pr_ssrocc _ _ _ = pr_occ

ARGUMENT EXTEND ssrocc TYPED AS ssrindex list PRINTED BY pr_ssrocc
| [ natural(n) ssrindex_list(occ) ] -> [ ArgArg (check_index loc n) :: occ  ]
| [ "-" ssrindex_list(occ) ]     -> [ ArgArg (-1) :: occ ]
| [ "+" ssrindex_list(occ) ]     -> [ ArgArg 0 :: occ ]
END

let get_occ_indices = function
  | [ArgArg -1]      -> [0]
  | ArgArg -1 :: occ -> List.map (fun n -> -get_index n) occ
  | ArgArg 0 :: occ    -> List.map get_index occ
  | occ                -> List.map get_index occ

let pf_mkprod gl c cl =
  let x = constr_name c in
  let t = pf_type_of gl c in
  if x <> Anonymous || noccurn 1 cl then mkProd (x, t, cl) else
  mkProd (Name (pf_type_id gl t), t, cl)

let pf_abs_prod gl c cl = pf_mkprod gl c (subst_term c cl)

(** Discharge occ switch (combined occurrence / clear switch *)

type ssrdocc = ssrclear option * ssrocc

let mkocc occ = None, occ
let noclr = mkocc []
let mkclr clr  = Some clr, []
let nodocc = mkclr []

let pr_docc = function
  | None, occ -> pr_occ occ
  | Some clr, _ -> pr_clear mt clr

let pr_ssrdocc _ _ _ = pr_docc

ARGUMENT EXTEND ssrdocc TYPED AS ssrclear option * ssrocc PRINTED BY pr_ssrdocc
| [ "{" ne_ssrhyp_list(clr) "}" ] -> [ mkclr clr ]
| [ "{" ssrocc(occ) "}" ] -> [ mkocc occ ]
END

(** Generalization (discharge) item *)

(* An item is a switch + term pair.                                     *)

type ssrgen = ssrdocc * ssrterm

let pr_gen prc (docc, dt) = pr_docc docc ++ pr_term prc dt

let pr_ssrgen prc _ _ = pr_gen prc

ARGUMENT EXTEND ssrgen TYPED AS ssrdocc * ssrterm PRINTED BY pr_ssrgen
| [ ssrdocc(docc) ssrterm(dt) ] -> [ docc, dt ]
| [ ssrterm(dt) ] -> [ nodocc, dt ]
END

let has_occ ((_, occ), _) = occ <> []
let hyp_of_var v =  SsrHyp (dummy_loc, destVar v)

let interp_clr = function
| Some clr, (k, c) when k = notermkind && is_pf_var c -> hyp_of_var c :: clr 
| Some clr, _ -> clr
| None, _ -> []

let isOpenTerm = function SsrTerm (_, n), _ -> n > 0 | _ -> false

let pf_interp_gen gl to_ind ((oclr, occ), t) =
  let clr = interp_clr (oclr, t) in
  if to_ind && occ = [] && isOpenTerm t then
    let c = pf_abs_ssrterm gl t in
    mkProd (constr_name (snd t), pf_type_of gl c, pf_concl gl), c, clr
  else
    let cl, c = pf_fill_occ_term gl occ t in
    pf_mkprod gl c cl, c, clr

let genclrtac cl cs clr = tclTHEN (apply_type cl cs) (cleartac clr)
let exactgentac cl cs = tclTHEN (apply_type cl cs) (convert_concl cl)

let gentac gen gl =
  let cl, c, clr = pf_interp_gen gl false gen in genclrtac cl [c] clr gl

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
  | _ -> anomaly "missing gen list"

let cons_dep (gensl, clr) =
  if List.length gensl = 1 then ([] :: gensl, clr) else
  error "multiple dependents switches '/'"

ARGUMENT EXTEND ssrdgens_tl TYPED AS ssrgen list list * ssrclear
                            PRINTED BY pr_ssrdgens
| [ "{" ne_ssrhyp_list(clr) "}" ssrterm(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (mkclr clr, dt) dgens ]
| [ "{" ne_ssrhyp_list(clr) "}" ] ->
  [ [[]], clr ]
| [ "{" ssrocc(occ) "}" ssrterm(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (mkocc occ, dt) dgens ]
| [ "/" ssrdgens_tl(dgens) ] ->
  [ cons_dep dgens ]
| [ ssrterm(dt) ssrdgens_tl(dgens) ] ->
  [ cons_gen (nodocc, dt) dgens ]
| [ ] ->
  [ [[]], [] ]
END

ARGUMENT EXTEND ssrdgens TYPED AS ssrdgens_tl PRINTED BY pr_ssrdgens
| [ ":" ssrgen(gen) ssrdgens_tl(dgens) ] -> [ cons_gen gen dgens ]
END

let genstac (gens, clr) =
  tclTHENLIST (cleartac clr :: List.rev_map gentac gens)

(* Common code to handle generalization lists along with the defective case *)

let with_defective maintac deps clr =
  let top_gen = mkclr clr, (notermkind, mkVar !top_id) in
  tclTHEN (introid !top_id) (maintac deps top_gen)

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

(** View hint database. *)

(* There are three databases of lemmas used to mediate the application  *)
(* of reflection lemmas: one for forward chaining, one for backward     *)
(* chaining, and one for secondary backwards chaining.                  *)

(* View hints *)

let rec isCxHoles = function (CHole _, None) :: ch -> isCxHoles ch | _ -> false

let pr_raw_ssrhintref prc _ _ = function
  | CAppExpl (_, (None, r), args) when isCHoles args ->
    prc (CRef r) ++ str "|" ++ int (List.length args)
  | CApp (_, (_, CRef _), _) as c -> prc c
  | CApp (_, (_, c), args) when isCxHoles args ->
    prc c ++ str "|" ++ int (List.length args)
  | c -> prc c

let pr_rawhintref = function
  | RApp (_, f, args) when isRHoles args ->
    pr_rawconstr f ++ str "|" ++ int (List.length args)
  | c -> pr_rawconstr c

let pr_glob_ssrhintref _ _ _ (c, _) = pr_rawhintref c

let pr_ssrhintref prc _ _ = prc

let mkhintref loc c n = match c with
  | CRef r -> CAppExpl (loc, (None, r), mkCHoles loc n)
  | _ -> mkAppC (c, mkCHoles loc n)

ARGUMENT EXTEND ssrhintref
        TYPED AS constr      PRINTED BY pr_ssrhintref
    RAW_TYPED AS constr  RAW_PRINTED BY pr_raw_ssrhintref
   GLOB_TYPED AS constr GLOB_PRINTED BY pr_glob_ssrhintref
  | [ constr(c) ] -> [ c ]
  | [ constr(c) "|" natural(n) ] -> [ mkhintref loc c n ]
END

(* View purpose *)

let pr_viewpos = function
  | 0 -> str " for move/"
  | 1 -> str " for apply/"
  | 2 -> str " for apply//"
  | _ -> mt ()

let pr_ssrviewpos _ _ _ = pr_viewpos

ARGUMENT EXTEND ssrviewpos TYPED AS int PRINTED BY pr_ssrviewpos
  | [ "for" "move" "/" ] -> [ 0 ]
  | [ "for" "apply" "/" ] -> [ 1 ]
  | [ "for" "apply" "/" "/" ] -> [ 2 ]
  | [ "for" "apply" "//" ] -> [ 2 ]
  | [ ] -> [ 3 ]
END

let pr_ssrviewposspc _ _ _ i = pr_viewpos i ++ spc ()

ARGUMENT EXTEND ssrviewposspc TYPED AS ssrviewpos PRINTED BY pr_ssrviewposspc
  | [ ssrviewpos(i) ] -> [ i ]
END

(* The table and its display command *)

let viewtab : rawconstr list array = Array.make 3 []

let _ = 
  let init () = Array.fill viewtab 0 3 [] in
  let freeze () = Array.copy viewtab in
  let unfreeze vt = Array.blit vt 0 viewtab 0 3 in
  Summary.declare_summary "ssrview"
    { Summary.freeze_function   = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function     = init;
      Summary.survive_module = false;
      Summary.survive_section   = false }

let mapviewpos f n k = if n < 3 then f n else for i = 0 to k - 1 do f i done

let print_view_hints i =
  let pp_viewname = str "Hint View" ++ pr_viewpos i ++ str " " in
  let pp_hints = pr_list spc pr_rawhintref viewtab.(i) in
  ppnl (pp_viewname ++ hov 0 pp_hints ++ Pp.cut ())

VERNAC COMMAND EXTEND PrintView
| [ "Print" "Hint" "View" ssrviewpos(i) ] -> [ mapviewpos print_view_hints i 3 ]
END

(* Populating the table *)

let cache_viewhint (_, (i, lvh)) =
  let mem_raw h = List.exists (Topconstr.eq_rawconstr h) in 
  let add_hint h hdb = if mem_raw h hdb then hdb else h :: hdb in
  viewtab.(i) <- List.fold_right add_hint lvh viewtab.(i)
  
let export_viewhint x = Some x

let subst_viewhint (_, subst, (i, lvh as ilvh)) =
  let lvh' = list_smartmap (Detyping.subst_rawconstr subst) lvh in
  if lvh' == lvh then ilvh else i, lvh'
      
let classify_viewhint (_, x) = Libobject.Substitute x

let (in_viewhint, out_viewhint)=
  Libobject.declare_object {(Libobject.default_object "VIEW_HINTS") with
       Libobject.open_function = (fun i o -> if i = 1 then cache_viewhint o);
       Libobject.cache_function = cache_viewhint;
       Libobject.subst_function = subst_viewhint;
       Libobject.classify_function = classify_viewhint;
       Libobject.export_function = export_viewhint }

let glob_view_hints lvh =
  List.map (Constrintern.intern_constr Evd.empty (Global.env ())) lvh

let add_view_hints lvh i = Lib.add_anonymous_leaf (in_viewhint (i, lvh))

VERNAC COMMAND EXTEND HintView
  |  [ "Hint" "View" ssrviewposspc(n) ne_ssrhintref_list(lvh) ] ->
     [ mapviewpos (add_view_hints (glob_view_hints lvh)) n 2 ]
END

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
(*  1- using a view hint if the view is an instance of some    *)
(*     (reflection) inductive predicate.                       *)
(*  2- applying the view if it coerces to a function, adding   *)
(*     implicit arguments.                                     *)
(* They require guessing the view hints and the number of      *)
(* implicits, respectively, which we do by brute force.        *)

let view_error s gl rv =
  errorstrm (str ("Cannot " ^ s ^ " view ") ++ pf_pr_rawconstr gl rv)

let interp_view ist gl gv id =
  match glob_constr ist gl gv with
  | RApp (loc, RHole _, rargs) ->
    let rv = RApp (loc, RVar (loc, id), rargs) in
    let oc = interp_open_constr ist gl (rv, None) in
    mkNamedLambda id (pf_get_hyp_typ gl id) (snd (pf_abs_evars gl oc))
  | rv ->  
  let interp rc rargs =
    let oc = interp_open_constr ist gl (mkRApp rc rargs, None) in
    let _, c = pf_abs_evars gl oc in
    match kind_of_term c with
    | App (f, args) -> mkApp (f, Array.sub args 0 (Array.length args - 1))
    | _ -> mkNamedLambda id (pf_get_hyp_typ gl id) c in
  let rec simple_view rargs n =
    if n < 0 then view_error "use" gl rv else
    try interp rv rargs with _ -> simple_view (mkRHole :: rargs) (n - 1) in
  let view_nbimps = interp_view_nbimps ist gl rv in
  let view_args = [mkRApp rv (mkRHoles view_nbimps); mkRVar id] in
  let rec view_with = function
  | [] -> simple_view [mkRVar id] (interp_nbargs ist gl rv)
  | hint :: hints -> try interp hint view_args with _ -> view_with hints in
  view_with (if view_nbimps < 0 then [] else viewtab.(0))

let pf_with_view gl view cl c = match view with
  | [f] ->
    let c' = mkApp (f, [|c|]) in pf_abs_prod gl c' (prod_applist cl [c]), c'
  | _ -> cl, c

(** Equations *)

(* argument *)

type ssreqid = ssripat option

let pr_eqid = function Some pat -> str " " ++ pr_ipat pat | None -> mt ()
let pr_ssreqid _ _ _ = pr_eqid

(* We must use primitive parsing here to avoid conflicts with the  *)
(* basic move, case, and elim tactics.                             *)
ARGUMENT EXTEND ssreqid TYPED AS ssripat option PRINTED BY pr_ssreqid
| [ "(**)" ] -> [ Util.anomaly "Grammar placeholder match" ]
END

let input_ssreqid strm =
  match Stream.npeek 1 strm with
  | ["IDENT", id] ->
    accept_before_syms [":"] strm; Some (IpatId (id_of_string id))
  | ["", "_"] -> accept_before_syms [":"] strm; Some (IpatWild)
  | ["", "?"] -> accept_before_syms [":"] strm; Some (IpatAnon)
  | ["", "->"] -> accept_before_syms [":"] strm; Some (IpatRw L2R)
  | ["", "<-"] -> accept_before_syms [":"] strm; Some (IpatRw R2L)
  | ["", ":"] -> None
  | _ -> raise Stream.Failure

let ssreqid_p4 = Gram.Entry.of_parser "ssreqid" input_ssreqid

GEXTEND Gram
  GLOBAL: ssreqid ssreqid_p4;
  ssreqid: [[ eqid = ssreqid_p4 -> eqid ]];
END

(* creation *)

let mkEq dir cl c t n =
  let eqargs = [|t; c; c|] in eqargs.(dir_org dir) <- mkRel n;
  mkArrow (mkApp (build_coq_eq(), eqargs)) (lift 1 cl), mkRefl t c

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
  | [] -> introid !top_id gl
  | (_, (SsrTerm (_, 0), c)) :: _ -> havetac !top_id c gl
  | (_, t) :: gens' ->
    let gl' = pf_image gl (genstac (gens', clr)) in
    havetac !top_id (snd (pf_fill_term gl' t)) gl

let interp_ssrarg ist gl (gvs, garg) =
  let _, arg = interp_wit globwit_ssrarg wit_ssrarg ist gl ([], garg) in
  let _, (dgens, _) = arg in
  let interp_view_with_arg gv =
    interp_view ist (pf_image gl (defdgenstac dgens)) gv !top_id in
  (List.map interp_view_with_arg gvs, arg)

(** The "clear" tactic *)

(* We just add a numeric version clears the n top assumptions. *)

let poptac n = introstac (list_tabulate (fun _ -> IpatWild) n)

TACTIC EXTEND ssrclear
  | [ "clear" natural(n)] -> [ poptac n ]
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
  | _, (Some pat, (dgens, ipats)) ->
    tclTHEN (with_dgens dgens eqmovetac) (eqmoveitac pat ipats)
  | _, (_, (([gens], clr), ipats)) ->
    tclTHEN (genstac (gens, clr)) (introstac ipats)
  | _, (_, ((_, clr), ipats)) ->
    tclTHENLIST [movehnftac; cleartac clr; introstac ipats]

TACTIC EXTEND ssrmove
| [ "move" ssrmovearg(arg) ssrrpat(pat) ] ->
  [ tclTHEN (ssrmovetac arg) (ipattac pat) ]
| [ "move" ssrmovearg(arg) ssrclauses(clauses) ] ->
  [ tclCLAUSES (ssrmovetac arg) clauses ]
| [ "move" ssrrpat(pat) ] -> [ ipattac pat ]
| [ "move" ] -> [ movehnftac ]
END

(** The "case" tactic *)

(*
let dep_x = Name (id_of_string "dep_var")

let understand_dep sigma (i, env, rc) = function
| _, (SsrError e, _) -> raise e
| _, (SsrTerm (_, 0), c) when isVar c ->
  i, env, mkRApp (rc, [mkRVar (destVar c)])
| _, (SsrTerm (_, 2), c) when isAbsHole c ->
  i, env, mkRApp (rc, mkRHoles 1)
| _, (SsrTerm (_, n), c) ->
  let t = Retyping.get_type_of sigma env c in
  let id = id_of_string (sprintf "Kdep %d" i) in
  let env' = Environ.push_named (id, Some c, None, t) in
  (i + 1, env', mkRApp (rc, [mkRApp (mkRVar id, mkRHoles n)])

let pf_understand_dep_case gl deps kt =
  let kc = pf_abs_ssrterm gl kt in
  let kct, mind = pf_reduce_to_quantified_ind gl (pf_type_of gl kc) in
  let env = pf_env gl and sigma = project gl in
  let npar, ndep = Inductiveops.inductive_nargs env mind in
  let kdc, _ =
     Reductionops.splay_arity env sigma
        (Inductiveops.type_of_inductive env mind) in
  let ndc = npar + ndep - List.length deps in
  if ndc < npar then error "too many dependent patterns" else
  let id1 = id_of_string "Rdep 1" and id2 = id_of_string "Rdep 2" in
  let t2 = compose_prod kdc (mkEtaApp (mkInd mind) 1 (List.length kdc)) in
  let env1 = Environ.push_named (id1, None, kct) in
  let env2 = Environ.push_named (id2, None, t2) in
  let rc1 = mkRApp (mkRVar id1) (mkRHoles (nb_prod kct)) in
  let rc2 = mkRApp (mkRVar id2) (mkRHoles ndc) in
  let _, env', rc =
    List.fold_left (understand_dep sigma) (0, env2, rc2) deps in
  let eqrc = RRef (dummy_loc, IndRef (destInd (build_coq_eq ()))) in
  let rc' = mkRApp (eqrc, mkRHoles 1 @ [rc1, rc]) in
  let n, dc, c1, d2 =
    try
      let n, c = pf_abs_evars gl (understand_tcc sigma env' rc') in
      let dc, c' = decompose_lam_n n d in
      let _, a = destApp c' in
      let env'' = push_rels_assum dc env' in
      let t2 = Retyping.get_type_of sigma (push_rels_assum dc env') a.(2) in
      let _, a2 = destApp t2)) npar ndep in
      n, dc, a.(1), Array.sub a2 npar ndep 
    with _ -> error "dependent patterns do not match type instance" in
  let 
*)

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
  tclTHENLIST [pattac; ctac c; cleartac (List.flatten clrs')]

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
  | Some pat -> ipatstac [IpatAll; pat]

let ssrcasetac (view, (eqid, (dgens, ipats))) =
  let casetac = with_dgens dgens (ndefectcasetac view eqid) in
  tclEQINTROS casetac (popcaseeqtac eqid) ipats

TACTIC EXTEND ssrcase
| [ "case" ssrcasearg(arg) ssrclauses(clauses) ] ->
  [ tclCLAUSES (ssrcasetac arg) clauses ]
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
  convert_concl (mkApp (compose_lam dc (whdEtaApp cl2 n), args1)) gl

let depelimtac view eqid c cl clrs =
  let pattac = if eqid = None then convert_concl else protectreceqtac in
  tclTHENLIST [pattac cl; elimtac view c; cleartac (List.flatten clrs)]

let ndefectelimtac view eqid deps ((_, occ), _ as gen) gl =
  let cl, c, clr = pf_interp_gen gl true gen in
  if deps = [] && eqid = None && occ = [] then
    depelimtac view eqid c (prod_applist cl [c]) [clr] gl else
  let cl', args =
    let _, _, cl' = destProd cl in
    let force_dep = occ = [ArgArg 0] || (eqid <> None && deps = []) in
    if not force_dep && noccurn 1 cl' then cl', [] else cl, [c] in
  with_deps deps (depelimtac view eqid c) cl' args clr gl

let unprotecttac gl =
  let prot = destConst (mkSsrConst "protect_term") in
  onClauses (unfold_option [[], EvalConstRef prot]) allClauses gl

let popelimeqtac = function
| None -> tclIDTAC
| Some pat -> tclTHENLIST [intro_all; pushelimeqtac; ipattac pat; unprotecttac]

let ssrelimtac (view, (eqid, (dgens, ipats))) =
  let elimtac = with_dgens dgens (ndefectelimtac view eqid) in
  tclEQINTROS elimtac (popelimeqtac eqid) ipats

TACTIC EXTEND ssrelim
| [ "elim" ssrarg(arg) ssrclauses(clauses) ] ->
  [ tclCLAUSES (ssrelimtac arg) clauses ]
| [ "elim" ] -> [ ssrelimtac no_ssrarg ]
END

(** 6. Backward chaining tactics: apply, exact, congr. *)

(** The "apply" tactic *)

ARGUMENT EXTEND ssragen TYPED AS ssrgen PRINTED BY pr_ssrgen
| [ "{" ne_ssrhyp_list(clr) "}" ssrterm(dt) ] -> [ mkclr clr, dt ]
(* | [ "{" "}" ssrterm(dt) ] -> [ noclr, dt ] *)
| [ ssrterm(dt) ] -> [ nodocc, dt ]
END

ARGUMENT EXTEND ssragens TYPED AS ssrdgens PRINTED BY pr_ssrdgens
| [ "{" ne_ssrhyp_list(clr) "}" ssrterm(dt) ssragens(agens) ] ->
  [ cons_gen (mkclr clr, dt) agens ]
| [ "{" ne_ssrhyp_list(clr) "}" ] -> [ [[]], clr]
| [ ssrterm(dt) ssragens(agens) ] ->
  [ cons_gen (nodocc, dt) agens ]
| [ ] -> [ [[]], [] ]
END

type ssrapplyarg = open_constr list * ssrarg

let mk_applyarg views agens ipats = [], (views, (None, (agens, ipats)))

let pr_ssrapplyarg prc prlc prt (_, arg) = pr_ssrarg prc prlc prt arg

let interp_agen ist gl ((goclr, _), (k, gc)) (clr, rcs) =
  let rc = glob_constr ist gl gc in
  let rcs' = rc :: rcs in
  match goclr with
  | None -> clr, rcs'
  | Some ghyps ->
    let clr' = interp_hyps ist gl ghyps @ clr in
    if k <> notermkind then clr', rcs' else
    match rc with
    | RVar (loc, id) -> SsrHyp (loc, id) :: clr', rcs'
    | RRef (loc, VarRef id) -> SsrHyp (loc, id) :: clr', rcs'
    | _ -> clr', rcs'

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
  | hint :: hints ->
    try Some (interp_refine ist gl (mkRApp hint args))
    with _ -> interp_refine_args ist gl args hints

let mkRAppViewArgs ist gl rv nb_goals =
  let nb_view_imps = interp_view_nbimps ist gl rv in
  if nb_view_imps < 0 then view_error "apply" gl rv else
  mkRApp rv (mkRHoles nb_view_imps) :: mkRHoles nb_goals

let interp_apply_view i ist gl gv =
  let rv = glob_constr ist gl gv in
  let args = mkRAppViewArgs ist gl rv i in
  let interp_with hint = interp_refine ist gl (mkRApp hint args) in
  let rec loop = function
  | [] -> view_error "apply" gl rv
  | hint :: hints -> try interp_with hint with _ -> loop hints in
  loop viewtab.(i)

let dependent_apply_error =
  try Util.error "Could not fill dependent hole in \"apply\"" with err -> err

let rec refine_with oc gl =
  try Refine.refine oc gl with _ -> raise dependent_apply_error

let rec refine_with_list = function
  | lemma :: lemmas ->
    tclTHENLAST (refine_with lemma) (refine_with_list lemmas)
  | [] ->
    tclIDTAC

let open_arg i (_, c) = let _, a = destApplication c in a.(i)

let interp_ssrapplyarg ist gl (_, (gviews, (_, ((ggenl, gclr), gipats)))) =
  let clr = interp_hyps ist gl gclr in
  let ipats = List.map (interp_ipat ist gl) gipats in
  match gviews, ggenl with
  | [], [agens] ->
    let clr', lemma = interp_agens ist gl agens in
    let dt = notermkind, snd (pf_abs_evars gl lemma) in
    [lemma], ([], (None, (([[(Some clr', []), dt]], clr), ipats)))
  | [gv1], [] ->
    let v1 = interp_apply_view 1 ist gl gv1 in
    [v1], ([open_arg 2 v1], (None, (([], clr), ipats)))
  | [gv1; gv2], [] -> 
    let v1 = interp_apply_view 1 ist gl gv1 in
    let gl1 = pf_image_last gl (refine_with v1) in
    let v12 = [v1; interp_apply_view 2 ist gl1 gv2] in
    v12, (List.map (open_arg 2) v12, (None, (([], clr), ipats)))
  | _ ->
    [], ([], (None, (([], clr), ipats)))

ARGUMENT EXTEND ssrapplyarg TYPED AS open_constr list * ssrarg
  PRINTED BY pr_ssrapplyarg
  INTERPRETED BY interp_ssrapplyarg
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

let apply_id id gl =
  let n = pf_nbargs gl (mkVar id) in
  let mkRlemma i = mkRApp (mkRVar id) (mkRHoles i) in
  let cl = pf_concl gl in
    let rec loop i =
    if i > n then errorstrm (str "Could not apply " ++ pr_id id) else
    try pf_match gl (mkRlemma i) cl with _ -> loop (i + 1) in
  refine_with (loop 0) gl

let apply_top_tac gl =
  tclTHENLIST [introid !top_id; apply_id !top_id; clear [!top_id]] gl

let ssrapplytac (lemmas, (_, (_, ((gens, clr), ipats)))) =
  let apptac = match lemmas, gens with
  | [], _ ->
    tclTHEN apply_top_tac (cleartac clr)
  | [lemma], [[(Some clr', _), _]] ->
    tclTHENLIST [cleartac clr; refine_with lemma; cleartac clr']
  | _ ->
    tclTHEN (refine_with_list lemmas) (cleartac clr) in
  tclINTROS apptac ipats

TACTIC EXTEND ssrapply
| [ "apply" ssrapplyarg(arg) ] -> [ ssrapplytac arg ]
| [ "apply" ] -> [ apply_top_tac ]
END

(** The "exact" tactic *)

ARGUMENT EXTEND ssrexactarg TYPED AS ssrapplyarg PRINTED BY pr_ssrapplyarg
| [ ":" ssragen(gen) ssragens(dgens) ] ->
  [ mk_applyarg [] (cons_gen gen dgens) [] ]
| [ ssrview(view1) ssrview(view2) ssrclear(clr) ] ->
  [ mk_applyarg (view1 @ view2) ([], clr) [] ]
| [ ssrview(view) ssrclear(clr) ] ->
  [ mk_applyarg view ([], clr) [] ]
| [ ssrclear_ne(clr) ] ->
  [ mk_applyarg [] ([], clr) [] ]
END

let vmexacttac pf gl = exact_no_check (mkCast (pf, VMcast, pf_concl gl)) gl

TACTIC EXTEND ssrexact
| [ "exact" ssrexactarg(arg) ] -> [ tclBY (ssrapplytac arg) ]
| [ "exact" ] -> [ tclORELSE donetac (tclBY apply_top_tac) ]
| [ "exact" "<:" lconstr(pf) ] -> [ vmexacttac pf ]
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
  let _, f = pf_abs_evars gl (interp_open_constr ist gl gf) in
  let rf = Detyping.detype false [] [] f in
  let m = pf_nbargs gl f in
  if n > 0 then
    match interp_congrarg_at ist gl n rf m with
    | Some f' -> f'
    | None ->
    errorstrm (str "No " ++ pr_int n ++ str "-congruence with "
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

(** Coq rewrite compatibility flag *)

let ssr_strict_match = ref false

let _ =
  Goptions.declare_bool_option 
    { Goptions.optsync  = true;
      Goptions.optname  = "strict redex matching";
      Goptions.optkey   = SecondaryTable ("Match", "Strict");
      Goptions.optread  = (fun () -> !ssr_strict_match);
      Goptions.optwrite = (fun b -> ssr_strict_match := b) }

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
  | Some (ErrorTerm _, _ as t) -> str "[" ++ pr_term prlc t ++ str "]"
  | Some (_, c) -> str "[" ++ prlc c ++ str "]"

let pr_ssrredex _ prlc _ = pr_redex prlc

ARGUMENT EXTEND ssrredex_ne TYPED AS ssrterm option PRINTED BY pr_ssrredex
  | [ "[" lconstr(c) "]" ] -> [ Some (notermkind, c) ]
END

ARGUMENT EXTEND ssrredex TYPED AS ssrredex_ne PRINTED BY pr_ssrredex
  | [ ssrredex_ne(rdx) ] -> [ rdx ]
  | [ ] -> [ None ]
END

(** Rewrite clear/occ switches *)

let pr_rwocc = function
  | None, [] -> mt ()
  | None, occ -> pr_occ occ
  | Some clr,  _ ->  pr_clear_ne clr

let pr_ssrrwocc _ _ _ = pr_rwocc

ARGUMENT EXTEND ssrrwocc TYPED AS ssrdocc PRINTED BY pr_ssrrwocc
| [ "{" ssrhyp_list(clr) "}" ] -> [ mkclr clr ]
| [ "{" ssrocc(occ) "}" ] -> [ mkocc occ ]
| [ ] -> [ noclr ]
END

(** Rewrite rules *)

type ssrwkind = RWred of ssrsimpl | RWdef | RWeq
type ssrrule = ssrwkind * ssrterm

let pr_rwkind = function
  | RWred s -> pr_simpl s
  | RWdef -> str "/"
  | RWeq -> mt ()

let wit_ssrrwkind, globwit_ssrrwkind, rawwit_ssrrwkind =
  add_genarg "ssrrwkind" pr_rwkind

let pr_rule prc = function
  | RWred s, _ -> pr_simpl s
  | RWdef, r-> str "/" ++ pr_term prc r
  | RWeq, r -> pr_term prc r

let pr_ssrrule prc _ _ = pr_rule prc

let noruleterm loc = notermkind, mkCProp loc

ARGUMENT EXTEND ssrrule_nt TYPED AS ssrrwkind * ssrterm PRINTED BY pr_ssrrule
  | [ ssrsimpl_ne(s) ] -> [ RWred s, noruleterm loc ]
  | [ "/" ssrterm(t) ] -> [ RWdef, t ] 
END

ARGUMENT EXTEND ssrrule_ne TYPED AS ssrrule_nt PRINTED BY pr_ssrrule
  | [ ssrrule_nt(r) ] -> [ r ]
  | [ ssrterm(t) ] -> [ RWeq, t ] 
END

ARGUMENT EXTEND ssrrule TYPED AS ssrrule_nt PRINTED BY pr_ssrrule
  | [ ssrrule_ne(r) ] -> [ r ]
  | [ ] -> [ RWred Nop, noruleterm loc ]
END

(** Rewrite arguments *)

type ssrrwarg = (ssrdir * ssrmult) * ((ssrdocc * ssrredex) * ssrrule)

let pr_rwarg prc prlc ((d, m), ((docc, rx), r)) =
  pr_rwdir d ++ pr_mult m ++ pr_rwocc docc ++ pr_redex prlc rx ++ pr_rule prc r

let pr_ssrrwarg prc prlc _ = pr_rwarg prc prlc

let mk_rwarg (d, (n, _ as m)) ((clr, occ as docc), rx) (rt, _ as r) =   
 if rt <> RWeq then begin
   if rt = RWred Nop && not (m = nomult && occ = [] && rx = None)
                     && (clr = None || clr = Some []) then
     anomaly "Improper rewrite clear switch";
   if d = R2L && rt <> RWdef then
     error "Right-to-left switch on simplification";
   if n <> 1 && (rt = RWred Cut || rx = None) then
     error "Bad or useless multiplier";
   if occ <> [] && rx = None && rt <> RWdef then
     error "Missing redex for simplification occurrence"
 end; (d, m), ((docc, rx), r)

let norwmult = L2R, nomult
let norwocc = noclr, None

ARGUMENT EXTEND ssrrwarg_nt
  TYPED AS (ssrdir * ssrmult) * ((ssrdocc * ssrredex) * ssrrule)
  PRINTED BY pr_ssrrwarg
  | [ "-" ssrmult(m) ssrrwocc(docc) ssrredex(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg (R2L, m) (docc, rx) r ]
  | [ "-/" ssrterm(t) ] ->     (* just in case '-/' should become a token *)
    [ mk_rwarg (R2L, nomult) norwocc (RWdef, t) ]
  | [ ssrmult_ne(m) ssrrwocc(docc) ssrredex(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg (L2R, m) (docc, rx) r ]
  | [ "{" ne_ssrhyp_list(clr) "}" ssrredex_ne(rx) ssrrule_ne(r) ] ->
    [ mk_rwarg norwmult (mkclr clr, rx) r ]
  | [ "{" ne_ssrhyp_list(clr) "}" ssrrule(r) ] ->
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
  | [ ssrterm(t) ] -> [ mk_rwarg norwmult norwocc (RWeq, t) ]
END

let simplintac occ rdx sim gl = match rdx with
  | None -> simpltac sim gl
  | Some t ->
    let cl, c, _ = pf_interp_gen gl false (mkocc occ, t) in
    let simptac = convert_concl (prod_applist cl [pf_nf gl c]) in
    match sim with
    | Simpl -> simptac gl
    | SimplCut -> tclTHEN simptac (tclTRY donetac) gl
    | _ -> Util.error "useless redex switch"

let rwtermtac dir t gl = rewritetac dir (pf_abs_ssrterm gl t) gl

let rec get_evalref c =  match kind_of_term c with
  | Var id -> EvalVarRef id, c
  | Const k -> EvalConstRef k, c
  | App (c', _) -> get_evalref c'
  | Cast (c', _, _) -> get_evalref c'
  | _ -> error "Bad unfold head term"

let nb_occ v =
  let rec add_occs n c = if c = v then n + 1 else fold_constr add_occs n c in
  add_occs 0

let unfold_val = mkVar (id_of_tag "unfold occurrence")

(* Strip a pattern generated by a prenex implicit to its constant. *)
let strip_unfold_term t = match t with
  | SsrTerm (' ', n), c when n > 0 ->
    let _, c' = decompose_lam_n n c in let f, _ = decompose_app c' in
    if isConst f && c' = mkEtaApp f n 1 then notermkind, f else t
  | _ -> t

(* We disable the zeta-reductions of the simple unfold when they would *)
(* interfere with the "in" tactical.                                   *)

let unfoldtac occ t gl =
  let t' = strip_unfold_term t in
  let cl, c, _ = pf_interp_gen gl false (mkocc occ, t') in
  let r, v = get_evalref c in
  let iocc = get_occ_indices occ in
  if c = v && List.for_all ((<) 0) iocc && pf_ctx_let_depth gl = 0
    then unfold_in_concl [iocc, r] gl else
  let m = nb_occ v c in
  let rec mk_occ (i, occ') c' =
    if c' = v then (i + 1, occ') else
    if c' = unfold_val then (i + m, i :: occ') else
    fold_constr mk_occ (i, occ') c' in
  let _, occ' = mk_occ (1, []) (prod_applist cl [unfold_val]) in
  tclTHEN (convert_concl (prod_applist cl [c])) (unfold_in_concl [occ', r]) gl

let unfoldintac occ rdx t gl = match rdx with
| None ->
  unfoldtac occ t gl
| Some r ->
  let cl, c, _ = pf_interp_gen gl false (mkocc occ, r) in
  let tcl = pf_type_of gl cl in
  let cl' = mkLambda (Anonymous, tcl, mkApp (mkRel 1, [|c|])) in
  let gl' = pf_image gl (tclTHEN (apply_type cl' [cl]) (unfoldtac [] t)) in
  let _, args = destApplication (pf_concl gl') in
  convert_concl (prod_applist cl [args.(0)]) gl

let foldtac occ rdx t gl =
  let n, pat = match t with
  | ErrorTerm e, _ -> raise e
  | SsrTerm (_, n), pat -> n, pat in
  let cl, c = match rdx with
  | Some rxt ->
    pf_fill_occ_term gl occ rxt
  | None ->
    let rpat = pf_abs_cterm gl n (try pf_red_product gl pat with _ -> pat) in
    try let cl, args = pf_fill_occ_pat gl occ n rpat in cl, whd_app rpat args
    with _ -> errorstrm (str "no fold occurrence for " ++ pr_pattern n pat) in
  try convert_concl (subst1 (pf_match_pattern gl n pat c) cl) gl with _ ->
  errorstrm (str "fold pattern " ++ pr_pattern n pat ++ spc ()
            ++ str "does not match redex " ++ pf_pr_constr gl c)

let coq_prod = lazy (build_prod ())

let converse_dir = function L2R -> R2L | R2L -> L2R

let compose_dep_lam dc c0 =
  let mkdeplam (c, ndeps) (x, t) =
    let ndep = noccurn 1 c in
    (if ndep then lift (-1) c else mkLambda (x, t, c)), ndep :: ndeps in
  List.fold_left mkdeplam (c0, []) dc

let compose_ndep_lam dc ndeps c0 args =
  let ndep = Array.of_list (List.rev ndeps) in
  let mkndeplam i (c, j) (x, t) =
    if ndep.(i) then mkLambda (x, t, c), j else subst1 args.(j) c, j - 1 in
  fst (list_fold_left_i mkndeplam 0 (c0, Array.length args - 1) dc)

let rwcltac cl dir rule gl0 =
  let cvttac gl =
    try convert_concl cl gl with _ ->
    errorstrm (str "dependent type error in rewrite of" ++ spc ()
               ++ pf_pr_constr gl cl) in
  let rwtac gl =
    let gls, _ as tacres =
      try rewritetac dir rule gl with _ ->
      anomaly "ssreflect internal rewrite failed" in
    let cl' = pf_concl (first_goal gls) in
    if not (eq_constr cl' (pf_concl gl0)) then tacres else
    errorstrm (str "rewrite loop " ++ pf_pr_constr gl cl ++ spc ()
              ++ str "<-> " ++ pf_pr_constr gl cl') in
  tclTHEN cvttac rwtac gl0

let rec rwrxtac occ rdx_pat dir rule_pat gl =
  let rule = pf_abs_ssrterm gl rule_pat in
  let dc, (eqind, eqargs) = try
    let _, t = pf_reduce_to_quantified_ind gl (pf_type_of gl rule) in
    let dc, indt = decompose_prod t in dc, destApplication indt
    with _ -> [], (mkProp, [||]) in
  let n = List.length dc in
  let coq_prod = Lazy.force coq_prod in
  if eqind = coq_prod.typ then
    let mkrule =
      let _, rule' = decompose_lam (pf_hnf_constr gl rule) in
      match kind_of_term rule' with
      | App (cpair, pair_args) when isConstruct cpair ->
        fun i -> fst (compose_dep_lam dc pair_args.(i + 1))
      | _ ->
        let proj_args = Array.append eqargs [|whdEtaApp rule n|] in
        fun i ->
        let proj = if i = 1 then coq_prod.proj1 else coq_prod.proj2 in
        compose_lam dc (mkApp (proj, proj_args)) in
    let rwtac dir' i = rwrxtac occ rdx_pat dir' (notermkind, mkrule i) in
    if eqargs.(0) = build_coq_True () then rwtac (converse_dir dir) 2 gl else
    tclORELSE (rwtac dir 1) (rwtac dir 2) gl
  else let is_rel = eqind <> build_coq_eq () in
  if (is_rel || !ssr_strict_match) && occ = [] && rdx_pat = None then
    rewritetac dir rule gl else
  if is_rel then error "not implemented: redex selection for Relation" else
  let pp_rule label = str label ++ pr_term (pf_pr_constr gl) rule_pat in
  let lhs, ndeps = compose_dep_lam dc eqargs.(dir_org dir) in
  let nl = List.fold_right (fun b nl -> if b then nl else nl + 1) ndeps 0 in
  let cl, args = match rdx_pat with
  | None ->
    let res = try pf_fill_occ_pat gl occ nl lhs with _ -> mkProp, [||] in
    if not (closed0 (fst res)) then res else
    errorstrm (pp_rule "couldn't rewrite with ")
  | Some rdx_term ->
    let cl, rdx = pf_fill_occ_term gl occ rdx_term in
    if closed0 cl then
      errorstrm (str "No occurrence of redex " ++ pf_pr_constr gl rdx)
    else try cl, pf_understand_holes gl nl 0 lhs rdx with _ ->
    let pp_tag = pp_rule "rewrite rule " ++ str " doesn't match redex" in
    errorstrm (hv 4 (pp_tag ++ spc() ++ pf_pr_constr gl rdx)) in
  let c = whd_app lhs args in
  let eta_rule = whdEtaApp rule n in
  let c_rule = compose_ndep_lam dc ndeps eta_rule args in
  let cl' = mkApp (mkLambda (Name !pattern_id, pf_type_of gl c, cl), [|c|]) in
  rwcltac cl' dir c_rule gl

(* Resolve forward reference *)
let _ = ipat_rewritetac := (fun dir c -> rwrxtac [] None dir (notermkind, c))

let rwargtac ((dir, mult), (((oclr, occ), rx), (kind, t))) gl =
  let rwtac = match kind with
  | RWred sim -> simplintac occ rx sim
  | RWdef -> if dir = R2L then foldtac occ rx t else unfoldintac occ rx t
  | RWeq -> rwrxtac occ rx dir t in
  tclTHEN (tclMULT mult rwtac) (cleartac (interp_clr (oclr, t))) gl

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

let pr_ssrtermspc prc _ _ dt = spc () ++ pr_term prc dt

ARGUMENT EXTEND ssrtermspc TYPED AS ssrterm PRINTED BY pr_ssrtermspc
  | [ ssrterm(dt) ] -> [ dt ]
END

let ssrrewritetac rwargs = tclTHENLIST (List.map rwargtac rwargs)

let ssrrewritebindtac t bl =
  Equality.general_rewrite_bindings true (force_term t, bl)

TACTIC EXTEND ssrrewrite
  | [ "rewrite" ssrrwargs_nt(args) ssrclauses(clauses) ] ->
    [ tclCLAUSES (ssrrewritetac args) clauses ]
  | [ "rewrite" ssrtermspc(r) "with" bindings(bl) ssrclauses(clauses) ] ->
    [ tclCLAUSES (ssrrewritebindtac r bl) clauses ]
  | [ "rewrite" ssrtermspc(r) ssrrwargs(args) ssrclauses(clauses) ] ->
    [ tclCLAUSES (tclTHEN (rwrxtac [] None L2R r)
                          (ssrrewritetac args)) clauses ]
END

(** The "unlock" tactic *)

let pr_ssrunlockarg prc _ _ (occ, t) = pr_occ occ ++ pr_term prc t

ARGUMENT EXTEND ssrunlockarg TYPED AS ssrocc * ssrterm
  PRINTED BY pr_ssrunlockarg
  | [  "{" ssrocc(occ) "}" ssrterm(t) ] -> [ occ, t ]
  | [  ssrterm(t) ] -> [ [], t ]
END

let rec unlocktac = function
  | (occ, t) :: args ->
   tclTHEN (unfoldtac occ t) (unlocktac args)
  | [] ->
    let locked = mkSsrConst "locked" in
    let key = mkSsrConst "master_key" in
    tclTHEN (unfoldtac [] (notermkind, locked)) (simplest_case key)

TACTIC EXTEND ssrunlock
  | [ "unlock" ssrunlockarg_list(args) ssrclauses(clauses) ] ->
    [  tclCLAUSES (unlocktac args) clauses ]
END

(** 8. Forward chaining tactics (pose, set, have, suffice, wlog) *)

(** Defined identifier *)

type ssrfwdid = identifier

let pr_ssrfwdid _ _ _ id = pr_spc () ++ pr_id id

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

type ssrfwdkind = FwdHint of string | FwdHave | FwdPose

type ssrfwdfmt = ssrfwdkind * ssrbindfmt list

let pr_fwdkind = function FwdHint s -> str (s ^ " ") | _ -> str " :=" ++ spc ()
let pr_fwdfmt (fk, _ : ssrfwdfmt) = pr_fwdkind fk

let wit_ssrfwdfmt, globwit_ssrfwdfmt, rawwit_ssrfwdfmt =
  add_genarg "ssrfwdfmt" pr_fwdfmt

type ssrfwd = ssrfwdfmt * ssrterm

let pr_ssrfwd prc _ _ (k, c) = pr_fwdfmt k ++ pr_term prc c

let mkFwdVal fk c = (fk, []), (notermkind, c)

let mkFwdCast fk loc t c =
  (fk, [BFcast]), (notermkind, CCast (loc, c, dC, t))

let mkFwdHint s t =
  let loc = constr_loc t in mkFwdCast (FwdHint s) loc t (CHole loc)

ARGUMENT EXTEND ssrfwd TYPED AS ssrfwdfmt * ssrterm PRINTED BY pr_ssrfwd
  | [ ":=" lconstr(c) ] -> [ mkFwdVal FwdPose c ]
  | [ ":" lconstr (t) ":=" lconstr(c) ] -> [ mkFwdCast FwdPose loc t c ]
END

(* Representation level-specific printers. *)

let pr_gen_fwd prval prc prlc fk (bs, c) =
  let prc s = str s ++ spc () ++ prval prc prlc c in
  match fk, bs with
  | FwdHint s, [Bcast t] -> str s ++ spc () ++ prlc t
  | FwdHint s, _ ->  prc (s ^ "(* typeof *)")
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
| (fk, h), (SsrTerm (_, n), c) ->
  let pc = pat_of_ssrterm n c in
  pr_gen_fwd prval pr_constr prl_constr fk (format_constr h pc)

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

let ssrposetac (id, (_, t)) gl = posetac id (pf_abs_ssrterm gl t) gl
  
TACTIC EXTEND ssrpose
| [ "pose" ssrfixfwd(ffwd) ] -> [ ssrposetac ffwd ]
| [ "pose" ssrcofixfwd(ffwd) ] -> [ ssrposetac ffwd ]
| [ "pose" ssrfwdid(id) ssrposefwd(fwd) ] -> [ ssrposetac (id, fwd) ]
END

(** The "set" tactic *)

type ssrsetfwd = ssrfwd * ssrdocc

let guard_setrhs s i = s.[i] = '{'

let pr_setrhs occ prc prlc c =
  if occ = nodocc then pr_guarded guard_setrhs prlc c else pr_docc occ ++ prc c

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

let ssrsettac id ((_, t), (_, occ)) gl =
  let cl, c = pf_fill_occ_term gl occ t in
  let cl' = mkLetIn (Name id, c, pf_type_of gl c, cl) in
  tclTHEN (convert_concl cl') (introid id) gl

TACTIC EXTEND ssrset
| [ "set" ssrfwdid(id) ssrsetfwd(fwd) ssrclauses(clauses) ] ->
  [ tclCLAUSES (ssrsettac id fwd) clauses ]    
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
| [ ":" lconstr(t) ssrhint(hint) ] -> [ mkFwdHint ":" t, hint ]
| [ ":" lconstr(t) ":=" lconstr(c) ] -> [ mkFwdCast FwdHave loc t c, nohint ]
| [ ":=" lconstr(c) ] -> [ mkFwdVal FwdHave c, nohint ]
END

(* Tactic. *)

let basecuttac name c = apply (mkApp (mkSsrConst name, [|c|]))

let havegentac c gl =
  let c' = pf_abs_ssrterm gl c in
  apply_type (mkArrow (pf_type_of gl c') (pf_concl gl)) [c'] gl

let havetac clr pats (((fk, _), c), hint) =
 let itac = tclTHEN (cleartac clr) (introstac pats) in
 if fk = FwdHave then tclTHEN (havegentac c) itac else
 let ctac gl = basecuttac "ssr_have" (pf_prod_ssrterm gl c) gl in
 tclTHENS ctac [hinttac hint; itac]

TACTIC EXTEND ssrhave
| [ "have" ssrclear(clr) ssrhpats(pats) ssrhavefwd(fwd) ] ->
  [ havetac clr pats fwd ]
END

(** The "suffice" tactic *)

ARGUMENT EXTEND ssrsufffwd
       TYPED AS ssrhavefwd      PRINTED BY pr_closed_ssrhavefwd
   RAW_TYPED AS ssrhavefwd  RAW_PRINTED BY pr_raw_ssrhavefwd
  GLOB_TYPED AS ssrhavefwd GLOB_PRINTED BY pr_glob_ssrhavefwd
| [ ":" lconstr(t) ssrhint(hint) ] ->[ mkFwdHint ":" t, hint ]
END

let sufftac clr pats ((_, c), hint) =
  let htac = tclTHEN (introstac pats) (hinttac hint) in
  let ctac gl = basecuttac "ssr_suff" (pf_prod_ssrterm gl c) gl in
  tclTHENS ctac [htac; cleartac clr]

TACTIC EXTEND ssrsuff
| [ "suff" ssrclear(clr) ssrhpats(pats) ssrsufffwd(fwd) ] ->
  [ sufftac clr pats fwd ]
END

TACTIC EXTEND ssrsuffices
| [ "suffices" ssrclear(clr) ssrhpats(pats) ssrsufffwd(fwd) ] ->
  [ sufftac clr pats fwd ]
END

(** The "wlog" (Without Loss Of Generality) tactic *)

type ssrwgen = ssrclear * ssrhyp

let pr_wgen (clr, hyp) = spc () ++ pr_clear mt clr ++ pr_hyp hyp
let pr_ssrwgen _ _ _ = pr_wgen

ARGUMENT EXTEND ssrwgen TYPED AS ssrclear * ssrhyp PRINTED BY pr_ssrwgen
| [ ssrclear(clr) ssrhyp(id) ] -> [ clr, id ]
END

type ssrwlogfwd = ssrwgen list * ssrfwd

let pr_ssrwlogfwd pr_fwd prc prlc prt (gens, t) =
  str ":" ++ pr_list mt pr_wgen gens ++ spc() ++ pr_fwd prc prlc prt t

let pr_closed_ssrwlogfwd = pr_ssrwlogfwd pr_closed_ssrfwd
let pr_glob_ssrwlogfwd   = pr_ssrwlogfwd pr_glob_ssrfwd
let pr_raw_ssrwlogfwd    = pr_ssrwlogfwd pr_raw_ssrfwd

ARGUMENT EXTEND ssrwlogfwd
       TYPED AS ssrwgen list * ssrfwd      PRINTED BY pr_closed_ssrwlogfwd
   RAW_TYPED AS ssrwgen list * ssrfwd  RAW_PRINTED BY pr_raw_ssrwlogfwd
  GLOB_TYPED AS ssrwgen list * ssrfwd GLOB_PRINTED BY pr_glob_ssrwlogfwd
| [ ":" ssrwgen_list(gens) "/" lconstr(t) ] -> [ gens, mkFwdHint "/" t]
END

let wlogtac clr0 pats (gens, (_, ct)) hint gl =
  let mkabs (_, SsrHyp (_, x)) = mkNamedProd x (pf_get_hyp_typ gl x) in
  let mkclr (clr, x) clrs = cleartac clr :: cleartac [x] :: clrs in
  let mkpats (_, SsrHyp (_, x)) pats = IpatId x :: pats in
  let cl0 = mkArrow (pf_prod_ssrterm gl ct) (pf_concl gl) in
  let c = List.fold_right mkabs gens cl0 in
  let tac2clr = List.fold_right mkclr gens [cleartac clr0] in
  let tac2ipat = introstac (List.fold_right mkpats gens pats) in
  let tac2 = tclTHENLIST (List.rev (tac2ipat :: tac2clr)) in
  tclTHENS (basecuttac "ssr_wlog" c) [hinttac hint; tac2] gl

TACTIC EXTEND ssrwlog
| [ "wlog" ssrclear(clr) ssrhpats(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ wlogtac clr pats fwd hint ]
END

TACTIC EXTEND ssrwithoutloss
| [ "without" "loss"
      ssrclear(clr) ssrhpats(pats) ssrwlogfwd(fwd) ssrhint(hint) ] ->
  [ wlogtac clr pats fwd hint ]
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
