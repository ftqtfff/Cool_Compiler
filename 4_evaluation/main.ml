open Printf

let do_debug = ref false

type static_type = (* the static type of a Cool expression *)
  | Class of string (* string denotes the type/class name, such as "Object", "Int" ... *) 
  | SELF_TYPE of string (* SELF_TYPE_c *)

let type_to_str t = match t with
  | Class(x) -> x
  | SELF_TYPE(c) -> "SELF_TYPE"

let type_to_class t = 
  match t with
  | SELF_TYPE(c) -> (Class c)
  | Class(c) -> (Class c)

let run_time_error ln msg = 
  printf "ERROR: %s: Exception: %s\n" ln msg ;
  exit 1 ;

type loc = string
type id = loc * string
type cool_type = id 

type cool_program = (cool_class list)
and cool_class = cool_type * (cool_type option) * (feature list)  
and feature = 
  | Attribute of id * cool_type * (exp option)
  | Method of id * (formal list) * cool_type * exp
and formal = id * cool_type
and letBinding = id * cool_type * (exp option)
and caseElem = id * cool_type * exp

and exp = {
  loc : loc ; 
  exp_kind : exp_kind ;
  static_type : static_type ; (* should it be mutable though? probably not *)
}
and exp_kind = 
  | Assign of id * exp
  | Integer of Int32.t
  | String of Int32.t * string
  | Identifier of id
  | Dynamic_dispatch of exp * id * (exp list)
  | Static_dispatch of exp * cool_type * id * (exp list)
  | Self_dispatch of id * (exp list)
  | If of exp * exp * exp
  | While of exp * exp
  | Block of (exp list)
  | New of cool_type
  | Isvoid of exp
  | Plus of exp * exp
  | Minus of exp * exp 
  | Times of exp * exp
  | Divide of exp * exp
  | Lt of exp * exp
  | Le of exp * exp
  | Equals of exp * exp
  | Not of exp
  | Negate of exp
  | True
  | False
  | Let of (letBinding list) * exp 
  | Case of exp * (caseElem list)
  | Internal of string * string

(* this is the incomplete definition from the video *)
(* used for new exp*)
(* 
and class_map = (string * ((string * exp) list)) list 
 *)
(* used for dispatch exp *)

(* 
and imp_map = 
  ( (string * string)
  *
  ((string list) * exp) ) list  
*)

type cool_class_map = (string * (cm_attr list)) list
and cm_attr = string * string * string * ( exp option ) 

(* in the video, imp_map[cname, mname] -> formal_params, method_body *)
type cool_imp_map = (string * (im_method list)) list
and im_method = string * ((string list) * string * exp)


type cool_parent_map = 
  (string * string) list

type cool_address = int
type cool_value = 
  | Cool_Int of Int32.t
  | Cool_Bool of bool
  | Cool_String of Int32.t * string
  | Cool_Object of string * ((string * cool_address) list)
  | Void (* of cool_value *)

let str_to_cool_str str = 
  let l = Int32.of_int (String.length str) in
  Cool_String(l, str)
  

(************************************************************************************)
(*                                Debugging and Tracing                             *)
(************************************************************************************)


let debug fmt = 
  let handle result_string = 
    if !do_debug then printf "%s" result_string
  in
  kprintf handle fmt

(* cheating func to help us pass typechecker *)
let exp_kind_to_exp e_kind = 
  let fake_exp = {
    loc = "0"; (* we dont care *)
    exp_kind = e_kind ;
    static_type = Class("Int") ; (* we dont care *)
  } in 
  fake_exp

let rec exp_to_str e = 
  match e.exp_kind with 
  | Assign(id, exp) -> sprintf "Assign(%s, %s)" (id_to_str id) (exp_to_str exp)
  | Integer(i) -> sprintf "Integer(%ld)" i
  | String(l, str) -> sprintf "String(%ld, %s)" l str 
  | Identifier(id) -> sprintf "Identifier(%s)" (id_to_str id)
  | Static_dispatch(ro, typ, func_name, args) -> 
    let arg_str = List.fold_left (fun acc element ->
        acc ^ ", " ^ (exp_to_str element)
      ) "" args in
    sprintf "Static_Dispatch(%s @ %s . %s, [%s])" (exp_to_str ro) (id_to_str typ) (id_to_str func_name) arg_str
  | Dynamic_dispatch(receiver_obj, func_name, args) ->
    let arg_str = List.fold_left (fun acc element ->
        acc ^ ", " ^ (exp_to_str element)
      ) "" args in
    sprintf "Dispatch(%s, %s, [%s])" (exp_to_str receiver_obj) (id_to_str func_name) arg_str
  | Self_dispatch(func_name, args) -> 
      let arg_str = List.fold_left (fun acc element ->
        acc ^ ", " ^ (exp_to_str element)
      ) "" args in
    sprintf "Self_dispatch(%s, [%s])" (id_to_str func_name) arg_str
  | Block(exps) ->
    sprintf "Block of Expressions"
  | New(s) -> sprintf "New(%s)" (id_to_str s)
  | Plus(e1, e2) -> sprintf "Plus(%s, %s)" (exp_to_str e1) (exp_to_str e2)
  | Not(e1) -> sprintf "Not(%s)" (exp_to_str e1)
  | Equals(e1, e2) -> sprintf "Equals(%s, %s)" (exp_to_str e1) (exp_to_str e2)
  | Internal(iclass, imethod) -> sprintf "Internal(%s.%s)" iclass imethod
  | Let(binding_list, exp) -> sprintf "Let"
  | If(e1, e2, e3) -> sprintf "IF(%s, %s, %s)" (exp_to_str e1) (exp_to_str e2) (exp_to_str e3)
  | While(e1, e2) -> sprintf "While(%s, %s)" (exp_to_str e1) (exp_to_str e2)
  | _ -> sprintf "UNDEFINED EXP \n" 
and id_to_str (loc, id) = 
  id

let value_to_str v = 
  match v with 
  | Cool_Int(i) -> sprintf "Int(%ld)" i
  | Cool_Bool(b) -> sprintf "Bool(%b)" b
  | Cool_String(len, s) -> sprintf "String(%ld, %s)" len s 
  | Void -> sprintf "Void"
  | Cool_Object(cname, attrs) -> 
    let attr_str = List.fold_left (fun acc (aname, aaddr) ->
        sprintf "%s, %s = %d" acc aname aaddr
      ) "" attrs in 
    sprintf "%s([%s])" cname attr_str

let env_to_str env = 
  let binding_str = List.fold_left (fun acc (aname, aaddr) ->
      sprintf "%s, %s = %d" acc aname aaddr
    ) "" (List.sort compare env) in 
  sprintf "[%s]" binding_str

let store_to_str store = 
  let binding_str = List.fold_left (fun acc (addr, cvalue) ->
      sprintf "%s, %d = %s" acc addr (value_to_str cvalue)
    ) "" (List.sort compare store) in 
  sprintf "[%s]" binding_str

let indent_count = ref 0 
let debug_indent () = 
  debug "%s" (String.make !indent_count ' ')


type environment = (string * cool_address) list 
type store = (cool_address * cool_value) list 

let new_location_counter = ref 1000 
let newloc () = 
  incr  new_location_counter ; 
  !new_location_counter

(************************************************************************************)
(*                                       MAIN                                       *)
(************************************************************************************)
let main () = begin
  (* input is the .cl-type file *)
  let fname = Sys.argv.(1) in
  let fin = open_in fname in

  let read () =   (* read a line from the input file *)
    input_line fin
  in
  let rec range k =   (* range ke function generates a list of [k, k-1, ..., 1] *)
    if k <= 0 then []
    else k :: (range(k-1))
  in
  let read_list worker =
    let k = int_of_string (read()) in (* Read the number of elements *)
    (* printf "read_list of %d\n" k;  *) (* k is the number of elements *)
    let lst = range k in
    List.map(fun _ -> worker ()) lst (* return a list here for each element, we apply the worker function once *)
  in
  let rec read_ast () = 
    (* printf "reading annotated ast \n" ;  *)
    read_list read_cool_class
  and read_id () = 
    let loc = read() in
    let name = read() in
    (loc, name)
  and read_cool_class () = 
    let cname = read_id () in
    let inherits = match read() with
      | "no_inherits" -> None
      | "inherits"  ->  
        let super = read_id () in  (* parent class *)
        Some(super)
      | x->failwith("cannot happen: read_cool_class ()" ^x)
    in
    let features = read_list read_feature in
    (cname, inherits, features)
  and read_feature () = 
    match read() with 
    | "attribute_no_init" ->
      let fname = read_id ()  in  (* feature name *)
      let ftype = read_id ()  in
      Attribute (fname, ftype, None)
    | "attribute_init"  ->
      let fname = read_id ()  in (* feature name *)
      let ftype = read_id ()  in
      let finit = read_exp () in
      Attribute (fname, ftype, (Some finit))
    | "method"  ->
      let mname = read_id ()  in
      let formals = read_list read_formal in
      let mtype = read_id ()  in
      let mbody = read_exp () in 
      Method (mname, formals, mtype, mbody) (* mtype means the method's return type *)
    | x-> failwith("cannot happen: " ^ x)
  and read_formal () =
    let fname = read_id () in 
    let ftype = read_id () in
    (fname,ftype)
  and read_letBinding () =
    match read() with 
    | "let_binding_no_init" ->
      let bVar = read_id () in
      let bTyp = read_id () in
      (bVar, bTyp, None)      
    | "let_binding_init" -> 
      let bVar = read_id () in 
      let bTyp = read_id () in
      let bExp = read_exp () in
      (bVar, bTyp, (Some bExp))
    | x -> failwith("letBinding error")
  and read_caseElem () =      
    let caseVar = read_id () in
    let caseTyp = read_id () in
    let caseValue = read_exp () in
    (caseVar, caseTyp, caseValue)
  and read_internal () = 
    let line = read () in 
    let lst = String.split_on_char '.' line in 
    match lst with
    | [iclass; imethod] -> 
      (iclass, imethod)
    | _ -> failwith "internal expression was bad!\n"  
  and read_exp () = 
    let eloc = read () in
    let etype = read () in 
    let ekind = match read () with 
      | "integer" ->
        let ival = read () in
        Integer(Int32.of_string ival)
      | "string" ->
        let str = read () in
        let l =  Int32.of_int (String.length str) in 
        String(l, str)
      | "identifier" ->
        let ivar = read_id () in
        Identifier(ivar)
      | "plus" -> 
        let a = read_exp () in
        let b = read_exp () in
        Plus(a, b)
      | "minus" ->
        let a = read_exp () in
        let b = read_exp () in
        Minus(a, b)
      | "times" ->
        let a = read_exp () in
        let b = read_exp () in
        Times(a, b)
      | "divide" -> 
        let a = read_exp () in
        let b = read_exp () in
        Divide(a, b)
      | "assign" ->
        let a = read_id () in
        let rhs = read_exp () in
        Assign(a, rhs)
      | "dynamic_dispatch" ->
        let e = read_exp () in
        let met = read_id () in
        let argList = read_list read_exp in  
        Dynamic_dispatch(e, met, argList)
      | "static_dispatch" -> 
        let e = read_exp () in
        let typ = read_id () in
        let met = read_id () in
        let argList = read_list read_exp in
        Static_dispatch(e, typ, met, argList)
      | "self_dispatch" ->
        let met = read_id () in
        let argList = read_list read_exp in
        Self_dispatch(met, argList)
      | "if" ->
        let predicate = read_exp () in
        let the = read_exp () in
        let els = read_exp () in
        If(predicate, the, els)
      | "while" ->
        let predicate = read_exp () in
        let body = read_exp () in
        While(predicate, body)
      | "block" ->
        let bodyList = read_list read_exp in
        Block(bodyList)
      | "new" ->
        let clas = read_id () in
        New(clas)
      | "isvoid" ->
        let e = read_exp () in
        Isvoid(e)
      | "lt" ->
        let a = read_exp () in
        let b = read_exp () in
        Lt(a,b)
      | "le" ->
        let a = read_exp () in
        let b = read_exp () in
        Le(a,b)
      | "eq" ->
        let a = read_exp () in
        let b = read_exp () in
        Equals(a,b)
      | "not" ->
        let a = read_exp () in 
        Not(a)
      | "negate" -> 
        let a = read_exp () in
        Negate(a)
      | "true" ->
        True
      | "false" -> 
        False
      | "let" -> 
        let bindingList = read_list read_letBinding in
        let letBody = read_exp () in
        Let(bindingList, letBody)
      | "case" ->
        let caseExpr = read_exp () in
        let caseElemList = read_list read_caseElem in
        Case(caseExpr, caseElemList)
      | "internal" -> 
        let iclass, imethod = read_internal () in 
        Internal(iclass, imethod)
      | x->(* SOMETHING *) failwith("Experession kind unbound : "^x)
    in 
    {
      loc = eloc ;
      exp_kind = ekind ;
      static_type = Class(etype) ;
    }
  in
  let rec read_cm () = 
    read_list read_cm_class
  and read_cm_class () = 
    let cname = read () in 
    let attrs = read_list read_cm_attr in
    (cname, attrs)
  and read_cm_attr () = 
    match read () with 
    | "no_initializer" -> 
      let aname = read () in
      let tname = read () in 
      ("no_initializer", aname, tname, None)
    | "initializer" -> 
      let aname = read () in
      let tname = read () in 
      let init_exp = read_exp () in 
      ("initializer", aname, tname, (Some init_exp))
    | x -> failwith("not possible")
  in
  let rec read_im () = 
    read_list read_im_class
  and read_im_class () = 
    let cname = read () in 
    let methods = read_list read_im_method in 
    (cname, methods)
  and read_im_method () = 
    let mname = read () in 
    let formals = read_list read in 
    let pcname = read () in
    let method_body_exp = read_exp () in
    (* printf "method name is: %s\n" mname;  *)
    (mname, (formals, pcname, method_body_exp))
  in
  let rec read_pm () = 
    read_list read_pairs
  and read_pairs () = 
    let ccname = read () in 
    let pcname = read () in 
    (ccname, pcname)
  in
  (* the first line is always "class_map", so we consume it *)



  let _ = read () in 

  let class_map = read_cm () in 

  let _ = read () in 

  let imp_map = read_im () in 

  let _ = read () in 

  let _ = read_pm () in 

  let _ = read_ast () in 
(*   printf "annotated ast done! \n" ;  *)

  (************************************************************************************)
  (*                                     Evaluation                                   *)
  (************************************************************************************)
  (* 
type environment = (string * cool_address) list 
type store = (cool_address * cool_value) list  
*)

  let rec eval (so : cool_value)        (* self object *)
      (s : store)             (* store; addresses -> value *)
      (e : environment)       (* env; var -> addresses *)
      (exp : exp)             (* expression to evaluate *)
    : (cool_value * store)  (* resulted value * updated store  *)
    = 
    indent_count := !indent_count + 2 ; 
    debug_indent () ; debug "eval: %s\n" (exp_to_str exp) ; 
    debug_indent () ; debug "self: %s\n" (value_to_str so) ; 
    debug_indent () ; debug "sto: %s\n" (store_to_str s) ; 
    debug_indent () ; debug "env: %s\n" (env_to_str e) ; 
    let new_value, new_store = match exp.exp_kind with 
    | Integer(i) -> Cool_Int(i), s 
    | String((l, str)) -> Cool_String(l, str), s 
    | Plus(e1, e2) -> 
      let v1, s2 = eval so s e e1 in 
      let v2, s3 = eval so s2 e e2 in 
      let result_value = match v1, v2 with 
        | Cool_Int(i1), Cool_Int(i2) -> 
          Cool_Int(Int32.add i1 i2)
        | _, _ -> failwith "error: plus "
      in
      result_value, s3 
    | Minus(e1, e2) -> 
      let v1, s2 = eval so s e e1 in 
      let v2, s3 = eval so s2 e e2 in 
      let result_value = match v1, v2 with 
        | Cool_Int(i1), Cool_Int(i2) -> 
          Cool_Int(Int32.sub i1 i2)
        | _, _ -> failwith "error: minus "
      in
      result_value, s3 
    | Times(e1, e2) -> 
      let v1, s2 = eval so s e e1 in 
      let v2, s3 = eval so s2 e e2 in 
      let result_value = match v1, v2 with 
        | Cool_Int(i1), Cool_Int(i2) -> 
          Cool_Int(Int32.mul i1 i2)
        | _, _ -> failwith "error: times "
      in
      result_value, s3 
    | Divide(e1, e2) -> 
      let v1, s2 = eval so s e e1 in 
      let v2, s3 = eval so s2 e e2 in 
      let result_value = match v1, v2 with 
        | _, Cool_Int(0l) -> run_time_error exp.loc "division by zero" 
        | Cool_Int(i1), Cool_Int(i2) -> 
          Cool_Int(Int32.div i1 i2)
        | _, _ -> failwith "error: divide "
      in
      result_value, s3 
    | Equals(e1, e2) -> 
      let v1, s2 = eval so s e e1 in 
      let v2, s3 = eval so s2 e e2 in 
      let result_value = match v1, v2 with 
        | Void, Void -> 
          Cool_Bool(true)
        | Void, _
        | _, Void -> 
          Cool_Bool(false)
        | Cool_Int(i1), Cool_Int(i2) -> 
          let i3 = (i1=i2) in
          Cool_Bool(i3)
        | Cool_String(_,i1), Cool_String(_,i2)->
          let i3 = (i1=i2) in
          Cool_Bool(i3)
        | Cool_Bool(i1), Cool_Bool(i2)->
          let i3 = (i1=i2) in
          Cool_Bool(i3)
        | Cool_Object(_, _), Cool_Object(_, _) -> (* TODO: not correct, should compare pointer value for obj *)
          Cool_Bool(false)
        | _, _ -> failwith "error: le "
      in
      result_value, s3 
    | Le(e1, e2) -> 
      let v1, s2 = eval so s e e1 in 
      let v2, s3 = eval so s2 e e2 in 
      let result_value = match v1, v2 with 
        | Cool_Int(i1), Cool_Int(i2) -> 
          let i3 = (i1<=i2) in
          Cool_Bool(i3)
        | Cool_String(_,i1), Cool_String(_,i2)->
          let i3 = (i1<=i2) in
          Cool_Bool(i3)
        | Cool_Bool(i1), Cool_Bool(i2)->
          let i3 = (i1<=i2) in
          Cool_Bool(i3)
          | _, _ -> failwith "error: le "
      in
      result_value, s3 
    | Lt(e1, e2) -> 
      let v1, s2 = eval so s e e1 in 
      let v2, s3 = eval so s2 e e2 in 
      let result_value = match v1, v2 with 
        | Cool_Int(i1), Cool_Int(i2) -> 
          let i3 = (i1<i2) in
          Cool_Bool(i3)
        | Cool_String(_,i1), Cool_String(_,i2)->
          let i3 = (i1<i2) in
          Cool_Bool(i3)
        | Cool_Bool(i1), Cool_Bool(i2)->
          let i3 = (i1<i2) in
          Cool_Bool(i3)
        | _, _ -> failwith "error: lt "
      in
      result_value, s3 
    | Not(e1) -> 
      let v1, s2 = eval so s e e1 in 
      let result_value = match v1 with 
        | Cool_Bool(true) -> Cool_Bool(false)
        | Cool_Bool(false) -> Cool_Bool(true)
        | _ -> begin
          printf "error %s\n" (exp_to_str e1) ;
          failwith "error: Not "  ;
        end
      in
      result_value, s2
    | Negate(e1) -> 
      let v1, s2 = eval so s e e1 in 
      let result_value = match v1 with 
        | Cool_Int(i1) -> 
          Cool_Int(Int32.neg i1)
        | _ -> failwith "error: Neg "
      in
      result_value, s2
    | If(e1,e2,e3) -> 
      let v1, s2 = eval so s e e1 in 
      let result_value,s_pos = match v1 with 
        | Cool_Bool(true) -> 
          let v2, s3 = eval so s2 e e2 in 
          v2,s3
        | Cool_Bool(false) -> 
          let v3, s3 = eval so s2 e e3 in 
          v3,s3
        | _ -> failwith "error: If "
      in
      result_value, s_pos
   | While(e1, e2) ->
      let v1, s2 = eval so s e e1 in 
      let s_pos = match v1 with 
        | Cool_Bool(true) -> 
          let v2, s3 = eval so s2 e e2 in 
          let fake_exp = {
            loc = "0"; (* we dont care *)
            exp_kind = While (e1,e2)  ;
            static_type = Class("Int") ; (* we dont care *)
          } in 
          let v3,s4 = eval so s3 e fake_exp in
          s4
        | Cool_Bool(false) -> 
          s2
        | _ -> failwith "error: while "
      in
      Void, s_pos
    | Isvoid(e1) -> 
      let v1, s2 = eval so s e e1 in 
      let result_value = match v1 with 
        | Void -> 
          Cool_Bool(true)
        | _ -> Cool_Bool(false)
      in
      result_value, s2
    | Assign((loc, vname), rhs) -> 
      let v1, s2 = eval so s e rhs in 
      let l1 = List.assoc vname e in (* this is effectively environment[vname] *)
      let s3 = (l1, v1) :: (List.remove_assoc l1 s2) in
      v1, s3 
    | New((loc, typ)) -> (* TODO: missing rules for self type !*)
      let cname = match so with 
        | Cool_Object(so_typ, _) -> 
          if typ = "SELF_TYPE" then so_typ
          else typ
        | _ -> typ 
      in
      let attrs_and_inits = List.assoc cname class_map in  (* TODO: what if cannot find cname? *)
      let new_attr_locs = List.map( fun (has_init, aname, atype, ainit) -> 
          newloc () 
        ) attrs_and_inits in 
      let attr_names = List.map( fun (_, aname, _, _) -> 
          aname) attrs_and_inits in 
      let attr_types = List.map( fun (_, _, atype, _) -> 
          atype) attrs_and_inits in 
      let attrs_and_locs = List.combine attr_names new_attr_locs in 
      let v1 = Cool_Object(cname, attrs_and_locs) in 
      let attr_locs_and_types = List.combine new_attr_locs attr_types in 
      let store_updates = List.map (fun (loc, typ) -> 
          match typ with 
          | "Int" -> (loc, Cool_Int(0l))   
          | "Bool" -> (loc, Cool_Bool(false))
          | "String" -> (loc, Cool_String((Int32.of_int 0), ""))
          | _ -> (loc, Void)
        ) attr_locs_and_types in 
      let s2 = s @ store_updates in 
      let tmp_store = ref s2 in 
      let final_store = List.fold_left ( fun accumulated_store (_, aname, _, ainit) -> 
        match ainit with 
        | Some(init) -> begin
          let assign_exp = {
            loc = "0"; 
            exp_kind = Assign(("0", aname), init);
            static_type = Class("String");
          } in 
          let _, tmp_store = eval v1 accumulated_store attrs_and_locs assign_exp in 
            tmp_store
        end
        | None -> !tmp_store

        ) s2 attrs_and_inits in 
      v1, final_store
    | Identifier((loc, vname)) -> 
      begin
        match vname with 
        | "self" -> 
          so, s
        | _ -> (
          let l = List.assoc vname e in
          let final_value = List.assoc l s in 
          final_value, s         
        )
      end

    | Static_dispatch(e0, (_, tname), (_, mname), input_args) ->  
      let current_store = ref s in 

      let arg_values = List.map (fun arg_exp ->
        let arg_value, new_store = eval so !current_store e arg_exp in 
        current_store := new_store ;
        arg_value
      ) input_args in 
      let v0, s_n2 = eval so !current_store e e0 in 
    
      if v0 = Void then begin 
        run_time_error exp.loc "static dispatch on void"
      end; 

      begin match v0 with 
      | Cool_Object(ro_name, ro_attrs_and_locs) -> 
        let methods = List.assoc tname imp_map in 
        let (xi, pc_name, e_n1) = List.assoc mname methods in 
        let lxi = List.map (fun _ -> newloc()) xi in 
        if List.length lxi <> List.length arg_values then begin
          failwith "parameter count mismatch"
        end ;
        let store_updates = List.combine lxi arg_values in 
        let s_n3 = store_updates @ !current_store in 
        let x_env = List.combine xi lxi in 
        let new_env = x_env @ ro_attrs_and_locs in 
        eval v0 s_n3 new_env e_n1

      | _ -> failwith "Static dispatch: value not matched!"
      end



    | Self_dispatch((loc, mname), input_args) 
    | Dynamic_dispatch(_, (loc, mname), input_args) -> begin
      let current_store = ref s in 
      (* arg_values correspond to v1...vn *)
      let arg_values = List.map (fun arg_exp ->
        let arg_value, new_store = eval so !current_store e arg_exp in 
        current_store := new_store ;
        arg_value
      ) input_args in  (* !current_store = s_n in the CRM *)

      (* v0 is either a class (dynamic disp) or self_type (self disp) *)
      let v0 = match exp.exp_kind with 
      | Dynamic_dispatch(e0, _, _) ->
        let v0, s_n2 = eval so !current_store e e0 in
        current_store := s_n2 ;
        v0
      | _ -> so
      in
      if v0 = Void then begin 
        run_time_error exp.loc "dispatch on void"
      end; 

      begin match v0 with 
      | Cool_Object(ro_name, ro_attrs_and_locs) -> 
        let methods = List.assoc ro_name imp_map in 
        let (xi, pc_name, e_n1) = List.assoc mname methods in (* imp_map(ro_name, mname) = ((x1, ... , xn), _,  e_n1) *)
        let lxi = List.map (fun _ -> newloc()) xi in (* create location for each xi *)
        if List.length lxi <> List.length arg_values then begin
          failwith "parameter count mismatch"
        end ;
        let store_updates = List.combine lxi arg_values in 
        let s_n3 = store_updates @ !current_store in 
        let x_env = List.combine xi lxi in 
        let new_env = x_env @ ro_attrs_and_locs in 
        eval v0 s_n3 new_env e_n1
      | _ ->
        let obj_name = match v0 with 
        | Cool_String(l, str) -> "String"
        | Cool_Int(i) -> "Int"
        | _ -> failwith "Not valid dispatch targets"
        in 
        let methods = List.assoc obj_name imp_map in 
        let (xi, pc_name, e_n1) = List.assoc mname methods in
        let lxi = List.map (fun _ -> newloc()) xi in
        if List.length lxi <> List.length arg_values then begin
          failwith "parameter count mismatch"
        end;
        let store_updates = List.combine lxi arg_values in 
        let s_n3 = store_updates @ !current_store in 
        let x_env = List.combine xi lxi in 
        eval v0 s_n3 x_env e_n1

(* 
        printf "%s\n" str ;
        (v0, !current_store) *)
      | _ -> failwith "Dynamic dispatch: value not matched!"
      end
    end
    | True ->
      Cool_Bool(true), s 
    | False ->
      Cool_Bool(false), s 
    | Block(input_args) ->
      let current_store = ref s in 
      let arg_values = List.map (fun arg_exp ->
        let arg_value, new_store = eval so !current_store e arg_exp in 
        current_store := new_store ;
        arg_value
      ) input_args in
      let final_value = (List.hd (List.rev arg_values)) in 
      (final_value, !current_store)
    (*
      Let of (letBinding list) * exp 
      letBinding = id * cool_type * (exp option)
      type environment = (string * cool_address) list // cool_address == int 
    *)
    | Let(binding_list, let_body) ->  (* | Let((vloc, vname), (typeloc, typename), None, let_body) -> *)
           ( match binding_list with
           | [] -> 
             let (v2, s4) = eval so s e let_body in
             (v2, s4)
           | ((vloc, vname), (typeloc, typename), bExp) :: tail ->
               (
               let let_exp = {
                loc = exp.loc;
                exp_kind = Let (tail, let_body);
                static_type = exp.static_type ; 
               } in 
               match bExp with
               | None ->
                 let v1 = match typename with 
                  | "Int" -> Cool_Int(0l)  
                  | "Bool" -> Cool_Bool(false)
                  | "String" -> Cool_String((Int32.of_int 0), "")
                  | _ -> Void
                 in 
                 let l1 = newloc () in
                 let s3 = s @ ((l1, v1) :: []) in
                 let e_prime = 
                     if List.mem_assoc vname e then begin
                        List.map ( fun (id, addr) ->
                        if id = vname then
                            (id, l1)
                        else
                            (id, addr)
                        )e
                     end
                     else 
                       e @ ((vname, l1)  :: [])
                 in 
                 let (v2, s4) = eval so s3 e_prime let_exp in
                 (v2, s4)
               | Some(bExpOpt) ->
                 let (v1, s2) = eval so s e bExpOpt in
                 let l1 = newloc () in
                 let s3 = s2 @ ((l1, v1) :: []) in
                 let e_prime = 
                     if List.mem_assoc vname e then begin
                        List.map ( fun (id, addr) ->
                        if id = vname then
                            (id, l1)
                        else
                            (id, addr)
                        )e
                     end
                     else 
                       e @ ((vname, l1)  :: [])
                 in 
                 let (v2, s4) = eval so s3 e_prime let_exp in
                 (v2, s4)
               )  
           ) 


    | Internal(iclass, imethod) -> begin
      (* first find the argument to internal, ~= eval for Identifier *)
      let get x = 
        let l = List.assoc x e in 
        let final_value = List.assoc l s in 
        final_value
      in 
      match iclass, imethod with 
      | "Object", "abort" -> 
        begin
          printf "abort\n" ;
          exit 1 
        end

      | "Object", "type_name" ->
        begin
          let v_to_s v = 
            match v with 
            | Cool_Int(i) -> "Int"
            | Cool_Bool(b) -> "Bool"
            | Cool_String(len, s) -> "String"
            | Void -> "Void"
            | Cool_Object(cname, attrs) -> cname
          in
          let cool_str = (str_to_cool_str (v_to_s so)) in 
          cool_str, s
        end
      | "IO", "out_string" -> 
        begin
          match (get "x") with 
          | Cool_String(l, str) -> 
            let newline_regexp = Str.regexp (Str.quote "\\n") in
            let str = Str.global_replace newline_regexp "\n" str in
            let tab_regexp = Str.regexp (Str.quote "\\t") in
            let str = Str.global_replace tab_regexp "\t" str in
            printf "%s" str ; flush stdout ;
            so, s 
          | _ -> failwith "IO.out_string argument error!"
        end
      | "IO", "out_int" -> 
        begin
          match (get "x") with 
          | Cool_Int(i) -> 
            printf "%ld" i ; 
            so, s 
          | _ -> failwith "IO.out_int argument error!"
        end
      | "IO","in_int" -> begin
          try
            let all_input = (read_line()) in
            let lists = String.split_on_char ' ' all_input in
            let rec rm_space(t)=begin
              if(List.length t > 1) then begin
                if List.hd t = "" then rm_space(List.tl t)
                else t
              end 
              else begin
                if List.hd t = "" then ["0"] else t
              end
            end
            in
            let int_input = (List.hd (rm_space(lists))) in
            let t1=(int_of_string int_input) in
            let s1 = begin
              if t1 > 2147483647 || t1 < -2147483648 then Cool_Int(Int32.zero) else Cool_Int(Int32.of_int(t1))
            end
            in
            s1,s
          with _ ->
            Cool_Int(Int32.zero),s
        end
      | "IO","in_string" -> begin
          let str = (read_line()) in
          Cool_String((Int32.of_int(String.length str)), str), s  
        end
      | "String", "concat" -> 
        begin
          let str = match so with 
            | Cool_String(l, s) -> s 
            | _ -> failwith "concat error"
          in
          let newstr = match get("s") with 
            | Cool_String(l, s) -> s
            | _ -> failwith "concat error: argument must be a string"
          in
          let ret = String.concat str [""; newstr] in 
          Cool_String((Int32.of_int(String.length ret)), ret), s  
        end
      | "String", "substr" ->
        begin
          (* run_time_error "0" "String.substr out of range" *)
          let str = match so with 
            | Cool_String(l, s) -> s 
            | _ -> failwith "substring error"
          in
          let i = match get("i") with 
            | Cool_Int(i) -> i 
          in 
          let l = match get("l") with 
            | Cool_Int(i) -> i 
          in 
          try
            let substr = String.sub str (Int32.to_int i) (Int32.to_int l) in
            Cool_String((Int32.of_int(String.length substr)), substr), s  
          with
            | _ -> run_time_error exp.loc "String.substr out of range"
        end
      | _, _ -> failwith "Havent coded this internal function yet!"
    end
      
    | _ -> begin
        printf "unhandled expression %s\n" (exp_to_str exp) ;
        failwith "cannot evaluate: unhandled expression!" ;
      end
    in
    debug_indent () ; debug "ret: %s\n" (value_to_str new_value) ; 
    debug_indent () ; debug "outgoing store: %s\n" (store_to_str new_store) ;
    indent_count := !indent_count - 2 ; 
    ( new_value, new_store )
  in 

(*
Environment: COOL variable names -> COOL addresses
Store: COOL addresses -> COOL values
Class Map: Class Names -> (Attr Names, list of Attr Initializers)		!CHECK PA4
Imp Map: (Class Name, Method Name) -> (formal param names, method body)		!CHECK PA4
*)
  let new_exp = {
    loc = "0";
    exp_kind = New(("0", "Main")) ;
    static_type = Class("Object") ;
  } in 
  let dispatch_main = {
    loc = "0";
    exp_kind = Dynamic_dispatch(new_exp, ("0", "main"), []);
    static_type = Class("Object");
  } in

(*   debug "myexp = %s\n" (exp_to_str dispatch_main) ; *)
  let so = Void in 
  let store = [] in 
  let environment = [] in 
  let final_value, final_store = 
    eval so store environment dispatch_main in 
  debug "result = %s\n" (value_to_str final_value)


end;;
main() ;; (* invoke main function *)


