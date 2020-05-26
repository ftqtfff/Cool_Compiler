open Printf
type static_type = (* the static type of a Cool expression *)
  | Class of string (* string denotes the type/class name, such as "Object", "Int" ... *) 
  | SELF_TYPE of string (* SELF_TYPE_c *)

let type_to_str t = match t with
  | Class(x) -> x
  | SELF_TYPE(c) -> "SELF_TYPE"

let searchInheritanceTable inheritTbl className =
    if Hashtbl.mem inheritTbl className then 
       Hashtbl.find inheritTbl className
    else begin 
       printf "Class %s is not in the inheritanceTable\n" className;
       exit 1
    end

(*The function below recursively checks the next class in the inheritance table*)
let rec checkInheritanceCycle inheritTbl parentClassName startClassName = 
    if parentClassName = "" then false (* This means that startClassName = "Object" *)
    else
      if parentClassName = startClassName then
         true
      else 
         let nextClassName = searchInheritanceTable inheritTbl parentClassName in    
         checkInheritanceCycle inheritTbl nextClassName startClassName         

let rec checkDuplicateElem listName =
    match listName with
    | [] -> false
    | hd :: tl -> List.exists (fun listElem -> hd = listElem) tl || checkDuplicateElem tl

(* <= --- subtyping (Liskov Substitution Principle) *)
(* Int <= Object *)
(* String <= String *)
(* ColorPoint <= Point if ColorPoint inherits Point *)
let rec is_subtype inheritTbl t1 t2 =
(*Turn to Class style*)
  let t1Class = match t1 with
         | SELF_TYPE(c) -> (Class c)
         | Class(c) -> (Class c)

  in
  let t2Class = match t2 with 
         | SELF_TYPE(c) -> (Class c)
         | Class(c) -> (Class c)
              
  in
  match t1Class, t2Class with
  | Class(x), Class("Object") -> true (* true means that it is a subtype *)
  | Class("Object"), Class(y) when y <> "Object" -> false 
  | Class(x), Class(y) when x = y -> true 
  | Class(x), Class(y) when x <> y ->
    let t1ParentClass = Hashtbl.find inheritTbl x in
    is_subtype inheritTbl (Class t1ParentClass) (Class y) 
  | x, y -> 
    printf "is_subtype error\n";
    exit 1
  


let rec lub_type inheritTbl t1 t2  = 
(*Turn to Class style*)
     let t1Class = match t1 with
         | SELF_TYPE(c) -> (Class c)
         | Class(c) -> (Class c)
     in
     let t2Class = match t2 with 
         | SELF_TYPE(c) -> (Class c)
         | Class(c) -> (Class c)            
     in
     if is_subtype inheritTbl t1Class t2Class  then 
        t2Class
     else begin
        let t2ParentClass = searchInheritanceTable inheritTbl (type_to_str t2Class) in
        lub_type inheritTbl t1Class (Class t2ParentClass) 
     end
     
    
let rec lub_type_sequence inheritTbl hdType remainder  =  (* static_type, static_type list *)
    match remainder with
    | [] -> 
      hdType
    | newHdType :: tail ->
      let type_accu = lub_type inheritTbl hdType newHdType in
      lub_type_sequence inheritTbl type_accu tail

let typeNormalize t = 
    (*Turn to Class style*)
    match t with
         | SELF_TYPE(c) -> (Class c)
         | Class(c) -> (Class c)

type objectGlobal_environment = (static_type * string,  static_type) Hashtbl.t  (* ( (Class currentClassName), attrName), attrType *)
type methodGlobal_environment = ( static_type * string, (static_type list) * string ) Hashtbl.t (* ((Class currentClassName), methodName), (formalList type, returnType) *)
type classLocal_features = (string * string * string, bool) Hashtbl.t (* (className, "attr" or "meth", featureName), trueORfalse is used to store all feature names(attributes + methods) of a class excluding the ones inherited *)
type inheritance_table = (string, string) Hashtbl.t (* child className, parent className *) 

(* Cool Language Syntax Type *)
type cool_program = (cool_class list)
and loc = string (* loc = location *)
and id = loc * string
and cool_type = id
and cool_class = cool_type * (cool_type option) * (feature list)  
and feature = 
  | Attribute of id * cool_type * (exp option)
  | Method of id * (formal list) * cool_type * exp
and formal = id * cool_type
and binding = id * cool_type * (exp option)
and caseElem = id * cool_type * exp
and exp = {
      loc : loc ; 
      exp_kind : exp_kind ;
      mutable static_type : static_type option; (* this is a variable which can be changed *)
                                                (* Every expression node in our AST has this mutable static_type 
                                                 * annotation which we will fill in by typechecking. *)
}

and exp_kind = 
  | Assign of id * exp
  | Integer of string
  | String of string
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
  | Let of (binding list) * exp   (* e.g., let x : t <- e1 in e2 *)
  | Case of exp * (caseElem list)
  | Internal of cool_type * string * string (* (0, typeName), Class.method *)


let main () = begin
  (* De-serialize the CL-AST File : f_pa_name *)
  let f_pa_name = Sys.argv.(1) in
  let fin = open_in f_pa_name in

  let read () =   (* read a line from the input file *)
    input_line fin
  in
  let rec range k =   (* range ke function generates a list of [k, k-1, ..., 1] *)
    if k <= 0 then []
    else k :: (range(k-1))
  in
  let read_list worker =
    let k = int_of_string (read()) in (* Read the number of elements *)
    (* printf"read_list of %d\n" k; *)  (* k is the number of elements *)
    let lst = range k in
    List.map(fun _ -> worker ()) lst (* return a list here for each element, we apply the worker function once *)
  in
  
  (* Read in the CL-AST file without annotation (From PA3) *)
  let rec read_cool_program () =
    read_list read_cool_class
  
  and read_id () = 
    let loc = read() in
    let name = read() in
    (loc, name)

  and read_cool_class () = 
    let cname = read_id () in  (* cname means class name *)
    let inherits = match read() with
      | "no_inherits" -> None
      | "inherits"  ->  
        let super = read_id () in  (* parent class *)
        Some(super)
      | x->failwith("cannot happen: " ^x)
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

  and read_exp() =
    let eloc = read () in
    let ekind = match read () with  (* expression kind *)
      | "integer" ->
        let ival = read () in
        Integer(ival)
      | "string" ->
        let ival = read () in
        String(ival)
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
      | x->(* SOMETHING *) failwith("Experession kind unbound : "^x)
    in
    {
       loc = eloc ;
       exp_kind = ekind ;
       static_type = None ;
    }
 
  in  
  let ast = read_cool_program() in  (* ast stores the info of AST-file from PA3 *)
  close_in fin;  (* Finish reading the file AST without type annotation *)
  (* printf "CL-AST deserialised,  %d  classes\n" (List.length ast); *)
  (* all loc = 0 for basic classes *)
  let rec basic_ast = int_class :: string_class :: bool_class :: io_class :: object_class :: []  
  and int_class = ( ("0", "Int"), (Some ("0", "Object") ), int_features )
  and int_features = 
      (
       let int_attr_init =     
       {
        loc = "0" ;
        exp_kind = (Integer "0") ;
        static_type = Some(Class "Int") ;
       }
       in 
       (Attribute (("0", "self"), ("0", "SELF_TYPE"), (Some int_attr_init)) ) 
      ) :: [] 
      
  and string_class = ( ("0", "String"), (Some ("0", "Object")), string_features )
  and string_features =
      ( 
       let string_attr_init = 
       {
        loc = "0";
	exp_kind = (String "");
	static_type = Some(Class "String");
       }
       in
       (Attribute (("0", "self"), ("0", "SELF_TYPE"), (Some string_attr_init)) ) 
      ) ::
	  
      (
       let string_met_formals = (("0", "s"), ("0", "String")) :: [] in 
       let string_meth_mbody =        (* Interal = 0 * type * className * methodName *)
           {
            loc = "0";
            exp_kind = (Internal (("0", "String"), "String", "concat"));
            static_type = Some (Class "String") ;
           }
       in 
       (Method (("0", "concat"), string_met_formals, ("0", "String"), string_meth_mbody) ) 
      ) :: 

      (
       let string_met_formals = [] in
       let string_meth_mbody =
           {
            loc = "0";
            exp_kind = (Internal (("0", "Int"), "String", "length"));
            static_type = Some (Class "Int");
           } 
       in 
       (Method (("0", "length"), string_met_formals, ("0", "Int"), string_meth_mbody) ) 
      ) ::

      (
       let string_met_formals = (("0", "i"), ("0", "Int")) :: (("0", "l"), ("0", "Int")) :: [] in
       let string_meth_mbody =
           {
            loc = "0"; 
            exp_kind = ( Internal (("0", "String"), "String", "substr") );
            static_type = Some (Class "String");
           } 
       in
       (Method (("0", "substr"), string_met_formals, ("0", "String"), string_meth_mbody) ) 
      ) :: [] 
      
  and bool_class = ( ("0", "Bool"), (Some ("0", "Object") ), bool_features )
  and bool_features = 
      ( 
       let bool_attr_init = 
       {
        loc = "0";
        exp_kind = False;
        static_type = Some(Class "Bool");
       }
       in
       (Attribute (("0", "self"), ("0", "SELF_TYPE"), (Some bool_attr_init)) ) 
      ) :: []
       
  and io_class = ( ("0", "IO"), (Some ("0", "Object") ), io_features )
  and io_features = 
      (
       let io_met_formals = [] in 
       let io_meth_mbody =
           { 
            loc = "0";
            exp_kind = (Internal (("0", "Int"), "IO", "in_int"));
            static_type = Some (Class "Int");
           } 
       in   
       (Method (("0", "in_int"), io_met_formals, ("0", "Int"), io_meth_mbody) )
      ) ::

      (
       let io_met_formals = [] in 
       let io_meth_mbody = 
           {
            loc = "0";
            exp_kind = (Internal (("0", "String"), "IO", "in_string")); 
            static_type = Some (Class "String");
           }
       in   
       (Method (("0", "in_string"), io_met_formals, ("0", "String"), io_meth_mbody) )
      ) ::
 
      (
       let io_met_formals = (("0", "x"), ("0", "Int")) :: [] in 
       let io_meth_mbody = 
           {
            loc = "0";
            exp_kind = (Internal (("0", "SELF_TYPE"), "IO", "out_int"));
            static_type = Some (SELF_TYPE "IO"); 
           }
       in   
       (Method (("0", "out_int"), io_met_formals, ("0", "SELF_TYPE"), io_meth_mbody) )
      ) ::

      ( 
       let io_met_formals = (("0", "x"), ("0", "String")) :: [] in 
       let io_meth_mbody = 
          {
           loc = "0";
           exp_kind = (Internal (("0", "SELF_TYPE"), "IO", "out_string"));
           static_type = Some (SELF_TYPE "IO"); 
          }
       in   
       (Method (("0", "out_string"), io_met_formals, ("0", "SELF_TYPE"), io_meth_mbody) )
      ) :: []
      
  and object_class = ( ("0", "Object"), (Some ("0", "") ), object_features )
  and object_features =
      (
       let object_met_formals = [] in 
       let object_meth_mbody =
           { 
            loc = "0";
            exp_kind = (Internal (("0", "Object"), "Object", "abort"));
            static_type = Some (Class "Object");
           } 
       in   
       (Method (("0", "abort"), object_met_formals, ("0", "Object"), object_meth_mbody) )
      ) ::
 
      (
       let object_met_formals = [] in 
       let object_meth_mbody = 
          { 
            loc = "0";
            exp_kind = (Internal (("0", "SELF_TYPE"), "Object", "copy"));
            static_type = Some (SELF_TYPE "Object");
           } 
       in   
       (Method (("0", "copy"), object_met_formals, ("0", "SELF_TYPE"), object_meth_mbody) )
      ) ::

      ( 
       let object_met_formals = [] in 
       let object_meth_mbody = 
          {
           loc = "0";
           exp_kind = (Internal (("0", "String"), "Object", "type_name"));
           static_type = Some (Class "String");
          }
       in   
       (Method (("0", "type_name"), object_met_formals, ("0", "String"), object_meth_mbody) )
      ) :: []
    
  in
  let all_ast = basic_ast @ ast in (* @ means list concatenation, all_ast is used to fill all tables and for the final output *)
  let base_classes = List.map (fun ( (_,cname), _, _ )-> cname ) basic_ast in  (* Object is the root class *)
  let user_classes = List.map (fun ( (_,cname), _, _ )-> cname ) ast in (*   user_classes are the classes defined by users (other than base classes) *)
  let all_classes = base_classes @ user_classes in  
  let all_classes = List.sort compare all_classes in
  
  let inheritanceTable : inheritance_table = Hashtbl.create 255 in 
  List.iter (fun ((_, cname), inheritType, features) ->  (* fill the inheritanceTable from all_ast *)
      match inheritType with
      | None -> Hashtbl.add inheritanceTable cname "Object"
      | Some((parentLoc, parentType)) -> 
           if (List.mem parentType all_classes) || parentType = "" then
              Hashtbl.add inheritanceTable cname parentType
           else begin
              printf "ERROR: %s: Type-Check: class %s inherits from unknown class %s\n" parentLoc cname parentType;
              exit 1
           end
      ;
  ) all_ast;

   (* Check for redefined class *)
   let rec checkRedefinedClass listName =
   match listName with
   | [] -> ()
   | ((cloc, cname),_,_) :: tl -> 
     if (List.exists (fun ((clocList, cnameList),_,_) -> (locRecord:=clocList; cname = cnameList) ) tl) then begin
        printf "ERROR: %s: Type-Check: class %s redefined\n" !locRecord cname; 
        exit 1
     end
     else
        checkRedefinedClass tl
   
   and locRecord = ref "yes" in
   checkRedefinedClass all_ast
   ;

  (* Check for cycled inheritance error *)
  List.iter (fun className -> 
       if checkInheritanceCycle inheritanceTable (Hashtbl.find inheritanceTable className) className then begin
          printf "ERROR: 0: Type-Check: inheritance cycle: %s %s\n" (Hashtbl.find inheritanceTable className) className;
          exit 1
       end
       else ()  
  ) all_classes;



  (* check basic class inheritance errors *)
  List.iter(fun((cloc,cname),inherits,features) ->   (* class location, class name, inherits option, features *)
      match cname with
      | "Int" | "Bool" | "String" | "IO" ->
         printf "ERROR: %s: Type-Check: cannot redefine the class %s\n" cloc cname;
         exit 1
      | x -> ()
      ;
      match inherits with
      | None -> ()
      | Some(iloc, iname)  ->  (* inherited type *)
        match iname with
        | "Int" | "Bool" | "String"  -> 
          printf "ERROR: %s: Type-Check: class %s inherits from %s\n" iloc cname iname;
          exit 1
        | x -> ()
        ;
        if not (List.mem iname all_classes) then begin
          printf "ERROR: %s: Type-Check: inheriting from undefined class %s\n" iloc iname;
          exit 1
        end;
  ) ast;
  

  (* fill the classLocalTable, objectGlobalTable and methodGlobalTable *)
  (* the parent class of "Object" is "" *)
  (* Check for the duplicate attribute or method within the same class error, Check the redefine errors *)
  let classLocalTable : classLocal_features = Hashtbl.create 255 in
  let objectGlobalTable : objectGlobal_environment = Hashtbl.create 255 in  
  let methodGlobalTable : methodGlobal_environment = Hashtbl.create 255 in
  let rec getFormalTypeList formalList classN methodN = 
      match formalList with
      | [] -> []
      | ( (fLoc, fName), (fTypeLoc, fTypeName) ) :: tl -> 
        if fName = "self" then begin
           printf "ERROR: %s: Type-Check: class %s has method %s with formal parameter named self\n" fLoc classN methodN;
           exit 1  
        end
        ;
        if fTypeName = "SELF_TYPE" then begin
           printf "ERROR: %s: Type-Check: class %s has method %s with formal parameter of unknown type SELF_TYPE\n" fTypeLoc classN methodN;
           exit 1  
        end
        ;
        (Class fTypeName) :: getFormalTypeList tl classN methodN      
  in
  let rec parentTableFunc parentName startClassName =            
      if parentName = "" then
         ()
      else begin        
         parentTableFunc (searchInheritanceTable inheritanceTable parentName) startClassName;                     
         let _, _, feats = List.find( fun ((_,cnameInner),_,_) -> cnameInner = parentName ) all_ast in 
         List.iter (fun feat -> 
                    match feat with
                    | Attribute ((_, attrName), (_, attrType), _) when attrName <> "self" ->
                      if attrType = "SELF_TYPE" then
                         Hashtbl.add objectGlobalTable ((Class startClassName), attrName) (SELF_TYPE parentName) 
                      else
                         Hashtbl.add objectGlobalTable ((Class startClassName), attrName) (Class attrType) 

                    | Method((_, methName), formals, (_, methType), _) ->
                      let formalTypeList = getFormalTypeList formals parentName methName in
                      Hashtbl.add methodGlobalTable ((Class startClassName), methName) (formalTypeList, methType)
                    | x -> ()
                    ) feats ;        
      end
  in
  let currentTableFunc className =
      let _, _, feats = List.find( fun ((_,cnameInner),_,_) -> cnameInner = className ) all_ast in       
      List.iter (fun feat -> 
                 match feat with
                 | Attribute ((attrLoc, attrName), (_, attrType), _) ->
                   if Hashtbl.mem classLocalTable (className, "attr", attrName) then begin
                      printf "ERROR: %s: duplicate attribute %s in class %s\n" attrLoc attrName className;
                      exit 1 
                   end 
                   ;
                   Hashtbl.add classLocalTable (className, "attr", attrName) true;
                     
                  
                   if (not (List.mem className base_classes)) && attrName = "self" then begin
                      printf "ERROR: %s:  Type-Check: class %s has an attribute named self\n" attrLoc className;
                      exit 1 
                   end
                   ;
                   

                   if Hashtbl.mem objectGlobalTable ( (Class className), attrName) then begin
                      printf "ERROR: %s: Type-Check: class %s redefines attribute %s\n" attrLoc className attrName;
                      exit 1 
                   end
                   ;

                   if attrType = "SELF_TYPE" then
                      Hashtbl.add objectGlobalTable ((Class className), attrName) (SELF_TYPE className) 
                   else
                      Hashtbl.add objectGlobalTable ((Class className), attrName) (Class attrType)

                 | Method((methLoc, methName), formals, (methTypeLoc, methType), _) ->

                   if not (List.mem methType all_classes) && methType <> "SELF_TYPE" then begin
                      printf "ERROR: %s: Type-Check: class %s has method %s with unknown return type %s\n" methTypeLoc className methName methType; 
                      exit 1
                   end
                   ;
                   if Hashtbl.mem classLocalTable (className, "meth", methName) then begin
                      printf "ERROR: %s: duplicate method %s in class %s\n" methLoc methName className;
                      exit 1 
                   end 
                   ;
                   Hashtbl.add classLocalTable (className, "meth", methName) true
                   ;
                   
                   (* check duplicate formal elements *)
                   let rec checkDuplicateFormal listName =
                   match listName with
                   | [] -> ()
                   | (loc, name) :: tl -> 
                     if (List.exists (fun listElem -> (loc, name) = listElem) tl) then begin
                        printf "ERROR: %s: Type-Check: class %s has method %s with duplicate formal parameter named %s\n" loc className methName name; 
                        exit 1
                     end
                     else
                        checkDuplicateFormal tl
                   in
                   checkDuplicateFormal ( List.map (fun ((fLoc, fName), _) -> (fLoc, fName)) formals )
                   ;

                   let formalTypeList = getFormalTypeList formals className methName in
                   if Hashtbl.mem methodGlobalTable ( (Class className), methName) then begin
                      let argTypeList, retType = Hashtbl.find methodGlobalTable ( (Class className), methName) in
                      if argTypeList <> formalTypeList then begin
                         printf "ERROR: %s: Type-Check: class %s redefines method %s and changes number of formals\n" methLoc className methName;
                         exit 1 
                      end
                      ;
                      if retType <> methType then begin
                         printf "ERROR: %s: Type-Check: class %s redefines method %s and changes return type\n" methLoc className methName;
                         exit 1 
                      end
                   end
                   ;
                   Hashtbl.add methodGlobalTable ((Class className), methName) (formalTypeList, methType)                    
                 ) feats; 
      Hashtbl.add objectGlobalTable ((Class className), "self") (SELF_TYPE className)
  in  
  let tableFunc className = 
      parentTableFunc (searchInheritanceTable inheritanceTable className) className; (* add parentClass content *)
      currentTableFunc className  (* add currentClass content *)
  in 
  List.iter( fun ((cloc, cname),_,_) -> 
       tableFunc cname;
       (* Check for SELF_TYPE class *)
       if cname = "SELF_TYPE" then begin
          printf "ERROR: %s: Type-Check: class named %s\n" cloc cname;
          exit 1
       end
       ;      
       (* Check for a missing method main in class Main *) 
       if cname = "Main" then begin
           let _, _, feats = List.find(fun ((_,cname2),_,_) -> cname2 = "Main" ) all_ast in
           List.iter(fun feat -> 
                (match feat with
                | Method((_, "main"), mainFormals,_,_) ->
                if (List.length mainFormals) > 0 then begin
                   printf "ERROR: 0: Type-Check: class Main method main with 0 parameters not found\n" ;
                   exit 1
                end
                | _ -> ()
                )
           ) feats
           ;
           
           if not ( Hashtbl.mem methodGlobalTable ((Class cname), "main") ) then begin
              printf "ERROR: 0: Type-Check: class Main method main not found\n";
              exit 1
           end
      end
  ) all_ast;

  (* check for Main class *)
  if not (List.mem "Main" all_classes) then begin
     printf "ERROR: 0: Type-Check: class Main not found\n";
     exit 1
  end
  ;
  
   
    (* This is the time to do expression typechecking. 
     * We want to iterate over every class.
     *    Then over every feature.
     *         Then typechecking the expressions in that feature.
     *
     * We implement our expression typechecking procedure by reading the typing rules from CRM
     *
     * Every "line" in a typing rule corresponds to a line in your typechecking code.
     *)
     
    (* SELF_TYPE == any class that conforms to currentClass *)
    (* typecheck function is used to annotate the CL-AST file without type annotation *)
    let rec typecheck (o: objectGlobal_environment) (m : methodGlobal_environment) (currentClass : static_type)  (exp : exp) : static_type = 
     let static_type = match exp.exp_kind with
     | Identifier((vloc, vname)) -> 
         if Hashtbl.mem o ( (typeNormalize currentClass), vname) then begin
            let retStatic_type = Hashtbl.find o ( (typeNormalize currentClass), vname) in      
            retStatic_type     
         end
         else begin
            printf "ERROR: %s: Type-Check: unbound identifier %s\n" vloc vname;
            exit 1
         end
         
     | Assign((vloc, vname), expRHS) ->
         if vname = "self" then begin
            printf "ERROR: %s: Type-Check: cannot assign to %s\n" vloc vname;
            exit 1
         end
         ;
         let t = 
             if Hashtbl.mem o ( (typeNormalize currentClass), vname) then
                Hashtbl.find o ( (typeNormalize currentClass), vname)
             else begin
                printf "ERROR: %s: Type-Check: unbound identifier %s\n" vloc vname;
                exit 1
             end  
          in
          let t_prime = typecheck o m currentClass expRHS in 
          if is_subtype inheritanceTable t_prime t then
            t_prime
          else begin
            printf "ERROR: %s: Type-Check: %s does not conform to %s in assignment\n" expRHS.loc (type_to_str t_prime) (type_to_str t);
            exit 1
          end  
     | True -> (Class "Bool")
     | False -> (Class "Bool")     
     | Integer(i) -> (Class "Int")
     | String(i) -> (Class "String")
     | New((cloc, cname)) ->  (* class location, class name *)
          let t_prime = 
          if cname = "SELF_TYPE" then
            (SELF_TYPE (type_to_str (typeNormalize currentClass) ) )
          else       
            (Class cname)
          in
          t_prime
          
     | Dynamic_dispatch(e0, (fLoc, fName), argList) -> (* exp, id, exp list *)   
       let t0 = typecheck o m currentClass e0 in
       let argTypeList = List.map (fun arg -> typecheck o m currentClass arg ) argList in 
       let t0_prime = 
         if t0 = (SELF_TYPE (type_to_str (typeNormalize currentClass)) ) then
            (typeNormalize currentClass)
         else
            (typeNormalize t0)
       in 
       let argPrimeTypeList, returnPrimeType = 
         if Hashtbl.mem m (  t0_prime, fName) then
            Hashtbl.find m ( t0_prime, fName)
        else begin
            printf "ERROR: %s: Type-Check: unknown method %s in dispatch on %s\n" fLoc fName (type_to_str t0_prime);
            exit 1
        end 
       in
       if List.length argTypeList <> List.length argPrimeTypeList then begin
          printf "ERROR: %s: Type-Check: wrong number of actual arguments (%d vs. %d)\n" fLoc (List.length argTypeList) (List.length argPrimeTypeList);
          exit 1
       end
       ;
       let argID = ref 0 in
       List.iter2 (fun ti ti_prime ->
                       argID := !argID + 1
                       ; 
                       if is_subtype inheritanceTable ti ti_prime then
                          ()
                       else begin
                          let tiString = 
                              match ti with
                              | Class(x) -> x
                              | SELF_TYPE(x) -> "SELF_TYPE("^x^")" 
                          in
                          let ti_primeString = 
                              match ti_prime with
                              | Class(x) -> x
                              | SELF_TYPE(x) -> "SELF_TYPE("^x^")" 
                          in
                          printf "ERROR: %s: Type-Check: argument #%d type %s does not conform to formal type %s\n" fLoc !argID tiString ti_primeString;
                          exit 1
                       end
                  ) 
       argTypeList argPrimeTypeList
       ;
       let tnPlus1 = 
           if returnPrimeType = "SELF_TYPE" then
               t0
              (*(SELF_TYPE "SELF_TYPE" )*)
           else
              (Class returnPrimeType)
       in 
       tnPlus1

      | Self_dispatch((fLoc, fName), argList) ->
        let argTypeList = List.map (fun arg -> typecheck o m currentClass arg ) argList in 
        let t0 = (SELF_TYPE (type_to_str (typeNormalize currentClass))) in
        let t0_prime = (typeNormalize currentClass) in
        let argPrimeTypeList, returnPrimeType = 
          if Hashtbl.mem m ( t0_prime, fName) then
             Hashtbl.find m ( t0_prime, fName)
          else begin
             printf "ERROR: %s: Type-Check: unknown method %s in dispatch on %s\n" fLoc fName (type_to_str t0_prime);
             exit 1
          end 
        in
        if List.length argTypeList <> List.length argPrimeTypeList then begin
           printf "ERROR: %s: Type-Check: wrong number of actual arguments (%d vs. %d)\n" fLoc (List.length argTypeList) (List.length argPrimeTypeList);
          exit 1
        end
        ;
        let argID = ref 0 in
        List.iter2 (fun ti ti_prime -> 
                        argID := !argID + 1
                        ; 
                        if is_subtype inheritanceTable ti ti_prime then
                           ()
                        else begin
                          let tiString = 
                              match ti with
                              | Class(x) -> x
                              | SELF_TYPE(x) -> "SELF_TYPE("^x^")" 
                          in
                          let ti_primeString = 
                              match ti_prime with
                              | Class(x) -> x
                              | SELF_TYPE(x) -> "SELF_TYPE("^x^")" 
                          in
                          printf "ERROR: %s: Type-Check: argument #%d type %s does not conform to formal type %s\n" fLoc !argID tiString ti_primeString;
                          exit 1
                        end
                   ) 
        argTypeList argPrimeTypeList
        ;
        let tnPlus1 = 
           if returnPrimeType = "SELF_TYPE" then
               t0
              (*(SELF_TYPE "SELF_TYPE" )*)
           else
              (Class returnPrimeType)
        in 
        tnPlus1
       
      | Static_dispatch(e0, (tLoc, tName), (fLoc, fName), argList) ->  
       let t0 = typecheck o m currentClass e0 in
       let argTypeList = List.map (fun arg -> typecheck o m currentClass arg ) argList in
       let t = (Class tName) in
       if is_subtype inheritanceTable t0 t then
         ()
       else begin
         let t0String = 
             match t0 with
            | Class(x) -> x
            | SELF_TYPE(x) -> "SELF_TYPE("^x^")" 
         in
         let tString = 
             match t with
            | Class(x) -> x
            | SELF_TYPE(x) -> "SELF_TYPE("^x^")" 
         in
         printf "ERROR: %s: Type-Check: %s does not conform to %s in static dispatch\n" tLoc t0String tString ;
         exit 1
       end
       ;
       let argPrimeTypeList, returnPrimeType = 
         if Hashtbl.mem m ((typeNormalize t), fName) then
            Hashtbl.find m ((typeNormalize t), fName)
        else begin
            printf "ERROR: %s: Type-Check: unknown method %s in dispatch on %s\n" fLoc fName (type_to_str t) ;
            exit 1
        end 
       in
       if List.length argTypeList <> List.length argPrimeTypeList then begin
          printf "ERROR: %s: Type-Check: wrong number of actual arguments (%d vs. %d)\n" fLoc (List.length argTypeList) (List.length argPrimeTypeList);
          exit 1
       end
       ;
       let argID = ref 0 in
       List.iter2 (fun ti ti_prime ->
                       argID := !argID + 1
                       ;  
                       if is_subtype inheritanceTable ti ti_prime then
                          ()
                       else begin
                          let tiString = 
                              match ti with
                              | Class(x) -> x
                              | SELF_TYPE(x) -> "SELF_TYPE("^x^")" 
                          in
                          let ti_primeString = 
                              match ti_prime with
                              | Class(x) -> x
                              | SELF_TYPE(x) -> "SELF_TYPE("^x^")" 
                          in
                          printf "ERROR: %s: Type-Check: argument #%d type %s does not conform to formal type %s\n" fLoc !argID tiString ti_primeString;
                          exit 1
                       end
                  ) 
       argTypeList argPrimeTypeList
       ;
       let tnPlus1 = 
           if returnPrimeType = "SELF_TYPE" then
               t0 
              (*(SELF_TYPE "SELF_TYPE")*)
           else
              (Class returnPrimeType)
       in 
       tnPlus1 
       
     | If(e1, e2, e3) ->     
       let t1 = typecheck o m currentClass e1 in
       if t1 <> (Class "Bool") then begin
          printf "ERROR: %s: Type-Check: conditional has type %s instead of Bool\n" 
             exp.loc (type_to_str t1) ;
          exit 1
       end;
       let t2 = typecheck o m currentClass e2 in
       let t3 = typecheck o m currentClass e3 in
       lub_type inheritanceTable t2 t3 
       
     | Block(bodyList) ->   
       let typeList = List.map(fun bodyElem -> typecheck o m currentClass bodyElem ) bodyList in
       let tn = List.hd (List.rev typeList) in
       tn

     | Let(binding_list, let_body) ->  (* | Let((vloc, vname), (typeloc, typename), None, let_body) -> *)
          ( match binding_list with
           | [] -> 
             let letBodyType = typecheck o m currentClass let_body in
             letBodyType
           | ((vloc, vname), (typeloc, typename), bExp) :: tail ->
               if vname = "self" then begin
                  printf "ERROR: %s: Type-Check: binding self in a let is not allowed\n" vloc;
                  exit 1
               end
               ;
               if (List.mem typename all_classes) || typename = "SELF_TYPE" then
                  ()
               else begin
                  printf "ERROR: %s: Type-Check: unknown type %s\n" typeloc typename; 
                  exit 1
               end
               ;
               match bExp with
               | None ->
                 let t0_prime = 
                   if typename = "SELF_TYPE" then
                      (SELF_TYPE (type_to_str (typeNormalize currentClass)) )
                      (*(SELF_TYPE "SELF_TYPE" )*)
                   else (Class typename) 
                 in
                 Hashtbl.add o ( (typeNormalize currentClass), vname) t0_prime ; (* add vname to o -- add it to the object environment *)
                 let tailExp  = 
                 {
                   loc = exp.loc ;
                   exp_kind = Let(tail, let_body);
                   static_type = exp.static_type ;
                 } 
                 in
                 let t1 = typecheck o m currentClass tailExp in
                 Hashtbl.remove o ((typeNormalize currentClass), vname) ; (* remove the type assignment in the object environment *)
                 t1
               | Some(bExpOpt) -> 
                 let t0_prime = 
                   if typename = "SELF_TYPE" then
                      (SELF_TYPE (type_to_str (typeNormalize currentClass) ) )
                      (*(SELF_TYPE "SELF_TYPE" )*)
                   else (Class typename) 
                 in
                 let t1 = typecheck o m currentClass bExpOpt in
                 if is_subtype inheritanceTable t1 t0_prime then begin
                    Hashtbl.add o ((typeNormalize currentClass), vname) t0_prime ; (* add vname to o -- add it to the object environment *)
                    let tailExp  = 
                    {
                      loc = exp.loc ;
                      exp_kind = Let(tail, let_body);
                      static_type = exp.static_type;
                    } 
                    in
                    let t2 = typecheck o m currentClass tailExp in
                    Hashtbl.remove o ((typeNormalize currentClass), vname); (* remove the type assignment in the object environment *)
                    t2
                 end
                 else begin
                   printf "ERROR: %s: Type-Check: initializer type %s does not conform to type %s\n" bExpOpt.loc (type_to_str t1) (type_to_str t0_prime);
                   exit 1
                 end   
              ) 
   
    | Case(e0, caseElemList) -> (* caseCondition_exp, caseElem=((varId, typeId, caseValue_exp) list) *)
      (* check duplicate case types *)
       let rec checkDuplicateCase listName =
       (match listName with
       | [] -> ()
       | (loc, name) :: tl -> 
       if (List.exists (fun (listElemLoc, listElemType) -> name = listElemType) tl) then begin
         printf "ERROR: %s: Type-Check: case branch type %s is bound twice\n" loc name; 
         exit 1
       end
       else
         checkDuplicateCase tl
       )
       in
       checkDuplicateCase ( List.map (fun (_, (caseLoc, caseType), _) -> (caseLoc, caseType)) caseElemList )
       ;
       let t0 = typecheck o m currentClass e0 in
       let typePrimeList = List.map 
           (fun  ( (_, xi), (tiLoc, tiName), ei)  -> 
               if tiName = "SELF_TYPE" then begin
                  printf "ERROR: %s: Type-Check: using SELF_TYPE as a case branch type is not allowed\n" tiLoc;
                  exit 1
               end
               ;
               if (List.mem tiName all_classes) then
                  Hashtbl.add o ((typeNormalize currentClass), xi) (Class tiName)
               else begin
                  printf "ERROR: %s: Type-Check: unknown type %s\n" tiLoc tiName; 
                  exit 1
               end
               ;
               let ti_prime = typecheck o m currentClass ei in
               Hashtbl.remove o ((typeNormalize currentClass), xi) ;
               ti_prime
           ) 
          caseElemList
       in 
       lub_type_sequence inheritanceTable (List.hd typePrimeList) (List.tl typePrimeList) 
       
     | While(e1, e2) ->
       let t1 = typecheck o m currentClass e1 in
       if t1 <> (Class "Bool") then begin
          printf "ERROR: %s: Type-Check: predicate has type %s instead of Bool\n" 
             exp.loc (type_to_str t1) ;
          exit 1
       end;
       let t2 = typecheck o m currentClass e2 in
       (Class "Object")
       
     | Isvoid(e1) ->
       let t1 = typecheck o m currentClass e1 in
       (Class "Bool")
     
     | Not(e1) ->
       let t1 = typecheck o m currentClass e1 in
       if t1 <> (Class "Bool") then begin
          printf "ERROR: %s: Type-Check: not %s instead of Bool\n"  exp.loc (type_to_str t1) ;
          exit 1
       end;
       (Class "Bool")
     
     | Lt(e1,e2) ->
       let t1 = typecheck o m currentClass e1 in
       if (typeNormalize t1) <> (Class "Int") then begin
          printf "ERROR: %s: Type-Check: compare %s instead of Int\n" 
             exp.loc (type_to_str t1) ;
          exit 1
       end;
       let t2 = typecheck o m currentClass e2 in
       if (typeNormalize t2) <> (Class "Int") then begin
          printf "ERROR: %s: Type-Check: compare %s instead of Int\n" 
               exp.loc (type_to_str t2) ;
          exit 1
       end;
       (Class "Bool")
       
     | Le(e1,e2) ->
       let t1 = typecheck o m currentClass e1 in
    
       if (typeNormalize t1) <> (Class "Int") then begin
          printf "ERROR: %s: Type-Check: compare %s instead of Int\n" 
             exp.loc (type_to_str t1) ;
          exit 1
       end;
       let t2 = typecheck o m currentClass e2 in
       if (typeNormalize t2) <> (Class "Int") then begin
          printf "ERROR: %s: Type-Check: compare %s instead of Int\n" 
               exp.loc (type_to_str t2) ;
          exit 1
       end;
       (Class "Bool") 
     
     | Negate(e1) ->
       let t1 = typecheck o m currentClass e1 in
       if t1 <> (Class "Int") then begin
          printf "ERROR: %s: Type-Check: negate %s instead of Int\n"  exp.loc (type_to_str t1) ;
          exit 1
       end;
       (Class "Int")
     
     | Plus(e1, e2) ->
       (*
        * O |- e1 : t1       [line 1]
        * t1 = Int           [2]
        * O |- e1 : t2       [line 3]
        * t2 = Int           [4]
        * t3 = Int           [5], t3 is the return type
        * ----------------------------
        * O |- e1 + e2 : t3  [line 6]
       *)

       (* [1] *)
       let t1 = typecheck o m currentClass e1 in
       if t1 <> (Class "Int") then begin
          printf "ERROR: %s: Type-Check: arithmetic on %s instead of Ints\n" 
             exp.loc (type_to_str t1) ;
          exit 1
       end;
       (* [2] *)
       let t2 = typecheck o m currentClass e2 in
       if t2 <> (Class "Int") then begin
          printf "ERROR: %s: Type-Check: arithmetic on Int %s instead of Ints\n" 
               exp.loc (type_to_str t2) ;
          exit 1
       end;
       (* [3] *)
       (Class "Int")
       
     | Minus(e1, e2) ->
       let t1 = typecheck o m currentClass e1 in
       if t1 <> (Class "Int") then begin
          printf "ERROR: %s: Type-Check: arithmetic on %s instead of Ints\n" 
             exp.loc (type_to_str t1) ;
          exit 1
       end;
       let t2 = typecheck o m currentClass e2 in
       if t2 <> (Class "Int") then begin
          printf "ERROR: %s: Type-Check: arithmetic on Int %s instead of Ints\n" 
               exp.loc (type_to_str t2) ;
          exit 1
       end;
       (Class "Int")
       
     | Times(e1, e2) ->
       let t1 = typecheck o m currentClass e1 in
       if t1 <> (Class "Int") then begin
          printf "ERROR: %s: Type-Check: arithmetic on %s instead of Ints\n" 
             exp.loc (type_to_str t1) ;
          exit 1
       end;
       let t2 = typecheck o m currentClass e2 in
       if t2 <> (Class "Int") then begin
          printf "ERROR: %s: Type-Check: arithmetic on Int %s instead of Ints\n" 
               exp.loc (type_to_str t2) ;
          exit 1
       end;
       (Class "Int")
       
     | Divide(e1, e2) ->
       let t1 = typecheck o m currentClass e1 in
       if t1 <> (Class "Int") then begin
          printf "ERROR: %s: Type-Check: arithmetic on %s instead of Ints\n" 
             exp.loc (type_to_str t1) ;
          exit 1
       end;
       let t2 = typecheck o m currentClass e2 in
       if t2 <> (Class "Int") then begin
          printf "ERROR: %s: Type-Check: arithmetic on Int %s instead of Ints\n" 
               exp.loc (type_to_str t2) ;
          exit 1
       end;
       (Class "Int")
       
     | Equals(e1,e2) ->
       let t1 = typecheck o m currentClass e1 in
       let t2 = typecheck o m currentClass e2 in
       (match (type_to_str t1) with
       | "Int" | "String"  | "Bool" ->
          if t1 <> t2 then begin
            printf "ERROR: %s: Type-Check: comparison between %s and %s\n" exp.loc (type_to_str t1) (type_to_str t2);
            exit 1
          end
       | x -> 
           (match (type_to_str t2) with
           | "Int" | "String" | "Bool" ->
              if t1 <> t2 then begin
                 printf "ERROR: %s: Type-Check: comparison between %s and %s\n" exp.loc (type_to_str t1) (type_to_str t2);
                 exit 1
              end
           | x -> () 
           )
       );
       (Class "Bool")

     | Internal(_,_,_) ->
       ( match exp.static_type with
         | Some(x) -> x
         | _ -> failwith("Internal typechecking error")
       ) 
                  
    in
    (* annotate the AST with the new-found static type *)
    exp.static_type <- Some(static_type); 
    static_type (* The returning value of this typecheck function *)
 
  in

  (* Now we iterate over every class and typecheck all features *)
  List.iter (fun ((cloc, cname), inherits, features) ->
    List.iter (fun feat ->
     (* Insert the last two typechecking rules here *)
      match feat with
      | Attribute((anameloc, aname), (declared_loc, declared_type), Some(init_exp)) ->  (* x : Int <- 5 + 3 *)
        let t0 = Hashtbl.find objectGlobalTable ( (Class cname), aname) in        
        let t1 = typecheck objectGlobalTable methodGlobalTable (Class cname) init_exp in
        let isNew =
            (match init_exp.exp_kind with
            | New(x) -> true
            | _ -> false
            )
        in 
        if is_subtype inheritanceTable t1 t0 && not ( ( (typeNormalize t1) = (typeNormalize t0) ) && ( (type_to_str t0) = "SELF_TYPE") && ( (type_to_str t1) <> "SELF_TYPE" ) && isNew ) then
           ()  
        else begin
           let t0String = 
             match t0 with
            | Class(x) -> x
            | SELF_TYPE(x) -> "SELF_TYPE("^x^")" 
           in
           let t1String = 
             match t1 with
            | Class(x) -> x
            | SELF_TYPE(x) -> "SELF_TYPE("^x^")" 
           in
           printf "ERROR: %s: Type-Check: %s does not conform to %s in initialized attribute\n" (* Int does not conform to string *)
               anameloc t1String t0String;
           exit 1
        end
      | Attribute((anameloc, aname), (declared_loc, declared_type), None ) -> 
        let t = Hashtbl.find objectGlobalTable ( (Class cname), aname) in
        if (type_to_str t) <> declared_type then begin
            printf "Something wrong with your object hash table\n";
            exit 1
        end
      | Method((mloc, mname), formals, (mTypeLoc, mtype), metBody ) ->  (* id , (id*id)list, id, _ *)        
        let t0 = mtype in
        (* update objectGlobalTable *)
        List.iter ( fun ((fLoc, fName), (fTypeLoc, fTypeName)) ->
          Hashtbl.add objectGlobalTable ((Class cname), fName) (Class fTypeName)
        ) formals;
        let t0_prime = typecheck objectGlobalTable methodGlobalTable (Class cname) metBody in 
        List.iter ( fun ((fLoc, fName), (fTypeLoc, fTypeName)) ->
             Hashtbl.remove objectGlobalTable ((Class cname), fName)
        ) formals;

        let tmp = 
           if t0 = "SELF_TYPE" then 
              (SELF_TYPE cname)
           else
              (Class t0)
        in
        let isNew =
            (match metBody.exp_kind with
            | New(x) -> true
            | _ -> false
            )
        in 
        if is_subtype inheritanceTable t0_prime tmp && not( ((typeNormalize t0_prime) = (typeNormalize tmp)) &&  ((type_to_str tmp) = "SELF_TYPE") && ((type_to_str t0_prime) <> "SELF_TYPE") && isNew ) then
           ()
        else begin
             let t0_primeString = 
             match t0_prime with
             | Class(x) -> x
             | SELF_TYPE(x) -> "SELF_TYPE("^x^")" 
             in
             let tmpString = 
             match tmp with
             | Class(x) -> x
             | SELF_TYPE(x) -> "SELF_TYPE("^x^")" 
             in
             printf "ERROR: %s: Type-Check: %s does not conform to %s in method %s\n" mTypeLoc t0_primeString tmpString mname;
             exit 1
        end
   ) features;  
  ) ast;


  (* Now we output the CL-TYPE file *)
  let cmname = (Filename.chop_extension f_pa_name) ^ ".cl-type" in
  let fout = open_out cmname in 
  let rec output_cool_program ast = output_class_list ast
  and output_class_list ast =
      fprintf fout "%d\n" (List.length ast);
      List.iter output_class ast

  and output_class ast = 
    match ast with
    | clas, None, class_features -> 
      output_id clas;
      fprintf fout "no_inherits\n";
      fprintf fout "%d\n" (List.length class_features);
      List.iter output_feature class_features
    | clas, Some(parentClas), class_features -> 
      output_id clas;
      fprintf fout "inherits\n";
      output_id parentClas;
      fprintf fout "%d\n" (List.length class_features);
      List.iter output_feature class_features

(* feature = 
  | Attribute of id * cool_type * (exp option)
  | Method of id * (formal list) * cool_type * exp *)

  and output_feature ast_feature = 
      match ast_feature with
      | Attribute(attr_name, attr_type, None) ->
        fprintf fout "attribute_no_init\n"; 
        output_id attr_name;
        output_id attr_type
      | Attribute(attr_name, (attr_typeLoc, attr_type), Some(init_exp)) ->
        fprintf fout "attribute_init\n";
        output_id attr_name ;
        output_id (attr_typeLoc, attr_type) ;
        output_exp init_exp

      | Method(meth_name, formals, (meth_typeLoc, meth_type), body_exp) ->
        fprintf fout "method\n";
        output_id meth_name; 
        fprintf fout "%d\n" (List.length formals); 
        List.iter output_formal formals;
        output_id (meth_typeLoc, meth_type);
        output_exp body_exp
        

  and output_formal (formalName, formalType) = 
      output_id formalName;
      output_id formalType

  and output_exp e =
    fprintf fout "%s\n" e.loc; 
   (*This is new for PA4. We are outputting the TYPE ANNOTATION after the location
   * in our ANNOTATED AST. *)
   (match e.static_type with 
    | None -> printf "loc : %s, we forgot to do typechecking\n" e.loc; exit 1
    | Some(Class(c)) -> fprintf fout "%s\n" c
    | Some(SELF_TYPE(c)) -> fprintf fout "SELF_TYPE\n" 
      
    );
    match e.exp_kind with
    | Integer(ival) -> fprintf fout "integer\n%s\n" ival 
    | String(ival) -> fprintf fout "string\n%s\n" ival 
    | True -> fprintf fout "true\n" 
    | False -> fprintf fout "false\n" 
    | Identifier(id) -> 
        fprintf fout "identifier\n";
        output_id id
    | Plus(exp1, exp2) -> 
      fprintf fout "plus\n" ;
      output_exp exp1 ;
      output_exp exp2 
    | Minus(exp1, exp2) -> 
      fprintf fout "minus\n" ;
      output_exp exp1 ;
      output_exp exp2 
    | Times(exp1, exp2) -> 
      fprintf fout "times\n" ;
      output_exp exp1 ;
      output_exp exp2 
    | Divide(exp1, exp2) -> 
      fprintf fout "divide\n" ;
      output_exp exp1 ;
      output_exp exp2 
    | Assign(id, exp) -> 
      fprintf fout "assign\n" ;
      output_id id ;
      output_exp exp 
    | Dynamic_dispatch(exp, meth, argList) -> 
      fprintf fout "dynamic_dispatch\n" ;
      output_exp exp ;
      output_id meth ;
      fprintf fout "%d\n" (List.length argList) ;
      List.iter output_exp argList
    | Static_dispatch(exp, typ, meth, argList) ->
      fprintf fout "static_dispatch\n" ;
      output_exp exp ;
      output_id typ ;
      output_id meth ;
      fprintf fout "%d\n" (List.length argList) ;
      List.iter output_exp argList
    | Self_dispatch(meth, argList) ->
      fprintf fout "self_dispatch\n" ;
      output_id meth ;
      fprintf fout "%d\n" (List.length argList) ;
      List.iter output_exp argList
    | Block(bodyList) -> 
      fprintf fout "block\n";
      fprintf fout "%d\n" (List.length bodyList);
      List.iter output_exp bodyList
    | Le(exp1, exp2) -> 
      fprintf fout "le\n" ;
      output_exp exp1 ;
      output_exp exp2 
    | Lt(exp1, exp2) -> 
      fprintf fout "lt\n" ;
      output_exp exp1 ;
      output_exp exp2 
    | Equals(exp1, exp2) -> 
      fprintf fout "eq\n" ;
      output_exp exp1 ;
      output_exp exp2 
    | Not(exp) -> 
      fprintf fout "not\n" ;
      output_exp exp ;
    | Negate(exp) -> 
      fprintf fout "negate\n" ;
      output_exp exp ;
    | Isvoid(exp) -> 
      fprintf fout "isvoid\n" ;
      output_exp exp ;
    | New(clas) -> 
      fprintf fout "new\n" ;
      output_id clas ;
    | While(exp1, exp2) -> 
      fprintf fout "while\n" ;
      output_exp exp1 ;
      output_exp exp2 
    | If(exp1, exp2, exp3) -> 
      fprintf fout "if\n" ;
      output_exp exp1 ;
      output_exp exp2 ;
      output_exp exp3 
    | Let(bindingList, letBody) ->
      fprintf fout "let\n" ;
      fprintf fout "%d\n" (List.length bindingList) ;
      List.iter output_letBinding bindingList ;
      output_exp letBody
    | Case(caseExpr, caseElemList) ->
      fprintf fout "case\n" ;
      output_exp caseExpr ;
      fprintf fout "%d\n" (List.length caseElemList) ;
      List.iter output_case caseElemList
    | Internal((typeLoc, typeName), className, methodName) -> 
      fprintf fout "internal\n";
      fprintf fout "%s.%s\n" className methodName
      
  and output_id (loc, lexme) = 
    fprintf fout "%s\n%s\n" loc lexme
   
  and output_letBinding ast_bind = 
    match ast_bind with 
     | (var, typ, None) ->  (* BindingNoInit *)
       fprintf fout "let_binding_no_init\n";
       output_id var;
       output_id typ
     | (var, typ, (Some exp)) -> (* BindingInit *)
       fprintf fout "let_binding_init\n";
       output_id var;
       output_id typ;
       output_exp exp
       
  and output_case (caseVar, caseType, caseBody) =
        output_id caseVar;
        output_id caseType;
        output_exp caseBody
  in

    fprintf fout "class_map\n"; 
    fprintf fout "%d\n" (List.length all_classes); 
    let classMap_numAttr className = 
        let initList = [] in
        let rec accuFunc accuClassName accuList = 
            if accuClassName = "" then
               [] @ accuList
            else
               let tmpList = accuFunc (searchInheritanceTable inheritanceTable accuClassName) accuList in
               let attributes = 
                   let _, _, features = List.find(fun ((_,cname2),_,_) -> cname2 = accuClassName ) all_ast in
                   List.filter(fun feature -> match feature with
                   | Attribute ((_, aname),_,_) when aname <> "self" -> true
                   | _ -> false
                   ) features         
               in
               tmpList @ attributes            
        in
        let resultList = accuFunc className initList in
        List.length resultList
    in

    let rec classMap_outputAttr className =            
      if className = "" then
         ()
      else begin        
         classMap_outputAttr (searchInheritanceTable inheritanceTable className); (* output parent class map*)  
         let attributes = 
             let _, _, features = List.find(fun ((_,cname2),_,_) -> cname2 = className ) all_ast in
             List.filter(fun feature -> match feature with
             | Attribute ((_, aname),_,_) when aname <> "self" -> true
             | _ -> false
             ) features         
         in
         List.iter (fun attr -> match attr with
                   | Attribute((_,aname),(_,atype),None)->
                     fprintf fout "no_initializer\n%s\n%s\n" aname atype
                   | Attribute((_,aname),(_,atype),(Some init))->
                     fprintf fout "initializer\n%s\n%s\n" aname atype;
                     output_exp init
                   | Method _->  failwith "method unexpected"
                   )attributes;       
      end
    in
    List.iter (fun cname ->  (* name of class, # attrs, each attr in turn *)
        fprintf fout "%s\n" cname;  
        fprintf fout "%d\n" (classMap_numAttr cname);  
        classMap_outputAttr cname      
    )all_classes;    
      


    fprintf fout "implementation_map\n"; 
    fprintf fout "%d\n" (List.length all_classes);
    let implementationMap_numMeth className = 
        let initList = [] in
        let rec accuFunc accuClassName accuList = 
            if accuClassName = "" then
               [] @ accuList
            else
               let tmpList = accuFunc (searchInheritanceTable inheritanceTable accuClassName) accuList in
               let methods = 			
	           let _, _, features = List.find(fun ((_,cname2),_,_) -> cname2 = accuClassName ) all_ast in
		   List.filter (fun feature -> match feature with
		               | Attribute _ -> false 
		               | Method _ -> true
		               ) features
	       in
               let methodsNames = 
                   List.map ( fun ( Method((locN, nameN),_,(locT, nameT),_ )) ->
                   nameN 
                   )methods
               in
               let methodNamesFilter = List.filter (fun x ->
                  if (List.mem x tmpList) then 
                     false
                  else
                     true
               ) methodsNames                                
               in
               tmpList @ methodNamesFilter           
        in
        let resultList = accuFunc className initList in
        List.length resultList
    in

    let rec implementationMap_outputMeth className topClassNameList =            
      if className = "" then
         ()
      else begin        
         implementationMap_outputMeth (searchInheritanceTable inheritanceTable className) (className :: topClassNameList); (* output parent implementation map*)  
         let methods = 			
	     let _, _, features = List.find(fun ((_,cname2),_,_) -> cname2 = className ) all_ast in
             List.filter (fun feature -> match feature with
		         | Attribute _ -> false 
		         | Method( (locN, nameN),_,_,_ ) ->
                           (
                            let ret = 
                            List.exists (fun n-> 
                              (Hashtbl.mem classLocalTable (n, "meth", nameN))
                            ) topClassNameList
                            in
                           if ret then
                              false
                           else
                              true
                           )
		         ) features
	 in
         List.iter (fun attr -> match attr with 
                   | Method ((_, mname), formals, (_, mtype), exp) -> 
                     fprintf fout "%s\n" mname ;
                     fprintf fout "%d\n" (List.length formals);
                     List.iter (fun ( (_,fname),(_,_) ) ->
                          fprintf fout "%s\n" fname ;
                     ) formals ;
                     fprintf fout "%s\n" className;
                     output_exp exp

                    | _ -> failwith "attribute unexpected"
         ) methods;      
      end
    in
    List.iter (fun cname ->  (* name of class, # attrs, each attr in turn *)
        fprintf fout "%s\n" cname;  
        fprintf fout "%d\n" (implementationMap_numMeth cname);  
        implementationMap_outputMeth cname []      
    )all_classes; 
	
    (* output parent_map *)
    fprintf fout "parent_map\n"; 
    fprintf fout "%d\n" (List.length all_classes - 1);
    List.iter (fun cname ->  (* name of class, # attrs, each attr in turn *)
        if cname <> "Object" then begin
           fprintf fout "%s\n" cname;  
           fprintf fout "%s\n" (searchInheritanceTable inheritanceTable cname)
        end   
    ) all_classes; 

   (* output typed ast *)
   output_cool_program ast;
   close_out fout
end;;
main() ;; (* invoke main function *)

