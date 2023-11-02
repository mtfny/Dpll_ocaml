(* MP1 2023/2024 - dpll.ml *)

open List

(* fonctions utilitaires *)
(* ----------------------------------------------------------- *)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;-3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [
  [1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];
  [19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];
  [-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];
  [-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];
  [-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];
  [-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];
  [-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];
  [-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];
  [-14;-17];[-15;-18]]

(* ----------------------------------------------------------- *)


(* Début des fonctions auxilères pour simplifie *)

(* without_l : int a list -> int a list
   Retourne la clause donnée en paramètre sans le littéral l *)
let rec without_l l clause = 
  match clause with 
  | [] -> []
  | head::rest -> 
      if head = l then 
        without_l l rest
      else
      head::(without_l l rest) 

(* simplifie_aux : int a list -> int a list
  Simplifie le littéral l dans la clause
   - si la clause contient l , retourne None 
   - si la clause ne contient que not l, retourne la clause vide
   - si la clause contient not l, retourne la clause sans not l 
   - sinon, retourne la clause sans modification *)
let simplifie_aux l clause = 
  if List.mem l clause then 
    None 
  else if List.mem (0-l) clause then 
      let tmp = (without_l (0-l) clause ) in 
      match tmp with 
      | [] -> Some ([]) 
      | _ -> Some (tmp )
  else
    Some (clause)

(* Fin des fonctions auxilières pour simplifie *)


(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)

let simplifie l clauses = 
  (* Filter_map inverse l'odre de la liste, donc on réinverse l'ordre 
  pour obtenir la liste dans l'ordre original *)
  List.rev (filter_map (simplifie_aux l) clauses)


(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* la clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(*
let () = print_modele (solveur_split exemple_3_12 [])
let () = print_modele (solveur_split exemple_7_2 [])
let () = print_modele (solveur_split exemple_7_4 [])
let () = print_modele (solveur_split exemple_7_8 [])
*)


(* let () = print_modele (solveur_split coloriage []) *)

(* solveur dpll récursif *)
(* ----------------------------------------------------------- *)


(* Début des fonctions auxiliaires pour pur *)

(* fusionner_listes : int a list -> int a list -> int a list
   Retoune la concaténation de deux listes *)
   
let rec fusionner_listes liste1 liste2 =
  match liste1 with
  | [] -> liste2
  | tete :: reste -> tete :: fusionner_listes reste liste2


(* clauses_into_list : int list list -> int list
   Retourne la concaténation des clauses en une seule liste *)

let rec clauses_into_list clauses = 
  match clauses with 
  | [] -> []
  | head::rest -> fusionner_listes  head (clauses_into_list rest)


(*  
    pur_aux : int list -> int list -> int 
    - Retourne un littéral 
      si la tête de l1 est pur à la fois dans l1 et dans l2 
      (not (tete de l1) n'apparait ni dans l1 ni dans l2 )
    - sinon, lève une exception  *)

let rec pur_aux l1 l2 = 
  match l1 with 
  | [] -> raise (Failure "pas de littéral pur")
  | head :: rest -> 
    if not (List.mem  (0-head) rest) && not (List.mem (0-head) l2) then 
      head 
    else
      pur_aux rest (head::l2)

(* Fin des fonctions auxilières pour pur *)


(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)

let pur clauses =
  try 
    pur_aux (clauses_into_list clauses) []
  with
  | Failure message -> raise (Failure "pas de littéral pur")

(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)

let rec unitaire clauses =
  match clauses with 
  | [] -> raise (Failure "Not_found")
  | head::rest -> 
    (* Si une clause ne contient qu'un seul élément *)
    if List.length head = 1 then 
      (* Renvoi de cet élément*)
      match head with 
      | [head_bis] -> head_bis
    else
      (* Récursion sur la formule, privée de la première clause *)
      unitaire rest
  


(*Fonctions auxiliaires pour le solveur*)

(*let rec moms l clauses =
  match clause with
  | pattern -> pattern*)


let first clauses =
  match clauses with
  | [] -> failwith"liste vide"
  | elem1 :: rest -> match elem1 with
                    | [] -> failwith "vide"
                    | tete1 :: reste1 -> tete1;;

(* Fin des fonctions auxiliaires pour le solveur *)


(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
    (* la clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
    (* branchement *) 
  try
    (*cas : clause unitaire*)
    let lit_unitaire = unitaire clauses in 
    solveur_dpll_rec (simplifie lit_unitaire clauses) (lit_unitaire::interpretation) 
  with
    |Failure message -> 
      try 
        (*cas : litteral pur*)
        let lit_pur = pur clauses in
        solveur_dpll_rec (simplifie lit_pur clauses) (lit_pur::interpretation)
      with
        |Failure message ->
          try 
            (*cas : premier litteral du premier élément *)
            let fst_lit = first clauses in 
            solveur_dpll_rec (simplifie fst_lit clauses) (fst_lit::interpretation)
          with
            |Failure message -> 
              try 
                (*cas : négation du premier litteral du premier élément *)
                let not_fst_lit = 0 - first clauses in 
                solveur_dpll_rec ((simplifie not_fst_lit clauses)) (not_fst_lit::interpretation)
              with
                | Failure message -> None  

let solveur_dpll clauses =
  solveur_dpll_rec clauses []


(* tests *)
(* ----------------------------------------------------------- *)
(* let () = print_modele (solveur_dpll_rec exemple_7_2 []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])
