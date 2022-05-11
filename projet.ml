
(* EXERCICE 2 *)

(* 
   1. Trouvez une structure de donnée adaptée à l’implantation des polynômes à coefficient dans F2  

   La structure que nous avons choisi est une liste de couple d'entier, Ci-dessous la liste typef2.
*) 

type typef2 = (int * int) list;;


(*
   2. Programmez la somme, le produit par la méthode de Karatsuba, la division rapide 
   par la méthode de Newton, ainsi que l’algorithme d’Euclide de F2[X]
*)


let p1 : typef2 = [ (0,1) ; (1,1) ; (3,1) ];;
let p2 : typef2 = [ (1,1) ; (2,1) ; (3,1) ];;

let p3 : typef2 = [ (0,1) ; (1,1) ; (2,1) ; (3,1) ; (4,1) ; (5,1) ];; 
let p4 : typef2 = [ (1,0) ; (2,1) ; (3,0) ];;
  

(*La somme de Polynôme*)
let rec add_poly (p1 : typef2) (p2 : typef2) =
  match (p1, p2) with
  | [], p -> p
  | p, [] -> p
  | (i, x) :: p1', (j, y) :: p2' when i=j ->if (x+y=0) then  add_poly p1' p2' else (i,x+y)::add_poly p1' p2'
  | (i, x) :: p1', (j, y) :: p2' ->if i < j then (i, x) :: add_poly p1' p2 else (j, y) :: add_poly p1 p2'
;;


(*La Multiplication par la méthode de Karatsuba*)

(*Function permettantde  multiplier les coefficiants de deux polynômes*)
let mult_coeff (p1 : typef2) n =
  let rec aux p n (acc : typef2) =
    match p with
    | [] -> List.rev acc
    | (i, x) :: l' -> aux l' n ((i, x * n) :: acc)
  in aux p1 n [];;

(*Function permettant de retourner le degre d'un polynôme*)
let rec degre (p:typef2) =match p with
  |[]->0
  |(i,x)::[]->i
  |(i,x)::l'-> degre l';;

(*Function permettant de multiplier un monôme X^n par un polynôme*)
let multXn (p : typef2) n =
  let rec aux p1 n (acc : typef2) =
    match p1 with
    | [] -> List.rev acc
    | (x, y) :: l -> aux l n ((x + n, y) :: acc)
  in
  aux p n [];;


(*  Fonction auxiliaire pour la méthode de Karatsuba 
 l’appel à cut p n renvoie le couple de polynômes
(p0, p1) tel que p = p0 + X^ip1 ;

*)

let rec cut1 (p1 : typef2) n =
  match (p1 : typef2) with
  | [] -> []
  | (i, x) :: l' when i < n -> ((i, x) :: cut1 l' n : typef2)
  | (i, x) :: l' -> [];; 


let rec cut2 (p1 : typef2) n =
  match (p1 : typef2) with
  | [] -> []
  | (i, x) :: l' when i >= n -> ((i-n, x) :: cut2 l' n : typef2)
  | (i, x) :: l' -> cut2 l' n;;

let cut (p : typef2) n = (cut1 p n, cut2 p n)

 
let rec coeff (p:typef2) = match p with
  |[]->0
  |(x,i)::[]->i
  |(x,i)::l'->coeff l';;                         

let rec multinaive (p : typef2) (q : typef2) =
  match p with
  | [] -> []
  | (i, x) :: l' -> (add_poly (mult_coeff (multXn q i) x) (multinaive l' q) : typef2);;



(* Multiplication de deux polynômes par la méthode de Karatsuba*)
let rec karatsuba (p : typef2) (q : typef2) : typef2 =
  if (degre p < 2 || degre q < 2) then multinaive p q
  else
    let k =
      if max (degre p) (degre q) mod 2 = 0 then max (degre p) (degre q) / 2
      else (max (degre p) (degre q) + 1) / 2
    in
    let a0 = cut1 p k  and a1 = cut2 p k and b0 = cut1 q k and b1 = cut2 q k
    in
    let c0 = karatsuba a0 b0 and c2 = karatsuba a1 b1 and u = karatsuba (add_poly a0 a1) (add_poly b0 b1)
    in
    let c1 = add_poly (add_poly u (mult_coeff c0 (-1))) (mult_coeff c2 (-1))
    in
    add_poly (add_poly c0 (multXn c1 k)) (multXn c2 (2 * k)) ;;


(* Division de deux polynômes par la méthode de Newton*)
let rec moduloXn (p: typef2) (n:float)=
  match (p : typef2) with
  | [] -> []
  | (i, x) :: l' when float_of_int(i) < n -> ((i, x) :: moduloXn l' n : typef2)
  | (i, x) :: l' -> [];;

let renv_poly (p: typef2) k : typef2=
  if (k<degre p)
  then failwith "Erreur il faut un K superieur ou egale au degre du polynome p"
  else
    let rec renv_recur (p: typef2) acc = match p with
      |[]->List.rev acc
      |(i,x)::l'-> renv_recur l' [(k-i,x)]@acc
    in renv_recur p [];;



(* Calcul du quotient de la division  *)

let quotient (p: typef2) (q: typef2) =
  if ( degre(p) >= degre(q)) then
    let poly = mult_coeff (renv_poly q (degre(q))) (1/(coeff (q)))
    and h = float_of_int (degre(p)-degre(q)+1)
    in
    let rec calcul_G (g: typef2) i =
      if (2.**i >=h)
      then g 
      else calcul_G (moduloXn  (add_poly  (mult_coeff g (2))  (mult_coeff (karatsuba (poly) (karatsuba g g)) (-1)))    (2.**(i +.1.))   )   (i+.1.)
    in let calcul_Q= renv_poly (moduloXn(karatsuba(renv_poly (p) (degre(p)))(mult_coeff (calcul_G [(0,1)] (0.)) (1/(coeff (q))) ) ) (h)) (degre(p)-degre(q))
    in (calcul_Q);
  else
    p
;;


(* Calcul du reste de la division  *)
let reste (p:typef2) (q:typef2) = add_poly (p) (mult_coeff (karatsuba (q) (quotient p q)) (-1));;


(* 
   Division de deux polynômes par l'algorithme d'Euclide
*)


let algo_euclide (p : typef2) (q : typef2) = 
  let rec pgcd (p1 : typef2) (q1 : typef2) =
    if q1=[] 
    then
      p1
    else pgcd q1 ( reste p1 q1)
  in pgcd p q ;;

let pgcd (p: typef2)(q : typef2)=
  if degre(p)>degre(q) then
    algo_euclide p q
  else
    algo_euclide q p;; 


(* 
   3- Fonction qui calcule l’ordre d’un polynôme de degré supérieur à 1 et de terme constant égal à 1.
*)

let rec ordre (p : typef2)=
  let rec ordre_rec (p: typef2) i=
    if (( quotient ([(i,1)]) p)=[(0,1)])then
      i
    else
      ordre_rec p (i+1)
  in ordre_rec p 1
;; 
