(* Mikolaj Grzywacz 394321 
CR: Michał Chojnowski *)

type t =
	| Empty
	| Node of t * (int * int) * t * int * int 
	(* lewe * przedzial * prawe * wysokosc * below*)
	
type typ =
	| Nothing
	| Something of int 
	(*Uzywane do funkcji split_lewo, split_prawo i add*)
	

let empty = Empty

let height =
	function
		| Node (_, _, _, h,_) -> h
		| Empty -> 0
  
let belVal = 
	function
		| Node (_, _, _, _, bel) -> bel
		| Empty -> 0

let is_empty = 
	function
		| Empty -> true
		| _ -> false

(* sumuje 4 integery tak zby nie wyszly za max_int*)
let sum a b c d =
	if max (max a b) (max c d) = max_int 
		|| a >= max_int - b 
		|| c >= max_int - d 
		|| a + b >= max_int - c - d 
		then
			max_int
		else
			a + b + c + d		

(*oblicza dlugosc przedzialu (zeby nie przkroczyla max_int), zalozenie b>=a*)		
let sum_sizeVal a b =
	if a>=0 then
		if (b - a) - max_int >= 0 then max_int
		else b - a
	else 
		if a<0 && b>=0 then
			if (abs a + b - max_int) >= 0 then max_int
			else abs a + b
		else 
			if (b - a - max_int) >= 0 then max_int
			else b - a

(*zwraca dlugosc przedzialu*)
let sizeVal =
	function
		| Node (_, (a,b), _, _, _) -> 
			let suma_1 = sum_sizeVal a b in
			sum suma_1 0 1 0
		| Empty -> 0
		
let make l k r = 
	Node (l, k, r, max (height l) (height r) + 1, sum (belVal l) (sizeVal l) (belVal r) (sizeVal r))

(*bal praktycznie bez zmian (ostatnia linikja i matche)*)
let bal l k r =
	let hl = height l in
	let hr = height r in
	if hl > hr + 2 then
		match l with
			| Node (ll, lk, lr, _, _) ->
				if height ll >= height lr then make ll lk (make lr k r)
					else
					(match lr with
						| Node (lrl, lrk, lrr, _, _) ->
							make (make ll lk lrl) lrk (make lrr k r)
						| Empty -> assert false)
			| Empty -> assert false
	else if hr > hl + 2 then
		match r with
			| Node (rl, rk, rr, _, _) ->
				if height rr >= height rl then make (make l k rl) rk rr
				else
					(match rl with
						| Node (rll, rlk, rlr, _, _) ->
							make (make l k rll) rlk (make rlr rk rr)
						| Empty -> assert false)
			| Empty -> assert false
	else make l k r
  
let rec min_elt = 
	function
		| Node (Empty, k, _, _, _) -> k
		| Node (l, _, _, _, _) -> min_elt l
		| Empty -> raise Not_found
		
let rec remove_min_elt = 
	function
		| Node (Empty, _, r, _, _) -> r
		| Node (l, k, r, _, _) -> bal (remove_min_elt l) k r
		| Empty -> invalid_arg "PSet.remove_min_elt"

(* int -> (int * int) -> int *)
(*uzywam tylko do splita*)
(*czy liczba a jest w przedziale (c,d)*)
let cmp_split a (c,d) =
(* compare x y -> x < y (-1) *)
	if a < c then -1
	else 
		if a > d then 1
		else 0
		
(*porownywanie przedzialow*)
let cmp (a,b) (c,d) =
(* compare x y -> x < y (-1) *)
	if b < (c -1) && c <> min_int then -1
	else 
		if d < (a - 1) && a <> min_int then 1
		else 0
	
(*dodaje przedzial ale musi byc inny niz dotychczasowe*)
let rec add_distinct x = 
	function
		| Node (l, k, r, h, bel) ->
			let c = cmp x k in
			if c <= 0 then (*tak wlasciwie to i tak c nie bedzie rowne 0 nigdy*)
				let nl = add_distinct x l in
				bal nl k r
			else
				let nr = add_distinct x r in
				bal l k nr
		| Empty -> Node (Empty, x, Empty, 1, 0)

(*wszystie przedzialy sa rozlaczne w obu drzewach*)
let rec join l v r =
	match (l, r) with
		| (Empty, _) -> add_distinct v r
		| (_, Empty) -> add_distinct v l
		| (Node(ll, lv, lr, lh, _), Node(rl, rv, rr, rh, _)) ->
			if lh > rh + 2 then bal ll lv (join lr v r) 
			else
				if rh > lh + 2 then bal (join l v rl) rv rr 
				else make l v r

(*dodaje dwa drzewa do siebie, ale muszą być parami rozne*)
(*l ma mniejsze r wieksze elementy*)
let rec join_double l r =
	match (l, r) with
		| (Empty, _) -> r
		| (_, Empty) -> l
		| (Node(ll, lv, lr, lh, _), Node(rl, rv, rr, rh, _)) ->
			if lh > rh + 2 then bal ll lv (join_double lr r) 
			else  bal (join_double l rl) rv rr 

(*najistotniejsza funkcja ;)*)
let split x set =
	let rec aux s = 
		match s with
			| Empty -> (Empty, false, Empty)
			| Node (l, v, r, _, _) ->
				let c = cmp_split x v in	
				if c = 0 then 
					let (va, vb) = v in
					((if va=x then l else add_distinct (va, x - 1) l), true, (if vb=x then r else add_distinct (x + 1, vb) r))
				else 
					if c < 0 then
						let (ll, pres, rl) = aux l in 
						(ll, pres, join rl v r)
					else
						let (lr, pres, rr) = aux r in 
						(join l v lr, pres, rr)
	in
	aux set

(* int -> t -> t * typ *)
(*Bierze kraniec przedzialu i drzewo i zwraca drzewo mniejszych elementow, oraz *)
(*koniec przedzialu w ktorym x wystapil lub nic gdy elementu nie bylo*) 
let split_lewo x set =
	let rec aux s =
		match s with
		| Empty -> (Empty, Nothing)
		| Node (l, v, r, _, _) ->
			let c = cmp_split x v in	
				if c = 0 then 
					let (va, vb) = v in
					(l, Something va)
				else 
					if c < 0 then
						aux l
					else
						let (lr, pres) = aux r in 
						(join l v lr, pres)
	in
	aux set
(* int -> t -> t * typ*)
(*Bierze kraniec przedzialu i drzewo i zwraca drzewo wiekszych elementow, oraz *)
(*poczatek przedzialu w ktorym x wystapil lub nic gdy elementu nie bylo*) 
let split_prawo x set =
	let rec aux s =
		match s with
			| Empty -> (Empty, Nothing)
			| Node (l, v, r, _, _) ->
				let c = cmp_split x v in	
				if c = 0 then 
					let (va, vb) = v in
					(r, Something vb)
				else 
					if c < 0 then
						let (rl, press) = aux l in 
						(join rl v r, press)
					else
						aux r
	in
	aux set
	
	
(*splituje i usuwa*)
let remove (a,b) set =
	let (ll,_,_) = split a set in
	let (_,_,rr) = split b set in
	join_double ll rr
		

let add (a,b) set =
	(* rozwaza przypadek graniczny dla a i b, i wyciaga odpowiedni przedzial*)
	(*splitujemy o 1 element dalej (a-1), (b+1) zeby "zlapac wysuniete przedzialy" *) 
	(*potem laczy go z mniejszym i wiekszym poddrzewem*)
	let (l,t_l) = if a=min_int then (Empty,Nothing) else split_lewo (a - 1) set in
	let (r,t_r) = if b=max_int then (Empty,Nothing) else split_prawo (b + 1) set in 
	let (pocz, kon) = 
		match t_l,t_r with 
			| Something lsth, Something rsth ->  (lsth,rsth)
			| Nothing, Something rsth -> (a,rsth)
			| Something lsth, Nothing -> (lsth,b)
			| Nothing, Nothing -> (a,b)
	in
	join l (pocz, kon) r
	
let below liczba set = 
	let (l,p,_) = split liczba set in
	if p=true then
		sum (belVal l) (sizeVal l) 1 0
	else 
		sum (belVal l) (sizeVal l) 0 0

let mem x set =
	let (_,czy,_) = split x set in
	czy
	
let iter f set =
	let rec loop = 
		function
			| Empty -> ()
			| Node (l, k, r, _, _) -> loop l; f k; loop r in
	loop set
	
let fold f set acc =
	let rec loop acc = 
		function
			| Empty -> acc
			| Node (l, k, r, _, _) ->
				loop (f k (loop acc l)) r in
	loop acc set
	
let elements set = 
	let rec loop acc = 
		function
			| Empty -> acc
			| Node(l, k, r, _, _) -> loop (k :: loop acc r) l in
	loop [] set