module BTree

open Cp

// (1) Datatype definition --------------------------------------------------

type BTree<'a> = Empty | Node of ('a * (BTree<'a> * BTree<'a>))

let inBTree x = either (konst Empty) Node x

let outBTree x =
    match x with
    | Empty -> i1 ()
    | Node (y,(t1,t2)) -> i2 (y,(t1,t2))


// (2) Ana + cata + hylo -------------------------------------------------------
// recBTree g = id -|- (id >< (g >< g))

let baseBTree f g x = (id -|- (f >< (g >< g))) x

let recBTree g x = baseBTree id g x        
let rec cataBTree a x = (a << (recBTree (cataBTree a)) << outBTree) x

let rec anaBTree f x = (inBTree << (recBTree (anaBTree f) ) << f) x

let hyloBTree a c x = (cataBTree a << anaBTree c) x

// (3) Map ---------------------------------------------------------------------

let fmap f x = (cataBTree ( inBTree << baseBTree f id )) x

// (4) Examples ----------------------------------------------------------------

// (4.1) Inversion (mirror) ----------------------------------------------------

let invBTree x =  cataBTree (inBTree << (id -|- (id >< swap))) x

// (4.2) Counting --------------------------------------------------------------

let countBTree x = cataBTree (either (konst 0) (succ << (uncurry (+)) << p2)) x

// (4.3) Serialization ---------------------------------------------------------

let inord y = 
        let join(x,(l,r))=l@[x]@r
        in either nil join y
  

let inordt x = cataBTree (inord) x

let preord x = 
           let f(x,(l,r))=x::l@r
           in (either nil f) x

let preordt x = cataBTree preord x

let postordt x = 
        let f(x,(l,r))=l@r@[x]
        in cataBTree (either nil f) x

// (4.4) Quicksort -------------------------------------------------------------

let rec part p li =
       match li with
       |[] -> ([],[])
       |(h::t) -> if not(p h) then let (s,l) = part p t in (h::s,l) else let (s,l) = part p t in (s,h::l) 


let qsep li =
    match li with
    | [] -> i1 ()
    | (h::t) -> i2(h,(part ((<) h) t) )

let qSort x = hyloBTree inord qsep x

// (4.5) Traces ----------------------------------------------------------------

let tunion(a,(l,r)) = (List.map (List.append [a]) l)@(List.map(List.append [a]) r) 

let traces x = cataBTree (either (konst [[]]) tunion) x

// (4.6) Towers of Hanoi -------------------------------------------------------

let present x = inord x

let strategy (d,x) = 
        match x with
        |0 -> Left ()
        |_ -> Right ((x-1,d),((not d,x-1),(not d,x-1)))

let hanoi x = hyloBTree present strategy x

// (5) Depth and balancing (using mutual recursion) --------------------------


let baldepth x = 
        let f((b1,d1),(b2,d2)) = ((b1,b2),(d1,d2)) 
        let h(a,((b1,b2),(d1,d2))) = (b1 && b2 && abs(d1-d2)<=1,1+max d1 d2)
        let g x = either (konst(true,1)) (h<<(id><f)) x 
        in cataBTree g x

let depthBTree x = p2(baldepth x)
let balBTree x = p1(baldepth x)
