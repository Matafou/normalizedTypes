
Inductive iex {A: Type} (P: A -> Prop): SProp := iex_intro: forall x, P x -> iex P.
Inductive isig {A: Type} (P: A -> SProp): Type := isig_intro: forall x, P x ->  isig P.
 

(* We replace usual notations: *)
Notation "'iexists' x .. y , p" := (iex (fun x => .. (iex (fun y => p)) ..)) (at level 100, x binder, y binder, right associativity,
   format "'[' 'iexists'  '/  ' x  ..  y ,  '/  ' p ']'") : type_scope.
Notation "{ x | 'irr' P }" := (isig (fun x => P)) (at level 0, x at level 99, P at level 100) : type_scope .
