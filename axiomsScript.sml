val _ = new_type ("arrow", 0)
val _ = new_type ("object", 0)

val _ = new_constant("id", ``:object -> arrow``)
val _ = new_constant("arrow_compose", ``:arrow -> arrow -> arrow``);

val _ = new_constant("dom", “:arrow -> object”)
val _ = new_constant("cod", “:arrow -> object”)

Overload "o" = ``arrow_compose``

(*identity*)         

val _ = new_axiom("id1", ``!X. dom (id X) = X ∧ cod (id X) = X``)

val _ = new_axiom("idL", ``!X a. cod a = X ==> (id X) o a = a``);

val _ = new_axiom("idR", ``!X a. dom a = X ==> a o (id X) = a``);

(*composition*)     

val _ = new_axiom("compose", ``!f g. cod f = dom g ⇒ dom (g o f) = dom f ∧ cod (g o f) = cod g``);

val _ = new_axiom("compose_assoc",
                  “∀f g h. cod f = dom g ∧ cod g = dom h ⇒
                           (h o g) o f = h o (g o f)”)
                           
(* product*)

(* A <--pr1-- A \times B --pr2--> B *)
(*universal property, for every f: T --> A, g: T --> B, there exists a unique arrow
⟨f,g⟩, such that pr1 o ⟨f,g⟩ = f ∧ pr2 o ⟨f, g⟩ = g*)

val _ = new_constant("is_prod",
                     “: object -> object -> object -> arrow -> arrow -> bool”)

val _ = new_axiom("prod_def", “∀A B C pr1 pr2.
                                 is_prod A B C pr1 pr2 <=> 
                                 dom pr1 = C ∧ cod pr1 = A ∧
                                 dom pr2 = C ∧ cod pr2 = B ∧
                                 (∀X f g.
                                  dom f = X ∧ cod f = A ∧
                                  dom g = X ∧ cod g = B ⇒
                                  ∃!i. dom i = X ∧ cod i = C ∧
                                       pr1 o i = f ∧ pr2 o i = g)”)

val _ = new_constant("prod_obj", “:object -> object -> object”)                                        
val _ = new_constant("p1", “:object -> object -> arrow”)

val _ = new_constant("p2", “:object -> object -> arrow”)

val _ = new_constant("prod_ar", “:arrow -> arrow -> arrow”)       

val _ = new_axiom("prod_exists", “∀A B. is_prod A B (prod_obj A B) (p1 A B) (p2 A B)”)                                  
                                  
(* pullback *)

val _ = new_constant("is_pullback", “:arrow -> arrow -> object -> arrow -> arrow -> bool”)

val _ = new_axiom("pullback_def",
                  “∀f g P i j.
                   is_pullback f g P i j ⇔
                   cod f = cod g ∧
                   dom i = P ∧ dom j = P ∧
                   cod i = dom f ∧ cod j = dom g ∧
                   f o i = g o j ∧
                   (∀X t1 t2. dom t1 = X ∧ dom t2 = X ∧
                              cod t1 = A ∧ cod t2 = B ∧
                              f o t1 = g o t2 ⇒
                              ∃!u. dom u = X ∧ cod u = P ∧
                                   i o u = t1 ∧ j o u = t2)”)
                                   
val _ = new_axiom("pullback_exists",
                  “∀f g. cod f = cod g ⇒ ∃P i j. is_pullback f g P i j”)
                  
(*terminal object*)

val _ = new_constant("is_terminal", “:object -> bool”)

val _ = new_axiom("terminal_def", “∀A. is_terminal A ⇔
                                       ∀X. ∃!tx. dom tx = X ∧ cod tx = A”)

val _ = new_constant("terminal", “:object”)

val _ = new_axiom("terminal_exists", “is_terminal terminal”)    
(* mono *)

val _ = new_constant("mono", “:arrow -> bool”)

val _ = new_axiom("mono_def",
                  “∀f. is_mono f ⇔
                  ∀g1 g2. dom g1 = dom g2 ∧ cod g1 = cod g2 ∧ cod g2 = dom f ∧
                          g1 o f = g2 o f ⇒ g1 = g2”)                                                                                                                    
(*subobject classifier + truth map*)

val _ = new_constant("is_sct", “:arrow -> bool”)            
                        
val _ = new_axiom("sct_def",
                 “is_sct true0 ⇔
                 ∃t. is_terminal t ∧ dom true = t ∧ is_mono true0 ∧
                 ∀m. is_mono m ⇒
                     ∃!phi j. is_pullback phi true0 (dom m) m j 
                 ”)
val _ = new_constant("true", “:arrow”)
val _ = new_constant("omega", “: object”)

val _ = new_axiom("sct_exists", “is_sct true ∧ dom true = t ∧ cod true = omega”)
    
(*power object*)

val _ = new_axiom("power_def",
                  “∀B A f. dom f = prod B A ∧ cod f = omega ⇒
                  ∃!g. dom g = A ∧ cod g = PB ∧
                       f = ev B o prod_ar (pr1 B A) (g o (pr2 B A))”)




val _ = new_constant("pobj", “:object -> object”)

val _ = new_constant("ev", “:object -> arrow”)


