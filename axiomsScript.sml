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

val _ = new_constant("prod_obj", “:object -> object -> object”)                                        
val _ = new_constant("p1", “:object -> object -> arrow”)

val _ = new_constant("p2", “:object -> object -> arrow”)

val _ = new_constant("prod_ar", “:arrow -> arrow -> arrow”)        
    
val _ = new_axiom("prod_diag", “∀A B. dom (pr1 A B) = prod_obj A B ∧
                                      dom (pr2 A B) = prod_obj A B ∧
                                      cod (pr1 A B) = A ∧
                                      cod (pr1 A B) = B”)              
                     
val _ = new_axiom("prod_up", “∀A B X f g.
                                  dom f = X ∧ cod f = A ∧
                                  dom g = X ∧ cod g = B ⇒
                                  dom (prod_ar f g) = X ∧
                                  cod (prod_ar f g) = C ∧
                                  (pr1 A B) o (prod_ar f g) = f ∧
                                  (pr2 A B) o (prod_ar f g) = g ∧
                                  (∀u. dom u = X ∧ cod u = C ∧
                                  (pr1 A B) o u = f ∧
                                  (pr2 A B) o u = g) ⇒ u = (prod_ar f g)”)                                
                                                                  
(* pullback *)

val _ = new_constant("pb_obj", “: arrow -> arrow -> object”)

val _ = new_constant("pb_ars", “: arrow -> arrow -> (arrow # arrow)”)

val _ = new_axiom("pb_diag",
                  “∀f g.
                     cod f = cod g ⇒
                     dom (FST (pb_ars f g)) = dom (SND (pb_ars f g)) ∧
                     dom (SND (pb_ars f g)) = pb_obj f g ∧
                     cod (FST (pb_ars f g)) = dom f ∧
                     cod (SND (pb_ars f g)) = dom g ∧
                     f o (FST (pb_ars f g)) = g o (SND (pb_ars f g))
                  ”)

val _ = new_constant("pb_induce",
                     “: arrow -> arrow -> arrow -> arrow -> arrow”)
                                  
val _ = new_axiom("pb_up",
                  “∀X x1 x2 f g.
                     dom x1 = dom x2 ∧ dom x2 = X ∧
                     cod x1 = dom f ∧ cod x2 = dom g ∧
                     f o x1 = g o x2 ⇒
                     dom (pb_induce f g x1 x2) = X ∧
                     cod (pb_induce f g x1 x2) = pb_obj f g ∧
                     (FST (pb_ars f g)) o (pb_induce f g x1 x2) = x1 ∧
                     (SND (pb_ars f g)) o (pb_induce f g x1 x2) = x2 ∧
                     (∀u. dom u = X ∧ cod u = pb_obj f g ∧
                          (FST (pb_ars f g)) o u = x1 ∧
                          (SND (pb_ars f g)) o u = x2 ⇒
                          u = pb_induce f g x1 x2)
                  ”)
                                                     
(*terminal object*)

val _ = new_constant("terminal", “: object”)

val _ = new_constant("mterminal", “: object -> arrow”)    

val _ = new_axiom("terminal_diag", “∀X. dom (mterminal X) = X ∧
                                        cod (mterminal X) = terminal”)

val _ = new_axiom("mterminal_unique",
                  “∀f g. dom f = dom g ∧ cod f = cod g ∧ cod g = terminal ⇒
                         f = g”)                                        

(* mono *)

val _ = new_constant("is_mono", “:arrow -> bool”)

val _ = new_axiom("is_mono_def",
                  “∀f. is_mono f ⇔
                  ∀g1 g2. dom g1 = dom g2 ∧ cod g1 = cod g2 ∧ cod g2 = dom f ∧
                          g1 o f = g2 o f ⇒ g1 = g2”)                                                                                                                    
(*subobject classifier + truth map*)

            
val _ = new_constant("omega", “:object”)

val _ = new_constant("true", “: arrow”)

val _ = new_axiom("true_diag", “dom true = terminal ∧ cod true = omega”)

val _ = new_constant("char", “:arrow -> arrow”)


val _ = new_axiom("char_diag",
                 “∀m. is_mono_m ⇒ dom (char m) = cod m ∧ cod (char m) = omega”)    
val _ = new_axiom("omega_char_sc",
                 “∀m. is_mono m ⇒
                      true o (mterminal (dom m)) = (char m) o m ∧
                      (∀X x1 x2.
                        dom x1 = X ∧ dom x2 = X ∧
                        cod x1 = cod m ∧ cod x2 = terminal ∧
                        x1 o (char m) = x2 o true ⇒
                        ∃!u. dom u = X ∧ cod u = dom m ∧
                        x1 = m o u ∧ x2 = (mterminal (dom m)) o u)
                      ”)    

(*power object*)

val _ = new_constant("pow", “: object -> object”)

val _ = new_constant("mem", “: object -> arrow”)

val _ = new_constant("transpose", “: arrow -> arrow”)    

val _ = new_axiom("transpose_diag",
                 “∀f B A. dom f = prod_obj B A ∧ cod f = omega ⇒
                          dom (transpose f) = A ∧ cod (transpose f) = pow B ∧
                          (mem B) o (prod_ars (p1 B A) ((transpose f) o (p2 B A))) = f”)                

val _ = new_axiom("transpose_unique",
                 “∀f B A g. dom f = prod_obj B A ∧ cod f = omega ∧
                          dom g = A ∧ cod g = pow B ∧
                          (mem B) o (prod_ars (p1 B A) (g o (p2 B A))) = f ⇒
                          g = transpose f”)

