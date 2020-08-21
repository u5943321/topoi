val _ = new_type ("arrow", 0)
val _ = new_type ("object", 0)

val _ = new_constant("id", ``:object -> arrow``)
val _ = new_constant("arrow_compose", ``:arrow -> arrow -> arrow``);

val _ = new_constant("dom", “:arrow -> object”)
val _ = new_constant("cod", “:arrow -> object”)

Overload "o" = ``arrow_compose``

(*identity*)         

val id1 = new_axiom("id1", ``!X. dom (id X) = X ∧ cod (id X) = X``)

val idL = new_axiom("idL", ``!X a. cod a = X ==> (id X) o a = a``);

val idR = new_axiom("idR", ``!X a. dom a = X ==> a o (id X) = a``);

(*composition*)     

val compose = new_axiom("compose", ``!f g. cod f = dom g ⇒ dom (g o f) = dom f ∧ cod (g o f) = cod g``);

val compose_assoc = new_axiom("compose_assoc",
                  “∀f g h. cod f = dom g ∧ cod g = dom h ⇒
                           (h o g) o f = h o (g o f)”)
                           
(* product*)

(* A <--pr1-- A \times B --pr2--> B *)
(*universal property, for every f: T --> A, g: T --> B, there exists a unique arrow
⟨f,g⟩, such that pr1 o ⟨f,g⟩ = f ∧ pr2 o ⟨f, g⟩ = g*)

val prod_obj = new_constant("product", “:object -> object -> (arrow # arrow)”)                          
    
val prod_diag = new_axiom("prod_diag", “∀A B. dom (FST (product A B)) = dom (SND (product A B)) /\
                                              cod (FST (product A B)) = A /\
                                              cod (SND (product A B)) = B /\
                                              
                                       ”)              
                     
val prod_up = new_axiom("prod_up", “∀A B f g.
                                  dom f = dom g ∧ cod f = A ∧ cod g = B ⇒
                                  dom (prod_ar f g) = dom g ∧
                                  cod (prod_ar f g) = prod_obj A B ∧
                                  (p1 A B) o (prod_ar f g) = f ∧
                                  (p2 A B) o (prod_ar f g) = g ∧
                                  (∀u. dom u = dom g ∧ cod u = prod_obj A B ∧
                                  (p1 A B) o u = f ∧
                                  (p2 A B) o u = g ⇒ u = (prod_ar f g))”)                                
                                                                  
(* pullback *)


val pb_ars = new_constant("pullback", “: arrow -> arrow -> (arrow # arrow)”)

val pb_diag = new_axiom("pb_diag",
                  “∀f g.
                     cod f = cod g ⇒
                     dom (FST (pullback f g)) = dom (SND (pullback f g)) ∧
                     dom (SND (pullback f g)) = dom (SND (pullback f g)) ∧
                     cod (FST (pullback f g)) = dom f ∧
                     cod (SND (pullback f g)) = dom g ∧
                     f o (FST (pullback f g)) = g o (SND (pullback f g))
                  ”)

val pb_induce = new_constant("pb_induce",
                     “: arrow -> arrow -> arrow -> arrow -> arrow”)
                                  
val pb_up = new_axiom("pb_up",
                  “∀x1 x2 f g.
                     cod f = cod g ∧
                     dom x1 = dom x2 ∧
                     cod x1 = dom f ∧ cod x2 = dom g ∧
                     f o x1 = g o x2 ⇒
                     dom (pb_induce f g x1 x2) = dom x1 ∧
                     cod (pb_induce f g x1 x2) = pb_obj f g ∧
                     (FST (pb_ars f g)) o (pb_induce f g x1 x2) = x1 ∧
                     (SND (pb_ars f g)) o (pb_induce f g x1 x2) = x2 ∧
                     (∀u. dom u = dom x1 ∧ cod u = pb_obj f g ∧
                          (FST (pb_ars f g)) o u = x1 ∧
                          (SND (pb_ars f g)) o u = x2 ⇒
                          u = pb_induce f g x1 x2)
                  ”)
                                                     
(*terminal object*)

val terminal = new_constant("terminal", “: object”)

val mterminal = new_constant("mterminal", “: object -> arrow”)    

val _ = new_axiom("terminal_diag", “∀X. dom (mterminal X) = X ∧
                                        cod (mterminal X) = terminal”)

val _ = new_axiom("mterminal_unique",
                  “∀f g. dom f = dom g ∧ cod f = terminal ∧ cod g = terminal ⇒
                         f = g”)                                        

(* mono *)

val _ = new_constant("is_mono", “:arrow -> bool”)

val is_mono_def = new_axiom("is_mono_def",
                  “∀f. is_mono f ⇔
                   ∀g1 g2. dom g1 = dom g2 ∧ cod g1 = dom f ∧ cod g2 = dom f ∧
                          f o g1 = f o g2 ⇒ g1 = g2”)                                                                                                                    
(*subobject classifier + truth map*)

            

val _ = new_constant("true", “: arrow”)

val _ = new_axiom("true_diag", “dom true = terminal”)

val _ = new_constant("char", “:arrow -> arrow”)


val _ = new_axiom("char_diag",
                 “∀m. is_mono m ⇒ dom (char m) = cod m ∧ cod (char m) = cod true”)    
val omega_char_sc = new_axiom("omega_char_sc",
                 “∀m. is_mono m ⇒
                      true o (mterminal (dom m)) = (char m) o m ∧
                      (∀x1 x2.
                        dom x1 = dom x2 ∧
                        cod x1 = cod m ∧ cod x2 = terminal ∧
                        x1 o (char m) = x2 o true ⇒
                        ∃!u. dom u = dom x2 ∧ cod u = dom m ∧
                        x1 = m o u ∧ x2 = (mterminal (dom m)) o u)
                      ”)    

(*power object*)

val _ = new_constant("pow", “: object -> object”)

val _ = new_constant("mem", “: object -> arrow”)

val _ = new_constant("transpose", “: arrow -> arrow”)    

val _ = new_axiom("transpose_diag",
                 “∀f B A. dom f = prod_obj B A ∧ cod f = omega ⇒
                          dom (transpose f) = A ∧ cod (transpose f) = pow B ∧
                          (mem B) o (prod_ar (p1 B A) ((transpose f) o (p2 B A))) = f”)                

val _ = new_axiom("transpose_unique",
                 “∀f B A g. dom f = prod_obj B A ∧ cod f = omega ∧
                          dom g = A ∧ cod g = pow B ∧
                          (mem B) o (prod_ar (p1 B A) (g o (p2 B A))) = f ⇒
                          g = transpose f”)
                       

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, 
                  pp_elements = [TOK "⟨", TM, TOK ",",TM, TOK "⟩"], 
                  term_name = "prod_ar", paren_style = OnlyIfNecessary}

Definition is_iso_def:
is_iso f ⇔ (∃f'. dom f' = cod f ∧ cod f = dom f ∧ f o f' = id (cod f) ∧ f' o f = id (dom f))
End

        
Definition are_iso_def:
are_iso A B ⇔ ∃f g. dom f = A ∧ cod f = B ∧ dom g = B ∧ cod g = A ∧
                    f o g = id B ∧ g o f = id A
End


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC,450), 
                  pp_elements = [TOK "≅"], 
                  term_name = "are_iso", paren_style = OnlyIfNecessary}                                      

Definition diagonal_def:
diagonal B = prod_ar (id B) (id B)
End

Theorem diagonal_dom:
∀B. dom (diagonal B) = B
Proof
rw[diagonal_def] >>
‘dom (id B) = B’ by metis_tac[id1] >> metis_tac[prod_up]
QED

Theorem diagonal_is_mono:
∀B. is_mono ⟨id B,id B⟩
Proof
rw[is_mono_def] >> 
‘(p1 B B) o (⟨id B,id B⟩ o g1) = (p1 B B) o (⟨id B,id B⟩ o g2)’ by simp[] >>
‘dom (id B) = B’ by simp[id1] >>
‘(p1 B B) o ⟨id B,id B⟩ = id B’
 suffices_by
 (‘(p1 B B) o (⟨id B,id B⟩ o g1) = ((p1 B B) o ⟨id B,id B⟩) o g1 ∧
   (p1 B B) o (⟨id B,id B⟩ o g2) = ((p1 B B) o ⟨id B,id B⟩) o g2’
   by metis_tac[prod_diag,compose_assoc] >>
  rw[] >> ‘(id B) o g1 = (id B) o g2’ by metis_tac[] >>
  ‘dom ⟨id B,id B⟩ = B’ by metis_tac[id1,prod_diag] >> metis_tac[idL]) >>
 metis_tac[id1,prod_up]
QED


Definition is_pullback_def:
is_pullback pb1 pb2 f g ⇔ dom pb1 = dom pb2 ∧ cod f = cod g ∧ cod pb1 = dom f ∧ cod pb2 = dom g ∧
                          f o pb1 = g o pb2 ∧
                          ∀x1 x2. dom x1 = dom x2 ∧ cod x1 = dom f ∧ cod x2 = dom g ∧ f o x1 = g o x2 ⇒
                                  ∃!u. dom u = dom x2 ∧ cod u = dom pb2 ∧
                                       pb1 o u = x1 ∧ pb2 o u = x2
End                                                                


Theorem pb_is_pullback:
∀f g. cod f = cod g ⇒ is_pullback                                                                    
        
Theorem pb_unique:
∀f g. cod f = cod g ⇒
      ∀pb1 pb2. dom pb1 = dom pb2 ∧ cod pb1 = dom f ∧ cod pb2 = dom g ∧
                f o pb1 = g o pb2 ⇒
       ∀x1 x2. (dom x1 = dom x2 ∧ cod x1 = dom f ∧ cod x2 = dom g ∧
                f o x1 = g o x2 ∧
                ∃!u. dom u = dom x1 ∧ 
                     cod u = dom pb1 ∧z
                     pb1 o u = x1 ∧ pb2 o u = x2) ⇒
               dom x1 ≅ pb_obj f g
Proof
rw[] >>
‘dom (pb_induce f g x1 x2) = dom x1 ∧
 cod (pb_induce f g x1 x2) = pb_obj f g ∧
                     (FST (pb_ars f g)) o (pb_induce f g x1 x2) = x1 ∧
                     (SND (pb_ars f g)) o (pb_induce f g x1 x2) = x2 ∧
                     (∀u. dom u = dom x1 ∧ cod u = pb_obj f g ∧
                          (FST (pb_ars f g)) o u = x1 ∧
                          (SND (pb_ars f g)) o u = x2 ⇒
                          u = pb_induce f g x1 x2)’



drule pb_up >> rw[] >> first_x_assum drule >> rpt strip_tac >> rfs[]
first_x_assum (qspecl_then [‘pb1’,‘pb2’] assume_tac) >> rfs[]
      

Theorem pb_paste:

        
Theorem sing_is_mono:
∀B. is_mono (transpose (char ⟨id B,id B⟩))
Proof    
rw[]     
