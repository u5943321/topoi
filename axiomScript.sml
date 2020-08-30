val _ = new_type ("arrow", 0)
val _ = new_type ("object", 0)

val _ = new_constant("dom", “:arrow -> object”)
val _ = new_constant("cod", “:arrow -> object”)


Definition hom_def:
hom f X Y ⇔ dom f = X ∧ cod f = Y 
End                                                   
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC,450), 
                  pp_elements = [TOK "∶",TM,TOK "→"], 
                  term_name = "hom", paren_style = OnlyIfNecessary}


val _ = new_constant("id", ``:object -> arrow``)                      
val id1 = new_axiom("id1", ``!X. id X ∶ X → X``) 
val _ = export_rewrites["id1"]        
        
val _ = new_constant("compose", ``:arrow -> arrow -> arrow``);
Overload "o" = ``compose``

val idL0 = new_axiom("idL0", ``!X a. cod a = X ==> (id X) o a = a``);

Theorem idL[simp]:
∀f X Y. f∶X→Y ==> (id Y) o f = f
Proof
metis_tac[idL0,hom_def]
QED

val idR0 = new_axiom("idR0", ``!X a. dom a = X ==> a o (id X) = a``);

Theorem idR[simp]:
∀f X Y. f∶X→Y ==> f o (id X) = f
Proof
rw[idR0,hom_def]          
QED

val compose_hom0 = new_axiom("compose_hom0",
                            ``!f g. cod f = dom g ⇒
                                    dom (g o f) = dom f ∧
                                    cod (g o f) = cod g``);

Theorem compose_hom[simp]:
∀f g A B C. f∶ A → B ∧ g∶ B → C ⇒  g o f∶ A→ C
Proof
rw[compose_hom0,hom_def]
QED
                  
val compose_assoc0 = new_axiom("compose_assoc0",
                  “∀f g h. cod f = dom g ∧ cod g = dom h ⇒
                           (h o g) o f = h o (g o f)”)

Theorem compose_assoc[simp]:
∀f g h A B C D. f∶A → B ∧ g∶B → C ∧ h∶C→ D ⇒
                (h o g) o f = h o (g o f)
Proof
rw[compose_assoc0,hom_def]
QED

Definition is_product_def:
is_product A B p1 p2 ⇔ dom p1 = dom p2 ∧ cod p1 = A ∧ cod p2 = B ∧
                       ∀f g. dom f = dom g ∧ cod f = A ∧ cod g = B ⇒
                                  ∃!u. dom u = dom g ∧ cod u = dom p2 ∧
                                       p1 o u = f ∧ p2 o u = g
End
                                              
Theorem is_product_thm:
∀A B p1 p2. is_product A B p1 p2 ⇔
            (∃AB.p1∶ AB → A ∧ p2∶ AB → B ∧ 
                ∀f g X. f∶ X → A ∧ g∶ X → B ⇒
                        ∃!u. u∶ X → AB ∧
                             p1 o u = f ∧ p2 o u = g)
Proof              
rw[is_product_def,EQ_IMP_THM,hom_def] >> metis_tac[]
QED

val product_exists = new_axiom
                     ("product_exists",
                      “∀A B. ∃p1 p2. is_product A B p1 p2”)    
   

Definition is_pullback_def:
is_pullback f g pb1 pb2 ⇔
            cod f = cod g ∧ dom pb1 = dom pb2 ∧
            cod pb1 = dom f ∧ cod pb2 = dom g ∧ f o pb1 = g o pb2 ∧
            (∀x1 x2. dom x1 = dom x2 ∧ cod x1 = dom f ∧
                     cod x2 = dom g ∧
                     f o x1 = g o x2 ⇒
                     ∃!u. dom u = dom x2 ∧ cod u = dom pb2 ∧
                                           x1 = pb1 o u ∧
                                           x2 = pb2 o u)
End

Theorem is_pullback_thm:
∀f g pb1 pb2. is_pullback f g pb1 pb2 ⇔
         ∃A B C P. f∶A→C ∧ g∶B→C ∧ pb1∶P→A ∧ pb2∶P→B ∧
                   f ∘ pb1 = g ∘ pb2 ∧
                   ∀X x1 x2. x1∶X→ A ∧ x2∶ X→ B ∧ f o x1 = g o x2 ⇒
                             ∃!u. u∶X→P ∧
                                  x1 = pb1 o u ∧ x2 = pb2 o u
Proof
rw[hom_def,EQ_IMP_THM,is_pullback_def] (* 2 *)
>- metis_tac[]
>- metis_tac[]
QED

val pullback_exists = new_axiom
                     ("pullback_exists",
                      “∀f g. cod f = cod g ⇒
                             ∃pb1 pb2. is_pullback f g pb1 pb2”)    
           
Theorem pullback_exists_thm:
∀f g A B C. f∶A→ C ∧ g∶B→  C ⇒ ∃pb1 pb2. is_pullback f g pb1 pb2
Proof
rw[pullback_exists,hom_def]
QED

val terminal_exists = new_axiom
                     ("terminal_exists",
                      “∃t. is_terminal t”)    
        
Definition is_terminal_def:
is_terminal t ⇔ ∀X. ∃!u. u∶X→ t
End        

Definition is_mono_def:   
  is_mono f ⇔
  ∀g1 g2. dom g1 = dom g2 ∧ cod g1 = dom f ∧ cod g2 = dom f ∧
          f o g1 = f o g2 ⇒ g1 = g2
End

Theorem is_mono_thm:
∀f.is_mono f ⇔ ∃A B. f∶ A→ B ∧ ∀g1 g2 X. g1∶X→ A ∧ g2∶X→ A ∧
                                      f ∘ g1 = f∘g2 ⇒ g1 = g2
Proof
metis_tac[is_mono_def,hom_def]
QED

Definition mono_def:
mono f X Y ⇔ is_mono f ∧ f∶X→ Y
End

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC,450), 
                  pp_elements = [TOK "∶",TM,TOK "↣"], 
                  term_name = "mono", paren_style = OnlyIfNecessary}
        

Definition true_def:
is_true true t Omega ⇔ (dom true = t ∧ cod true = Omega ∧
                        is_mono true ∧ is_terminal t ∧
           ∀m. is_mono m ⇒
               ∃!char. dom char = cod m ∧ cod char = Omega ∧
                      ∃s. dom s = dom m ∧ cod s = t ∧
                          is_pullback char true m s)
End

        

Theorem true_thm:
∀true t Omega. is_true true t Omega ⇔
(true∶t ↣ Omega ∧ is_terminal t ∧
 ∀m B X. m∶ B ↣ X ⇒
         ∃!char. char∶X→ Omega ∧
                 ∃s. s∶ B → t ∧
                     is_pullback char true m s)
Proof
rw[true_def,hom_def,mono_def,EQ_IMP_THM] >> metis_tac[]
QED
      
val true_exists = new_axiom
                     ("true_exists",
                      “∃true t Omega. is_true true t Omega”)

                 

Definition is_power_def:
is_power B PB mem true ⇔ ∃t Omega. is_true true t Omega ∧
∀A p1 p2 f. is_product A B p1 p2 ∧ dom f = dom p2 ∧
cod f = Omega ⇒ ∃!g. dom g = A ∧ cod g = PB  ∧ mem o (id B × g) = ..
