val _ = new_type ("arrow", 0)
val _ = new_type ("object", 0)

val _ = new_constant("id", ``:object -> arrow``)
val _ = new_constant("arrow_compose", ``:arrow -> arrow -> arrow``);

val _ = new_constant("dom", “:arrow -> object”)
val _ = new_constant("cod", “:arrow -> object”)

Overload "o" = ``arrow_compose``

(*identity*)         

val id1 = new_axiom("id1", ``!X. dom (id X) = X ∧ cod (id X) = X``) 
val _ = export_rewrites["id1"]
  
val idL = new_axiom("idL", ``!X a. cod a = X ==> (id X) o a = a``);
val _ = export_rewrites["idL"]

val idR = new_axiom("idR", ``!X a. dom a = X ==> a o (id X) = a``);
val _ = export_rewrites["idR"]
(*composition*)     

val compose = new_axiom("compose", ``!f g. cod f = dom g ⇒ dom (g o f) = dom f ∧ cod (g o f) = cod g``);
val _ = export_rewrites["compose"]

val compose_assoc = new_axiom("compose_assoc",
                  “∀f g h. cod f = dom g ∧ cod g = dom h ⇒
                           (h o g) o f = h o (g o f)”)
val _ = export_rewrites["compose_assoc"]                           
(* product*)

val product = new_constant("product", “:object -> object -> (arrow # arrow)”)                          
    
val product_up = new_axiom("product_up",
                          “∀A B. dom (FST (product A B)) = dom (SND (product A B)) ∧
                                 cod (FST (product A B)) = A ∧
                                 cod (SND (product A B)) = B ∧
                                 (∀f g. dom f = dom g ∧ cod f = A ∧ cod g = B ⇒
                                        ∃!u. dom u = dom g ∧ cod u = dom (SND (product A B)) ∧
                                             f = (FST (product A B)) o u ∧
                                             g = (SND (product A B)) o u)        
                                              
                          ”)

(*add the notion of induced arrow in order to define iv in page 163*)

val product_induce = new_constant("product_induce", “:arrow -> arrow -> arrow”)      

val product_induce_def = new_axiom("product_induce_def",
                          “∀A B. dom (FST (product A B)) = dom (SND (product A B)) ∧
                                 cod (FST (product A B)) = A ∧
                                 cod (SND (product A B)) = B ∧
                                 (∀f g. dom f = dom g ∧ cod f = A ∧ cod g = B ⇒
                                        dom (product_induce f g) = dom g ∧
                                        cod (product_induce f g) = dom (SND (product A B)) ∧
                                        f = (FST (product A B)) o (product_induce f g) ∧
                                        g = (SND (product A B)) o (product_induce f g))        
                                              
                          ”)
val _ = export_rewrites["product_induce_def"]         

Overload product_obj = “λA B. dom (SND (product A B))”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC,450), 
                  pp_elements = [TOK "x"], 
                  term_name = "product_obj", paren_style = OnlyIfNecessary}

Overload product_arrow = “λf g. ⟨f o (FST (product (dom f) (dom g))),
                                 g o (SND (product (dom f) (dom g)))⟩”

val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, 
                  pp_elements = [TOK "(",TM, TOK "×",TM,TOK ")"], 
                  term_name = "product_arrow", paren_style = OnlyIfNecessary}                                                  
                                                            
val product_assoc = new_axiom("product_assoc",“∀A B C. ((A x B) x C) = (A x (B x C))”)                                                                   
(* pullback *)


val pullback = new_constant("pullback", “: arrow -> arrow -> (arrow # arrow)”)

val pullback_up = new_axiom("pullback_up",
                  “∀f g.
                     cod f = cod g ⇒
                     dom (FST (pullback f g)) = dom (SND (pullback f g)) ∧
                     cod (FST (pullback f g)) = dom f ∧
                     cod (SND (pullback f g)) = dom g ∧
                     f o (FST (pullback f g)) = g o (SND (pullback f g)) ∧
                     (∀x1 x2. dom x1 = dom x2 ∧ cod x1 = dom f ∧ cod x2 = dom g ∧ f o x1 = g o x2 ⇒
                              ∃!u. dom u = dom x2 ∧ cod u = dom (SND (pullback f g)) ∧
                                   (FST (pullback f g)) o u = x1 ∧
                                   (SND (pullback f g)) o u = x2
                     )
                  ”)

(*add the notion of "is pullback" as a definition in order to define iii in page 163*)

(*define in that way so rw etc will use def to decompose a map as factors through certain objects*)      

Definition is_pullback_def:
is_pullback f g (pb1, pb2) ⇔ cod f = cod g ∧ dom pb1 = dom pb2 ∧ cod pb1 = dom f ∧
                             cod pb2 = dom g ∧ f o pb1 = g o pb2 ∧
                             (∀x1 x2. dom x1 = dom x2 ∧ cod x1 = dom f ∧ cod x2 = dom g ∧
                                      f o x1 = g o x2 ⇒
                                      ∃!u. dom u = dom x2 ∧ cod u = dom pb2 ∧
                                           x1 = pb1 o u ∧
                                           x2 = pb2 o u)
End

                                                     
(*terminal object*)

val terminal = new_constant("terminal", “: object”)

val terminal_def = new_axiom("terminal_def", “∀X. ∃!u. dom u = X ∧ cod u = terminal”)

(*add a constant for the unique arrow to terminal object, in order to define the true map*)    

val X2t = new_constant("X2t", “:object -> arrow”)

val X2t_def = new_axiom("X2t_def",“∀X. dom (X2t X) = X ∧ cod (X2t X) = terminal”)                            val _ = export_rewrites["X2t_def"]               
(* mono *)

Definition is_mono_def:   
  is_mono f ⇔
  ∀g1 g2. dom g1 = dom g2 ∧ cod g1 = dom f ∧ cod g2 = dom f ∧
          f o g1 = f o g2 ⇒ g1 = g2
End                                                                                                                  
(*subobject classifier + truth map*)

val _ = new_constant("true", “: arrow”)

(*add subobject classifier as primitive notion in order to define iv in p163*)

val _ = new_constant("omega", “: object”)      

val true_def = new_axiom("true_def", “is_mono true ∧ dom true = terminal ∧ cod true = omega ∧
                              ∀m. is_mono m ⇒
                                  ∃!char. dom char = cod m ∧ cod char = omega ∧
                                          is_pullback char true (m, (X2t (dom m)))”)

val univalence = new_axiom("univalence", “∀A B. A ≅ B ⇒ A = B”)
                                          

Theorem true_itself[simp]:
is_mono true ∧ dom true = terminal ∧ cod true = omega
Proof
rw[true_def]
QED
        
val _ = new_constant("char", “:arrow -> arrow”)

val char_def = new_axiom("char_def", “∀m. is_mono m ⇒
                                          dom (char m) = cod m ∧ cod (char m) = omega ∧
                                          is_pullback (char m) true (m, (X2t (dom m)))”)                     val _ = export_rewrites["char_def"]                           
(*power object*)

val _ = new_constant("pow", “: object -> object”)

val _ = new_constant("mem", “: object -> arrow”)

val mem_def = new_axiom("mem_def",
                       “∀B. dom (mem B) = dom (SND (product B (pow B))) ∧ cod (mem B) = omega ∧
                            (∀A f. dom f = dom (SND (product B A)) ∧ cod f = omega ⇒
                                ∃!g. dom g = A ∧ cod g = pow B ∧
                                    f = (mem B) o
                                        product_induce (FST (product B A))
                                                       (g o (SND (product B A))))”)    
Theorem mem_itself[simp]:
∀B. dom (mem B) = dom (SND (product B (pow B))) ∧ cod (mem B) = omega
Proof
rw[mem_def]
QED
                       
val _ = new_constant("transpose", “:arrow -> arrow”)

val transpose_def = new_axiom("transpose_def",
                             “(∀B A f. dom f = dom (SND (product B A)) ∧ cod f = omega ⇒
                                       dom (transpose f) = A ∧ cod (transpose f) = pow B ∧
                                       f = (mem B) o
                                        product_induce (FST (product B A))
                                                       ((transpose f) o (SND (product B A))))”)

val _ = export_rewrites["transpose_def"]
                                                        
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, 
                  pp_elements = [TOK "⟨", TM, TOK ",",TM, TOK "⟩"], 
                  term_name = "product_induce", paren_style = OnlyIfNecessary}

Definition is_iso_def:
is_iso f ⇔ (∃f'. dom f' = cod f ∧ cod f' = dom f ∧ f o f' = id (cod f) ∧ f' o f = id (dom f))
End

        
Definition are_iso_def:
are_iso A B ⇔ ∃f g. dom f = A ∧ cod f = B ∧ dom g = B ∧ cod g = A ∧
                    f o g = id B ∧ g o f = id A
End


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC,450), 
                  pp_elements = [TOK "≅"], 
                  term_name = "are_iso", paren_style = OnlyIfNecessary}                                      

(*axioms end*)



(*char required for this part,transpose required for this part*)

Theorem product_with_terminal:
∀B. is_iso (FST (product B terminal))
Proof
rw[is_iso_def,product_up] >> qexists_tac ‘⟨id B, X2t B⟩’ >> rw[] (* 4 *)
>- metis_tac[product_induce_def,id1,X2t_def]
>- metis_tac[product_induce_def,id1,X2t_def]
>- metis_tac[product_induce_def,id1,X2t_def]
>- (‘dom (id (B x terminal)) = dom (SND (product B terminal)) ∧
    cod (id (B x terminal)) = (B x terminal) ∧
    FST (product B terminal) = FST (product B terminal) ∘ (id (B x terminal)) ∧
    SND (product B terminal) = SND (product B terminal) ∘ (id (B x terminal)) ∧
    
    dom (⟨id B,X2t B⟩ ∘ FST (product B terminal)) = dom (SND (product B terminal)) ∧
    cod (⟨id B,X2t B⟩ ∘ FST (product B terminal)) = (B x terminal) ∧
    FST (product B terminal) = FST (product B terminal) ∘ (⟨id B,X2t B⟩ ∘ FST (product B terminal))∧
    SND (product B terminal) = SND (product B terminal) ∘ (⟨id B,X2t B⟩ ∘ FST (product B terminal))’ suffices_by
    (‘dom (FST (product B terminal)) = dom (SND (product B terminal)) ∧
    cod (FST (product B terminal)) = B ∧
    cod (SND (product B terminal)) = terminal’ by metis_tac[product_up] >>
    ‘∃!u.
                 dom u = dom (SND (product B terminal)) ∧ cod u = (B x terminal) ∧
                 (FST (product B terminal)) = FST (product B terminal) ∘ u ∧
                 (SND (product B terminal)) = SND (product B terminal) ∘ u’ by fs[product_up] >>
     metis_tac[EXISTS_UNIQUE_THM]) >> 
    simp[product_induce_def,id1,X2t_def,idL,idR,idL] >>
    ‘dom (FST (product B terminal)) = (B x terminal) ∧
    cod ⟨id B,X2t B⟩ = (B x terminal) ∧
    dom ⟨id B,X2t B⟩ = B ∧ cod (FST (product B terminal)) = B’
    by fs[product_up,product_induce_def,id1,X2t_def] >>
    rw[] (* 4 *)
    >- metis_tac[compose]
    >- metis_tac[compose]
    >- (‘FST (product B terminal) ∘ ⟨id B,X2t B⟩ ∘ FST (product B terminal) =
        (FST (product B terminal) ∘ ⟨id B,X2t B⟩) ∘ FST (product B terminal)’
         suffices_by 
         (rw[] >>
         ‘FST (product B terminal) ∘ ⟨id B,X2t B⟩ = id B’ by fs[product_induce_def,id1,X2t_def] >>
         rw[idL]) >>
       ‘(FST (product B terminal) ∘ ⟨id B,X2t B⟩) ∘ FST (product B terminal) =
        FST (product B terminal) ∘ ⟨id B,X2t B⟩ ∘ FST (product B terminal)’
        suffices_by metis_tac[] >> irule compose_assoc >>
        fs[product_induce_def,id1,X2t_def])
     >- (‘dom (SND (product B terminal)) =
         dom (SND (product B terminal) ∘ ⟨id B,X2t B⟩ ∘ FST (product B terminal)) ∧
         cod (SND (product B terminal)) = terminal ∧
         cod (SND (product B terminal) ∘ ⟨id B,X2t B⟩ ∘ FST (product B terminal)) = terminal’
         suffices_by
          (rw[] >>
          ‘∃!u. dom u = (B x terminal) ∧ cod u = terminal’ by metis_tac[terminal_def] >>
          fs[EXISTS_UNIQUE_THM]) >>
         rw[] (* 3 *) >>
         fs[product_induce_def,id1,X2t_def,compose]))
QED
        
Theorem dom_terminal_mono:
∀f. dom f = terminal ⇒ is_mono f
Proof
rw[is_mono_def] >> metis_tac[terminal_def]
QED

Theorem pullback_mono_mono:
∀m. is_mono m ⇒ ∀f pb1 pb2. is_pullback f m (pb1, pb2) ⇒ is_mono pb1
Proof
rw[is_pullback_def,is_mono_def] >>
‘f o pb1 o g1 = f o pb1 o g2’ by simp[] >>
‘f o pb1 o g1 = (f o pb1) o g1 ∧ f o pb1 o g2 = (f o pb1) o g2’ by metis_tac[compose_assoc] >>
‘(m o pb2) o g1 = (m o pb2) o g2’ by metis_tac[] >>
rfs[compose_assoc] >> ‘pb2 ∘ g1 = pb2 ∘ g2’ by metis_tac[compose] >>
first_x_assum (qspecl_then [‘pb1 o g1’,‘pb2 o g1’] mp_tac) >> rw[compose] >>
‘f ∘ pb1 ∘ g2 = (f ∘ pb1) ∘ g2 ∧
 m ∘ pb2 ∘ g2 = (m ∘ pb2) ∘ g2’
 by fs[compose_assoc] >>
‘f ∘ pb1 ∘ g2 = m ∘ pb2 ∘ g2’ by metis_tac[] >> fs[] >>
metis_tac[EXISTS_UNIQUE_THM]
QED


Theorem diagonal_is_mono:
∀B. is_mono ⟨id B, id B⟩
Proof
rw[is_mono_def] >>
‘(FST (product B B)) o (⟨id B,id B⟩ o g1) = (FST (product B B)) o (⟨id B,id B⟩ o g2)’ by simp[] >>
‘dom (id B) = B’ by simp[id1] >>
‘(FST (product B B)) o ⟨id B,id B⟩ = id B’
 suffices_by
 (‘(FST (product B B)) o (⟨id B,id B⟩ o g1) = ((FST (product B B)) o ⟨id B,id B⟩) o g1 ∧
   (FST (product B B)) o (⟨id B,id B⟩ o g2) = ((FST (product B B)) o ⟨id B,id B⟩) o g2’
   by fs[product_induce_def,compose_assoc,id1,compose] >>
  rw[] >> ‘(id B) o g1 = (id B) o g2’ by metis_tac[] >>
  ‘dom ⟨id B,id B⟩ = B’ by metis_tac[id1,product_induce_def] >> metis_tac[idL]) >>
metis_tac[id1,product_induce_def] 
QED

Theorem product_component_eq:
∀A B p q. dom p = dom q ∧ cod p = (A x B) ∧ cod q = (A x B) ∧
          (FST (product A B)) o p = (FST (product A B)) o q ∧
          (SND (product A B)) o p = (SND (product A B)) o q ⇒
          p = q
Proof
rw[] >>
‘dom (FST (product A B) ∘ p) = dom p ∧ dom (SND (product A B) ∘ p) = dom p ∧
cod (FST (product A B) ∘ p) = A ∧ cod (SND (product A B) ∘ p) = B’
by fs[product_induce_def,compose] >>
‘dom (FST (product A B) ∘ p) = dom (SND (product A B) ∘ p)’ by metis_tac[] >>
drule (product_up|> SPEC_ALL |> CONJUNCT2 |> CONJUNCT2 |> CONJUNCT2) >> rw[] >>
metis_tac[EXISTS_UNIQUE_THM]
QED

Theorem product_FST_compose:
∀f g h. dom f = cod h ∧ dom g = cod h ⇒
            FST (product (cod f) (cod g)) o ⟨f, g⟩ o h = f o h        
Proof
metis_tac[product_induce_def,compose_assoc]
QED

Theorem product_SND_compose:
∀f g h. dom f = cod h ∧ dom g = cod h ⇒
            SND (product (cod f) (cod g)) o ⟨f, g⟩ o h = g o h        
Proof
metis_tac[product_induce_def,compose_assoc]
QED


Theorem product_SND_compose_alt:
∀f g h A B. dom f = cod h ∧ dom g = cod h ∧ cod f = A ∧ cod g = B ⇒
            SND (product A B) o ⟨f, g⟩ o h = g o h        
Proof
metis_tac[product_induce_def,compose_assoc]
QED

Theorem product_itself[simp]:
∀A B.
         dom (FST (product A B)) = (A x B) ∧ cod (FST (product A B)) = A ∧
         cod (SND (product A B)) = B
Proof
metis_tac[product_induce_def]
QED

Theorem product_induce_dom:
∀f g A. dom f = dom g ∧ dom f = A ⇒ dom ⟨f,g⟩ = A
Proof
metis_tac[product_induce_def]
QED


Theorem product_induce_cod:
∀f g A B. dom f = dom g ∧ cod f = A ∧ cod g = B ⇒ cod ⟨f,g⟩ = (A x B)
Proof
metis_tac[product_induce_def]
QED

Theorem product_FST:
∀f g A B. dom f = dom g ∧ cod f = A ∧ cod g = B ⇒ f = FST (product A B) ∘ ⟨f,g⟩
Proof
metis_tac[product_induce_def]
QED


Theorem product_SND:
∀f g A B. dom f = dom g ∧ cod f = A ∧ cod g = B ⇒ g = SND (product A B) ∘ ⟨f,g⟩
Proof
metis_tac[product_induce_def]
QED

Theorem compose_dom[simp]:
∀f g A. cod f = dom g ∧ dom f = A ⇒ dom (g ∘ f) = A
Proof
rw[compose]
QED


Theorem compose_cod[simp]:
∀f g B. cod f = dom g ∧ cod g = B ⇒ cod (g ∘ f) = B
Proof
rw[compose]
QED


        

Theorem is_mono_applied:
∀f.
         is_mono f ==>
         ∀g1 g2.
             dom g1 = dom g2 ∧ cod g1 = dom f ∧ cod g2 = dom f ∧
             f ∘ g1 = f ∘ g2 ⇒
             g1 = g2
Proof
metis_tac[is_mono_def]
QED

Theorem product_induce_is_mono:
!f g. dom f = dom g /\ is_mono g ==> is_mono ⟨f,g⟩
Proof
rw[is_mono_def] >>
first_x_assum irule >> fs[product_induce_def] >>
‘(SND (product (cod f) (cod g))) o ⟨f,g⟩ ∘ g1  = (SND (product (cod f) (cod g))) o ⟨f,g⟩ ∘ g2’
 by metis_tac[] >>
‘SND (product (cod f) (cod g)) ∘ ⟨f,g⟩ ∘ g1 = g o g1 /\
SND (product (cod f) (cod g)) ∘ ⟨f,g⟩ ∘ g2 = g o g2’ suffices_by metis_tac[] >>
strip_tac (* 2 *) >> irule product_SND_compose_alt >>
fs[product_induce_def]
QED        

Theorem id_is_mono:
∀X. is_mono (id X)
Proof           
rw[is_mono_def] >> metis_tac[idL]
QED
           
Theorem distribute_pullback:
∀b. is_pullback ⟨FST (product (cod b) (dom b)), b o (SND (product (cod b) (dom b)))⟩
            ⟨id (cod b), id (cod b)⟩
            (⟨b, id (dom b)⟩,b)
Proof
strip_tac >>
qabbrev_tac ‘X = dom b’ >> qabbrev_tac ‘B = cod b’ >>
simp[is_pullback_def,product_induce_def,id1,compose] >>
‘cod ⟨FST (product B X),b ∘ SND (product B X)⟩ = cod ⟨id B,id B⟩’
  by metis_tac[id1,compose,product_induce_def] >>
     (*okay, but I have to wait for ages.*)
(*
>- (‘cod ⟨id (cod b),id (cod b)⟩ = ((cod b) x (cod b))’
     by fs[product_induce_def,id1] >>
   ‘cod ⟨FST (product B X),b ∘ SND (product B X)⟩ = ((cod b) x (cod b))’
     suffices_by metis_tac[] >>
   ‘dom (FST (product B X)) = dom (b ∘ SND (product B X)) ∧
    cod (FST (product B X)) = cod b ∧
    cod (b ∘ SND (product B X)) = cod b’ suffices_by metis_tac[product_induce_def] >>
    fs[product_induce_def,compose]) *)
simp[] >>
‘⟨FST (product B X),b ∘ SND (product B X)⟩ ∘ ⟨b,id X⟩ = ⟨id B,id B⟩ ∘ b’
by
 (irule product_component_eq >>
  ‘dom (⟨FST (product B X),b ∘ SND (product B X)⟩ ∘ ⟨b,id X⟩) =
   dom (⟨id B,id B⟩ ∘ b)’
    by metis_tac[product_induce_def,id1,compose] >>
  simp[] >>
  map_every qexists_tac [‘B’,‘B’] >> fs[] >>
  ‘FST (product B B) ∘ ⟨FST (product B X),b ∘ SND (product B X)⟩ ∘ ⟨b,id X⟩ =
   (FST (product B B) ∘ ⟨FST (product B X),b ∘ SND (product B X)⟩) ∘ ⟨b,id X⟩’
    by fs[] >>
  ‘(FST (product B B) ∘ ⟨FST (product B X),b ∘ SND (product B X)⟩) =
   FST (product B X)’ by fs[] >>
  ‘FST (product B B) ∘ ⟨FST (product B X),b ∘ SND (product B X)⟩ ∘ ⟨b,id X⟩ =
   (FST (product B X)) o ⟨b,id X⟩’ by fs[] >>
  ‘FST (product B X) ∘ ⟨b,id X⟩ = b’ by fs[] >>
  ‘FST (product B B) ∘ ⟨id B,id B⟩ ∘ b = (FST (product B B) ∘ ⟨id B,id B⟩) ∘ b’
    by fs[] >>
  ‘FST (product B B) ∘ ⟨id B,id B⟩ = id B’ by fs[] >>
  ‘FST (product B B) ∘ ⟨id B,id B⟩ ∘ b = (id B) o b’ by metis_tac[] >>
  ‘SND (product B B) ∘ ⟨FST (product B X),b ∘ SND (product B X)⟩ ∘ ⟨b,id X⟩ =
   SND (product B B) ∘ ⟨id B,id B⟩ ∘ b’ suffices_by metis_tac[idL] >>
  fs[] >>
  ‘SND (product B B) ∘ ⟨id B,id B⟩ ∘ b =
  (SND (product B B) ∘ ⟨id B,id B⟩) ∘ b’ by fs[] >>
  ‘(SND (product B B) ∘ ⟨id B,id B⟩) = id B’ by fs[] >>
  ‘SND (product B B) ∘ ⟨id B,id B⟩ ∘ b = b’ by metis_tac[idL] >>
  rw[] >>
  ‘SND (product B B) ∘ ⟨FST (product B X),b ∘ SND (product B X)⟩ ∘ ⟨b,id X⟩ =
  (SND (product B B) ∘ ⟨FST (product B X),b ∘ SND (product B X)⟩) o ⟨b,id X⟩’
  by fs[] >>
  ‘SND (product B B) ∘ ⟨FST (product B X),b ∘ SND (product B X)⟩ =
   b ∘ SND (product B X)’ by fs[] >>
  ‘(SND (product B B) ∘ ⟨FST (product B X),b ∘ SND (product B X)⟩) o ⟨b,id X⟩ =    (b ∘ SND (product B X)) o ⟨b,id X⟩’ by fs[] >>
  ‘(b ∘ SND (product B X)) o ⟨b,id X⟩ = b ∘ (SND (product B X) o ⟨b,id X⟩)’
  by fs[] >>
  ‘(SND (product B X) o ⟨b,id X⟩) = (id X)’ by fs[] >>
  ‘b ∘ (SND (product B X) o ⟨b,id X⟩) = b o (id X)’ by fs[] >>
  metis_tac[idR]) >>
simp[] >>
(*last subgoal*)
rpt strip_tac >> simp[EXISTS_UNIQUE_ALT] >>
qexists_tac ‘(SND (product B X)) o x1’ >>
‘dom (SND (product B X) ∘ x1) = dom x2 ∧ cod (SND (product B X) ∘ x1) = X ∧
 x1 = ⟨b,id X⟩ ∘ (SND (product B X) ∘ x1) ∧ x2 = b ∘ (SND (product B X) ∘ x1) ∧
 (∀u'. dom u' = dom x2 ∧ cod u' = X ∧ x1 = ⟨b,id X⟩ ∘ u' ∧ x2 = b ∘ u' ⇒
       SND (product B X) ∘ x1 = u')’
suffices_by metis_tac[] >> fs[] >>
‘FST (product B X) ∘ x1 = x2 ∧
(b ∘ SND (product B X)) ∘ x1 = x2’
  by
   (‘(SND (product B B)) o ⟨id B,id B⟩ ∘ x2 =
    ((SND (product B B)) o ⟨id B,id B⟩) ∘ x2’ by fs[] >>
    ‘((SND (product B B)) o ⟨id B,id B⟩) = (id B)’ by fs[] >>
    ‘((SND (product B B)) o ⟨id B,id B⟩) ∘ x2 = (id B) o x2’ by metis_tac[] >>
    ‘(SND (product B B)) o ⟨id B,id B⟩ ∘ x2 = x2’ by metis_tac[idL] >>
    ‘(SND (product B B)) o ⟨FST (product B X),b ∘ SND (product B X)⟩ ∘ x1 =
     ((SND (product B B)) o ⟨FST (product B X),b ∘ SND (product B X)⟩) ∘ x1’
      by fs[] >>
    ‘(SND (product B B)) o ⟨FST (product B X),b ∘ SND (product B X)⟩ =
      b ∘ SND (product B X)’ by fs[] >>
    ‘(SND (product B B)) o ⟨FST (product B X),b ∘ SND (product B X)⟩ ∘ x1 =
     (b ∘ SND (product B X)) o x1’ by metis_tac[] >>
    ‘FST (product B X) ∘ x1 = x2’ suffices_by metis_tac[] >>
    ‘(FST (product B B)) o ⟨FST (product B X),b ∘ SND (product B X)⟩ ∘ x1 =
    ((FST (product B B)) o ⟨FST (product B X),b ∘ SND (product B X)⟩) ∘ x1’
     by fs[] >>
    ‘(FST (product B B)) o ⟨FST (product B X),b ∘ SND (product B X)⟩ =
    FST (product B X)’ by fs[] >>
    ‘(FST (product B B)) o ⟨FST (product B X),b ∘ SND (product B X)⟩ ∘ x1 =
    FST (product B X) o x1’ by metis_tac[] >>
    ‘(FST (product B B)) o ⟨id B,id B⟩ ∘ x2 =
     (FST (product B B) o ⟨id B,id B⟩) ∘ x2’ by fs[] >>
    ‘(FST (product B B) o ⟨id B,id B⟩) = id B’ by fs[] >>
    metis_tac[idL]) >> 
‘x1 = ⟨b,id X⟩ ∘ SND (product B X) ∘ x1’ by
(irule product_component_eq >> simp[] >> map_every qexists_tac [‘B’,‘X’] >>
fs[] >>
‘FST (product B X) ∘ ⟨b,id X⟩ ∘ SND (product B X) ∘ x1 =
 (FST (product B X) ∘ ⟨b,id X⟩ ∘ SND (product B X)) ∘ x1’ by fs[] >>
‘(FST (product B X) ∘ ⟨b,id X⟩ ∘ SND (product B X)) =
 (FST (product B X) ∘ ⟨b,id X⟩) ∘ SND (product B X)’ by fs[] >>
‘(FST (product B X) ∘ ⟨b,id X⟩) = b’ by fs[] >>
‘FST (product B X) ∘ ⟨b,id X⟩ ∘ SND (product B X) ∘ x1 =
 (b o (SND (product B X))) o x1’ by metis_tac[] >>
‘FST (product B X) ∘ x1  = (b ∘ SND (product B X)) ∘ x1 ∧
 SND (product B X) ∘ x1 =
 SND (product B X) ∘ ⟨b,id X⟩ ∘ SND (product B X) ∘ x1’
suffices_by metis_tac[] >>
‘SND (product B X) ∘ x1 =
 SND (product B X) ∘ ⟨b,id X⟩ ∘ SND (product B X) ∘ x1’
 suffices_by metis_tac[] >>
‘SND (product B X) ∘ ⟨b,id X⟩ = id X’ by fs[] >>
‘SND (product B X) ∘ ⟨b,id X⟩ ∘ SND (product B X) ∘ x1 =
 (SND (product B X) ∘ ⟨b,id X⟩) ∘ SND (product B X) ∘ x1’ by fs[] >>
‘(SND (product B X) ∘ ⟨b,id X⟩) ∘ SND (product B X) ∘ x1 =
 (id X) o SND (product B X) o x1’ by metis_tac[] >>
‘(id X) o SND (product B X) o x1 = SND (product B X) o x1’ by fs[] >>
metis_tac[]) >>
‘(b ∘ SND (product B X)) ∘ x1 = b ∘ SND (product B X) o x1’ by 
  (irule compose_assoc >> rw[Abbr‘X’]) >>
fs[] >>
(*only remains the mono part*)
rpt strip_tac >> irule is_mono_applied >>
‘dom (SND (product B X) ∘ ⟨b,id X⟩ ∘ u') = dom (⟨b,id X⟩ ∘ u')’
  by fs[Abbr‘B’,Abbr‘X’] >>
‘dom (⟨b,id X⟩ ∘ u') = dom u'’ by fs[Abbr‘B’,Abbr‘X’] >>
‘∃f. is_mono f ∧ f ∘ SND (product B X) ∘ ⟨b,id X⟩ ∘ u' = f ∘ u' ∧
     cod (SND (product B X) ∘ ⟨b,id X⟩ ∘ u') = dom f ∧ cod u' = dom f’
 suffices_by metis_tac[] >> 
qexists_tac ‘⟨b,id X⟩’ >> fs[] >>
irule product_induce_is_mono >>
simp[] >> metis_tac[id_is_mono]
QED

Theorem pullback_side_by_side:
is_pullback a b (e,f) ∧ is_pullback c d (b,g) ⇒
is_pullback (c o a) d (e, g o f)
Proof
simp[is_pullback_def] >> strip_tac >>
‘c ∘ b ∘ f = (c o b) o f ∧ d o g o f = (d o g) o f’ by simp[] >>
‘∀x1 x2. dom x1 = dom x2 ∧ cod x1 = dom a ∧ cod x2 = dom d ∧
         (c ∘ a) ∘ x1 = d ∘ x2 ⇒
        ∃!u. dom u = dom x2 ∧ cod u = dom f ∧ x1 = e ∘ u ∧
             x2 = (g ∘ f) ∘ u’ suffices_by metis_tac[] >>
rpt strip_tac >>
first_x_assum (qspecl_then [‘a o x1’,‘x2’] mp_tac) >>
simp[] >> ‘(c ∘ a) ∘ x1 = c o a o x1’ by (irule compose_assoc >> simp[]) >>
fs[] >> simp[EXISTS_UNIQUE_ALT] >> rpt strip_tac >>
last_x_assum (qspecl_then [‘x1’,‘u’] mp_tac) >> simp[] >>
‘dom x2 = dom u ∧ cod u = dom g ∧ a ∘ x1 = b ∘ u’ by metis_tac[] >>
rw[EXISTS_UNIQUE_ALT] >> qexists_tac ‘u'’ >> simp[EQ_IMP_THM] >>
gen_tac >>
‘dom u' = dom u ∧ cod u' = dom f ∧ x1 = e ∘ u'’ by metis_tac[] >>
‘x2 = g ∘ u’ by metis_tac[] >>
‘u = f o u'’ by metis_tac[] >>
‘(g o f) o u' = g o f o u'’ by fs[] >>
‘dom u'' = dom u ∧ cod u'' = dom f ∧ x1 = e ∘ u'' ∧ x2 = (g ∘ f) ∘ u'' ⇒
 u' = u''’ suffices_by metis_tac[] >> rpt strip_tac >>
‘u = f o u''’ suffices_by metis_tac[] >>
‘dom (f o u'') = dom x2 ∧ cod (f o u'') = dom g ∧ a ∘ x1 = b ∘ (f o u'') ∧ x2 = g ∘ (f o u'')’
  suffices_by metis_tac[] >>
‘(g ∘ f) ∘ u'' = g ∘ f ∘ u''’ by (irule compose_assoc >> metis_tac[]) >>
‘a ∘ x1 = b ∘ f ∘ u''’ suffices_by fs[] >>
‘b ∘ f ∘ u'' = (b ∘ f) ∘ u''’ by fs[] >>
‘(b ∘ f) ∘ u'' = (a o e) o u''’ by metis_tac[]  >>
‘(a ∘ e) ∘ u'' = a o e o u''’ by fs[] >>
fs[]
QED

Theorem lemma1_paste:
∀b. is_pullback  ((char ⟨id (cod b),id (cod b)⟩) o
                 ⟨FST (product (cod b) (dom b)),b ∘ SND (product (cod b) (dom b))⟩)
                 true
                 (⟨b,id (dom b)⟩,(X2t (cod b)) o b)       
Proof
rw[] >> irule pullback_side_by_side >> qexists_tac ‘⟨id (cod b),id (cod b)⟩’ >> rw[] (* 2 *)
>- metis_tac[distribute_pullback] >>
‘is_mono ⟨id (cod b),id (cod b)⟩’
  by metis_tac[product_induce_is_mono,id_is_mono] >>
drule char_def >> rw[]
QED

Theorem diagonal_is_mono[simp]:
∀X. is_mono ⟨id X,id X⟩
Proof
metis_tac[id_is_mono,product_induce_is_mono]
QED

Theorem transpose_dom[simp]:
∀B A f.
         dom f = (B x A) ∧ cod f = omega ⇒
         dom (transpose f) = A
Proof
metis_tac[transpose_def]
QED

Theorem product_one_component:
∀B P Q R f g.
 dom f = P ∧ cod f = Q ∧ dom g = Q ∧ cod g = R ⇒
 ⟨FST (product B Q),g o (SND (product B Q))⟩ o ⟨FST (product B P),f o (SND (product B P))⟩ =
 ⟨FST (product B P), g o f o (SND (product B P))⟩
Proof
rpt strip_tac >> irule product_component_eq >> fs[] >>
map_every qexists_tac [‘B’,‘R’] >> simp[] >>
‘FST (product B R) ∘ ⟨FST (product B Q), g ∘ SND (product B Q)⟩ ∘
 ⟨FST (product B P),f ∘ SND (product B P)⟩ =
 (FST (product B R) ∘ ⟨FST (product B Q),g ∘ SND (product B Q)⟩) ∘
 ⟨FST (product B P),f ∘ SND (product B P)⟩’
by fs[] >>
‘(FST (product B R) ∘ ⟨FST (product B Q),g ∘ SND (product B Q)⟩) = FST (product B Q)’ by fs[] >>
‘FST (product B Q) o ⟨FST (product B P),f ∘ SND (product B P)⟩ = FST (product B P)’ by fs[] >>
fs[] >>
‘SND (product B R) ∘ ⟨FST (product B Q),g ∘ SND (product B Q)⟩ ∘
 ⟨FST (product B P),f ∘ SND (product B P)⟩ =
 (SND (product B R) ∘ ⟨FST (product B Q),g ∘ SND (product B Q)⟩) ∘
 ⟨FST (product B P),f ∘ SND (product B P)⟩’ by fs[] >>
‘(SND (product B R) ∘ ⟨FST (product B Q),g ∘ SND (product B Q)⟩) = g ∘ SND (product B Q)’ by fs[] >>
‘(g ∘ SND (product B Q)) o ⟨FST (product B P),f ∘ SND (product B P)⟩ =
 g o SND (product B Q) o ⟨FST (product B P),f ∘ SND (product B P)⟩’ by fs[] >>
‘SND (product B Q) o ⟨FST (product B P),f ∘ SND (product B P)⟩ = f ∘ SND (product B P)’ by fs[] >>
fs[]
QED


Theorem pullback_unique:
∀f g i1 j1 i2 j2.
    is_pullback f g (i1,j1) ∧ is_pullback f g (i2,j2) ⇒
    ∃!h. dom h = dom i2 ∧ cod h = dom i1 ∧ j1 o h = j2 ∧ i1 o h = i2 ∧ is_iso h
Proof
rw[is_pullback_def] >>
‘∃!u1. dom u1 = dom j2 ∧ cod u1 = dom j1 ∧ i2 = i1 ∘ u1 ∧ j2 = j1 ∘ u1’ by metis_tac[] >>
‘∃!u2. dom u2 = dom j1 ∧ cod u2 = dom j2 ∧ i1 = i2 ∘ u2 ∧ j1 = j2 ∘ u2’ by metis_tac[] >>
fs[EXISTS_UNIQUE_ALT] >> qexists_tac ‘u1’ >> fs[] >>
‘is_iso u1’ suffices_by metis_tac[] >>
simp[is_iso_def] >> qexists_tac ‘u2’ >>
‘u1 ∘ u2 = id (cod u1) ∧ u2 ∘ u1 = id (dom u1)’ suffices_by metis_tac[] >>
‘u2 ∘ u1 = id (dom u1)’
 by
 (‘∃u. ∀u'. dom u' = dom j2 ∧ cod u' = dom j2 ∧ i2 = i2 ∘ u' ∧ j2 = j2 ∘ u' ⇔ u = u'’
   by metis_tac[] >> 
  ‘dom (id (dom u1)) = dom j2 ∧ cod (id (dom u1)) = dom j2 ∧ i2 = i2 ∘ (id (dom u1)) ∧
   j2 = j2 ∘ (id (dom u1)) ⇔ u = id (dom u1)’ by fs[] >>
  ‘dom u1 = dom j2 ∧ dom u1 = dom j2 ∧ i2 = i2 ∘ id (dom u1) ∧ j2 = j2 ∘ id (dom u1)’
    by metis_tac[idR,id1] >> 
  ‘dom (u2 o u1) = dom j2 ∧ cod (u2 o u1) = dom j2 ∧ i2 = i2 ∘ (u2 o u1) ∧ j2 = j2 ∘ (u2 o u1)’
    suffices_by metis_tac[idR,id1] >>
  ‘j2 = j2 ∘ u2 ∘ u1’
    by (‘j2 o u2 = j1 ∧ j1 o u1 = j2’ by metis_tac[] >>
        ‘cod u1 = dom u2’ by metis_tac[] >>
        ‘cod u2 = dom j2’ by metis_tac[] >>
        ‘j2 ∘ u2 ∘ u1 = (j2 ∘ u2) ∘ u1’ by fs[] >>
        metis_tac[]) >>
  ‘i2 = i2 ∘ u2 ∘ u1’
    by (‘i2 o u2 = i1 ∧ i1 o u1 = i2’ by metis_tac[] >>
        ‘cod u1 = dom u2’ by metis_tac[] >>
        ‘cod u2 = dom i2’ by metis_tac[] >>
        ‘i2 ∘ u2 ∘ u1 = (i2 ∘ u2) ∘ u1’ by fs[] >>
        metis_tac[]) >>
  metis_tac[compose]) >>
fs[] >>
‘∃u. ∀u'. dom u' = dom j1 ∧ cod u' = dom j1 ∧ i1 = i1 ∘ u' ∧ j1 = j1 ∘ u' ⇔ u = u'’ by metis_tac[]>>
‘dom (id (cod u1)) = dom j1 ∧ cod (id (cod u1)) = dom j1 ∧ i1 = i1 ∘ (id (cod u1)) ∧
 j1 = j1 ∘ (id (cod u1)) ⇔ u =  id (cod u1)’ by metis_tac[] >>
‘dom (id (cod u1)) = dom j1 ∧ cod (id (cod u1)) = dom j1’ by metis_tac[id1] >> 
‘i1 = i1 ∘ (id (cod u1)) ∧ j1 = j1 ∘ (id (cod u1))’ by fs[] >>
‘dom (u1 o u2) = dom j1 ∧ cod (u1 o u2) = dom j1 ∧ i1 = i1 ∘ u1 o u2 ∧ j1 = j1 ∘ u1 o u2’
 suffices_by metis_tac[] >>
‘i1 = i1 ∘ u1 ∘ u2 ∧ j1 = j1 ∘ u1 ∘ u2’ suffices_by metis_tac[compose] >>
‘i1 o u1 = i2 ∧ i2 o u2 = i1’ by metis_tac[] >> 
‘j1 o u1 = j2 ∧ j2 o u2 = j1’ by metis_tac[] >>
metis_tac[compose_assoc,compose]
QED

Theorem product_right_compose_eq:
∀B X h b b'. dom h = X ∧ cod h = X ∧ dom b  = X ∧ cod b = B ∧ dom b' = X ∧ cod b' = B ∧ ⟨b', id X⟩ o h = ⟨b , id X⟩ ⇒  b = b'
Proof
rpt strip_tac >>
‘(FST (product B X)) o ⟨b',id (dom b')⟩ ∘ h = (FST (product B X)) o ⟨b,id (dom b')⟩’ by fs[] >>
‘FST (product B X) ∘ ⟨b',id (dom b')⟩ ∘ h = (FST (product B X) ∘ ⟨b',id (dom b')⟩) ∘ h ’ by fs[] >>
‘(FST (product B X) ∘ ⟨b',id (dom b')⟩) = b'’ by fs[] >>
‘FST (product B X) ∘ ⟨b,id (dom b')⟩ = b’ by fs[] >>
‘b = b' o h’ by metis_tac[] >>
‘h = id X’ suffices_by metis_tac[idR] >>
‘(SND (product B X)) o ⟨b',id X⟩ ∘ h = (SND (product B X)) o ⟨b,id X⟩’ by metis_tac[] >>
‘(SND (product B X)) o ⟨b',id X⟩ ∘ h = h’
  by (‘(SND (product B X)) o ⟨b',id X⟩ ∘ h = ((SND (product B X)) o ⟨b',id X⟩) ∘ h’ by simp[] >>
      ‘((SND (product B X)) o ⟨b',id X⟩) = id X’ by simp[] >>
      metis_tac[idL]) >>
‘(SND (product B X)) o ⟨b,id X⟩ = id X’ by fs[] >> metis_tac[]
QED

    
Theorem singleton_is_mono:
∀B. is_mono (transpose (char (product_induce (id B) (id B))))
Proof
rw[] >> 
‘is_mono ⟨id B,id B⟩’ by fs[] >> 
‘dom ⟨id B,id B⟩ = B ∧ cod ⟨id B, id B⟩ = (B x B)’ by fs[] >>
‘dom (char ⟨id B,id B⟩) = (B x B) ∧ cod (char ⟨id B,id B⟩) = omega’ by fs[] >>
‘dom (transpose (char ⟨id B,id B⟩)) = B’ by metis_tac[transpose_def] >>
‘cod (transpose (char ⟨id B,id B⟩)) = pow B’ by metis_tac[transpose_def] >>
rw[is_mono_def] >>
qabbrev_tac ‘X = dom g2’ >> qabbrev_tac ‘B = cod g2’ >>
‘char ⟨id B,id B⟩ =
 (mem B) o ⟨FST (product B B), transpose (char ⟨id B,id B⟩) o (SND (product B B))⟩’ by fs[] >>
‘((char ⟨id B,id B⟩) ∘
 ⟨FST (product B X),g1 ∘ SND (product B X)⟩) =
 ((char ⟨id B,id B⟩) ∘
 ⟨FST (product B X),g2 ∘ SND (product B X)⟩)’
by
 (‘(char ⟨id B,id B⟩) ∘
   ⟨FST (product B X),g1 ∘ SND (product B X)⟩ =
   (mem B) o ⟨FST (product B X), (transpose (char ⟨id B,id B⟩)) o g1 o (SND (product B X))⟩’
   by
    (‘((mem B) o ⟨FST (product B B), transpose (char ⟨id B,id B⟩) o (SND (product B B))⟩) o
      ⟨FST (product B X),g1 ∘ SND (product B X)⟩ =
      (mem B) o ⟨FST (product B X),transpose (char ⟨id B,id B⟩) ∘ g1 ∘ SND (product B X)⟩’
      suffices_by metis_tac[] >>
     ‘((mem B) o ⟨FST (product B B), transpose (char ⟨id B,id B⟩) o (SND (product B B))⟩) o
      ⟨FST (product B X),g1 ∘ SND (product B X)⟩ =
      (mem B) o ⟨FST (product B B), transpose (char ⟨id B,id B⟩) o (SND (product B B))⟩ o
      ⟨FST (product B X),g1 ∘ SND (product B X)⟩’ by fs[] >>
     ‘⟨FST (product B B),transpose (char ⟨id B,id B⟩) ∘ SND (product B B)⟩ ∘
      ⟨FST (product B X),g1 ∘ SND (product B X)⟩ =
      ⟨FST (product B X),transpose (char ⟨id B,id B⟩) ∘ g1 ∘ SND (product B X)⟩’
      by metis_tac[product_one_component] >>
     fs[]) >>
   ‘(char ⟨id B,id B⟩) ∘
   ⟨FST (product B X),g2 ∘ SND (product B X)⟩ =
   (mem B) o ⟨FST (product B X), (transpose (char ⟨id B,id B⟩)) o g2 o (SND (product B X))⟩’
   by
    (‘((mem B) o ⟨FST (product B B), transpose (char ⟨id B,id B⟩) o (SND (product B B))⟩) o
      ⟨FST (product B X),g2 ∘ SND (product B X)⟩ =
      (mem B) o ⟨FST (product B X),transpose (char ⟨id B,id B⟩) ∘ g2 ∘ SND (product B X)⟩’
      suffices_by metis_tac[] >>
     ‘((mem B) o ⟨FST (product B B), transpose (char ⟨id B,id B⟩) o (SND (product B B))⟩) o
      ⟨FST (product B X),g2 ∘ SND (product B X)⟩ =
      (mem B) o ⟨FST (product B B), transpose (char ⟨id B,id B⟩) o (SND (product B B))⟩ o
      ⟨FST (product B X),g2 ∘ SND (product B X)⟩’ by fs[] >>
     ‘⟨FST (product B B),transpose (char ⟨id B,id B⟩) ∘ SND (product B B)⟩ ∘
      ⟨FST (product B X),g2 ∘ SND (product B X)⟩ =
      ⟨FST (product B X),transpose (char ⟨id B,id B⟩) ∘ g2 ∘ SND (product B X)⟩’
      by metis_tac[product_one_component] >>
     fs[]) >>
   ‘transpose (char ⟨id B,id B⟩) ∘ g1 ∘ SND (product B X) =
    (transpose (char ⟨id B,id B⟩) ∘ g1) ∘SND (product B X) ∧
    transpose (char ⟨id B,id B⟩) ∘ g2 ∘ SND (product B X) =
    (transpose (char ⟨id B,id B⟩) ∘ g2) ∘SND (product B X)’ by fs[] >>
   metis_tac[]) >>
‘is_pullback
     (char ⟨id B,id B⟩ ∘
     ⟨FST (product B X),g1 ∘ SND (product B X)⟩)
     true (⟨g1,id X⟩,X2t B ∘ g1)’ by metis_tac[lemma1_paste] >>
‘is_pullback
     (char ⟨id B,id B⟩ ∘
     ⟨FST (product B X),g2 ∘ SND (product B X)⟩)
     true (⟨g2,id X⟩,X2t B ∘ g2)’ by metis_tac[lemma1_paste] >>
‘is_pullback
     (char ⟨id B,id B⟩ ∘ ⟨FST (product B X),g1 ∘ SND (product B X)⟩)
     true (⟨g2,id X⟩,X2t B ∘ g2)’ by metis_tac[] >>
‘∃h. dom h = dom ⟨g1,id X⟩ ∧ cod h = dom ⟨g2,id X⟩ ∧ ⟨g2,id X⟩ o h = ⟨g1,id X⟩’
 by metis_tac[pullback_unique,EXISTS_UNIQUE_ALT] >>
irule  product_right_compose_eq >> simp[] >> qexists_tac ‘h’ >> simp[]
QED


(*need lemma pullback of mono is mono*)
(*
Theorem transpose_true_mono:
∀B. is_mono (transpose (true o (X2t B) o (FST (product B terminal)))) =      
*)

Theorem product_induce_component_eq:
∀f g i j. dom f = dom g ∧
          f = i ∧ g = j ⇒
⟨f,g⟩ = ⟨i,j⟩
Proof        
rw[]
QED

Theorem time_with_square:
∀a b c d A B C D X. dom a = A ∧ cod a = B ∧ dom b = B ∧ cod b = D ∧ dom c = C ∧ cod c = D ∧
                    dom d = A ∧ cod d = C ∧ c o d = b o a ⇒
                    ((id X) × c) o ((id X) × d) = ((id X) × b) o ((id X) × a)
Proof   
rw[] >> irule product_component_eq >> simp[] >> map_every qexists_tac[‘X’,‘cod c’] >> simp[] >>
rw[] (* 2 *)
>- (‘FST (product X (cod c)) ∘
        ⟨FST (product X (cod d)),c ∘ SND (product X (cod d))⟩ =
    FST (product X (cod d))’ by fs[] >>
   ‘FST (product X (cod d)) o ⟨FST (product X (dom d)),d ∘ SND (product X (dom d))⟩ =
    FST (product X (dom d))’ by fs[] >>
   ‘FST (product X (cod c)) ∘
        ⟨FST (product X (cod d)),c ∘ SND (product X (cod d))⟩ ∘
        ⟨FST (product X (dom d)),d ∘ SND (product X (dom d))⟩ =
    (FST (product X (cod c)) ∘
        ⟨FST (product X (cod d)),c ∘ SND (product X (cod d))⟩) ∘
        ⟨FST (product X (dom d)),d ∘ SND (product X (dom d))⟩’ by fs[] >>
   ‘FST (product X (cod c)) ∘
    ⟨FST (product X (cod d)),c ∘ SND (product X (cod d))⟩ ∘
    ⟨FST (product X (dom d)),d ∘ SND (product X (dom d))⟩ =  FST (product X (dom d))’
         by metis_tac[] >>
   ‘FST (product X (cod c)) ∘
        ⟨FST (product X (dom b)),b ∘ SND (product X (dom b))⟩ = FST (product X (dom b))’ by fs[] >>
   ‘FST (product X (dom b)) o ⟨FST (product X (dom d)),a ∘ SND (product X (dom d))⟩ =
   FST (product X (dom d))’ by fs[] >>
   ‘FST (product X (cod c)) ∘
        ⟨FST (product X (dom b)),b ∘ SND (product X (dom b))⟩ ∘
        ⟨FST (product X (dom d)),a ∘ SND (product X (dom d))⟩ =
    (FST (product X (cod c)) ∘
        ⟨FST (product X (dom b)),b ∘ SND (product X (dom b))⟩) ∘
        ⟨FST (product X (dom d)),a ∘ SND (product X (dom d))⟩’ by fs[] >>
   metis_tac[]) >>
‘SND (product X (cod c)) ∘
        ⟨FST (product X (cod d)),c ∘ SND (product X (cod d))⟩ ∘
        ⟨FST (product X (dom d)),d ∘ SND (product X (dom d))⟩ =
 (SND (product X (cod c)) ∘
        ⟨FST (product X (cod d)),c ∘ SND (product X (cod d))⟩) ∘
        ⟨FST (product X (dom d)),d ∘ SND (product X (dom d))⟩’ by fs[] >>
‘SND (product X (cod c)) ∘
 ⟨FST (product X (cod d)),c ∘ SND (product X (cod d))⟩ = c ∘ SND (product X (cod d))’ by fs[] >>
‘(c ∘ SND (product X (cod d))) o ⟨FST (product X (dom d)),d ∘ SND (product X (dom d))⟩ =
 c o SND (product X (cod d)) o ⟨FST (product X (dom d)),d ∘ SND (product X (dom d))⟩’ by fs[] >>
‘SND (product X (cod d)) o ⟨FST (product X (dom d)),d ∘ SND (product X (dom d))⟩ =
 d ∘ SND (product X (dom d))’ by fs[] >>
‘SND (product X (cod c)) ∘
        ⟨FST (product X (cod d)),c ∘ SND (product X (cod d))⟩ ∘
        ⟨FST (product X (dom d)),d ∘ SND (product X (dom d))⟩ = c o d o SND (product X (dom d))’
 by metis_tac[] >>
‘SND (product X (cod c)) ∘
        ⟨FST (product X (dom b)),b ∘ SND (product X (dom b))⟩ ∘
        ⟨FST (product X (dom d)),a ∘ SND (product X (dom d))⟩ =
 (SND (product X (cod c)) ∘
        ⟨FST (product X (dom b)),b ∘ SND (product X (dom b))⟩) ∘
        ⟨FST (product X (dom d)),a ∘ SND (product X (dom d))⟩’ by fs[] >>
‘(SND (product X (cod c)) ∘
        ⟨FST (product X (dom b)),b ∘ SND (product X (dom b))⟩) = b ∘ SND (product X (dom b))’
 by fs[] >>
‘SND (product X (cod c)) ∘
        ⟨FST (product X (dom b)),b ∘ SND (product X (dom b))⟩ ∘
        ⟨FST (product X (dom d)),a ∘ SND (product X (dom d))⟩ =
 b ∘ SND (product X (dom b)) o ⟨FST (product X (dom d)),a ∘ SND (product X (dom d))⟩’ by fs[] >>
‘SND (product X (dom b)) o ⟨FST (product X (dom d)),a ∘ SND (product X (dom d))⟩ =
a ∘ SND (product X (dom d))’ by fs[] >>
‘SND (product X (cod c)) ∘
        ⟨FST (product X (dom b)),b ∘ SND (product X (dom b))⟩ ∘
        ⟨FST (product X (dom d)),a ∘ SND (product X (dom d))⟩ = b o a o SND (product X (dom d))’ by fs[] >>
‘(c ∘ d) ∘ SND (product X (dom d)) = c ∘ d ∘ SND (product X (dom d)) ∧ 
(b ∘ a) ∘ SND (product X (dom d)) = b ∘ a ∘ SND (product X (dom d))’ suffices_by metis_tac[] >>
rw[]
QED

Theorem transpose_121:
∀A B f g. dom f = dom g ∧ cod f = cod g ∧ dom f = A ∧ cod f = pow B ⇒
          (f = g ⇔ (mem B) o ((id B) × f) = (mem B) o ((id B) × g))
Proof
simp[EQ_IMP_THM] >> rw[] >>
‘dom (mem B ∘ ⟨FST (product B (dom g)),f ∘ SND (product B (dom g))⟩) = (B x (dom f))’ by fs[] >>
‘cod (mem B ∘ ⟨FST (product B (dom g)),f ∘ SND (product B (dom g))⟩) = omega’ by fs[] >>
metis_tac[mem_def]
QED
  
Theorem cross_id_compose:
∀A B C D f g. dom f = B ∧ cod f = C ∧ dom g = C ∧ cod g = D ⇒
(id A × (g o f)) = (id A × g) o (id A × f)
Proof
rw[] >>
irule product_component_eq >> simp[] >> map_every qexists_tac [‘A’,‘cod g’] >> simp[] >>
‘FST (product A (cod g)) ∘ ⟨FST (product A (dom f)),g ∘ f ∘ SND (product A (dom f))⟩ =
 FST (product A (dom f))’ by fs[] >>
‘SND (product A (cod g)) ∘ ⟨FST (product A (dom f)),g ∘ f ∘ SND (product A (dom f))⟩ =
 g ∘ f ∘ SND (product A (dom f))’ by fs[] >>
fs[] >>
‘FST (product A (cod g)) ∘
        ⟨FST (product A (dom g)),g ∘ SND (product A (dom g))⟩ = FST (product A (dom g))’ by fs[] >>
‘FST (product A (cod g)) ∘
        ⟨FST (product A (dom g)),g ∘ SND (product A (dom g))⟩ ∘
        ⟨FST (product A (dom f)),f ∘ SND (product A (dom f))⟩ =
 (FST (product A (cod g)) ∘
        ⟨FST (product A (dom g)),g ∘ SND (product A (dom g))⟩) ∘
        ⟨FST (product A (dom f)),f ∘ SND (product A (dom f))⟩’ by fs[] >>
‘FST (product A (cod g)) ∘
        ⟨FST (product A (dom g)),g ∘ SND (product A (dom g))⟩ ∘
        ⟨FST (product A (dom f)),f ∘ SND (product A (dom f))⟩ =
 FST (product A (dom g)) o ⟨FST (product A (dom f)),f ∘ SND (product A (dom f))⟩’ by metis_tac[] >>
‘FST (product A (dom g)) o ⟨FST (product A (dom f)),f ∘ SND (product A (dom f))⟩ =
 FST (product A (dom f))’ by fs[] >>
rw[] >>
‘SND (product A (cod g)) ∘
     ⟨FST (product A (dom g)),g ∘ SND (product A (dom g))⟩ ∘
     ⟨FST (product A (dom f)),f ∘ SND (product A (dom f))⟩ =
 (SND (product A (cod g)) ∘
        ⟨FST (product A (dom g)),g ∘ SND (product A (dom g))⟩) ∘
        ⟨FST (product A (dom f)),f ∘ SND (product A (dom f))⟩’ by fs[] >>
‘(SND (product A (cod g)) ∘
        ⟨FST (product A (dom g)),g ∘ SND (product A (dom g))⟩) = g ∘ SND (product A (dom g))’
  by fs[] >>
‘SND (product A (cod g)) ∘
     ⟨FST (product A (dom g)),g ∘ SND (product A (dom g))⟩ ∘
     ⟨FST (product A (dom f)),f ∘ SND (product A (dom f))⟩ =
 (g ∘ SND (product A (dom g))) o ⟨FST (product A (dom f)),f ∘ SND (product A (dom f))⟩’
 by metis_tac[] >>
‘(g ∘ SND (product A (dom g))) o ⟨FST (product A (dom f)),f ∘ SND (product A (dom f))⟩ =
 g ∘ SND (product A (dom g)) o ⟨FST (product A (dom f)),f ∘ SND (product A (dom f))⟩’ 
 by (irule compose_assoc >> simp[]) >>
‘SND (product A (dom g)) o ⟨FST (product A (dom f)),f ∘ SND (product A (dom f))⟩ =
f ∘ SND (product A (dom f))’ by fs[]>>
metis_tac[]
QED

Theorem transpose_times_notation:
∀B A f. dom f = (B x A) ∧ cod f = omega ⇒
        mem B ∘ ((id B) × (transpose f)) = f
Proof
rw[] >> metis_tac[transpose_def]
QED
                  
Theorem exponential_exists:
∀B C. ∃B2C e.
        dom e = dom (SND (product B B2C)) ∧ cod e = C ∧
        ∀f A. dom f = dom (SND (product B A)) ∧ cod f = C ⇒
            ∃!g. dom g = A ∧ cod g = B2C ∧
                 f = e o ⟨FST (product B A), g o (SND (product B A))⟩
Proof
rw[] >>
‘is_mono (transpose (char ⟨id C,id C⟩))’ by metis_tac[singleton_is_mono] >>
qabbrev_tac ‘δ = char ⟨id C, id C⟩’ >>
qabbrev_tac ‘dot = transpose δ’ >>
drule char_def >> strip_tac >>
qabbrev_tac ‘σ = char dot’ >>
qabbrev_tac ‘htb = transpose (true o (X2t (B x terminal)))’ >>
qabbrev_tac ‘v = transpose (mem (C x B))’ >>
qabbrev_tac ‘u = transpose (σ ∘ v)’ >>
‘dom δ = (C x C)’ by cheat >>
‘cod δ = omega’ by cheat >>
‘dom dot = C’ by cheat >>
‘cod dot = pow C’ by cheat >>
‘dom σ = pow C’ by cheat >>
‘dom htb = terminal’ by cheat >>
‘cod htb = pow B’ by cheat >>
‘dom v = (B x (pow (C x B)))’ by cheat >>
‘cod v = pow C’ by cheat >>
‘dom u = pow (C x B)’ by cheat >>
‘cod u = pow B’ by cheat >>
drule (is_pullback_def |> SPEC_ALL |> EQ_IMP_RULE |> #1) >> simp[] >> rpt strip_tac >>
‘∃m. is_pullback u htb (m,(X2t BC))’ by cheat >>
drule (is_pullback_def |> SPEC_ALL |> EQ_IMP_RULE |> #1) >> simp[] >> rpt strip_tac >>
‘(mem B) o ⟨FST (product B (pow (C x B))), u o (SND (product B (pow (C x B))))⟩ = σ o v’
  by fs[transpose_def,Abbr‘u’] >>
‘(id B × u) o (id B × m) = (id B × htb) o (id B × (X2t BC))’
 by (irule time_with_square >> simp[]) >>
‘(mem B) o ((id B) × htb) = true o (X2t (B x terminal))’
 by simp[Abbr‘htb’] >>
‘true o (X2t (B x terminal)) o ((id B) × (X2t BC)) =
 σ o v o ((id B) × m)’
by
 (‘true ∘ X2t (B x terminal) ∘ (id B×X2t BC) =
   (true ∘ X2t (B x terminal)) ∘ (id B×X2t BC) ∧
   σ ∘ v ∘ (id B×m) = (σ ∘ v) ∘ (id B×m)’ by fs[] >>
  ‘(true ∘ X2t (B x terminal)) ∘ (id B×X2t BC) = (σ ∘ v) ∘ (id B×m)’ suffices_by metis_tac[] >>
  ‘(mem B ∘ (id B×htb)) o (id B×X2t BC)  = (σ ∘ v) ∘ (id B×m)’ suffices_by metis_tac[] >>
  ‘(mem B ∘ (id B×htb)) o (id B×X2t BC)  = (mem B ∘
        ⟨FST (product B (pow (C x B))),u ∘ SND (product B (pow (C x B)))⟩) ∘ (id B×m)’
   suffices_by metis_tac[] >>
  ‘(mem B ∘ (id B×htb)) ∘ (id B×X2t BC) = mem B ∘ (id B×htb) ∘ (id B×X2t BC)’ by fs[] >>
  ‘(mem B ∘
         ⟨FST (product B (pow (C x B))),u ∘ SND (product B (pow (C x B)))⟩) ∘
        (id B×m) =
   mem B ∘
         ⟨FST (product B (pow (C x B))),u ∘ SND (product B (pow (C x B)))⟩ ∘
        (id B×m)’ by fs[] >>
  ‘(id B×htb) ∘ (id B×X2t BC) = ⟨FST (product B (pow (C x B))),u ∘ SND (product B (pow (C x B)))⟩ ∘
        (id B×m)’ suffices_by metis_tac[] >>
  ‘⟨FST (product B (pow (C x B))),u ∘ SND (product B (pow (C x B)))⟩ =
   (id B × u)’ by simp[] >>
  metis_tac[time_with_square]) >>
last_x_assum (qspecl_then [‘v ∘ (id B×m)’,‘X2t (B x terminal) ∘ (id B×X2t BC)’] mp_tac) >>
simp[EXISTS_UNIQUE_ALT] >> strip_tac >>
rename [‘∀u''.
            dom u'' = (B x BC) ∧ cod u'' = C ∧
            v ∘ ⟨FST (product B BC),m ∘ SND (product B BC)⟩ = dot ∘ u'' ∧
            X2t (B x terminal) ∘
            ⟨FST (product B BC),X2t BC ∘ SND (product B BC)⟩ =
            X2t C ∘ u'' ⇔ e = u''’] >>
map_every qexists_tac [‘BC’,‘e’] >>
‘∀f A. dom f = (B x A) ∧ cod f = C ⇒
        ∃g.
           ∀g'.
               dom g' = A ∧ cod g' = BC ∧
               f = e ∘ ⟨FST (product B A),g' ∘ SND (product B A)⟩ ⇔
               g = g'’ suffices_by metis_tac[] >>
rpt strip_tac >>
‘(mem C ∘ (id C×dot)) = δ’ by simp[Abbr‘dot’] >>
‘dom (mem (C x B)) = (C x (B x pow (C x B)))’
  by simp[product_assoc] >>
‘mem (C x B) = (mem C) o ((id C) × v)’ by (simp[] >> fs[Abbr‘v’]) >>




     
‘∀g. dom g = A ∧ cod g = BC ⇒
     (f = e ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩ ⇔
     δ o (id C × f) = mem (C x B) o (id C × (id B × m o g)))’
by
 (rpt strip_tac >>
  ‘dom ⟨FST (product B A),g ∘ SND (product B A)⟩ = (B x A)’ by fs[] >>
  ‘cod ⟨FST (product B A),g ∘ SND (product B A)⟩ = (B x BC)’ by fs[] >>
  ‘dom e = (B x BC) ∧ cod e = C’ by metis_tac[] >>
  ‘cod (e ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩) = C’ by fs[] >>
  ‘dom (e ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩) = (B x A)’ by fs[] >>
  ‘f = e ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩ ⇔
  dot o f = dot o e ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩’
   by metis_tac[is_mono_def] >>
  ‘dom e = (B x BC) ∧ cod e = C’ by metis_tac[] >>
  ‘dot ∘ f = dot ∘ e ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩ ⇔
   (mem C) o ((id C) × (dot ∘ f)) =
   (mem C) o ((id C) ×dot ∘ e ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩)’
    by (irule transpose_121 >> simp[]) >>
  ‘mem C ∘ (id C×dot ∘ f) =  δ ∘ (id C×f) ∧
   mem C ∘ (id C×dot ∘ e ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩) =
   mem (C x B) ∘ (id C×(id B×m ∘ g))’ suffices_by metis_tac[] >>
  ‘(id C×dot ∘ f) = (id C×dot) o (id C× f)’
    by (irule cross_id_compose >> simp[]) >>
  ‘mem C ∘ (id C×dot ∘ f) = mem C o (id C×dot) o (id C× f)’ by metis_tac[] >>
  ‘mem C o (id C×dot) o (id C× f) = (mem C o (id C×dot)) o (id C× f)’ by fs[] >>
  ‘mem C ∘ (id C×dot ∘ e ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩) =
   mem (C x B) ∘ (id C×(id B×m ∘ g))’ suffices_by metis_tac[] >>
  ‘dot ∘ e = v o ⟨FST (product B BC),m ∘ SND (product B BC)⟩’ by metis_tac[] >>
  ‘⟨FST (product B BC),m ∘ SND (product B BC)⟩ = (id B × m)’ by simp[] >>
  ‘dot ∘ e ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩ =
   (dot ∘ e) ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩’ by fs[] >> 
  ‘mem C ∘ (id C× dot ∘ e ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩) =
   mem C ∘ (id C× (dot ∘ e) ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩)’ by metis_tac[] >>
  ‘mem C ∘ (id C× (v o (id B × m)) ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩) =
   mem (C x B) ∘ (id C×(id B×m ∘ g))’ suffices_by metis_tac[] >> 
  ‘(v ∘ (id B×m)) ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩ =
   v ∘ (id B×m) ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩’
     by (irule compose_assoc >>
        ‘cod (id B×m) = (B x (pow (C x B)))’ by simp[] >> simp[]) >>
  ‘mem C ∘
        (id C× v ∘ (id B×m) ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩) =
        mem (C x B) ∘ (id C×(id B×m ∘ g))’ suffices_by metis_tac[] >>
  ‘(id C×v ∘ (id B×m) ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩) =
   (id C×v) ∘ (id C × (id B×m) ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩)’
       (irule cross_id_compose >>
       ‘cod ((id B×m) ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩) = dom v’
        suffices_by  metis_tac[cross_id_compose] >> simp[]) >>
  ‘mem C ∘ (id C×v) ∘ (id C × (id B×m) ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩) =
   mem (C x B) ∘ (id C×(id B×m ∘ g))’ suffices_by metis_tac[] >>
  ‘(mem C ∘ (id C×v)) ∘
        (id C×(id B×m) ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩) =
   mem C ∘ (id C×v) ∘
        (id C×(id B×m) ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩)’
     by (irule compose_assoc >>
        ‘cod (id C×v) = dom (mem C)’ by fs[] >>
        ‘cod (id C×(id B×m) ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩) = (C x (B x pow (C x B))) ∧
        dom (id C×v) = (C x (B x pow (C x B)))’ suffices_by metis_tac[] >>
        cheat (*prove the codomain later... as a lemma*)) >>
   ‘(mem (C x B)) ∘
    (id C×(id B×m) ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩) =
     mem (C x B) ∘ (id C×(id B×m ∘ g))’ suffices_by metis_tac[] >>
   ‘(id C×(id B×m) ∘ ⟨FST (product B A),g ∘ SND (product B A)⟩) = (id C×(id B×m ∘ g))’
    suffices_by metis_tac[] >>
   cheat (*lemma later*)) >>






   
qabbrev_tac ‘h = transpose (δ o (id C × f))’ >>
‘∃g. h = m o g’
 suffices_by
  (rw[] >> qexists_tac ‘g’ >> rw[] >> cheat (*later..*))
‘htb o (X2t A) = u o h’
 suffices_by
   (strip_tac >> last_x_assum (qspecl_then [‘h’,‘X2t A’] mp_tac) >> simp[EXISTS_UNIQUE_ALT] >>
    rpt strip_tac >>
    ‘dom h = A ∧ cod h = pow (cod f x B)’ suffices_by metis_tac[] >>
    simp[Abbr‘h’,transpose_def] >>
    ‘dom (δ ∘ ⟨FST (product C (B x A)),f ∘ SND (product C (B x A))⟩) = ((C x B) x A) ∧
    cod (δ ∘ ⟨FST (product C (B x A)),f ∘ SND (product C (B x A))⟩) = omega’
     suffices_by metis_tac[transpose_def] >> simp[product_assoc]) >>
‘dom h = A ∧ cod h = pow (C x B)’ by cheat >> 
‘dom (htb ∘ X2t A) = dom (u ∘ h)’ by fs[] >>
drule transpose_121 >> simp[] >> strip_tac >>
‘mem B ∘ ⟨FST (product B A),htb ∘ X2t A ∘ SND (product B A)⟩ =
 mem B ∘ ⟨FST (product B A),u ∘ h ∘ SND (product B A)⟩’ suffices_by metis_tac[] >>
‘⟨FST (product B A),(htb ∘ X2t A) ∘ SND (product B A)⟩ = (id B × (htb o X2t A))’ by fs[] >>
‘(htb ∘ X2t A) ∘ SND (product B A) = htb ∘ X2t A ∘ SND (product B A)’ by fs[] >>
‘(id B×htb ∘ X2t A) = (id B × htb) o (id B × X2t A)’
 by (irule cross_id_compose >> simp[]) >>
‘mem B ∘ ⟨FST (product B A),htb ∘ X2t A ∘ SND (product B A)⟩  =
 mem B ∘ (id B × htb) o (id B × X2t A)’ by metis_tac[] >>
‘mem B ∘ (id B × htb) o (id B × X2t A) = (mem B ∘ (id B × htb)) o (id B × X2t A)’ by fs[] >>
‘(mem B ∘ (id B×htb)) = (true ∘ X2t (B x terminal))’ by simp[Abbr‘htb’,transpose_def] >>
‘⟨FST (product B A),u ∘ h ∘ SND (product B A)⟩ = (id B × (u o h))’ by fs[] >>
‘(true ∘ X2t (B x terminal)) o  (id B×X2t A) = mem B ∘ (id B × (u o h))’ suffices_by metis_tac[] >>
‘(id B×u ∘ h) = (id B×u) o (id B×h)’ by (irule cross_id_compose >> simp[]) >>
‘mem B ∘  (id B×u) ∘ (id B×h) = (mem B o (id B×u)) ∘ (id B×h)’ by fs[] >>
‘(mem B o (id B×u)) = σ o v’ by simp[Abbr‘u’,transpose_def] >>
‘(true ∘ X2t (B x terminal)) ∘ (id B×X2t A) = mem B ∘ (id B×u ∘ h)’ suffices_by metis_tac[]
‘(true ∘ X2t (B x terminal)) ∘ (id B×X2t A) = (σ ∘ v) o (id B×h)’ suffices_by metis_tac[] >>
‘(true ∘ X2t (B x terminal)) ∘ (id B×X2t A) = true o (X2t C) o f’
by
 (‘X2t (B x terminal) o  (id B×X2t A) = (X2t C) o f’
   by (‘dom (X2t (B x terminal) o  (id B×X2t A)) = dom ((X2t C) o f)’ by simp[] >>
       ‘cod (X2t (B x terminal) o  (id B×X2t A)) = cod ((X2t C) o f)’ by simp[] >>
       ‘cod (X2t (B x terminal) o  (id B×X2t A)) = terminal’ by simp[] >>
       metis_tac[EXISTS_UNIQUE_ALT,terminal_def])  >>
  ‘(true ∘ X2t (B x terminal)) ∘ (id B×X2t A)  = true ∘ X2t (B x terminal) ∘ (id B×X2t A)’
    by fs[] >>
  metis_tac[]) >>
‘true ∘ X2t C ∘ f = (σ ∘ v) ∘ (id B×h)’ suffices_by metis_tac[] >>
‘true ∘ X2t C = σ o dot’ by metis_tac[] >>
‘true ∘ X2t C ∘ f = (true o X2t C) ∘ f’ by fs[] >>
‘(σ ∘ dot) o f = (σ ∘ v) ∘ (id B×h)’ suffices_by metis_tac[] >>
‘(σ o dot) o f = σ o dot o f’ by fs[] >>
‘(σ ∘ v) ∘ (id B×h) = σ ∘ v ∘ (id B×h)’ by fs[] >>
‘dot ∘ f = v ∘ (id B×h)’ suffices_by metis_tac[] >>
(*just repeat the old thing....*)



 --------------




Theorem 
